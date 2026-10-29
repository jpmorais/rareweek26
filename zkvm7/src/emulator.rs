// emulator.rs — the prover OUTSIDE the circuit.
//
// Runs the program and produces the honest trace. Two phases:
//   (1) chronological execution: state, datapath, 32-bit auxiliaries, and the
//       per-row memory access (mem_*).
//   (2) memory witness: sort the active accesses by (addr, clk) into the s_*
//       columns, compute the is-zero witness d_inv and the ordering delta
//       limbs, and accumulate the grand-product column z with the fixed
//       Stage-1 challenges. This is trace-first: the prover computes the whole
//       sorted table and the circuit only verifies it.

use std::collections::HashMap;

use halo2_proofs::arithmetic::Field;
use halo2_proofs::halo2curves::bn256::Fr;

use crate::vm_trace::{limbs32, Instr, Op, TraceRow, MEM_BETA, MEM_GAMMA};

/// Fixed trace length the circuit expects.
pub const TRACE_LEN: usize = 32;

pub fn run_program(program: &[Instr]) -> Vec<TraceRow> {
    let mut pc: u64 = 0;
    let mut regs: [u64; 4] = [0, 0, 0, 0];
    let mut mem: HashMap<u64, u64> = HashMap::new();
    let mut trace = Vec::new();

    loop {
        assert!(trace.len() < TRACE_LEN, "trace exceeds TRACE_LEN (missing HALT?)");

        let instr = program
            .get(pc as usize)
            .unwrap_or_else(|| panic!("pc = {pc} out of program bounds"));

        let a = regs[instr.rs1 as usize];
        let b = regs[instr.rs2 as usize];

        let mut row = TraceRow {
            clk: trace.len() as u64,
            pc,
            op: instr.op,
            rd: instr.rd,
            rs1: instr.rs1,
            rs2: instr.rs2,
            imm: instr.imm,
            regs,
            a,
            b,
            c: 0,
            hi: 0,
            c_limbs: [0; 4],
            hi_limbs: [0; 4],
            a_limbs: [0; 4],
            b_limbs: [0; 4],
            mem_addr: 0,
            mem_value: 0,
            mem_type: 0,
            mem_active: 0,
            // sorted-table fields, filled in phase 2
            s_active: 0,
            s_addr: 0,
            s_value: 0,
            s_clk: 0,
            s_type: 0,
            d_inv: Fr::zero(),
            addr_delta_limbs: [0; 4],
            clk_delta_limbs: [0; 4],
            z: Fr::zero(),
            flags: TraceRow::flags_for(instr.op),
        };

        let mut halted = false;
        match instr.op {
            Op::Imm => {
                row.c = instr.imm;
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Add => {
                let sum = a + b;
                row.c = sum & 0xFFFF_FFFF;
                row.hi = sum >> 32;
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Mul => {
                let prod = a * b;
                row.c = prod & 0xFFFF_FFFF;
                row.hi = prod >> 32;
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Xor => {
                row.c = a ^ b;
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Load => {
                let addr = a;
                let value = *mem.get(&addr).unwrap_or(&0);
                row.c = value;
                row.mem_addr = addr;
                row.mem_value = value;
                row.mem_type = 0; // READ
                row.mem_active = 1;
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Store => {
                let addr = a;
                let value = b;
                mem.insert(addr, value);
                row.mem_addr = addr;
                row.mem_value = value;
                row.mem_type = 1; // WRITE
                row.mem_active = 1;
                pc += 1;
            }
            Op::Halt => {
                halted = true;
            }
        }

        row.c_limbs = limbs32(row.c);
        row.hi_limbs = limbs32(row.hi);
        row.a_limbs = limbs32(row.a);
        row.b_limbs = limbs32(row.b);

        trace.push(row);
        if halted {
            break;
        }
    }

    // pad with the frozen HALT row (clk keeps advancing)
    let last = *trace.last().expect("empty trace");
    while trace.len() < TRACE_LEN {
        let mut row = last;
        row.clk = trace.len() as u64;
        trace.push(row);
    }

    // phase 2: fill the memory witness (sorted table + d_inv + limbs + z)
    fill_memory_witness(&mut trace);

    trace
}

/// Rebuild ONLY the memory witness (sorted table, d_inv, ordering limbs, z)
/// from the current mem_* columns, without re-running execution. Tests use this
/// to produce a witness that is internally CONSISTENT with tampered mem_* values
/// — so a single downstream fence (a read rule) fires instead of the grand
/// product co-firing on a stale z.
pub fn rebuild_memory_witness(trace: &mut [TraceRow]) {
    fill_memory_witness(trace);
}

/// Phase 2: build the sorted memory table and the grand-product accumulator.
fn fill_memory_witness(trace: &mut [TraceRow]) {
    let n = trace.len();

    // (a) collect active accesses and sort by (addr, clk)
    let mut accesses: Vec<(u64, u64, u64, u64)> = trace
        .iter()
        .filter(|r| r.mem_active == 1)
        .map(|r| (r.mem_addr, r.mem_value, r.clk, r.mem_type))
        .collect();
    accesses.sort_by_key(|&(addr, _, clk, _)| (addr, clk));

    // (b) place sorted accesses at the top; the rest stay inactive
    for (i, row) in trace.iter_mut().enumerate() {
        if i < accesses.len() {
            let (addr, value, clk, ty) = accesses[i];
            row.s_active = 1;
            row.s_addr = addr;
            row.s_value = value;
            row.s_clk = clk;
            row.s_type = ty;
        } else {
            row.s_active = 0;
            row.s_addr = 0;
            row.s_value = 0;
            row.s_clk = 0;
            row.s_type = 0;
        }
    }

    // (c) is-zero witness d_inv and ordering delta limbs, per transition i→i+1
    for i in 0..n - 1 {
        let a_cur = Fr::from(trace[i].s_addr);
        let a_next = Fr::from(trace[i + 1].s_addr);
        let d = a_next - a_cur;
        // d_inv is the is-zero witness: inverse when d ≠ 0, else 0. Computed for
        // every row so `same_addr = 1 − d·d_inv` is correct wherever it's read.
        trace[i].d_inv = if d == Fr::zero() {
            Fr::zero()
        } else {
            d.invert().unwrap()
        };

        let both_active = trace[i].s_active == 1 && trace[i + 1].s_active == 1;
        if both_active {
            // addr delta ≥ 0 (sorted): decompose into bytes
            let addr_delta = trace[i + 1].s_addr - trace[i].s_addr;
            trace[i].addr_delta_limbs = limbs32(addr_delta);
            // clk delta − 1 ≥ 0, only when same address
            if trace[i + 1].s_addr == trace[i].s_addr {
                let clk_delta = trace[i + 1].s_clk - trace[i].s_clk - 1;
                trace[i].clk_delta_limbs = limbs32(clk_delta);
            } else {
                trace[i].clk_delta_limbs = [0; 4];
            }
        } else {
            trace[i].addr_delta_limbs = [0; 4];
            trace[i].clk_delta_limbs = [0; 4];
        }
    }
    // last row: no transition; leave d_inv = 0, limbs = 0 (q_step is 0 there).

    // (d) grand-product accumulator z
    let beta = Fr::from(MEM_BETA);
    let gamma = Fr::from(MEM_GAMMA);
    let fp = |active: u64, addr: u64, value: u64, clk: u64, ty: u64| -> Fr {
        Fr::from(active)
            + Fr::from(addr) * beta
            + Fr::from(value) * beta * beta
            + Fr::from(clk) * beta * beta * beta
            + Fr::from(ty) * beta * beta * beta * beta
    };

    let mut z = Fr::one();
    trace[0].z = z;
    for i in 0..n - 1 {
        // trace-side factor: (γ + fp) if active, else neutral 1
        let tf = if trace[i].mem_active == 1 {
            gamma + fp(
                trace[i].mem_active,
                trace[i].mem_addr,
                trace[i].mem_value,
                trace[i].clk,
                trace[i].mem_type,
            )
        } else {
            Fr::one()
        };
        // sorted-side factor
        let sf = if trace[i].s_active == 1 {
            gamma + fp(
                trace[i].s_active,
                trace[i].s_addr,
                trace[i].s_value,
                trace[i].s_clk,
                trace[i].s_type,
            )
        } else {
            Fr::one()
        };
        // Z[i+1] = Z[i] · tf / sf
        z = z * tf * sf.invert().unwrap();
        trace[i + 1].z = z;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn store_then_load_roundtrips() {
        let program = vec![
            Instr::imm(0, 42),
            Instr::imm(1, 7),
            Instr::store(1, 0), // m[7] = 42
            Instr::load(2, 1),  // r2 = m[7] = 42
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let st = trace[2];
        assert_eq!((st.mem_addr, st.mem_value, st.mem_type, st.mem_active), (7, 42, 1, 1));
        let ld = trace[3];
        assert_eq!((ld.mem_addr, ld.c, ld.mem_type, ld.mem_active), (7, 42, 0, 1));
        assert_eq!(trace[4].regs[2], 42);
    }

    #[test]
    fn overwrite_then_load_reads_latest() {
        let program = vec![
            Instr::imm(0, 5),
            Instr::imm(1, 100),
            Instr::imm(2, 200),
            Instr::store(0, 1), // m[5] = 100
            Instr::store(0, 2), // m[5] = 200
            Instr::load(3, 0),  // r3 = m[5] = 200
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let ld = trace.iter().find(|r| r.op == Op::Load).unwrap();
        assert_eq!(ld.c, 200);
    }

    #[test]
    fn sorted_table_is_sorted_and_active_first() {
        // three accesses to addresses 5, 5, 5 (two stores + one load).
        let program = vec![
            Instr::imm(0, 5),
            Instr::imm(1, 100),
            Instr::imm(2, 200),
            Instr::store(0, 1),
            Instr::store(0, 2),
            Instr::load(3, 0),
            Instr::halt(),
        ];
        let trace = run_program(&program);

        // count active accesses
        let n_active = trace.iter().filter(|r| r.mem_active == 1).count();
        assert_eq!(n_active, 3);

        // the first n_active sorted rows are active, the rest inactive
        for (i, r) in trace.iter().enumerate() {
            if i < n_active {
                assert_eq!(r.s_active, 1, "row {i} should be active in sorted table");
            } else {
                assert_eq!(r.s_active, 0, "row {i} should be inactive in sorted table");
            }
        }

        // sorted by (addr, clk): within the active block, (s_addr, s_clk) is
        // non-decreasing
        for i in 1..n_active {
            let prev = (trace[i - 1].s_addr, trace[i - 1].s_clk);
            let cur = (trace[i].s_addr, trace[i].s_clk);
            assert!(prev <= cur, "sorted table not ordered at row {i}");
        }
    }

    #[test]
    fn grand_product_returns_to_one() {
        // The whole point of the grand product: z must come back to 1 at the
        // end for an honest trace (sorted table is a faithful permutation).
        let program = vec![
            Instr::imm(0, 5),
            Instr::imm(1, 100),
            Instr::imm(2, 200),
            Instr::store(0, 1),
            Instr::store(0, 2),
            Instr::load(3, 0),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        assert_eq!(trace[0].z, Fr::one(), "z must start at 1");
        assert_eq!(trace[TRACE_LEN - 1].z, Fr::one(), "z must return to 1");
    }

    #[test]
    fn same_addr_read_returns_prior_value() {
        // In the sorted table, the LOAD (READ) to addr 5 must sit right after
        // the latest STORE (WRITE) to addr 5 and carry the same value.
        let program = vec![
            Instr::imm(0, 5),
            Instr::imm(1, 100),
            Instr::imm(2, 200),
            Instr::store(0, 1),
            Instr::store(0, 2),
            Instr::load(3, 0),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        // active sorted rows: all addr 5, ordered by clk. The last is the READ.
        let n_active = trace.iter().filter(|r| r.mem_active == 1).count();
        let last = trace[n_active - 1];
        assert_eq!(last.s_type, 0, "last access to addr 5 is the READ");
        assert_eq!(last.s_value, 200, "READ carries the latest written value");
        // and the row before it is the WRITE of 200
        let prev = trace[n_active - 2];
        assert_eq!(prev.s_value, 200);
    }

    #[test]
    fn print_trace() {
        let program = vec![
            Instr::imm(0, 42),
            Instr::imm(1, 3),
            Instr::store(1, 0),
            Instr::load(2, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        crate::vm_trace::print_trace(&trace);
    }
}