// emulator.rs — the prover OUTSIDE the circuit.
//
// Runs the program for real and produces the honest trace, with the full
// datapath witness (a, b, c) and the 32-bit auxiliaries (hi and the limbs)
// filled in. The division of labor that defines a zkVM:
//
//   emulator:  program -> trace          (computes; fast; not proven)
//   circuit:   "trace is valid for P"    (does not compute; only verifies)
//
// Conventions mirrored from the circuit:
//   - each TraceRow records the state at the START of the instruction;
//   - execution ends ON the HALT row (the circuit's q_last expects HALT);
//   - the circuit works with FIXED-length traces (TRACE_LEN). After HALT,
//     the final row repeats until the length is reached — HALT is absorbing
//     and freezes the whole state, so the repeated rows satisfy every chip
//     with no extra constraints. This keeps the fixed selector columns
//     identical across executions (a single verifying key), instead of
//     leaking the execution length.
//
// Arithmetic (ADD/MUL) wraps at 2^32; the euclidean division of the true
// result by 2^32 gives (c, hi):  a op b = c + hi*2^32,  c < 2^32. We compute
// a op b exactly in u64 and split with a mask/shift — the wrap is the mask,
// not the integer type. XOR is bitwise: c = a ^ b, no wrap, hi = 0. Every
// value that needs range/bitwise checking is decomposed into 8-bit limbs.

use crate::vm_trace::{limbs32, Instr, Op, TraceRow};

/// Fixed trace length the circuit expects.
pub const TRACE_LEN: usize = 32;

/// Runs `program` from pc = 0 and returns the trace, already padded to
/// exactly TRACE_LEN rows.
///
/// Padding: after HALT, the final row repeats — same pc and regs, with clk
/// still incrementing — until TRACE_LEN is reached. HALT is absorbing, so the
/// repeated rows satisfy every chip with no extra constraints, and the fixed
/// selector columns stay identical across executions (a single verifying key
/// instead of one that leaks the execution length).
pub fn run_program(program: &[Instr]) -> Vec<TraceRow> {
    let mut pc: u64 = 0;
    let mut regs: [u64; 4] = [0, 0, 0, 0];
    let mut trace = Vec::new();

    // execute until HALT
    loop {
        assert!(trace.len() < TRACE_LEN, "trace exceeds TRACE_LEN (missing HALT?)");

        let instr = program
            .get(pc as usize)
            .unwrap_or_else(|| panic!("pc = {pc} out of program bounds"));

        // read source registers (materialized into a/b)
        let a = regs[instr.rs1 as usize];
        let b = regs[instr.rs2 as usize];

        // trace row: state at the start of the instruction. c/hi/limbs are
        // filled below.
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
            flags: TraceRow::flags_for(instr.op),
        };

        // per-opcode semantics: fill c (and hi) and evolve the state.
        let mut halted = false;
        match instr.op {
            Op::Imm => {
                row.c = instr.imm;          // imm already < 2^32 (checked in Instr::imm)
                row.hi = 0;
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Add => {
                let sum = a + b;            // a,b < 2^32 ⇒ sum < 2^33, fits in u64
                row.c = sum & 0xFFFF_FFFF;  // result mod 2^32
                row.hi = sum >> 32;         // carry ∈ {0, 1}
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Mul => {
                let prod = a * b;           // a,b < 2^32 ⇒ prod < 2^64, fits in u64
                row.c = prod & 0xFFFF_FFFF; // result mod 2^32
                row.hi = prod >> 32;        // high 32 bits
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Xor => {
                row.c = a ^ b;              // bitwise; a,b < 2^32 ⇒ c < 2^32
                row.hi = 0;                 // XOR does not overflow: no high part
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Halt => {
                halted = true;              // execution ends ON the HALT row
            }
        }

        // limbs. c is written on every non-HALT opcode; hi only matters for
        // MUL; a/b limbs only matter for XOR (its triple lookups need the
        // operand chunks). limbs32 is correct for every value here, so we
        // decompose all of them unconditionally — the unused ones (e.g. a/b
        // limbs off XOR) are never read by any gate.
        row.c_limbs = limbs32(row.c);
        row.hi_limbs = limbs32(row.hi);
        row.a_limbs = limbs32(row.a);
        row.b_limbs = limbs32(row.b);

        trace.push(row);
        if halted {
            break;
        }
    }

    // pad: repeat the frozen HALT row (clk keeps advancing) up to TRACE_LEN.
    let last = *trace.last().expect("empty trace");
    while trace.len() < TRACE_LEN {
        let mut row = last;
        row.clk = trace.len() as u64;
        trace.push(row);
    }

    trace
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn computes_49() {
        // r2 = 3 + 4 = 7, r3 = 7 * 7 = 49
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 4),
            Instr::add(2, 0, 1),
            Instr::mul(3, 2, 2),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        assert_eq!(trace.len(), TRACE_LEN);
        // the real computation lands on the HALT row (index 4)
        assert_eq!(trace[4].regs, [3, 4, 7, 49]);
        assert_eq!(trace[4].op, Op::Halt);
    }

    #[test]
    fn clock_and_datapath() {
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 4),
            Instr::add(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        // ADD row: a and b are the read operands, c the result
        let add = trace[2];
        assert_eq!((add.a, add.b, add.c), (3, 4, 7));
        // clk matches the row index across the whole padded trace
        for (i, r) in trace.iter().enumerate() {
            assert_eq!(r.clk, i as u64);
        }
    }

    #[test]
    fn padding_freezes_state() {
        let program = vec![Instr::imm(0, 3), Instr::halt()];
        let trace = run_program(&program);
        assert_eq!(trace.len(), TRACE_LEN);
        // rows 1.. are the frozen HALT (clk still advancing)
        for (i, r) in trace.iter().enumerate().skip(1) {
            assert_eq!(r.op, Op::Halt);
            assert_eq!(r.pc, 1);
            assert_eq!(r.regs, [3, 0, 0, 0]);
            assert_eq!(r.clk, i as u64);
        }
    }

    #[test]
    fn add_carry_wraps() {
        // 2^32 - 1 + 1 = 2^32 ≡ 0 (mod 2^32), carry = 1.
        let program = vec![
            Instr::imm(0, 0xFFFF_FFFF),
            Instr::imm(1, 1),
            Instr::add(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let add = trace[2];
        assert_eq!(add.a, 0xFFFF_FFFF);
        assert_eq!(add.b, 1);
        assert_eq!(add.c, 0);            // wrapped
        assert_eq!(add.hi, 1);           // carry fired
        // c + hi*2^32 = a + b
        assert_eq!(add.c + add.hi * (1 << 32), add.a + add.b);
    }

    #[test]
    fn mul_high_part() {
        // (2^16) * (2^16) = 2^32 ≡ 0 (mod 2^32), hi = 1.
        let program = vec![
            Instr::imm(0, 1 << 16),
            Instr::imm(1, 1 << 16),
            Instr::mul(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let mul = trace[2];
        assert_eq!(mul.c, 0);            // low 32 bits
        assert_eq!(mul.hi, 1);           // high 32 bits
        // c + hi*2^32 = a * b
        assert_eq!(mul.c as u128 + (mul.hi as u128) * (1 << 32), mul.a as u128 * mul.b as u128);
    }

    #[test]
    fn xor_computes_and_decomposes() {
        // r0 = 0xF0F0_AAAA, r1 = 0x0FF0_5555, r2 = r0 ^ r1 = 0xFF00_FFFF.
        let x = 0xF0F0_AAAA;
        let y = 0x0FF0_5555;
        let program = vec![
            Instr::imm(0, x),
            Instr::imm(1, y),
            Instr::xor(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let xr = trace[2]; // the XOR row

        // result is the bitwise xor, hi is zero (no overflow)
        assert_eq!(xr.a, x);
        assert_eq!(xr.b, y);
        assert_eq!(xr.c, x ^ y);
        assert_eq!(xr.c, 0xFF00_FFFF);
        assert_eq!(xr.hi, 0);

        // the operand AND result limbs are all present, and per chunk the
        // limbs xor correctly: c_limb[i] = a_limb[i] ^ b_limb[i]. This is the
        // exact relation the XOR table will check in-circuit.
        for i in 0..4 {
            assert_eq!(xr.c_limbs[i], xr.a_limbs[i] ^ xr.b_limbs[i]);
        }

        // and the result register is updated on the next row
        assert_eq!(trace[3].regs[2], x ^ y);
    }

    #[test]
    fn limbs_recompose() {
        // every row's limbs must recompose to their value (c, hi, a, b).
        let program = vec![
            Instr::imm(0, 0x1234_ABCD),
            Instr::imm(1, 0xFFFF),
            Instr::mul(2, 0, 1),
            Instr::xor(3, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let recompose = |l: [u64; 4]| l[0] + (l[1] << 8) + (l[2] << 16) + (l[3] << 24);
        for r in &trace {
            assert_eq!(recompose(r.c_limbs), r.c);
            assert_eq!(recompose(r.hi_limbs), r.hi);
            assert_eq!(recompose(r.a_limbs), r.a);
            assert_eq!(recompose(r.b_limbs), r.b);
        }
    }

    #[test]
    fn print_trace() {
        let program = vec![
            Instr::imm(0, 0xF0F0_AAAA),
            Instr::imm(1, 0x0FF0_5555),
            Instr::add(2, 0, 1),
            Instr::mul(3, 0, 1),
            Instr::xor(3, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        crate::vm_trace::print_trace(&trace);
    }
}