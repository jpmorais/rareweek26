// emulator.rs — the prover OUTSIDE the circuit.
//
// Runs the program for real and produces the honest trace, with the full
// datapath witness (a, b, c) and the 32-bit arithmetic auxiliaries (hi and
// the limbs) filled in. The division of labor that defines a zkVM:
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
// 32-bit arithmetic. ADD and MUL wrap at 2^32. The euclidean division of the
// true result by 2^32 gives (c, hi):
//   a op b = c + hi * 2^32,   c < 2^32.
// We compute a op b exactly in u64 (a,b < 2^32, so a+b < 2^33 and a*b < 2^64
// both fit) and split it with a mask/shift — the wrap is the mask, not the
// integer type. c and hi are then decomposed into 8-bit limbs for the range
// checks. The circuit re-derives none of this; it only verifies it.

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
        // filled below, per opcode.
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
            flags: TraceRow::flags_for(instr.op),
        };

        // per-opcode semantics: fill c (and hi) and evolve the state.
        // a op b = c + hi * 2^32, with c < 2^32. We compute a op b exactly in
        // u64 (no real overflow: a,b < 2^32) and split with a mask/shift.
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
            // [SUB] semantics: a - b = c - hi * 2^32, with hi the borrow.
            // If a >= b there is no borrow; otherwise we add 2^32 to wrap.
            Op::Sub => {
                if a >= b {
                    row.c = a - b;
                    row.hi = 0;
                } else {
                    row.c = a + (1 << 32) - b; // a - b mod 2^32
                    row.hi = 1;                // borrow
                }
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Halt => {
                halted = true;              // execution ends ON the HALT row
            }
        }

        // limbs for the range checks: c is written on every non-HALT opcode,
        // hi only matters for MUL, but limbs32 is correct for any value here
        // (c = imm/result, hi = 0/carry/high) — decompose unconditionally.
        row.c_limbs = limbs32(row.c);
        row.hi_limbs = limbs32(row.hi);

        trace.push(row);
        if halted {
            break;
        }
    }

    // pad: repeat the frozen HALT row (clk keeps advancing) up to TRACE_LEN.
    // The HALT row already has c = hi = 0 and zero limbs, so the padding rows
    // carry consistent auxiliaries with no extra work.
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
    fn limbs_recompose() {
        // every row's limbs must recompose to c and hi.
        let program = vec![
            Instr::imm(0, 0x1234_ABCD),
            Instr::imm(1, 0xFFFF),
            Instr::mul(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        for r in &trace {
            let c = r.c_limbs[0] + (r.c_limbs[1] << 8) + (r.c_limbs[2] << 16) + (r.c_limbs[3] << 24);
            let hi = r.hi_limbs[0] + (r.hi_limbs[1] << 8) + (r.hi_limbs[2] << 16) + (r.hi_limbs[3] << 24);
            assert_eq!(c, r.c);
            assert_eq!(hi, r.hi);
        }
    }

    // [SUB] emulator tests for the new opcode
    #[test]
    fn sub_no_borrow() {
        // 7 - 3 = 4, no borrow
        let program = vec![
            Instr::imm(0, 7),
            Instr::imm(1, 3),
            Instr::sub(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let sub = trace[2];
        assert_eq!((sub.a, sub.b, sub.c, sub.hi), (7, 3, 4, 0));
        assert_eq!(trace[3].regs[2], 4);
    }

    // [SUB]
    #[test]
    fn sub_borrow_wraps() {
        // 3 - 4 = -1 ≡ 2^32 - 1 (mod 2^32), borrow = 1
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 4),
            Instr::sub(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let sub = trace[2];
        assert_eq!(sub.c, 0xFFFF_FFFF);
        assert_eq!(sub.hi, 1);
        // a - b = c - hi * 2^32  <=>  a + hi * 2^32 = b + c
        assert_eq!(sub.a + sub.hi * (1 << 32), sub.b + sub.c);
    }

    #[test]
    fn print_trace() {
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 4),
            Instr::add(2, 0, 1),
            Instr::mul(3, 2, 2),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        crate::vm_trace::print_trace(&trace);
    }
}