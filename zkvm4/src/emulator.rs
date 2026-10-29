// emulator.rs — the prover OUTSIDE the circuit.
//
// Runs the program for real and produces the honest trace, with the full
// datapath witness (a, b, c) filled in. The division of labor that defines a
// zkVM:
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
//   - arithmetic uses wrapping u64 (the circuit works in Fr; for the small
//     didactic values here the two coincide).

use crate::vm_trace::{Instr, Op, TraceRow};

/// Fixed trace length the circuit expects.
pub const TRACE_LEN: usize = 32;

/// Runs `program` from pc = 0 and returns the trace, already padded to
/// exactly TRACE_LEN rows. `max_steps` guards against programs that never
/// HALT (it must not exceed TRACE_LEN).
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

        // trace row: state at the start of the instruction
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
            flags: TraceRow::flags_for(instr.op),
        };

        // per-opcode semantics: fill c and evolve the state
        match instr.op {
            Op::Imm => {
                row.c = instr.imm;
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Add => {
                row.c = a.wrapping_add(b);
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Mul => {
                row.c = a.wrapping_mul(b);
                regs[instr.rd as usize] = row.c;
                pc += 1;
            }
            Op::Halt => {
                trace.push(row);
                break; // execution ends ON the HALT row
            }
        }

        trace.push(row);
    }

    // pad: repeat the frozen HALT row (clk keeps advancing) up to TRACE_LEN
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
    fn print_trace() {
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 4),
            Instr::add(2, 0, 1),
            Instr::mul(3, 2, 2),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        for (i, row) in trace.iter().enumerate() {
            println!("{i:>2} | {row:?}");
        }
    }    
}