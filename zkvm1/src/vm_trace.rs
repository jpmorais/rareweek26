// vm_trace.rs — the machine's vocabulary: opcodes, instructions, trace row.
//
// A minimal, purely arithmetic ISA: IMM, ADD, MUL, HALT. Four registers
// (r0..r3), no memory, no branching. All arithmetic happens in the field Fr
// (BN256).
//
// Conventions (mirrored by the circuit chips):
//   - each TraceRow records the state at the START of the instruction;
//   - execution ends ON the HALT row;
//   - padding repeats the HALT row (HALT is absorbing and freezes the
//     state), so there is no NOP opcode: HALT does double duty (stop + pad).
//
// Datapath columns a, b, c:
//   a = value read from regs[rs1]   (left operand)
//   b = value read from regs[rs2]   (right operand)
//   c = result, written into regs[rd] on the NEXT row
// The circuit cannot index an array by rs1; the prover writes the read value
// into a/b, and the RegFile proves (via Lagrange) that a/b match the right
// registers. The ALU produces c; the RegFile writes c into regs[rd].

/// The four opcodes. The integer value is the encoding used by the future
/// Fetch chip.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Imm = 0,  // rd = imm      (c = imm)
    Add = 1,  // rd = a + b    (c = a + b)
    Mul = 2,  // rd = a * b    (c = a * b)
    Halt = 3, // stop (and pad)
}

/// A program instruction. Uniform format: every field always present, the
/// unused ones left at zero.
#[derive(Clone, Copy, Debug)]
pub struct Instr {
    pub op: Op,
    pub rd: u64,
    pub rs1: u64,
    pub rs2: u64,
    pub imm: u64,
}

impl Instr {
    pub fn imm(rd: u64, value: u64) -> Self {
        assert!(rd < 4, "register index must be 0..3");
        Instr { op: Op::Imm, rd, rs1: 0, rs2: 0, imm: value }
    }
    pub fn add(rd: u64, rs1: u64, rs2: u64) -> Self {
        assert!(rd < 4 && rs1 < 4 && rs2 < 4);
        Instr { op: Op::Add, rd, rs1, rs2, imm: 0 }
    }
    pub fn mul(rd: u64, rs1: u64, rs2: u64) -> Self {
        assert!(rd < 4 && rs1 < 4 && rs2 < 4);
        Instr { op: Op::Mul, rd, rs1, rs2, imm: 0 }
    }
    pub fn halt() -> Self {
        Instr { op: Op::Halt, rd: 0, rs1: 0, rs2: 0, imm: 0 }
    }
}

/// A trace row: the full VM state at the start of the instruction. Values in
/// u64 (the synthesize step converts to Fr); for the small didactic values
/// of the course this is enough.
#[derive(Clone, Copy, Debug)]
pub struct TraceRow {
    pub clk: u64,
    pub pc: u64,
    pub op: Op,
    pub rd: u64,
    pub rs1: u64,
    pub rs2: u64,
    pub imm: u64,
    pub regs: [u64; 4],
    pub a: u64, // left operand:  value read from regs[rs1]
    pub b: u64, // right operand: value read from regs[rs2]
    pub c: u64, // result: written into regs[rd] on the next row
    /// One-hot opcode flags, in canonical order [imm, add, mul, hlt].
    /// Part of the witness: the emulator fills these, and synthesize copies
    /// them verbatim into the flag columns — it computes nothing.
    pub flags: [u64; 4],
}

impl TraceRow {
    /// The one-hot flag vector for an opcode, in order [imm, add, mul, hlt].
    pub fn flags_for(op: Op) -> [u64; 4] {
        [
            (op == Op::Imm) as u64,
            (op == Op::Add) as u64,
            (op == Op::Mul) as u64,
            (op == Op::Halt) as u64,
        ]
    }
}

/// Pretty-prints a trace as a table. Handy in `main` and in tests
/// (run tests with `-- --nocapture` to see the output).
pub fn print_trace(trace: &[TraceRow]) {
    println!(
        "{:>3} {:>3} {:>5} {:>2} {:>3} {:>3} {:>4} | {:>17} | {:>4} {:>4} {:>4}",
        "clk", "pc", "op", "rd", "rs1", "rs2", "imm", "regs", "a", "b", "c"
    );
    for r in trace {
        println!(
            "{:>3} {:>3} {:>5} {:>2} {:>3} {:>3} {:>4} | {:>17} | {:>4} {:>4} {:>4}",
            r.clk,
            r.pc,
            format!("{:?}", r.op),
            r.rd,
            r.rs1,
            r.rs2,
            r.imm,
            format!("{:?}", r.regs),
            r.a,
            r.b,
            r.c,
        );
    }
}