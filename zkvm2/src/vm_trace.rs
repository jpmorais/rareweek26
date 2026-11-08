// vm_trace.rs — the machine's vocabulary: opcodes, instructions, trace row.
//
// A minimal, purely arithmetic ISA: IMM, ADD, MUL, HALT. Four registers
// (r0..r3), no memory, no branching. Arithmetic is now 32-bit modular
// (wrapping) rather than full-field: ADD and MUL wrap at 2^32, and the
// circuit enforces that wrap via range checks. The prover still computes
// everything in the trace; the circuit only verifies.
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
//
// 32-bit arithmetic auxiliaries (new in this VM):
//   hi       = high part of the euclidean division of (a+b) or (a*b) by 2^32
//   c_limbs  = the four 8-bit limbs of c   (range-checked on every write)
//   hi_limbs = the four 8-bit limbs of hi  (range-checked under MUL only)
// These are witnesses: the emulator fills them, synthesize copies them, and
// the ALU + RangeCheck chips verify them.

/// The four opcodes. The integer value is the encoding used by the future
/// Fetch chip.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Imm = 0,  // rd = imm            (c = imm)
    Add = 1,  // rd = a + b mod 2^32 (c = (a + b) & 0xFFFF_FFFF)
    Mul = 2,  // rd = a * b mod 2^32 (c = (a * b) & 0xFFFF_FFFF)
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
        assert!(value < (1 << 32), "immediate must fit in 32 bits");
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
/// u64 (the synthesize step converts to Fr). All arithmetic values (regs, a,
/// b, c, hi) are < 2^32; the limbs are < 2^8.
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

    // --- 32-bit arithmetic auxiliaries (trace-first: the emulator fills
    //     these, synthesize copies them; the circuit only verifies) ---
    /// High part of the euclidean division by 2^32, i.e. hi in
    ///   a op b = c + hi * 2^32.
    ///   ADD: the carry, in {0, 1}          (confined by the ALU, cheap).
    ///   MUL: the high 32 bits of a*b        (confined by RangeCheck via limbs).
    /// Unused (0) for IMM and HALT.
    pub hi: u64,
    /// The four 8-bit limbs of `c`, little-endian: c = Σ c_limbs[i] · 2^(8i).
    /// Range-checked on every write (IMM, ADD, MUL).
    pub c_limbs: [u64; 4],
    /// The four 8-bit limbs of `hi`, little-endian: hi = Σ hi_limbs[i] · 2^(8i).
    /// Only meaningful for MUL (range-checked under q_mul); left 0 otherwise.
    pub hi_limbs: [u64; 4],

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

/// Split a 32-bit value into four little-endian 8-bit limbs, so that
///   v = limbs[0] + limbs[1]·2^8 + limbs[2]·2^16 + limbs[3]·2^24.
/// The value MUST fit in 32 bits; the emulator guarantees this by construction
/// (wrapping arithmetic), and the circuit re-proves it via the byte lookups.
/// The debug_assert is a didactic safety net: a wrapping bug that lets a value
/// exceed 32 bits is caught here, in Rust, instead of surfacing as an opaque
/// lookup failure in the MockProver.
pub fn limbs32(v: u64) -> [u64; 4] {
    debug_assert!(v < (1 << 32), "value {v} exceeds 32 bits");
    [
        v & 0xFF,
        (v >> 8) & 0xFF,
        (v >> 16) & 0xFF,
        (v >> 24) & 0xFF,
    ]
}

/// Pretty-prints a trace as a table, showing the FULL row: state, decode,
/// datapath, and every 32-bit auxiliary (hi plus all eight limbs). Handy in
/// `main` and in tests (run with `-- --nocapture` to see the output). The
/// limbs are printed little-endian, matching `limbs32`: c[0] is the low byte.
pub fn print_trace(trace: &[TraceRow]) {
    println!(
        "{:>3} {:>3} {:>5} {:>2} {:>3} {:>3} {:>10} | {:>17} | \
         {:>10} {:>10} {:>10} {:>10} | {:>15} | {:>15}",
        "clk", "pc", "op", "rd", "rs1", "rs2", "imm", "regs",
        "a", "b", "c", "hi", "c_limbs", "hi_limbs",
    );
    for r in trace {
        println!(
            "{:>3} {:>3} {:>5} {:>2} {:>3} {:>3} {:>10} | {:>17} | \
             {:>10} {:>10} {:>10} {:>10} | {:>15} | {:>15}",
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
            r.hi,
            format!("{:?}", r.c_limbs),
            format!("{:?}", r.hi_limbs),
        );
    }
}