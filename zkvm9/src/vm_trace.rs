// vm_trace.rs — the machine's vocabulary: opcodes, instructions, trace row.
//
// ISA: IMM, ADD, MUL, HALT, XOR, LOAD, STORE, JUMPI. Four registers, a
// read-write data memory (LOAD/STORE), and a conditional jump (JUMPI) for
// loops/branching. The prover computes everything in the trace; the circuit
// only verifies.
//
// The TraceRow now carries THREE layers:
//   (1) execution state + datapath (clk, pc, op, regs, a, b, c, ...)
//   (2) 32-bit auxiliaries (hi and the limbs) for arithmetic / XOR
//   (3) the memory access on this row (mem_*), PLUS the SORTED memory table
//       row (s_*, d_inv, delta limbs, z) used by the offline memory argument.
// Layers (1)+(2) are in chronological order. The s_* fields are DIFFERENT: the
// s_* of row i is the i-th row of the memory accesses SORTED by (addr, clk) —
// unrelated to what executes at cycle i. Both live on the same physical row so
// the grand product can compare them at the same rotation.
//
// STAGE 2 (zkvm8): the grand-product challenges beta/gamma are now real
// Fiat-Shamir challenges, drawn AFTER the first-phase columns are committed.
// The emulator therefore NO LONGER computes z — it cannot, since the challenge
// does not exist until proving time. The z field below is filled by the circuit
// in the second phase of synthesize. The emulator still produces everything
// else (the sorted table, d_inv, and the ordering limbs are all first-phase,
// challenge-independent).
//
// JUMPI: pc_next = (regs[rs1] != 0) ? imm : pc + 1. Destination is an immediate
// (fixed in the program), condition is register rs1 (read into the datapath `a`).
// It writes no register and touches no memory. Proving "regs[rs1] != 0" needs an
// is-nonzero witness: a_inv holds 1/a (or 0 when a == 0), filled EVERY row so the
// control gate's consistency check can be global. The pc is no longer monotone —
// but clk still advances by 1 per executed row, so the memory argument (which
// orders by (addr, clk)) is untouched.

use halo2_proofs::halo2curves::bn256::Fr;

/// The opcodes. The integer value is the encoding used by the Fetch chip; it
/// also matches the flag index in `flags_for`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Imm = 0,   // rd = imm
    Add = 1,   // rd = a + b mod 2^32
    Mul = 2,   // rd = a * b mod 2^32
    Halt = 3,  // stop (and pad)
    Xor = 4,   // rd = a ^ b
    Load = 5,  // rd = m[rs1]
    Store = 6, // m[rs1] = rs2
    Jumpi = 7, // pc = (regs[rs1] != 0) ? imm : pc + 1
}

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
    pub fn xor(rd: u64, rs1: u64, rs2: u64) -> Self {
        assert!(rd < 4 && rs1 < 4 && rs2 < 4);
        Instr { op: Op::Xor, rd, rs1, rs2, imm: 0 }
    }
    pub fn load(rd: u64, rs1: u64) -> Self {
        assert!(rd < 4 && rs1 < 4);
        Instr { op: Op::Load, rd, rs1, rs2: 0, imm: 0 }
    }
    pub fn store(rs1: u64, rs2: u64) -> Self {
        assert!(rs1 < 4 && rs2 < 4);
        Instr { op: Op::Store, rd: 0, rs1, rs2, imm: 0 }
    }
    pub fn halt() -> Self {
        Instr { op: Op::Halt, rd: 0, rs1: 0, rs2: 0, imm: 0 }
    }
    /// Conditional jump: if regs[rs1] != 0, pc <- target (an immediate address).
    pub fn jumpi(target: u64, rs1: u64) -> Self {
        assert!(rs1 < 4, "register index must be 0..3");
        assert!(target < (1 << 32), "jump target must fit in 32 bits");
        Instr { op: Op::Jumpi, rd: 0, rs1, rs2: 0, imm: target }
    }
}

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
    pub a: u64,
    pub b: u64,
    pub c: u64,

    // 32-bit auxiliaries
    pub hi: u64,
    pub c_limbs: [u64; 4],
    pub hi_limbs: [u64; 4],
    pub a_limbs: [u64; 4],
    pub b_limbs: [u64; 4],

    /// inverse of `a` for the is-nonzero gadget: 1/a when a != 0, else 0. Filled
    /// EVERY row (a is read every row), so the JUMPI control gate can enforce
    /// consistency globally without gating by the jumpi flag.
    pub a_inv: Fr,

    // memory access on this row (chronological)
    pub mem_addr: u64,
    pub mem_value: u64,
    pub mem_type: u64,   // 0 = READ, 1 = WRITE
    pub mem_active: u64, // 1 on LOAD/STORE

    // sorted memory table row (row i = i-th access sorted by (addr, clk)).
    // Active accesses are placed contiguously at the top; the rest are inactive
    // (s_active = 0) and take no part in the argument.
    pub s_active: u64,
    pub s_addr: u64,
    pub s_value: u64,
    pub s_clk: u64,
    pub s_type: u64,
    /// inverse of the address delta s_addr[i+1] − s_addr[i] (is-zero gadget).
    pub d_inv: Fr,
    /// 8-bit limbs of the address delta and (clk delta − 1), for ordering.
    pub addr_delta_limbs: [u64; 4],
    pub clk_delta_limbs: [u64; 4],
    /// grand-product accumulator value on this row. STAGE 2: filled by the
    /// circuit in the second phase of synthesize (depends on the Fiat-Shamir
    /// challenge), NOT by the emulator. Left at the Fr::zero() default until
    /// then.
    pub z: Fr,

    /// one-hot opcode flags [imm, add, mul, hlt, xor, load, store, jumpi].
    pub flags: [u64; 8],
}

impl TraceRow {
    pub fn flags_for(op: Op) -> [u64; 8] {
        [
            (op == Op::Imm) as u64,
            (op == Op::Add) as u64,
            (op == Op::Mul) as u64,
            (op == Op::Halt) as u64,
            (op == Op::Xor) as u64,
            (op == Op::Load) as u64,
            (op == Op::Store) as u64,
            (op == Op::Jumpi) as u64,
        ]
    }
}

/// Split a 32-bit value into four little-endian 8-bit limbs.
pub fn limbs32(v: u64) -> [u64; 4] {
    debug_assert!(v < (1 << 32), "value {v} exceeds 32 bits");
    [v & 0xFF, (v >> 8) & 0xFF, (v >> 16) & 0xFF, (v >> 24) & 0xFF]
}

/// Arithmetic view: state, decode, datapath, and every 8-bit limb group.
pub fn print_trace_arith(trace: &[TraceRow]) {
    println!(
        "{:>3} {:>3} {:>6} {:>2} {:>3} {:>3} {:>10} | {:>17} | \
         {:>10} {:>10} {:>10} {:>4} | {:>13} {:>13} {:>13} {:>13}",
        "clk", "pc", "op", "rd", "rs1", "rs2", "imm", "regs",
        "a", "b", "c", "hi", "a_limbs", "b_limbs", "c_limbs", "hi_limbs",
    );
    for r in trace {
        println!(
            "{:>3} {:>3} {:>6} {:>2} {:>3} {:>3} {:>10} | {:>17} | \
             {:>10} {:>10} {:>10} {:>4} | {:>13} {:>13} {:>13} {:>13}",
            r.clk, r.pc, format!("{:?}", r.op), r.rd, r.rs1, r.rs2, r.imm,
            format!("{:?}", r.regs), r.a, r.b, r.c, r.hi,
            format!("{:?}", r.a_limbs), format!("{:?}", r.b_limbs),
            format!("{:?}", r.c_limbs), format!("{:?}", r.hi_limbs),
        );
    }
}

/// Memory view: the chronological access (mem_*) and the sorted table (s_*).
pub fn print_trace(trace: &[TraceRow]) {
    println!(
        "{:>3} {:>6} | {:>8} {:>8} {:>4} {:>4} | {:>8} {:>8} {:>8} {:>5} {:>5}",
        "clk", "op", "m_addr", "m_val", "m_t", "m_a",
        "s_addr", "s_val", "s_clk", "s_ty", "s_act",
    );
    for r in trace {
        println!(
            "{:>3} {:>6} | {:>8} {:>8} {:>4} {:>4} | {:>8} {:>8} {:>8} {:>5} {:>5}",
            r.clk, format!("{:?}", r.op),
            r.mem_addr, r.mem_value, r.mem_type, r.mem_active,
            r.s_addr, r.s_value, r.s_clk, r.s_type, r.s_active,
        );
    }
}