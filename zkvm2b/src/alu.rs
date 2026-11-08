// alu.rs — the arithmetic: it constrains the result column c per opcode.
//
// 32-bit modular arithmetic. ADD and MUL wrap at 2^32; the wrap is expressed
// as the euclidean division of the true result by 2^32:
//
//     a op b = c + hi · 2^32,     with c < 2^32.
//
// The ALU owns the RELATION between a, b, c and hi — it proves the equation
// holds and (for ADD) that the carry is a single bit. It does NOT prove that
// c and hi fit in 32 bits: that confinement is the RangeCheck chip's job
// (8-bit limb lookups). The two together are what make the wrap sound — the
// equation alone would let a malicious prover pick an out-of-range (c, hi).
//
// One gate per operation, gated by its one-hot flag so it only fires on the
// matching row:
//
//   IMM:  f_imm · (c - imm)                = 0   c is the immediate
//   ADD:  f_add · (a + b - c - hi·2^32)    = 0   sum, with carry hi ∈ {0,1}
//         f_add · hi · (hi - 1)            = 0   carry is boolean (cheap: no
//                                                lookup — a single bit)
//   MUL:  f_mul · (a·b - c - hi·2^32)      = 0   product, hi = high 32 bits
//                                                (hi's range is checked by the
//                                                RangeCheck chip, not here)
//   [SUB] SUB:  f_sub · (a - b - c + hi·2^32)  = 0   difference, hi = borrow
//               f_sub · hi · (hi - 1)          = 0   borrow is boolean
//
// HALT has no gate here, and hi is left free on IMM/HALT rows: no gate reads
// hi there (the ALU reads it only under f_add/f_mul, the RangeCheck only under
// f_mul), so unconstrained hi on those rows is harmless. The operands a, b are
// bound to the right registers by the RegFile; here the ALU only relates them
// to c and hi. Keeping the gates separate makes a failing MockProver point at
// the specific opcode.

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};

use crate::flags::OpFlags;

#[derive(Clone, Copy, Debug)]
pub struct AluConfig {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    pub imm: Column<Advice>,
    pub hi: Column<Advice>,
    pub flags: OpFlags,
    pub q_exec: Column<Fixed>,
}

impl AluConfig {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        q_exec: Column<Fixed>,
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        imm: Column<Advice>,
        hi: Column<Advice>,
        flags: OpFlags,
    ) -> Self {
        // 2^32 as a field constant. The high part hi is weighted by this in the
        // euclidean-division equation a op b = c + hi·2^32.
        let two_32 = || Expression::Constant(Fr::from(1u64 << 32));

        meta.create_gate("alu: IMM", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.imm, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let imm = meta.query_advice(imm, Rotation::cur());
            // c is the immediate. c's 32-bit range is checked by RangeCheck.
            vec![q * f * (c - imm)]
        });

        meta.create_gate("alu: ADD (32-bit, with carry)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.add, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let hi = meta.query_advice(hi, Rotation::cur());
            let one = Expression::Constant(Fr::one());
            vec![
                // a + b = c + hi·2^32  (hi is the carry)
                q.clone() * f.clone() * (a + b - c - hi.clone() * two_32()),
                // carry is a single bit: hi·(hi-1) = 0. Cheap confinement, no
                // lookup needed — the ADD carry is 0 or 1 by construction
                // (a,b < 2^32 ⇒ a+b < 2^33).
                q * f * hi.clone() * (hi - one),
            ]
        });

        meta.create_gate("alu: MUL (32-bit, high part)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.mul, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let hi = meta.query_advice(hi, Rotation::cur());
            // a·b = c + hi·2^32. Here hi is the high 32 bits, up to 2^32-1, so
            // (unlike the ADD carry) it is NOT boolean — its 32-bit range is
            // confined by the RangeCheck chip via the hi_limbs lookups. The
            // field product a·b never wraps: a,b < 2^32 ⇒ a·b < 2^64 < p.
            vec![q * f * (a * b - c - hi * two_32())]
        });

        // [SUB] new gate: a - b = c - hi·2^32, with the borrow hi ∈ {0,1}.
        // Same shape as ADD: c's 32-bit range is checked by RangeCheck, and the
        // borrow is confined here by a boolean constraint. With a, b, c < 2^32
        // and hi ∈ {0,1}, (c, hi) is unique.
        meta.create_gate("alu: SUB (32-bit, with borrow)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.sub, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let hi = meta.query_advice(hi, Rotation::cur());
            let one = Expression::Constant(Fr::one());
            vec![
                // a - b = c - hi·2^32  (hi is the borrow)
                // TODO: write the SUB constraint a - b = c - hi·2^32, multiplied by q and f
                // borrow is a single bit: hi·(hi-1) = 0
                q * f * hi.clone() * (hi - one),
            ]
        });

        Self { a, b, c, imm, hi, flags, q_exec }
    }
}