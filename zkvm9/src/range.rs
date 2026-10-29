// range.rs — 32-bit range checks via 8-bit limb decomposition.
//
// This chip owns the "range confinement" half of the 32-bit arithmetic: it
// proves that the written value c and the MUL high part hi each fit in 32
// bits. The ALU owns the "relation" half (a op b = c + hi·2^32). Neither is
// sound alone — together they pin (c, hi) to the unique euclidean quotient and
// remainder, closing the wrap.
//
// Mechanism: a 32-bit value is split into four 8-bit limbs, little-endian:
//     v = l0 + l1·2^8 + l2·2^16 + l3·2^24.
// Two ingredients per value:
//   (a) a RECOMPOSITION gate: v equals the weighted sum of its limbs;
//   (b) four LOOKUPS: each limb is a byte (∈ byte_table = 0..255).
// (a) alone would let limbs be huge and still sum to v; (b) alone doesn't tie
// the limbs to v. Together: v = Σ (bytes) < 2^32.
//
// Which values, on which rows:
//   c  — range-checked on every WRITING opcode. q_write = f_imm + f_add +
//        f_mul + f_xor (one-hot ⇒ q_write ∈ {0,1}). XOR is included because it
//        writes c too: this c-recomposition is also the tie that makes the XOR
//        chip's chunk lookups add up to the written c. (On XOR the c_limbs byte
//        lookups here are redundant with the XOR table, but harmless.)
//   hi — range-checked only on MUL (on ADD the carry is a single bit, confined
//        by the ALU; on IMM/HALT/XOR hi is unused). Guard: f_mul.
//
// The recomposition GATES are additionally guarded by the fixed selector
// q_exec, which is 0 on the unusable blinding rows — a guard built only from
// advice flags can spuriously fire there. The lookups do NOT need q_exec: on
// the unusable rows the input collapses to 0, which is in the table.

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, TableColumn},
    poly::Rotation,
};

use crate::flags::OpFlags;

#[derive(Clone, Debug)]
pub struct RangeConfig {
    pub c: Column<Advice>,
    pub c_limbs: [Column<Advice>; 4],
    pub hi: Column<Advice>,
    pub hi_limbs: [Column<Advice>; 4],
    pub byte_table: TableColumn,
    pub flags: OpFlags,
    pub q_exec: Column<Fixed>,
}

impl RangeConfig {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        q_exec: Column<Fixed>,
        c: Column<Advice>,
        c_limbs: [Column<Advice>; 4],
        hi: Column<Advice>,
        hi_limbs: [Column<Advice>; 4],
        byte_table: TableColumn,
        flags: OpFlags,
    ) -> Self {
        // limb weights: 2^0, 2^8, 2^16, 2^24
        let weight = |i: usize| Expression::Constant(Fr::from(1u64 << (8 * i)));

        // --- recomposition of c: holds on every writing opcode ---
        meta.create_gate("range: c = Σ c_limbs·2^(8i)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f_imm = meta.query_advice(flags.imm, Rotation::cur());
            let f_add = meta.query_advice(flags.add, Rotation::cur());
            let f_mul = meta.query_advice(flags.mul, Rotation::cur());
            let f_xor = meta.query_advice(flags.xor, Rotation::cur());
            let q_write = f_imm + f_add + f_mul + f_xor; // one-hot ⇒ ∈ {0,1}

            let c = meta.query_advice(c, Rotation::cur());
            let l0 = meta.query_advice(c_limbs[0], Rotation::cur());
            let l1 = meta.query_advice(c_limbs[1], Rotation::cur());
            let l2 = meta.query_advice(c_limbs[2], Rotation::cur());
            let l3 = meta.query_advice(c_limbs[3], Rotation::cur());
            let recomposed =
                l0 * weight(0) + l1 * weight(1) + l2 * weight(2) + l3 * weight(3);

            vec![q * q_write * (c - recomposed)]
        });

        // --- recomposition of hi: holds only on MUL ---
        meta.create_gate("range: hi = Σ hi_limbs·2^(8i)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f_mul = meta.query_advice(flags.mul, Rotation::cur());

            let hi = meta.query_advice(hi, Rotation::cur());
            let l0 = meta.query_advice(hi_limbs[0], Rotation::cur());
            let l1 = meta.query_advice(hi_limbs[1], Rotation::cur());
            let l2 = meta.query_advice(hi_limbs[2], Rotation::cur());
            let l3 = meta.query_advice(hi_limbs[3], Rotation::cur());
            let recomposed =
                l0 * weight(0) + l1 * weight(1) + l2 * weight(2) + l3 * weight(3);

            vec![q * f_mul * (hi - recomposed)]
        });

        // --- byte lookups for c_limbs (conditioned by q_write) ---
        for i in 0..4 {
            meta.lookup("range: c_limb is a byte", |meta| {
                let f_imm = meta.query_advice(flags.imm, Rotation::cur());
                let f_add = meta.query_advice(flags.add, Rotation::cur());
                let f_mul = meta.query_advice(flags.mul, Rotation::cur());
                let f_xor = meta.query_advice(flags.xor, Rotation::cur());
                let q_write = f_imm + f_add + f_mul + f_xor;
                let limb = meta.query_advice(c_limbs[i], Rotation::cur());
                vec![(q_write * limb, byte_table)]
            });
        }

        // --- byte lookups for hi_limbs (conditioned by q_mul) ---
        for i in 0..4 {
            meta.lookup("range: hi_limb is a byte", |meta| {
                let f_mul = meta.query_advice(flags.mul, Rotation::cur());
                let limb = meta.query_advice(hi_limbs[i], Rotation::cur());
                vec![(f_mul * limb, byte_table)]
            });
        }

        Self { c, c_limbs, hi, hi_limbs, byte_table, flags, q_exec }
    }
}