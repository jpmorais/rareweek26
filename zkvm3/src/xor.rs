// xor.rs — bitwise 32-bit XOR via an 8-bit XOR lookup table.
//
// XOR is not expressible as a low-degree field polynomial (unlike ADD/MUL,
// which have the equation a op b = c + hi·2^32). It is inherently bitwise, so
// the whole relation c = a ^ b is imposed by a LOOKUP against a table of byte
// triples (x, y, x^y). Because XOR is bitwise it commutes with the 8-bit
// decomposition — limbs(a^b) = limbs(a) ^ limbs(b) chunk by chunk — so four
// independent byte-triple lookups suffice; no carry crosses chunk boundaries.
//
// This is the first opcode that decomposes the OPERANDS a and b (not just the
// result), because the triple lookup needs (a_limb[i], b_limb[i], c_limb[i]).
//
// What this chip owns (all guarded by f_xor):
//   - recompose a: a = Σ a_limbs·2^(8i)   (ties the operand chunks to a)
//   - recompose b: b = Σ b_limbs·2^(8i)
//   - four triple lookups: (a_limb[i], b_limb[i], c_limb[i]) ∈ xor_table
//
// What it does NOT own: c = Σ c_limbs. That tie (the written value c to its
// limbs) is the RangeCheck chip's c-recomposition, which now fires on XOR too
// (q_write includes f_xor). So the full chain closing soundness is:
//     a = Σ a_limbs, b = Σ b_limbs           (here)
//     c_limb[i] = a_limb[i] ^ b_limb[i]       (here, via the table)
//     c = Σ c_limbs                            (RangeCheck)
//   ⇒ c = a ^ b.
// The xor_table's columns are byte-valued, so the triple lookups already force
// every limb into [0,256) — no separate byte lookup is needed for XOR limbs.
//
// The recomposition GATES are guarded by q_exec (a fixed column, 0 on the
// unusable blinding rows) to keep them from firing there; the lookups need no
// such guard (their input collapses to (0,0,0), which is in the table).

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, TableColumn},
    poly::Rotation,
};

use crate::flags::OpFlags;

#[derive(Clone, Debug)]
pub struct XorConfig {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub a_limbs: [Column<Advice>; 4],
    pub b_limbs: [Column<Advice>; 4],
    pub c_limbs: [Column<Advice>; 4],
    pub xor_table: [TableColumn; 3],
    pub flags: OpFlags,
    pub q_exec: Column<Fixed>,
}

impl XorConfig {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        q_exec: Column<Fixed>,
        a: Column<Advice>,
        b: Column<Advice>,
        a_limbs: [Column<Advice>; 4],
        b_limbs: [Column<Advice>; 4],
        c_limbs: [Column<Advice>; 4],
        xor_table: [TableColumn; 3],
        flags: OpFlags,
    ) -> Self {
        let weight = |i: usize| Expression::Constant(Fr::from(1u64 << (8 * i)));

        // --- recompose a from its limbs (only on XOR) ---
        meta.create_gate("xor: a = Σ a_limbs·2^(8i)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.xor, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let l0 = meta.query_advice(a_limbs[0], Rotation::cur());
            let l1 = meta.query_advice(a_limbs[1], Rotation::cur());
            let l2 = meta.query_advice(a_limbs[2], Rotation::cur());
            let l3 = meta.query_advice(a_limbs[3], Rotation::cur());
            let recomposed =
                l0 * weight(0) + l1 * weight(1) + l2 * weight(2) + l3 * weight(3);
            vec![q * f * (a - recomposed)]
        });

        // --- recompose b from its limbs (only on XOR) ---
        meta.create_gate("xor: b = Σ b_limbs·2^(8i)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.xor, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let l0 = meta.query_advice(b_limbs[0], Rotation::cur());
            let l1 = meta.query_advice(b_limbs[1], Rotation::cur());
            let l2 = meta.query_advice(b_limbs[2], Rotation::cur());
            let l3 = meta.query_advice(b_limbs[3], Rotation::cur());
            let recomposed =
                l0 * weight(0) + l1 * weight(1) + l2 * weight(2) + l3 * weight(3);
            vec![q * f * (b - recomposed)]
        });

        // --- four triple lookups: (a_limb, b_limb, c_limb) ∈ (x, y, x^y) ---
        // Conditioned by f_xor: off XOR the inputs collapse to (0,0,0), which
        // is in the table (0^0=0), so the lookup passes trivially. On XOR it
        // forces c_limb[i] = a_limb[i] ^ b_limb[i] for each chunk.
        for i in 0..4 {
            meta.lookup("xor: (a,b,c) limb triple", |meta| {
                let f = meta.query_advice(flags.xor, Rotation::cur());
                let al = meta.query_advice(a_limbs[i], Rotation::cur());
                let bl = meta.query_advice(b_limbs[i], Rotation::cur());
                let cl = meta.query_advice(c_limbs[i], Rotation::cur());
                vec![
                    (f.clone() * al, xor_table[0]),
                    (f.clone() * bl, xor_table[1]),
                    (f * cl, xor_table[2]),
                ]
            });
        }

        Self { a, b, a_limbs, b_limbs, c_limbs, xor_table, flags, q_exec }
    }
}