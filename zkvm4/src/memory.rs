// memory.rs — offline memory-consistency argument (Stage 1: fixed challenges).
//
// Proves that LOAD/STORE behave like a real read-write memory: every READ
// returns the value of the most recent WRITE to the same address, and 0 if the
// address was never written (zero-initialised memory).
//
// TWO HALVES over the SORTED table, neither sound alone:
//   (A) grand product — the sorted table is a permutation of the trace rows
//                       (same multiset ⇒ nothing invented or dropped).
//   (B) consistency    — the sorted table, read top-to-bottom, obeys
//                       read-after-write.
// (A) checks the multiset but not the values; (B) operates on a possibly-forged
// table. Together they pin memory down.
//
// ACCESS BINDING (the third piece, easy to forget): the per-row access columns
// mem_addr/mem_value/mem_type/mem_active are tied to the datapath (a, b, c) and
// the opcode flags. Without it, mem_* are free witness and the whole argument
// floats free of the registers — a prover could drop a real LOAD from the
// argument (mem_active = 0) while RegFile still writes its free c into rd, or
// inject a phantom access. The binding is what makes the argument bite.
//
// WITNESS DOMAIN (the fourth piece, just as easy to forget): the sorted-side
// booleans s_active and s_type are prover-supplied witness, INDEPENDENT of the
// trace side. On the trace side mem_active/mem_type are booleans by the binding
// (derived from one-hot flags), but the sorted table is handed over fresh, so
// s_active and s_type must be forced boolean here. They are read as indicators
// everywhere below — both_active = s_active*s_active', is_read = s_active*(1 -
// s_type) — and an out-of-range value (e.g. s_type = 2) would corrupt those
// indicators and let a READ dodge the value rule. Two boolean gates close it.
//
// SORTED TABLE (witness, supplied by the prover): the memory accesses reordered
// by (s_addr, s_clk). Columns:
//   s_active, s_addr, s_value, s_clk, s_type   (s_type: 1 = WRITE, 0 = READ)
// Only ACTIVE rows (mem_active = 1, i.e. LOAD/STORE) take part in the argument.
// The grand product gates each factor by `active`, so inactive rows contribute
// the neutral factor 1 and are skipped; the consistency rules likewise skip
// them (guarded by s_active). So the prover only needs to SORT the active
// accesses — inactive rows of the sorted table can be left empty (s_active = 0).
// The clk is unique per active access, so the sort key (addr, clk) is a total
// order and the permutation is exact.
//
// GADGETS:
//   is_zero(d) on the address delta d = s_addr[i+1] - s_addr[i], via an inverse
//   witness d_inv:   same_addr = 1 - d*d_inv,   with   d*same_addr = 0.
//   This makes same_addr the exact indicator of "same address".
//
//   Ordering: addr delta and (clk delta - 1) are decomposed into 8-bit limbs
//   looked up in byte_table, proving each is in [0, 2^32) => non-negative =>
//   s_addr non-decreasing, and s_clk strictly increasing within an address.
//
// READ-AFTER-WRITE (two gates, covering every active READ exactly once):
//   * step rule (q_step, row i->i+1): a READ at row i+1 must equal val_cur if it
//     shares the address with row i, or 0 if the address changed. This checks
//     every active READ EXCEPT one sitting at the very top of the sorted table.
//   * row-0 rule (q_first): a READ at position 0 reads memory never written
//     before it => must return 0. The step rule can't see this row (it only
//     reaches READs from position 1 on), so this gate closes the gap. Without
//     it, a LOAD of the smallest never-written address could return garbage.
//
// GRAND PRODUCT (accumulator Z, ratio form, no division):
//   Z[0] = 1
//   Z[i+1]*(gamma + fp_sorted[i]) = Z[i]*(gamma + fp_trace[i])
//   Z[n] = 1
//   fp = active + addr*beta + value*beta^2 + clk*beta^3 + type*beta^4
// Z leaving 1 and returning to 1 => equal products => equal multisets.
//
// STAGE 1: beta, gamma are FIXED CONSTANTS below — NOT sound (a prover who knows
// them can forge a collision), but it validates all the algebra with a
// deterministic, inspectable Z. Stage 2 swaps these for real Fiat-Shamir
// challenges (promoting Z to a second phase); only that swap changes.

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, TableColumn, VirtualCells},
    poly::Rotation,
};

use crate::flags::OpFlags;

// Fixed Stage-1 challenges: arbitrary distinct nonzero constants.
const BETA: u64 = 0x1000_0001;
const GAMMA: u64 = 0x2000_0003;

#[derive(Clone, Copy, Debug)]
pub struct MemoryConfig {
    // datapath (bound to the access columns below)
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,

    // trace-side access columns (chronological order), plus clk as timestamp
    pub clk: Column<Advice>,
    pub mem_addr: Column<Advice>,
    pub mem_value: Column<Advice>,
    pub mem_type: Column<Advice>,
    pub mem_active: Column<Advice>,

    // sorted-side columns (witness)
    pub s_active: Column<Advice>,
    pub s_addr: Column<Advice>,
    pub s_value: Column<Advice>,
    pub s_clk: Column<Advice>,
    pub s_type: Column<Advice>,

    // is-zero gadget: inverse of the address delta
    pub d_inv: Column<Advice>,
    // ordering range-check limbs
    pub addr_delta_limbs: [Column<Advice>; 4],
    pub clk_delta_limbs: [Column<Advice>; 4],

    // grand-product accumulator
    pub z: Column<Advice>,

    // shared byte table (0..255) for the ordering limb lookups
    pub byte_table: TableColumn,

    pub flags: OpFlags,
    pub q_exec: Column<Fixed>,
    pub q_step: Column<Fixed>,
    pub q_first: Column<Fixed>,
    pub q_last: Column<Fixed>,
}

impl MemoryConfig {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        q_exec: Column<Fixed>,
        q_step: Column<Fixed>,
        q_first: Column<Fixed>,
        q_last: Column<Fixed>,
        clk: Column<Advice>,
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        mem_addr: Column<Advice>,
        mem_value: Column<Advice>,
        mem_type: Column<Advice>,
        mem_active: Column<Advice>,
        s_active: Column<Advice>,
        s_addr: Column<Advice>,
        s_value: Column<Advice>,
        s_clk: Column<Advice>,
        s_type: Column<Advice>,
        d_inv: Column<Advice>,
        addr_delta_limbs: [Column<Advice>; 4],
        clk_delta_limbs: [Column<Advice>; 4],
        z: Column<Advice>,
        byte_table: TableColumn,
        flags: OpFlags,
    ) -> Self {
        let one = || Expression::Constant(Fr::one());
        let beta = || Expression::Constant(Fr::from(BETA));
        let gamma = || Expression::Constant(Fr::from(GAMMA));
        let weight = |i: usize| Expression::Constant(Fr::from(1u64 << (8 * i)));

        let recompose = |limbs: [Expression<Fr>; 4]| {
            limbs[0].clone() * weight(0)
                + limbs[1].clone() * weight(1)
                + limbs[2].clone() * weight(2)
                + limbs[3].clone() * weight(3)
        };

        // fingerprint of a tuple (active, addr, value, clk, type) at cur row,
        // reading from the given column set.
        let fingerprint =
            |meta: &mut VirtualCells<Fr>,
             active: Column<Advice>,
             addr: Column<Advice>,
             value: Column<Advice>,
             clk_col: Column<Advice>,
             ty: Column<Advice>| {
                let b = beta();
                let a = meta.query_advice(active, Rotation::cur());
                let ad = meta.query_advice(addr, Rotation::cur());
                let va = meta.query_advice(value, Rotation::cur());
                let ck = meta.query_advice(clk_col, Rotation::cur());
                let t = meta.query_advice(ty, Rotation::cur());
                a + ad * b.clone()
                    + va * b.clone() * b.clone()
                    + ck * b.clone() * b.clone() * b.clone()
                    + t * b.clone() * b.clone() * b.clone() * b
            };

        // ===================== ACCESS BINDING =====================
        // Tie the per-row access columns to the datapath and the opcode. This is
        // what makes the memory argument constrain the REGISTERS: without it the
        // mem_* columns are free witness and everything below floats free.
        //
        //   mem_active = f_load + f_store      (memory row iff LOAD or STORE)
        //   mem_type   = f_store               (WRITE on STORE, READ on LOAD)
        //   mem_addr   = a       on LOAD/STORE (address = regs[rs1])
        //   mem_value  = b       on STORE      (value  = regs[rs2])
        //   mem_value  = c       on LOAD       (value read, flows to regs[rd])
        //
        // is_mem = f_load + f_store is <= 1 by the one-hot flag constraint, so it
        // is a valid selector. On IMM/ADD/MUL/XOR/HALT/padding all three flags
        // are 0 => mem_active = 0, mem_type = 0, and addr/value are unconstrained
        // (they never enter the argument, gated by mem_active = 0).
        meta.create_gate("memory: access binding", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f_load = meta.query_advice(flags.load, Rotation::cur());
            let f_store = meta.query_advice(flags.store, Rotation::cur());
            let m_active = meta.query_advice(mem_active, Rotation::cur());
            let m_type = meta.query_advice(mem_type, Rotation::cur());
            let m_addr = meta.query_advice(mem_addr, Rotation::cur());
            let m_value = meta.query_advice(mem_value, Rotation::cur());
            let a_v = meta.query_advice(a, Rotation::cur());
            let b_v = meta.query_advice(b, Rotation::cur());
            let c_v = meta.query_advice(c, Rotation::cur());

            let is_mem = f_load.clone() + f_store.clone();

            vec![
                q.clone() * (m_active - is_mem.clone()),
                q.clone() * (m_type - f_store.clone()),
                q.clone() * is_mem * (m_addr - a_v),
                q.clone() * f_store * (m_value.clone() - b_v),
                q * f_load * (m_value - c_v),
            ]
        });

        // ===================== GRAND PRODUCT =====================
        meta.create_gate("memory: Z init", |meta| {
            let q = meta.query_fixed(q_first, Rotation::cur());
            let z0 = meta.query_advice(z, Rotation::cur());
            vec![q * (z0 - one())]
        });

        meta.create_gate("memory: Z recurrence", |meta| {
            let q = meta.query_fixed(q_step, Rotation::cur());
            let z_cur = meta.query_advice(z, Rotation::cur());
            let z_next = meta.query_advice(z, Rotation::next());

            // Only ACTIVE rows (memory accesses) take part in the product; the
            // mem_active marker gates each side. An active row contributes its
            // (gamma + fp) factor; an inactive row contributes the neutral
            // factor 1, leaving Z unchanged. So the grand product runs over the
            // memory accesses only — inactive rows (IMM/ADD/HALT/padding) skip.
            //
            //   trace factor  = active*(gamma + fp_trace)  + (1 - active)*1
            //   sorted factor = s_active*(gamma + fp_sorted) + (1 - s_active)*1
            //   Z[i+1] * sorted_factor = Z[i] * trace_factor
            let active_t = meta.query_advice(mem_active, Rotation::cur());
            let active_s = meta.query_advice(s_active, Rotation::cur());
            let fp_trace = fingerprint(meta, mem_active, mem_addr, mem_value, clk, mem_type);
            let fp_sorted = fingerprint(meta, s_active, s_addr, s_value, s_clk, s_type);

            let trace_factor =
                active_t.clone() * (gamma() + fp_trace) + (one() - active_t);
            let sorted_factor =
                active_s.clone() * (gamma() + fp_sorted) + (one() - active_s);

            vec![q * (z_next * sorted_factor - z_cur * trace_factor)]
        });

        meta.create_gate("memory: Z end", |meta| {
            let q = meta.query_fixed(q_last, Rotation::cur());
            let z_last = meta.query_advice(z, Rotation::cur());
            vec![q * (z_last - one())]
        });

        // ===================== CONSISTENCY =====================

        // Sorted-side witness domain: s_active and s_type are prover-supplied and
        // read as booleans by every gate below (both_active, is_read). Force them
        // boolean here — the trace side gets this free from the binding, but the
        // sorted table is independent witness. Guarded by q_exec (every row).
        meta.create_gate("memory: s_active boolean", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let sa = meta.query_advice(s_active, Rotation::cur());
            vec![q * sa.clone() * (sa - one())]
        });
        meta.create_gate("memory: s_type boolean", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let st = meta.query_advice(s_type, Rotation::cur());
            vec![q * st.clone() * (st - one())]
        });

        // Guard: consistency only applies between two ADJACENT ACTIVE rows.
        // both_active = s_active[cur] * s_active[next]. This is what makes the
        // ordering/consistency skip inactive rows AND the active->inactive
        // boundary (where the address delta would go negative). So the prover
        // only needs the active accesses contiguous at the top of the sorted
        // table; inactive rows can be left zeroed.
        //
        // is_zero on the address delta: same_addr = 1 - d*d_inv, d*same_addr = 0
        meta.create_gate("memory: same_addr indicator", |meta| {
            let q = meta.query_fixed(q_step, Rotation::cur());
            let both_active = meta.query_advice(s_active, Rotation::cur())
                * meta.query_advice(s_active, Rotation::next());
            let d = meta.query_advice(s_addr, Rotation::next())
                - meta.query_advice(s_addr, Rotation::cur());
            let d_inv = meta.query_advice(d_inv, Rotation::cur());
            let same_addr = one() - d.clone() * d_inv;
            vec![q * both_active * d * same_addr]
        });

        // ordering: addr delta >= 0 via limb recomposition + byte lookups
        meta.create_gate("memory: addr delta recompose", |meta| {
            let q = meta.query_fixed(q_step, Rotation::cur());
            let both_active = meta.query_advice(s_active, Rotation::cur())
                * meta.query_advice(s_active, Rotation::next());
            let d = meta.query_advice(s_addr, Rotation::next())
                - meta.query_advice(s_addr, Rotation::cur());
            let limbs = [
                meta.query_advice(addr_delta_limbs[0], Rotation::cur()),
                meta.query_advice(addr_delta_limbs[1], Rotation::cur()),
                meta.query_advice(addr_delta_limbs[2], Rotation::cur()),
                meta.query_advice(addr_delta_limbs[3], Rotation::cur()),
            ];
            vec![q * both_active * (d - recompose(limbs))]
        });

        // ordering: within same address, clk strictly increases (delta - 1 >= 0)
        meta.create_gate("memory: clk delta recompose", |meta| {
            let q = meta.query_fixed(q_step, Rotation::cur());
            let both_active = meta.query_advice(s_active, Rotation::cur())
                * meta.query_advice(s_active, Rotation::next());
            let d_addr = meta.query_advice(s_addr, Rotation::next())
                - meta.query_advice(s_addr, Rotation::cur());
            let d_inv = meta.query_advice(d_inv, Rotation::cur());
            let same_addr = one() - d_addr * d_inv;

            let d_clk = meta.query_advice(s_clk, Rotation::next())
                - meta.query_advice(s_clk, Rotation::cur())
                - one();
            let limbs = [
                meta.query_advice(clk_delta_limbs[0], Rotation::cur()),
                meta.query_advice(clk_delta_limbs[1], Rotation::cur()),
                meta.query_advice(clk_delta_limbs[2], Rotation::cur()),
                meta.query_advice(clk_delta_limbs[3], Rotation::cur()),
            ];
            vec![q * both_active * same_addr * (d_clk - recompose(limbs))]
        });

        // byte lookups for the ordering limbs, conditioned by both_active so
        // inactive rows / boundaries impose nothing (input collapses to 0,
        // which is in byte_table).
        for i in 0..4 {
            meta.lookup("memory: addr delta limb byte", |meta| {
                let both_active = meta.query_advice(s_active, Rotation::cur())
                    * meta.query_advice(s_active, Rotation::next());
                let limb = meta.query_advice(addr_delta_limbs[i], Rotation::cur());
                vec![(both_active * limb, byte_table)]
            });
            meta.lookup("memory: clk delta limb byte", |meta| {
                let both_active = meta.query_advice(s_active, Rotation::cur())
                    * meta.query_advice(s_active, Rotation::next());
                let limb = meta.query_advice(clk_delta_limbs[i], Rotation::cur());
                vec![(both_active * limb, byte_table)]
            });
        }

        // read-after-write value rules. The next row must be an active READ.
        // The "same address" branch needs the current row active too (so
        // same_addr / val_cur are meaningful); the "new address, read 0" branch
        // covers a READ whose current neighbour is inactive (first active row,
        // or a read of a never-written address). We therefore split the guard:
        //   same-addr rule guarded by both_active,
        //   new-addr  rule guarded by is_read_next alone (val_next must be 0).
        meta.create_gate("memory: read value rule", |meta| {
            let q = meta.query_fixed(q_step, Rotation::cur());
            let active_cur = meta.query_advice(s_active, Rotation::cur());
            let active_next = meta.query_advice(s_active, Rotation::next());
            let both_active = active_cur * active_next.clone();

            let d_addr = meta.query_advice(s_addr, Rotation::next())
                - meta.query_advice(s_addr, Rotation::cur());
            let d_inv = meta.query_advice(d_inv, Rotation::cur());
            let same_addr = one() - d_addr * d_inv;

            let type_next = meta.query_advice(s_type, Rotation::next());
            let is_read_next = active_next * (one() - type_next);

            let val_cur = meta.query_advice(s_value, Rotation::cur());
            let val_next = meta.query_advice(s_value, Rotation::next());

            // same address (both active): val_next = val_cur
            let same_rule =
                both_active * same_addr.clone() * (val_next.clone() - val_cur);
            // new address (addr changed OR current inactive): val_next = 0
            let new_rule = (one() - same_addr) * val_next;

            vec![q * is_read_next * (same_rule + new_rule)]
        });

        // read-after-write, TOP OF TABLE. The step rule above checks a READ at
        // row i+1, so the earliest READ it can reach is position 1 — a READ
        // landing at position 0 of the sorted table is never seen. That row is
        // the smallest (addr, clk) access: it reads memory never written before
        // it, so under zero-initialisation it must return 0. Without this gate a
        // LOAD of the smallest never-written address could return garbage and
        // still satisfy the permutation. Guarded by q_first; harmless on a WRITE
        // (1 - ty = 0) or an inactive row (s_active = 0).
        meta.create_gate("memory: row-0 read is zero", |meta| {
            let q = meta.query_fixed(q_first, Rotation::cur());
            let active = meta.query_advice(s_active, Rotation::cur());
            let ty = meta.query_advice(s_type, Rotation::cur());
            let is_read = active * (one() - ty); // active READ
            let val = meta.query_advice(s_value, Rotation::cur());
            vec![q * is_read * val] // => s_value = 0
        });


        MemoryConfig {
            a, b, c,
            clk, mem_addr, mem_value, mem_type, mem_active,
            s_active, s_addr, s_value, s_clk, s_type,
            d_inv, addr_delta_limbs, clk_delta_limbs, z, byte_table,
            flags, q_exec, q_step, q_first, q_last,
        }
    }
}