mod constants;
mod poseidon;
mod util;

use ff::Field;
use halo2_proofs::halo2curves::bn256::Fr;
use crate::constants::{MDS, ROUND_CONSTANTS, FULL_ROUNDS, PARTIAL_ROUNDS, T};
use halo2_proofs::circuit::{SimpleFloorPlanner, Value, Layouter};
use halo2_proofs::plonk::{Advice, Circuit, Column, Fixed, Selector, Expression, ConstraintSystem, ErrorFront};
use halo2_proofs::poly::Rotation;

use util::poseidon_trace;

const MAX_OPS: usize = 8;

#[derive(Clone, Debug)]
pub struct PoseidonTable {
    // poseidon state
    pub s0: Column<Advice>,
    pub s1: Column<Advice>,
    pub s2: Column<Advice>,

    // inputs (repeated across all rows of one invocation)
    pub inp1: Column<Advice>,
    pub inp2: Column<Advice>,

    // round constants
    pub rc0: Column<Fixed>,
    pub rc1: Column<Fixed>,
    pub rc2: Column<Fixed>,

    // flags (Fixed, not Selector — needed inside the lookup)
    pub flag_start: Column<Fixed>,
    pub flag_full: Column<Fixed>,
    pub flag_partial: Column<Fixed>,
    pub flag_final: Column<Fixed>,
}

impl PoseidonTable {
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
        let s0 = meta.advice_column();
        let s1 = meta.advice_column();
        let s2 = meta.advice_column();
        let inp1 = meta.advice_column();
        let inp2 = meta.advice_column();

        let rc0 = meta.fixed_column();
        let rc1 = meta.fixed_column();
        let rc2 = meta.fixed_column();

        let flag_start = meta.fixed_column();
        let flag_full = meta.fixed_column();
        let flag_partial = meta.fixed_column();
        let flag_final = meta.fixed_column();

        // Gate start: initialize state with [0, inp1, inp2]
        meta.create_gate("start", |meta| {
            let flag = meta.query_fixed(flag_start, Rotation::cur());
            let inp1 = meta.query_advice(inp1, Rotation::cur());
            let inp2 = meta.query_advice(inp2, Rotation::cur());
            let s0 = meta.query_advice(s0, Rotation::cur());
            let s1 = meta.query_advice(s1, Rotation::cur());
            let s2 = meta.query_advice(s2, Rotation::cur());

            vec![
                flag.clone() * s0,            // capacity = 0
                flag.clone() * (s1 - inp1),   // s1 = inp1
                flag * (s2 - inp2),           // s2 = inp2
            ]
        });

        // Gate full round
        meta.create_gate("full round", |meta| {
            let q = meta.query_fixed(flag_full, Rotation::cur());

            let s0_cur = meta.query_advice(s0, Rotation::cur());
            let s1_cur = meta.query_advice(s1, Rotation::cur());
            let s2_cur = meta.query_advice(s2, Rotation::cur());

            let s0_next = meta.query_advice(s0, Rotation::next());
            let s1_next = meta.query_advice(s1, Rotation::next());
            let s2_next = meta.query_advice(s2, Rotation::next());

            let inp1_cur = meta.query_advice(inp1, Rotation::cur());
            let inp2_cur = meta.query_advice(inp2, Rotation::cur());
            let inp1_next = meta.query_advice(inp1, Rotation::next());
            let inp2_next = meta.query_advice(inp2, Rotation::next());

            let rc0 = meta.query_fixed(rc0, Rotation::cur());
            let rc1 = meta.query_fixed(rc1, Rotation::cur());
            let rc2 = meta.query_fixed(rc2, Rotation::cur());

            let a0 = s0_cur + rc0;
            let a1 = s1_cur + rc1;
            let a2 = s2_cur + rc2;

            // s-box: x^5 on all lanes
            let b0 = a0.clone() * a0.clone() * a0.clone() * a0.clone() * a0;
            let b1 = a1.clone() * a1.clone() * a1.clone() * a1.clone() * a1;
            let b2 = a2.clone() * a2.clone() * a2.clone() * a2.clone() * a2;

            let mds = MDS;
            let c0 = Expression::Constant(mds[0][0]) * b0.clone()
                + Expression::Constant(mds[0][1]) * b1.clone()
                + Expression::Constant(mds[0][2]) * b2.clone();
            let c1 = Expression::Constant(mds[1][0]) * b0.clone()
                + Expression::Constant(mds[1][1]) * b1.clone()
                + Expression::Constant(mds[1][2]) * b2.clone();
            let c2 = Expression::Constant(mds[2][0]) * b0
                + Expression::Constant(mds[2][1]) * b1
                + Expression::Constant(mds[2][2]) * b2;

            vec![
                q.clone() * (c0 - s0_next),
                q.clone() * (c1 - s1_next),
                q.clone() * (c2 - s2_next),
                q.clone() * (inp1_cur - inp1_next),
                q * (inp2_cur - inp2_next),
            ]
        });

        // Gate partial round
        meta.create_gate("partial round", |meta| {
            let q = meta.query_fixed(flag_partial, Rotation::cur());

            let s0_cur = meta.query_advice(s0, Rotation::cur());
            let s1_cur = meta.query_advice(s1, Rotation::cur());
            let s2_cur = meta.query_advice(s2, Rotation::cur());

            let s0_next = meta.query_advice(s0, Rotation::next());
            let s1_next = meta.query_advice(s1, Rotation::next());
            let s2_next = meta.query_advice(s2, Rotation::next());

            let inp1_cur = meta.query_advice(inp1, Rotation::cur());
            let inp2_cur = meta.query_advice(inp2, Rotation::cur());
            let inp1_next = meta.query_advice(inp1, Rotation::next());
            let inp2_next = meta.query_advice(inp2, Rotation::next());

            let rc0 = meta.query_fixed(rc0, Rotation::cur());
            let rc1 = meta.query_fixed(rc1, Rotation::cur());
            let rc2 = meta.query_fixed(rc2, Rotation::cur());

            let a0 = s0_cur + rc0;
            let a1 = s1_cur + rc1;
            let a2 = s2_cur + rc2;

            // s-box: x^5 only on the first lane
            let b0 = a0.clone() * a0.clone() * a0.clone() * a0.clone() * a0;

            let mds = MDS;
            let c0 = Expression::Constant(mds[0][0]) * b0.clone()
                + Expression::Constant(mds[0][1]) * a1.clone()
                + Expression::Constant(mds[0][2]) * a2.clone();
            let c1 = Expression::Constant(mds[1][0]) * b0.clone()
                + Expression::Constant(mds[1][1]) * a1.clone()
                + Expression::Constant(mds[1][2]) * a2.clone();
            let c2 = Expression::Constant(mds[2][0]) * b0
                + Expression::Constant(mds[2][1]) * a1
                + Expression::Constant(mds[2][2]) * a2;

            vec![
                q.clone() * (c0 - s0_next),
                q.clone() * (c1 - s1_next),
                q.clone() * (c2 - s2_next),
                q.clone() * (inp1_cur - inp1_next),
                q * (inp2_cur - inp2_next),
            ]
        });

        PoseidonTable {
            s0, s1, s2, inp1, inp2,
            rc0, rc1, rc2,
            flag_start, flag_full, flag_partial, flag_final,
        }
    }

    fn populate(
        &self,
        layouter: &mut impl Layouter<Fr>,
        traces: &Vec<Vec<[Fr; T]>>,
    ) -> Result<(), ErrorFront> {
        // pad with hash(0,0) up to MAX_OPS so the fixed columns are
        // identical between keygen and prove
        let dummy = poseidon_trace(Fr::ZERO, Fr::ZERO);
        let mut padded = traces.clone();
        while padded.len() < MAX_OPS {
            padded.push(dummy.clone());
        }

        layouter.assign_region(
            || "poseidon table",
            |mut region| {
                let mut row = 0;
                let r_f = FULL_ROUNDS / 2;

                // dummy row (all zero) for disabled lookups
                region.assign_fixed(|| "flag_start", self.flag_start, row, || Value::known(Fr::ZERO))?;
                region.assign_fixed(|| "flag_full", self.flag_full, row, || Value::known(Fr::ZERO))?;
                region.assign_fixed(|| "flag_partial", self.flag_partial, row, || Value::known(Fr::ZERO))?;
                region.assign_fixed(|| "flag_final", self.flag_final, row, || Value::known(Fr::ZERO))?;
                region.assign_fixed(|| "rc0", self.rc0, row, || Value::known(Fr::ZERO))?;
                region.assign_fixed(|| "rc1", self.rc1, row, || Value::known(Fr::ZERO))?;
                region.assign_fixed(|| "rc2", self.rc2, row, || Value::known(Fr::ZERO))?;
                region.assign_advice(|| "s0", self.s0, row, || Value::known(Fr::ZERO))?;
                region.assign_advice(|| "s1", self.s1, row, || Value::known(Fr::ZERO))?;
                region.assign_advice(|| "s2", self.s2, row, || Value::known(Fr::ZERO))?;
                region.assign_advice(|| "inp1", self.inp1, row, || Value::known(Fr::ZERO))?;
                region.assign_advice(|| "inp2", self.inp2, row, || Value::known(Fr::ZERO))?;
                row += 1;

                for trace in padded.iter() {
                    let inp_a = trace[0][1];
                    let inp_b = trace[0][2];

                    // round rows
                    for i in 0..65 {
                        let is_start = i == 0;
                        let is_full = i < r_f || i >= r_f + PARTIAL_ROUNDS;
                        let is_partial = !is_full;

                        region.assign_fixed(|| "flag_start", self.flag_start, row,
                            || Value::known(if is_start { Fr::ONE } else { Fr::ZERO }))?;
                        region.assign_fixed(|| "flag_full", self.flag_full, row,
                            || Value::known(if is_full { Fr::ONE } else { Fr::ZERO }))?;
                        region.assign_fixed(|| "flag_partial", self.flag_partial, row,
                            || Value::known(if is_partial { Fr::ONE } else { Fr::ZERO }))?;
                        region.assign_fixed(|| "flag_final", self.flag_final, row,
                            || Value::known(Fr::ZERO))?;

                        region.assign_fixed(|| "rc0", self.rc0, row,
                            || Value::known(ROUND_CONSTANTS[i][0]))?;
                        region.assign_fixed(|| "rc1", self.rc1, row,
                            || Value::known(ROUND_CONSTANTS[i][1]))?;
                        region.assign_fixed(|| "rc2", self.rc2, row,
                            || Value::known(ROUND_CONSTANTS[i][2]))?;

                        region.assign_advice(|| "s0", self.s0, row,
                            || Value::known(trace[i][0]))?;
                        region.assign_advice(|| "s1", self.s1, row,
                            || Value::known(trace[i][1]))?;
                        region.assign_advice(|| "s2", self.s2, row,
                            || Value::known(trace[i][2]))?;

                        region.assign_advice(|| "inp1", self.inp1, row,
                            || Value::known(inp_a))?;
                        region.assign_advice(|| "inp2", self.inp2, row,
                            || Value::known(inp_b))?;

                        row += 1;
                    }

                    // final row (result ready for lookup)
                    region.assign_fixed(|| "flag_start", self.flag_start, row,
                        || Value::known(Fr::ZERO))?;
                    region.assign_fixed(|| "flag_full", self.flag_full, row,
                        || Value::known(Fr::ZERO))?;
                    region.assign_fixed(|| "flag_partial", self.flag_partial, row,
                        || Value::known(Fr::ZERO))?;
                    region.assign_fixed(|| "flag_final", self.flag_final, row,
                        || Value::known(Fr::ONE))?;

                    region.assign_fixed(|| "rc0", self.rc0, row,
                        || Value::known(Fr::ZERO))?;
                    region.assign_fixed(|| "rc1", self.rc1, row,
                        || Value::known(Fr::ZERO))?;
                    region.assign_fixed(|| "rc2", self.rc2, row,
                        || Value::known(Fr::ZERO))?;

                    region.assign_advice(|| "s0", self.s0, row,
                        || Value::known(trace[65][0]))?;
                    region.assign_advice(|| "s1", self.s1, row,
                        || Value::known(trace[65][1]))?;
                    region.assign_advice(|| "s2", self.s2, row,
                        || Value::known(trace[65][2]))?;

                    region.assign_advice(|| "inp1", self.inp1, row,
                        || Value::known(inp_a))?;
                    region.assign_advice(|| "inp2", self.inp2, row,
                        || Value::known(inp_b))?;

                    row += 1;
                }

                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
pub struct PoseidonChip {
    pub sel: Selector,
    pub in1: Column<Advice>,
    pub in2: Column<Advice>,
    pub out: Column<Advice>,
    pub on: Column<Advice>,
    pub table: PoseidonTable,
}

impl PoseidonChip {
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        table: PoseidonTable,
    ) -> Self {
        let sel = meta.complex_selector();
        let in1 = meta.advice_column();
        let in2 = meta.advice_column();
        let out = meta.advice_column();
        let on = meta.advice_column();

        // on must be boolean
        meta.create_gate("boolean on", |meta| {
            let sel = meta.query_selector(sel);
            let on = meta.query_advice(on, Rotation::cur());
            vec![
                sel * on.clone() * (on - Expression::Constant(Fr::ONE)),
            ]
        });

        // lookup into poseidon table
        meta.lookup_any("poseidon lookup", |cells| {
            let sel = cells.query_selector(sel);
            let on = cells.query_advice(on, Rotation::cur());
            let in1 = cells.query_advice(in1, Rotation::cur());
            let in2 = cells.query_advice(in2, Rotation::cur());
            let out = cells.query_advice(out, Rotation::cur());

            let do_lookup = sel * on;

            let flag = cells.query_fixed(table.flag_final, Rotation::cur());
            let table_inp1 = cells.query_advice(table.inp1, Rotation::cur());
            let table_inp2 = cells.query_advice(table.inp2, Rotation::cur());
            let table_out = cells.query_advice(table.s0, Rotation::cur());

            // every table expression is tagged by flag_final (a fixed query),
            // as required by the PSE lookup_any
            vec![
                (do_lookup.clone(),        flag.clone()),
                (do_lookup.clone() * in1,  flag.clone() * table_inp1),
                (do_lookup.clone() * in2,  flag.clone() * table_inp2),
                (do_lookup * out,          flag * table_out),
            ]
        });

        PoseidonChip { sel, in1, in2, out, on, table }
    }

    // verify that (in1, in2, out) appears in the table as a final row.
    // values are assigned directly; the lookup decides if the triple holds.
    fn verify(
        &self,
        layouter: &mut impl Layouter<Fr>,
        in1: Fr,
        in2: Fr,
        out: Fr,
    ) -> Result<(), ErrorFront> {
        layouter.assign_region(
            || "poseidon verify",
            |mut region| {
                self.sel.enable(&mut region, 0)?;

                region.assign_advice(|| "on", self.on, 0, || Value::known(Fr::ONE))?;
                region.assign_advice(|| "in1", self.in1, 0, || Value::known(in1))?;
                region.assign_advice(|| "in2", self.in2, 0, || Value::known(in2))?;
                region.assign_advice(|| "out", self.out, 0, || Value::known(out))?;

                Ok(())
            },
        )
    }
}

pub struct PoseidonCircuit {
    pub traces: Vec<Vec<[Fr; T]>>,    // populate the table (known hashes)
    pub queries: Vec<(Fr, Fr, Fr)>,   // (in1, in2, out) triples to verify
}

#[derive(Clone, Debug)]
pub struct PoseidonCircuitConfig {
    pub poseidon: PoseidonChip,
}

impl Circuit<Fr> for PoseidonCircuit {
    type Config = PoseidonCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { traces: vec![], queries: vec![] }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let table = PoseidonTable::configure(meta);
        let poseidon = PoseidonChip::configure(meta, table);

        PoseidonCircuitConfig { poseidon }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), ErrorFront> {

        // populate the poseidon table (pads to MAX_OPS internally)
        config.poseidon.table.populate(&mut layouter, &self.traces)?;

        // verify each (in1, in2, out) triple against the table
        for (in1, in2, out) in self.queries.iter() {
            config.poseidon.verify(&mut layouter, *in1, *in2, *out)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::dev::MockProver;
    use crate::poseidon::hash;

    const K: u32 = 11; // dummy row + 8 blocks * 66 rows = 529, plus lookup overhead

    // two honest hash executions: both triples are correct
    #[test]
    fn accepts_two_valid_hashes() {
        let a = (Fr::from(3), Fr::from(7));
        let b = (Fr::from(42), Fr::from(99));

        let traces = vec![
            poseidon_trace(a.0, a.1),
            poseidon_trace(b.0, b.1),
        ];

        let queries = vec![
            (a.0, a.1, hash([a.0, a.1])),
            (b.0, b.1, hash([b.0, b.1])),
        ];

        let circuit = PoseidonCircuit { traces, queries };
        let prover = MockProver::run(K, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // one honest triple, one forged output: the lookup must reject
    #[test]
    fn rejects_forged_hash() {
        let a = (Fr::from(3), Fr::from(7));
        let b = (Fr::from(42), Fr::from(99));

        let traces = vec![
            poseidon_trace(a.0, a.1),
            poseidon_trace(b.0, b.1),
        ];

        let queries = vec![
            (a.0, a.1, hash([a.0, a.1])),   // valid
            (b.0, b.1, Fr::from(12345)),    // forged output
        ];

        let circuit = PoseidonCircuit { traces, queries };
        let prover = MockProver::run(K, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn rejects_intermediate_state_as_output() {
        let a = (Fr::from(3), Fr::from(7));
        let trace = poseidon_trace(a.0, a.1);

        // s0 of an intermediate round (not the final row 65)
        let intermediate = trace[30][0];

        let traces = vec![trace];

        let queries = vec![
            (a.0, a.1, intermediate),   // matches an intermediate row, not the final
        ];

        let circuit = PoseidonCircuit { traces, queries };
        let prover = MockProver::run(K, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }    
}