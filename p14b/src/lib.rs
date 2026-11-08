mod constants;
mod poseidon;
mod util;


// Round based
// Each round (FullRound and PartialRound)
// (s0, s1, s2) as inputs in each round
// (s0 + rc0, s1 + rc1, s2 + rc2) different rc's each round
// In full round, each element power 5
// In partial round, only first element power 5
// multiply the tuple by the matrix MDS
// output will be (s0', s1', s2')


// We can write a formula for partial and full rounds
// partial round
// (s0 + rc0, s1 + rc1, s2 + rc2)
// ((s0 + rc0)^5, (s1 + rc1)^5, (s2 + rc2)^5)
// s0' = (s0 + rc0)^5 * M[0][0] + (s1 + rc1)*M[0][1] + (s2 + rc2)*M[0][2]
// s1' = ...
// s2' = ...


use ff::Field;
use halo2_proofs::halo2curves::bn256::Fr;
use crate::constants::{MDS, ROUND_CONSTANTS, FULL_ROUNDS, PARTIAL_ROUNDS, T};
use halo2_proofs::circuit::{SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, Fixed, Instance, Selector, Expression};
use halo2_proofs::poly::Rotation;

pub struct PoseidonCircuit {
    pub trace: Vec<[Fr; T]>,
}


// INITIAL           s0   s1   s2    rc0    rc1    rc2    
// AFTER ROUND1      s0'  s1'  s2'

#[derive(Clone, Debug)]
pub struct PoseidonConfig {
    pub s0: Column<Advice>,
    pub s1: Column<Advice>,
    pub s2: Column<Advice>,
    pub rc0: Column<Fixed>,
    pub rc1: Column<Fixed>,
    pub rc2: Column<Fixed>,
    pub q_full: Selector,
    pub q_partial: Selector,
    pub instance: Column<Instance>,
}

impl Circuit<Fr> for PoseidonCircuit  {
    type Config = PoseidonConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { trace: vec![] }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
        
        let s0 = meta.advice_column();
        let s1 = meta.advice_column();
        let s2 = meta.advice_column();

        let rc0 = meta.fixed_column();
        let rc1 = meta.fixed_column();
        let rc2 = meta.fixed_column();

        let q_full = meta.selector();
        let q_partial = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(s0);
        // meta.enable_equality(s1);
        // meta.enable_equality(s2);
        meta.enable_equality(instance);

        meta.create_gate("full round", |meta| {
            let q = meta.query_selector(q_full);

            let s0_cur = meta.query_advice(s0, Rotation::cur());
            let s1_cur = meta.query_advice(s1, Rotation::cur());
            let s2_cur = meta.query_advice(s2, Rotation::cur());

            let s0_next = meta.query_advice(s0, Rotation::next());
            let s1_next = meta.query_advice(s1, Rotation::next());
            let s2_next = meta.query_advice(s2, Rotation::next());

            let rc0 = meta.query_fixed(rc0, Rotation::cur());
            let rc1 = meta.query_fixed(rc1, Rotation::cur());
            let rc2 = meta.query_fixed(rc2, Rotation::cur());

            // AddRoundConstant
            let a0 = s0_cur + rc0;
            // TODO: add the round constant rc1 to s1_cur and bind it to `a1`
            // TODO: add the round constant rc2 to s2_cur and bind it to `a2`

            // S-box: x^5 in all states
            let b0 = a0.clone() * a0.clone() * a0.clone() * a0.clone() * a0;
            // TODO: apply the S-box (power 5) to `a1` and bind it to `b1`
            // TODO: apply the S-box (power 5) to `a2` and bind it to `b2`

            // MDS
            let mds = MDS;
            let c0 = Expression::Constant(mds[0][0]) * b0.clone()
                + Expression::Constant(mds[0][1]) * b1.clone()
                + Expression::Constant(mds[0][2]) * b2.clone();
            let c1 = Expression::Constant(mds[1][0]) * b0.clone()
                + Expression::Constant(mds[1][1]) * b1.clone()
                + Expression::Constant(mds[1][2]) * b2.clone();
            // TODO: compute the third row of the MDS product (mds[2][0..3] times b0, b1, b2) and bind it to `c2`

            vec![
                q.clone() * (c0 - s0_next),
                q.clone() * (c1 - s1_next),
                q * (c2 - s2_next),
            ]            

        });

        meta.create_gate("partial round", |meta| {
                let q = meta.query_selector(q_partial);

                let s0_cur = meta.query_advice(s0, Rotation::cur());
                let s1_cur = meta.query_advice(s1, Rotation::cur());
                let s2_cur = meta.query_advice(s2, Rotation::cur());

                let s0_next = meta.query_advice(s0, Rotation::next());
                let s1_next = meta.query_advice(s1, Rotation::next());
                let s2_next = meta.query_advice(s2, Rotation::next());

                let rc0 = meta.query_fixed(rc0, Rotation::cur());
                let rc1 = meta.query_fixed(rc1, Rotation::cur());
                let rc2 = meta.query_fixed(rc2, Rotation::cur());

                // AddRoundConstant
                let a0 = s0_cur + rc0;
                let a1 = s1_cur + rc1;
                let a2 = s2_cur + rc2;

                // S-box: x^5 only in the first state
                let b0 = a0.clone() * a0.clone() * a0.clone() * a0.clone() * a0;

                // MDS
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

                // TODO: return the three constraints, each multiplied by the selector `q`: c0 = s0_next, c1 = s1_next, c2 = s2_next
            });

            PoseidonConfig {
                s0, s1, s2, rc0, rc1, rc2, q_full, q_partial, instance
            }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fr>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        
        let output_cell = layouter.assign_region(
                || "poseidon",
                |mut region| {

                    // Round constants
                    for (i, rc) in ROUND_CONSTANTS.iter().enumerate() {
                        region.assign_fixed(|| "rc0", config.rc0, i, || Value::known(rc[0]))?;
                        region.assign_fixed(|| "rc1", config.rc1, i, || Value::known(rc[1]))?;
                        region.assign_fixed(|| "rc2", config.rc2, i, || Value::known(rc[2]))?;
                    }

                    // Trace
                    let mut output_cell = None;
                    for (i, state) in self.trace.iter().enumerate() {
                        let cell = region.assign_advice(
                            || "s0", config.s0, i, || Value::known(state[0])
                        )?;
                        region.assign_advice(|| "s1", config.s1, i, || Value::known(state[1]))?;
                        region.assign_advice(|| "s2", config.s2, i, || Value::known(state[2]))?;
                        if i == 65 {
                            output_cell = Some(cell);
                        }
                    }

                    // Selectors
                    let r_f = FULL_ROUNDS / 2;
                    for i in 0..65 {
                        if i < r_f || i >= r_f + PARTIAL_ROUNDS {
                            config.q_full.enable(&mut region, i)?;
                        } else {
                            config.q_partial.enable(&mut region, i)?;
                        }
                    }

                    Ok(output_cell.unwrap())
                },
            )?;

            layouter.constrain_instance(output_cell.cell(), config.instance, 0)?;

            Ok(())        
    }
    
}

#[cfg(test)]
mod tests {

    use std::println;

use crate::{PoseidonCircuit, util::poseidon_trace};
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    #[test]
    fn it_works() {

        let input1 = Fr::from(1);
        let input2 = Fr::from(2);
        let trace = poseidon_trace(input1, input2);
        println!("{:#?}", trace);

        let instance = vec![vec![trace[65][0].clone()]];

        let circuit = PoseidonCircuit {
            trace
        };

        let prover = MockProver::run(7, &circuit, instance).unwrap();
        prover.assert_satisfied();


    }
}
