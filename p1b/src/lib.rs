// Goal: prove knowledge of three private values x, y and z such that x * y = z.
// The values go in row 0 of the advice columns a, b and c, and the selector q
// turns the multiplication constraint on for that row only.

use ff::PrimeField;
use halo2_proofs::plonk::{Advice, Circuit, Column, Selector};
use halo2_proofs::circuit::{SimpleFloorPlanner, Value};
use halo2_proofs::poly::Rotation;

pub struct MyCircuit<F: PrimeField> {
    x: Value<F>,
    y: Value<F>,
    z: Value<F>
}

#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    // TODO: declare the field for the second advice column, named `b`
    c: Column<Advice>,
    q: Selector
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: Value::unknown(), y: Value::unknown(), z: Value::unknown() }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {

        let a = meta.advice_column();
        // TODO: create the second advice column and bind it to `b`
        let c = meta.advice_column();
        let q = meta.complex_selector();

        meta.create_gate("mul gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            // TODO: query column `b` at the current row
            let c = meta.query_advice(c, Rotation::cur());
            let q = meta.query_selector(q);

            // TODO: return the constraint, active only when the selector is on, enforcing that `c` is the product of `a` and `b`
        });

        CircuitConfig {
            a, b, c, q
        }
        
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<F>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        
        layouter.assign_region(|| "region", |mut region| {

            region.assign_advice(|| "x", config.a, 0, || self.x)?;
            // TODO: assign `self.y` to column `b` at offset 0
            region.assign_advice(|| "z", config.c, 0, || self.z)?;

            config.q.enable(&mut region, 0)?;
            Ok(())

        })?;

        Ok(())

    }
}


#[cfg(test)]
mod tests {
    use std::println;

use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;

use super::*;

    #[test]
    fn mul_ok() {

        let circuit = MyCircuit::<Fr> {
            x: Value::known(Fr::from(3)),
            y: Value::known(Fr::from(4)),
            z: Value::known(Fr::from(12))
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn mul_fail() {

        let circuit = MyCircuit::<Fr> {
            x: Value::known(Fr::from(3)),
            y: Value::known(Fr::from(4)),
            z: Value::known(Fr::from(13))
        };

        let k = 4;
        let instance = vec![];
        let prover = MockProver::run(k, &circuit, instance).unwrap();
        assert!(prover.verify().is_err());

        let advices = prover.advice();
        for i in 0..(2 as usize) {
            println!("a{i}={:?}, b{i}={:?}, c{i}={:?}", advices[0][i], advices[1][i], advices[2][i]);
        }

    }
}
