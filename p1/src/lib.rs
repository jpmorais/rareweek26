
use ff::PrimeField;
use halo2_proofs::plonk::{Advice, Circuit, Column, Selector, Expression};
use halo2_proofs::circuit::{SimpleFloorPlanner, Value};
use halo2_proofs::poly::Rotation;

pub struct MyCircuit<F: PrimeField> {
    x: Value<F>,
    y: Value<F>
}

#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    q: Selector
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: Value::unknown(), y: Value::unknown() }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {

        let a = meta.advice_column();
        let b = meta.advice_column();
        let q = meta.complex_selector();

        meta.create_gate("add gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let q = meta.query_selector(q);

            vec![q*(a + b - Expression::Constant(F::from(8)))]
        });

        CircuitConfig {
            a, b, q
        }
        
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<F>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        
        layouter.assign_region(|| "region", |mut region| {

            region.assign_advice(|| "x", config.a, 0, || self.x)?;
            region.assign_advice(|| "y", config.b, 0, || self.y)?;

            // region.enable_selector(|| "selector", &config.q, 0)?;
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
    fn add_two_ok() {

        let circuit = MyCircuit::<Fr> {
            x: Value::known(Fr::from(4)),
            y: Value::known(Fr::from(4))
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn add_two_fail() {

        let circuit = MyCircuit::<Fr> {
            x: Value::known(Fr::from(4)),
            y: Value::known(Fr::from(3))
        };

        let k = 4;
        let instance = vec![];
        let prover = MockProver::run(k, &circuit, instance).unwrap();
        assert!(prover.verify().is_err());

        let advices = prover.advice();
        for i in 0..(2 as usize) {
            println!("a{i}={:?}, b{i}={:?}", advices[0][i], advices[1][i]);
        }

    }
}
