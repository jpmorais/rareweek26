use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Selector}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


struct MyCircuit<Fp> {
    x: Vec<Value<Fp>>,
    y: Vec<Value<Fp>>,
    z: Vec<Value<Fp>>,
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q: Selector
}

impl Circuit<Fp> for MyCircuit<Fp> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: vec![], y: vec![], z: vec![] }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let q = meta.complex_selector();

        meta.create_gate("add gate", |meta| {

            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let q = meta.query_selector(q);

            vec![q*(a + b - c)]

        });

        CircuitConfig {
            a, b, c, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {

            for i in 0..5 {

                region.assign_advice(|| "a", config.a, i, || self.x[i])?;
                region.assign_advice(|| "b", config.b, i, || self.y[i])?;
                region.assign_advice(|| "c", config.c, i, || self.z[i])?;

                config.q.enable(&mut region, i)?;
            }

            Ok(())

        })


    }

}



#[cfg(test)]
mod tests {
    use halo2_proofs::dev::MockProver;

use super::*;

    #[test]
    fn it_works() {

        //  1 1 2
        //  1 2 3
        //  2 3 5
        //  3 5 8
        //  5 8 13

        let circuit = MyCircuit {
            x: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5))],
            y: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8))],
            z: vec![
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(13))],
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

    }

        #[test]
    fn it_does_not_works() {

        //  1 1 2
        //  1 2 3
        //  2 3 5
        //  3 5 8
        //  5 8 14  <- 5 + 8 != 14

        let circuit = MyCircuit {
            x: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5))],
            y: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8))],
            z: vec![
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(14))],
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());

    }

}
