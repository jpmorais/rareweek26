// Goal: prove knowledge of seven rows of private values where a + b = c in every row.
// The rows look like the Fibonacci sequence, but nothing links one row to the next,
// because the circuit has no copy constraints.

use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Instance, Selector}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


pub struct MyCircuit {
    x: Vec<Value<Fp>>,
    y: Vec<Value<Fp>>,
    z: Vec<Value<Fp>>,
}

#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    instance: Column<Instance>,
    q: Selector
}

impl Circuit<Fp> for MyCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: vec![], y: vec![], z: vec![] }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        let b = meta.advice_column();
        // TODO: create the third advice column and bind it to `c`
        let instance = meta.instance_column();
        let q = meta.complex_selector();

        meta.create_gate("add gate", |meta| {

            let a = meta.query_advice(a, Rotation::cur());
            // TODO: query column `b` at the current row
            // TODO: query column `c` at the current row

            let q = meta.query_selector(q);

            vec![q*(a + b - c)]

        });

        CircuitConfig {
            a, b, c, instance, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {

            for i in 0..7 {

                region.assign_advice(|| "a", config.a, i, || self.x[i])?;
                // TODO: assign `self.y[i]` to column `b` at offset `i`
                // TODO: assign `self.z[i]` to column `c` at offset `i`

                // TODO: enable the selector at offset `i`
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
        //  8 13 21
        //  13 21 34

        let circuit = MyCircuit {
            x: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(13))],
            y: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(13)),
            Value::known(Fp::from(21))],
            z: vec![
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(13)),
            Value::known(Fp::from(21)),
            Value::known(Fp::from(34))],
        };

        let instance = vec![];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn it_fails() {

        //  1 1 2
        //  1 2 3
        //  2 3 5
        //  3 5 8
        //  5 8 13
        //  8 13 21
        //  13 21 35  <- 13 + 21 != 35

        let circuit = MyCircuit {
            x: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(13))],
            y: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(13)),
            Value::known(Fp::from(21))],
            z: vec![
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(8)),
            Value::known(Fp::from(13)),
            Value::known(Fp::from(21)),
            Value::known(Fp::from(35))],
        };

        let instance = vec![];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        assert!(prover.verify().is_err());

    }

}
