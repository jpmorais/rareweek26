// Goal: prove knowledge of four private values where each one fits in 8 bits (0 to 255).
// The values go in the advice column a, the numbers 0 to 255 go in the lookup table,
// and the selector q turns the lookup on for the four rows that hold the values.

use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Selector, TableColumn}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


struct MyCircuit<Fp> {
    x: [Value<Fp>;4],
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    // TODO: declare the field `table`, the lookup table column
    q: Selector
}

impl Circuit<Fp> for MyCircuit<Fp> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: [Value::unknown();4]}
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        let table = meta.lookup_table_column();
        let q = meta.complex_selector();

        meta.lookup(|meta | {

            let a = meta.query_advice(a, Rotation::cur());
            let q = meta.query_selector(q);

            // TODO: return the lookup input `q * a` paired with the column `table`

        });

        CircuitConfig {
            a, table, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {
            
            // advice at proof time
            for i in 0..4 {

                region.assign_advice(|| "a", config.a, i, || self.x[i])?;

            }

            // selector at compile time
            for i in 0..4 {
                config.q.enable(&mut region, i)?;
            }

            Ok(())

        })?;

        layouter.assign_table(|| "8 bits numbers", |mut table| {

            for i in 0..256 {
                // TODO: assign the number `i` to the table column at offset `i`
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

        let circuit = MyCircuit {
            x: [
            Value::known(Fp::from(1)),
            Value::known(Fp::from(200)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(255))],
        };

        let instance = vec![];
        let prover = MockProver::run(9, &circuit, instance).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn it_fails() {

        let circuit = MyCircuit {
            x: [
            Value::known(Fp::from(1)),
            Value::known(Fp::from(200)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(256))],
        };

        let instance = vec![];
        let prover = MockProver::run(9, &circuit, instance).unwrap();
        assert!(prover.verify().is_err());

    }


}
