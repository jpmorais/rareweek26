// Goal: range check where the range is defined by the prover, not by the circuit.
// The prover fills the advice column `table` with the allowed values and proves that each value of `a` appears in it.
// Because the table is an advice column, the circuit uses lookup_any instead of lookup, and the selectors q and q_t
// work as tags that mark which rows of `a` and of `table` take part in the lookup.

use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Selector}};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::poly::Rotation;


struct MyCircuit<Fr> {
    x: [Value<Fr>;4],
    values: Vec<u64>
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    table: Column<Advice>,
    q: Selector,
    q_t: Selector
}

impl Circuit<Fr> for MyCircuit<Fr> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: [Value::unknown();4], values: vec![]}
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {

        let a = meta.advice_column();
        let table = meta.advice_column();
        let q = meta.complex_selector();
        // TODO: create the complex selector that tags the table rows and bind it to `q_t`

        meta.lookup_any("range check as advice", |meta| {

            let a = meta.query_advice(a, Rotation::cur());
            let table = meta.query_advice(table, Rotation::cur());
            let q = meta.query_selector(q);
            // TODO: query the selector `q_t`

            // TODO: return the tag pair (`q`, `q_t`) and the pair (`q * a`, `q_t * table`)

        });



        CircuitConfig {
            a, table, q, q_t
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fr>) -> Result<(), halo2_proofs::plonk::ErrorFront> {

        layouter.assign_region(|| "region", |mut region| {
            
            // advice at proof time
            for i in 0..4 {

                region.assign_advice(|| "a", config.a, i, || self.x[i])?;

            }

            // selector at compile time
            for i in 0..4 {
                config.q.enable(&mut region, i)?;
            }

            // selector at compile time
            for i in 0..10 {
                // TODO: enable the selector `q_t` at offset `i`
            }

            // advice as table
            for i in 0..self.values.len() {
                // TODO: assign `self.values[i]` to the column `table` at offset `i`
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
            Value::known(Fr::from(21)),
            Value::known(Fr::from(23)),
            Value::known(Fr::from(22)),
            Value::known(Fr::from(25))],
            values: vec![20, 21, 22, 23, 24, 25, 26, 27, 28]
        };

        let instance = vec![];
        let prover = MockProver::run(5, &circuit, instance).unwrap();
        prover.assert_satisfied();

    }


        #[test]
    fn it_fails() {

        let circuit = MyCircuit {
            x: [
            Value::known(Fr::from(21)),
            Value::known(Fr::from(23)),
            Value::known(Fr::from(22)),
            Value::known(Fr::from(30))],
            values: vec![20, 21, 22, 23, 24, 25, 26, 27, 28]
        };

        let instance = vec![];
        let prover = MockProver::run(5, &circuit, instance).unwrap();
        assert!(prover.verify().is_err());

    }




}
