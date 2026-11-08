// Goal: prove knowledge of four pairs of private values whose sums are constants fixed by the circuit.
// The pairs go in the advice columns a and b. The constants 3, 5, 7 and 9 go in the fixed column c,
// so the prover cannot change them, and the selector q turns the constraint a + b = c on in every row.

use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Selector, Fixed}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


pub struct MyCircuit<Fp> {
    x: [Value<Fp>;4],
    y: [Value<Fp>;4],
}

#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Fixed>,
    q: Selector
}

impl Circuit<Fp> for MyCircuit<Fp> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: [Value::unknown();4], y: [Value::unknown();4] }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        let b = meta.advice_column();
        // TODO: create the fixed column and bind it to `c`
        let q = meta.complex_selector();

        meta.create_gate("add gate", |meta| {

            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());

            // TODO: query the fixed column `c` at the current row and bind it to `c`
            // let c = meta.query_any(c, Rotation::cur());

            let q = meta.query_selector(q);

            vec![q*(a + b - c)]

        });

        CircuitConfig {
            a, b, c, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {
            
            // advices
            for i in 0..4 {

                region.assign_advice(|| "a", config.a, i, || self.x[i])?;
                region.assign_advice(|| "b", config.b, i, || self.y[i])?;

            }


            // fixed
            for i in 0..4 {

                // TODO: assign the constant `2*i + 3` to the fixed column `c` at offset `i`
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

        let circuit = MyCircuit {
            x: [
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(4))],
            y: [
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(4)),
            Value::known(Fp::from(5))],
        };

        let instance = vec![];
        let prover = MockProver::run(4, &circuit, instance).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn it_fails() {

        let circuit = MyCircuit {
            x: [
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(4))],
            y: [
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(5)),
            Value::known(Fp::from(5))],
        };

        let instance = vec![];
        let prover = MockProver::run(4, &circuit, instance).unwrap();
        assert!(prover.verify().is_err());

    }


}
