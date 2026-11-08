// Goal: prove knowledge of two private values x and y, and of z = x * x + y.
// The values go in rows 0, 1 and 2 of the single advice column a. Only x and y
// are inputs: synthesize computes z, and the gate enabled at row 0 constrains it.

use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::circuit::{SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, Selector};
use halo2_proofs::poly::Rotation;

pub struct MyCircuit {
    x: Value<Fr>,
    y: Value<Fr>,
}

#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    q: Selector
}

impl Circuit<Fr> for MyCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: Value::unknown(), y: Value::unknown() }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
        
        let a = meta.advice_column();
        let q = meta.selector();

        meta.create_gate("square add gate", |meta| {

            let a1 = meta.query_advice(a, Rotation::cur());
            let a2 = meta.query_advice(a, Rotation::next());
            // TODO: query column `a` two rows after the current row and bind it to `a3`

            let q = meta.query_selector(q);

            // TODO: return the constraint, active only when the selector is on, enforcing that `a3` equals `a1` squared plus `a2`

        });

        CircuitConfig {
            a, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fr>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        
        layouter.assign_region(|| "region", |mut region| {

            region.assign_advice(|| "a0", config.a, 0, || self.x)?;
            region.assign_advice(|| "a1", config.a, 1, || self.y)?;
            // TODO: compute the witness value `z` from `self.x` and `self.y`
            // TODO: assign `z` to column `a` at offset 2

            // TODO: enable the selector at the row that lets the gate read rows 0, 1 and 2

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
            x: Value::known(Fr::from(3)),
            y: Value::known(Fr::from(4)),
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }


}
