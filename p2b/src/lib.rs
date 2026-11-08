// Goal: prove knowledge of three private values x, y and z such that x * y = z.
// The values go in rows 0, 1 and 2 of the single advice column a. The selector q
// is enabled at row 2, and the gate looks back at the two previous rows.

use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::circuit::{SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, Selector};
use halo2_proofs::poly::Rotation;

struct MyCircuit {
    x: Value<Fr>,
    y: Value<Fr>,
    z: Value<Fr>
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    q: Selector
}

impl Circuit<Fr> for MyCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: Value::unknown(), y: Value::unknown(), z: Value::unknown() }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
        
        let a = meta.advice_column();
        let q = meta.selector();

        meta.create_gate("mul gate", |meta| {

            // TODO: query column `a` two rows before the current row and bind it to `a1`
            // TODO: query column `a` one row before the current row and bind it to `a2`
            let a3 = meta.query_advice(a, Rotation::cur());

            let q = meta.query_selector(q);

            // TODO: return the constraint, active only when the selector is on, enforcing that `a3` is the product of `a1` and `a2`

        });

        CircuitConfig {
            a, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fr>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        
        layouter.assign_region(|| "region", |mut region| {

            region.assign_advice(|| "a0", config.a, 0, || self.x)?;
            // TODO: assign `self.y` to column `a` at offset 1
            region.assign_advice(|| "a2", config.a, 2, || self.z)?;

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
            z: Value::known(Fr::from(12))
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn it_fails() {

        let circuit = MyCircuit {
            x: Value::known(Fr::from(3)),
            y: Value::known(Fr::from(4)),
            z: Value::known(Fr::from(13))
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());

    }

}
