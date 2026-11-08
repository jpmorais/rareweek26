use halo2_proofs::{circuit::{AssignedCell, SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Selector}};
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
        // TODO: create the third advice column and bind it to `c`
        let q = meta.complex_selector();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);

        meta.create_gate("add gate", |meta| {

            let a = meta.query_advice(a, Rotation::cur());
            // TODO: query column `b` at the current row
            // TODO: query column `c` at the current row

            // TODO: query the selector `q`

            vec![q*(a + b - c)]

        });

        CircuitConfig {
            a, b, c, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {

            
            // a_next = b_cur
            // b_next = c_cur

            let mut prev_b = None;
            let mut prev_c = None;
            
            for i in 0..5 {

                let cell_a = region.assign_advice(|| "a", config.a, i, || self.x[i])?;
                let cell_b = region.assign_advice(|| "b", config.b, i, || self.y[i])?;
                let cell_c = region.assign_advice(|| "c", config.c, i, || self.z[i])?;

                config.q.enable(&mut region, i)?;

                if let Some(prev) = prev_b {
                    region.constrain_equal(prev, cell_a.cell())?;
                }

                if let Some(prev) = prev_c {
                    // TODO: constrain the `c` cell of the previous row to be equal to the `b` cell of this row
                }

                prev_b = Some(cell_b.cell());
                prev_c = Some(cell_c.cell());
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
        //  9 3 12  <- a + b = c in this row, but a must be 2, the b of the previous row
        //  3 12 15
        //  12 15 27

        let circuit = MyCircuit {
            x: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(1)),
            Value::known(Fp::from(9)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(12))],
            y: vec![
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(12)),
            Value::known(Fp::from(15))],
            z: vec![
            Value::known(Fp::from(2)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(12)),
            Value::known(Fp::from(15)),
            Value::known(Fp::from(27))],
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err())


    }

}
