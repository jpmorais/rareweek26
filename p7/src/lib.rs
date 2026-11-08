use halo2_proofs::{circuit::{AssignedCell, SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Instance, Selector}};
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
    instance: Column<Instance>,
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
        let instance = meta.instance_column();
        let q = meta.complex_selector();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(instance);

        meta.create_gate("add gate", |meta| {

            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let q = meta.query_selector(q);

            vec![q*(a + b - c)]

        });

        CircuitConfig {
            a, b, c, instance, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        let (cell_a0, cell_b0, cell_clast) = layouter.assign_region(|| "region", |mut region| {

            
            // a_next = b_cur
            // b_next = c_cur

            let mut prev_b = None;
            let mut prev_c = None;
            let mut first_a = None;
            let mut first_b = None;
            
            for i in 0..5 {

                let cell_a = region.assign_advice(|| "a", config.a, i, || self.x[i])?;
                let cell_b = region.assign_advice(|| "b", config.b, i, || self.y[i])?;
                let cell_c = region.assign_advice(|| "c", config.c, i, || self.z[i])?;

                config.q.enable(&mut region, i)?;

                if let Some(prev) = prev_b {
                    region.constrain_equal(prev, cell_a.cell())?;
                }

                if let Some(prev) = prev_c {
                    region.constrain_equal(prev, cell_b.cell())?;
                }

                if i == 0 {
                    first_a = Some(cell_a.cell());
                    first_b = Some(cell_b.cell());
                }

                prev_b = Some(cell_b.cell());
                prev_c = Some(cell_c.cell());
            }

            Ok((first_a.unwrap(),first_b.unwrap(), prev_c.unwrap()))

        })?;

        layouter.constrain_instance(cell_a0, config.instance, 0)?;
        layouter.constrain_instance(cell_b0, config.instance, 1)?;
        
        layouter.constrain_instance(cell_clast, config.instance, 2)?;

        Ok(())


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

        let instance = vec![Fp::from(1),Fp::from(1),Fp::from(13)];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        prover.assert_satisfied();

    }

        #[test]
    fn it_does_not_works() {

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

        let instance = vec![Fp::from(1),Fp::from(1),Fp::from(14)];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        assert!(prover.verify().is_err())


    }

}
