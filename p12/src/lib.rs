use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, ErrorFront, Selector};
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::poly::Rotation;

// advice
// 1 1 2 3 5 8 13 ...   a[cur] + a[next] = a[next_next]

pub struct MyCircuit {
    pub x: Value<Fr>,
    pub y: Value<Fr>,
    pub n: u8,
}

#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    q: Selector,
}

impl Circuit<Fr> for MyCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        MyCircuit { x: Value::unknown(), y: Value::unknown(), n: self.n }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a = meta.advice_column();
        let q = meta.selector();

        meta.create_gate("fibo gate", |meta| {
            let a0 = meta.query_advice(a, Rotation::cur());
            let a1 = meta.query_advice(a, Rotation::next());
            let a2 = meta.query_advice(a, Rotation(2));
            let q = meta.query_selector(q);

            vec![q * (a0 + a1 - a2)]
        });

        CircuitConfig { a, q }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fr>) -> Result<(), ErrorFront> {
        layouter.assign_region(|| "only region", |mut region| {
            let mut cur = self.x;
            let mut next = self.y;

            region.assign_advice(|| "first", config.a, 0, || cur)?;
            region.assign_advice(|| "second", config.a, 1, || next)?;

            for i in 2..(self.n as usize) {
                let next_next = cur + next;
                region.assign_advice(|| "next_next", config.a, i, || next_next)?;

                cur = next;
                next = next_next;
            }

            // Gate at row i checks a[i] + a[i+1] = a[i+2]
            for i in 0..((self.n - 2) as usize) {
                config.q.enable(&mut region, i)?;
            }

            Ok(())
        })?;

        Ok(())
    }
}


#[cfg(test)]
mod tests {


use crate::MyCircuit;

use halo2_proofs::circuit::Value;
use halo2_proofs::halo2curves::bn256::{Bn256, G1Affine, Fr};
use halo2_proofs::plonk::{Circuit, create_proof, keygen_pk, keygen_vk, verify_proof};
use halo2_proofs::transcript::{Blake2bWrite, Blake2bRead, Challenge255, TranscriptWriterBuffer, TranscriptReadBuffer};
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use rand::rngs::OsRng;


    #[test]
    fn it_works() {

        // Params for trusted setup
        let k = 5;
        let params = ParamsKZG::<Bn256>::setup(k, OsRng);
        let verifier_params = params.verifier_params();        
        
        let dummy_circuit = MyCircuit {
            x: Value::unknown(),
            y: Value::unknown(),
            n: 5
        };

        // Keygen
        let vk = keygen_vk(&params, &dummy_circuit).unwrap();
        let pk = keygen_pk(&params, vk.clone(), &dummy_circuit).unwrap();

        // Proof generation
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        let circuit = MyCircuit {
            x: Value::known(Fr::from(1)),
            y: Value::known(Fr::from(1)),
            n: 5
        };

        let instance: Vec<Vec<Fr>> = vec![];
        create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<Bn256>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[instance],
            OsRng,
            &mut transcript
        ).unwrap();
        
        let proof: Vec<u8> = transcript.finalize();
        println!("Proof size: {} bytes", proof.len());
        
        // Verify proof
        let mut transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);        

        let instance: Vec<Vec<Fr>> = vec![];
        verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<Bn256>, Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>, SingleStrategy<Bn256>>(
            &verifier_params, pk.get_vk(), SingleStrategy::new(&verifier_params), &[instance], &mut transcript,
        ).unwrap();
     

    }
}
