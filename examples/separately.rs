use application::StandardPlonk;
use prelude::*;

use halo2_proofs::poly::commitment::Params;
use halo2_solidity_verifier::{
    compile_solidity, encode_calldata, BatchOpenScheme::Bdfg21, Evm, Keccak256Transcript,
    SolidityGenerator,
};

const K_RANGE: Range<u32> = 13..14;

fn main() {
    let mut rng = seeded_std_rng();

    let params = setup(K_RANGE, &mut rng);

    let vk = keygen_vk(&params[&K_RANGE.start], &StandardPlonk::default()).unwrap();
    let generator = SolidityGenerator::new(&params[&K_RANGE.start], &vk, Bdfg21, 0);
    let (verifier_solidity, _) = generator.render_separately().unwrap();
    save_solidity("Halo2VerifierReusable.sol", &verifier_solidity);

    let verifier_creation_code = compile_solidity(&verifier_solidity);
    let verifier_creation_code_size = verifier_creation_code.len();
    println!("Verifier creation code size: {verifier_creation_code_size}");

    let mut evm = Evm::default();
    let (verifier_address, _) = evm.create(verifier_creation_code);

    let deployed_verifier_solidity = verifier_solidity;

    for k in K_RANGE {
        let num_instances = k as usize;
        let circuit = StandardPlonk::rand(num_instances, &mut rng);

        let vk = keygen_vk(&params[&k], &circuit).unwrap();
        let pk = keygen_pk(&params[&k], vk, &circuit).unwrap();
        let generator = SolidityGenerator::new(&params[&k], pk.get_vk(), Bdfg21, num_instances);
        let (verifier_solidity, vk_solidity) = generator.render_separately().unwrap();
        save_solidity(format!("Halo2VerifyingArtifact-{k}.sol"), &vk_solidity);

        assert_eq!(deployed_verifier_solidity, verifier_solidity);

        let vk_creation_code = compile_solidity(&vk_solidity);
        let (vk_address, _) = evm.create(vk_creation_code);

        let calldata = {
            let instances = circuit.instances();
            let proof = create_proof_checked(&params[&k], &pk, circuit, &instances, &mut rng);
            encode_calldata(Some(vk_address.into()), &proof, &instances)
        };
        let (gas_cost, output) = evm.call(verifier_address, calldata);
        assert_eq!(output, [vec![0; 31], vec![1]].concat());
        println!("Gas cost of verifying standard Plonk with 2^{k} rows: {gas_cost}");
    }
}

fn save_solidity(name: impl AsRef<str>, solidity: &str) {
    const DIR_GENERATED: &str = "./generated";

    create_dir_all(DIR_GENERATED).unwrap();
    File::create(format!("{DIR_GENERATED}/{}", name.as_ref()))
        .unwrap()
        .write_all(solidity.as_bytes())
        .unwrap();
}

fn setup(k_range: Range<u32>, mut rng: impl RngCore) -> HashMap<u32, ParamsKZG<Bn256>> {
    k_range
        .clone()
        .zip(k_range.map(|k| ParamsKZG::<Bn256>::setup(k, &mut rng)))
        .collect()
}

fn create_proof_checked(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: impl Circuit<Fr>,
    instances: &[Fr],
    mut rng: impl RngCore + Send + Sync,
) -> Vec<u8> {
    use halo2_proofs::{
        poly::kzg::{
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::SingleStrategy,
        },
        transcript::TranscriptWriterBuffer,
    };

    let proof = {
        let mut transcript = Keccak256Transcript::new(Vec::new());
        create_proof::<_, ProverSHPLONK<_>, _, _, _, _>(
            params,
            pk,
            &[circuit],
            &[&[instances]],
            &mut rng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let result = {
        let mut transcript = Keccak256Transcript::new(proof.as_slice());
        verify_proof::<_, VerifierSHPLONK<_>, _, _, SingleStrategy<_>>(
            params,
            pk.get_vk(),
            SingleStrategy::new(params),
            &[&[instances]],
            &mut transcript,
            params.n(),
        )
    };
    assert!(result.is_ok());
    proof
}

mod application {
    use crate::prelude::*;

    #[derive(Clone)]
    pub struct StandardPlonkConfig {
        selectors: [Column<Fixed>; 5],
        wires: [Column<Advice>; 3],
    }

    impl StandardPlonkConfig {
        fn configure(meta: &mut ConstraintSystem<impl PrimeField>) -> Self {
            let [w_l, w_r, w_o] = [(); 3].map(|_| meta.advice_column());
            let [q_l, q_r, q_o, q_m, q_c] = [(); 5].map(|_| meta.fixed_column());
            let pi = meta.instance_column();
            [w_l, w_r, w_o].map(|column| meta.enable_equality(column));
            meta.create_gate(
                "q_l·w_l + q_r·w_r + q_o·w_o + q_m·w_l·w_r + q_c + pi = 0",
                |meta| {
                    let [w_l, w_r, w_o] =
                        [w_l, w_r, w_o].map(|column| meta.query_advice(column, Rotation::cur()));
                    let [q_l, q_r, q_o, q_m, q_c] = [q_l, q_r, q_o, q_m, q_c]
                        .map(|column| meta.query_fixed(column, Rotation::cur()));
                    let pi = meta.query_instance(pi, Rotation::cur());
                    Some(
                        q_l * w_l.clone()
                            + q_r * w_r.clone()
                            + q_o * w_o
                            + q_m * w_l * w_r
                            + q_c
                            + pi,
                    )
                },
            );
            StandardPlonkConfig {
                selectors: [q_l, q_r, q_o, q_m, q_c],
                wires: [w_l, w_r, w_o],
            }
        }
    }

    #[derive(Clone, Debug, Default)]
    pub struct StandardPlonk<F>(Vec<F>);

    impl<F: PrimeField> StandardPlonk<F> {
        pub fn rand<R: RngCore>(num_instances: usize, mut rng: R) -> Self {
            Self((0..num_instances).map(|_| F::random(&mut rng)).collect())
        }

        pub fn instances(&self) -> Vec<F> {
            self.0.clone()
        }
    }

    impl<F: PrimeField> Circuit<F> for StandardPlonk<F> {
        type Config = StandardPlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            meta.set_minimum_degree(4);
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let [q_l, q_r, q_o, q_m, q_c] = config.selectors;
            let [w_l, w_r, w_o] = config.wires;
            layouter.assign_region(
                || "",
                |mut region| {
                    for (offset, instance) in self.0.iter().enumerate() {
                        region.assign_advice(|| "", w_l, offset, || Value::known(*instance))?;
                        region.assign_fixed(|| "", q_l, offset, || Value::known(-F::ONE))?;
                    }
                    let offset = self.0.len();
                    let a = region.assign_advice(|| "", w_l, offset, || Value::known(F::ONE))?;
                    a.copy_advice(|| "", &mut region, w_r, offset)?;
                    a.copy_advice(|| "", &mut region, w_o, offset)?;
                    let offset = offset + 1;
                    region.assign_advice(|| "", w_l, offset, || Value::known(-F::from(5)))?;
                    for (column, idx) in [q_l, q_r, q_o, q_m, q_c].iter().zip(1..) {
                        region.assign_fixed(
                            || "",
                            *column,
                            offset,
                            || Value::known(F::from(idx)),
                        )?;
                    }
                    Ok(())
                },
            )
        }
    }
}

mod prelude {
    pub use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        halo2curves::{
            bn256::{Bn256, Fr, G1Affine},
            ff::PrimeField,
        },
        plonk::*,
        poly::{kzg::commitment::ParamsKZG, Rotation},
    };
    pub use rand::{
        rngs::{OsRng, StdRng},
        RngCore, SeedableRng,
    };
    pub use std::{
        collections::HashMap,
        fs::{create_dir_all, File},
        io::Write,
        ops::Range,
    };

    pub fn seeded_std_rng() -> impl RngCore {
        StdRng::seed_from_u64(OsRng.next_u64())
    }
}

mod rotation_tests {
    use halo2_proofs::{
        circuit::*,
        dev::MockProver,
        halo2curves::{
            bn256::{Bn256, Fr},
            ff::Field,
        },
        plonk::*,
        poly::{kzg::commitment::ParamsKZG, Rotation},
    };
    use itertools::Itertools;
    use std::{
        fs::{create_dir_all, File},
        io::Write,
        marker::PhantomData,
    };

    use halo2_solidity_verifier::{compile_solidity, encode_calldata, Evm, SolidityGenerator};

    use crate::{create_proof_checked, prelude::seeded_std_rng};

    #[derive(Debug, Clone)]
    struct Config {
        advice: Column<Advice>,
        eq_selector: Selector,
        instance: Column<Instance>,
    }

    #[derive(Debug, Clone)]
    struct Chip<F: Field> {
        config: Config,
        _marker: PhantomData<F>,
    }

    impl<F: Field> Chip<F> {
        pub fn construct(config: Config) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        pub fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: Column<Advice>,
            instance: Column<Instance>,
        ) -> Config {
            let eq_selector = meta.selector();

            meta.enable_equality(advice);
            meta.enable_equality(instance);

            meta.create_gate("eq", |meta| {
                //
                // advice | selector
                //   a    |    s
                let s = meta.query_selector(eq_selector);
                let a = meta.query_advice(advice, Rotation::cur());
                let a_prime = meta.query_advice(advice, Rotation(1 << 5));
                vec![s * (a - a_prime)]
            });

            Config {
                advice,
                eq_selector,
                instance,
            }
        }

        pub fn assign(&self, mut layouter: impl Layouter<F>, nrows: usize) -> Result<(), Error> {
            layouter.assign_region(
                || "",
                |mut region| {
                    for row in 0..nrows {
                        self.config.eq_selector.enable(&mut region, row)?;
                        region.assign_advice_from_instance(
                            || "advice",
                            self.config.instance,
                            row,
                            self.config.advice,
                            row,
                        )?;
                    }
                    Ok(())
                },
            )
        }
    }

    #[derive(Default)]
    struct MyCircuit<F>(PhantomData<F>);

    impl<F: Field> Circuit<F> for MyCircuit<F> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let instance = meta.instance_column();
            Chip::configure(meta, advice, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = Chip::construct(config);
            chip.assign(layouter.namespace(|| "entire table"), 1 << 4)?;
            Ok(())
        }
    }

    fn save_solidity(name: impl AsRef<str>, solidity: &str) {
        const DIR_GENERATED: &str = "./generated";

        create_dir_all(DIR_GENERATED).unwrap();
        File::create(format!("{DIR_GENERATED}/{}", name.as_ref()))
            .unwrap()
            .write_all(solidity.as_bytes())
            .unwrap();
    }

    #[test]
    fn test_rotation() {
        let circuit = MyCircuit(PhantomData);

        let public_input = vec![Fr::from(1); 1 << 4];

        let k = 5;
        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        let mut rng = seeded_std_rng();
        let params = ParamsKZG::<Bn256>::setup(k, &mut rng);

        let vk = keygen_vk(&params, &circuit).unwrap();
        let pk = keygen_pk(&params, vk.clone(), &circuit).unwrap();
        let generator = SolidityGenerator::new(
            &params,
            &vk,
            halo2_solidity_verifier::BatchOpenScheme::Bdfg21,
            public_input.len(),
        );
        let (verifier_solidity, vk_solidity) = generator.render_separately().unwrap();
        save_solidity(format!("Halo2VerifyingArtifact-{k}.sol"), &vk_solidity);

        let vk_creation_code = compile_solidity(&vk_solidity);
        let mut evm = Evm::default();
        let (vk_address, _) = evm.create(vk_creation_code);

        let verifier_creation_code = compile_solidity(&verifier_solidity);
        let verifier_creation_code_size = verifier_creation_code.len();
        println!("Verifier creation code size: {verifier_creation_code_size}");

        let (verifier_address, _) = evm.create(verifier_creation_code);

        let calldata = {
            let proof = create_proof_checked(&params, &pk, circuit, &public_input, &mut rng);
            encode_calldata(Some(vk_address.into()), &proof, &public_input)
        };
        let (gas_cost, output) = evm.call(verifier_address, calldata);
        assert_eq!(output, [vec![0; 31], vec![1]].concat());
        println!("Gas cost of verifying standard Plonk with 2^{k} rows: {gas_cost}");
    }

    #[test]
    fn test_rotation_og_verifier() {
        const VERIFIER_WRAPPER_SOLIDITY: &str = include_str!("../contracts/VerifierWrapper.sol");
        let circuit = MyCircuit(PhantomData);

        let public_input = vec![Fr::from(1); 1 << 4];

        let k = 7;
        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        let mut rng = seeded_std_rng();
        let params = ParamsKZG::<Bn256>::setup(k, &mut rng);

        let vk = keygen_vk(&params, &circuit).unwrap();
        let pk = keygen_pk(&params, vk.clone(), &circuit).unwrap();
        let generator = SolidityGenerator::new(
            &params,
            &vk,
            halo2_solidity_verifier::BatchOpenScheme::Bdfg21,
            public_input.len(),
        )
        .set_acc_encoding(None);
        let verifier_solidity = generator.render().unwrap();
        let verifier_creation_code = compile_solidity(verifier_solidity);
        let verifier_creation_code_size = verifier_creation_code.len();

        // compile the solidity file located at contracts/VerifierWrapper.sol
        let verifier_wrapper_creation_code = compile_solidity(VERIFIER_WRAPPER_SOLIDITY);

        let mut evm = Evm::unlimited();
        let (verifier_address, gas_cost) = evm.create(verifier_creation_code);
        let verifier_wrapper_address = evm.create(verifier_wrapper_creation_code).0;
        let verifier_runtime_code_size = evm.code_size(verifier_address);

        println!("Verifier creation code size: {verifier_creation_code_size}");
        println!("Verifier runtime code size: {verifier_runtime_code_size}");
        println!("Gas deployment cost verifier: {gas_cost}");

        let proof = create_proof_checked(&params, &pk, circuit, &public_input, &mut rng);

        let (gas_cost, output) =
            evm.call(verifier_address, encode_calldata(None, &proof, &public_input));
        assert_eq!(output, [vec![0; 31], vec![1]].concat());
        println!("Gas cost conjoined: {gas_cost}");
    }
}
