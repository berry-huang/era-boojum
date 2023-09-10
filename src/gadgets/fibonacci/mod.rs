use super::*;
use crate::cs::gates::{assert_no_placeholder_variables, ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant, NopGate, PublicInputGate};
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::Variable;
use crate::gadgets::tables::TriXor4Table;
use crate::gadgets::u32::UInt32;
use crate::gadgets::u8::UInt8;

pub fn fibonacci<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &UInt32<F>,
) -> UInt32<F> {
    let one = UInt32::allocated_constant(cs,1);
    let two = UInt32::allocated_constant(cs,2);
    // let no_gate = NopGate::new();
    // no_gate.add_to_cs(cs);

    one
}

pub fn l2_fibonacci(input: u32) -> u32 {
    1
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        cs::{
            gates::{ConstantsAllocatorGate, NopGate, ReductionGate},
            implementations::{
                pow::NoPow,
                transcript::{Blake2sTranscript, Transcript},
            },
            oracle::TreeHasher,
            CSGeometry,
        },
        field::goldilocks::GoldilocksField,
        gadgets::tables::{
            ch4::{create_ch4_table, Ch4Table},
            chunk4bits::{create_4bit_chunk_split_table, Split4BitChunkTable},
            maj4::{create_maj4_table, Maj4Table},
            trixor4::{create_tri_xor_table, TriXor4Table},
        },
        log,
    };
    use blake2::Digest;
    use crate::cs::gates::FmaGateInBaseFieldWithoutConstant;

    type F = GoldilocksField;

    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::gadgets::tables::{ByteSplitTable, create_byte_split_table};
    use crate::gadgets::traits::witnessable::{CSWitnessable, WitnessHookable};

    #[test]
    #[ignore]
    fn test_fibonacci_case1() {
        use crate::blake2::Blake2s256;
        type TreeHash = Blake2s256;
        type Transcript = Blake2sTranscript;
        prove_fibonacci::<TreeHash, Transcript>(3);
    }

    fn prove_fibonacci<
        T: TreeHasher<GoldilocksField, Output = TR::CompatibleCap>,
        TR: Transcript<GoldilocksField, TransciptParameters = ()>,
    >(n: u32) {
        use crate::config::SetupCSConfig;
        use crate::cs::implementations::prover::ProofConfig;
        use crate::field::goldilocks::GoldilocksExt2;
        use crate::worker::Worker;

        let worker = Worker::new_with_num_threads(8);

        let quotient_lde_degree = 8; // Setup params are not split yet, so it's should be equal to max(FRI lde degree, quotient degree)
        let fri_lde_degree = 8;
        let cap_size = 16;
        let mut prover_config = ProofConfig::default();
        prover_config.fri_lde_factor = fri_lde_degree;
        prover_config.pow_bits = 0; // not important in practice for anything. 2^20 Blake2s POW uses 30ms

        let reference_output = l2_fibonacci(n);

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 60,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        let max_variables = 1 << 25;
        let max_trace_len = 1 << 19;

        use crate::cs::cs_builder::*;
        use crate::cs::GateConfigurationHolder;
        use crate::cs::StaticToolboxHolder;

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<F, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        {
            // satisfiability check
            use crate::config::DevCSConfig;

            let builder_impl =
                CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, max_variables, max_trace_len,);
            let builder = new_builder::<_, F>(builder_impl);

            let builder = configure(builder);
            let mut owned_cs = builder.build(());

            let cs = &mut owned_cs;

            let mut circuit_input = UInt32::allocate_checked(cs, n);

            let _output = fibonacci(cs, &circuit_input);
            assert_eq!((_output.witness_hook(&*cs))().unwrap(), reference_output);

            drop(cs);
            // let (_, padding_hint) = owned_cs.pad_and_shrink();
            let mut owned_cs = owned_cs.into_assembly();
            assert!(owned_cs.check_if_satisfied(&worker));
        }

        use crate::cs::cs_builder_reference::*;
        use crate::cs::cs_builder_verifier::*;

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, SetupCSConfig>::new(geometry, max_variables, max_trace_len,);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(());

        let cs = &mut owned_cs;

        let mut circuit_input = UInt32::allocate_checked(cs, n);

        let _output = fibonacci(cs, &circuit_input);
        drop(cs);
        // let (_, padding_hint) = owned_cs.pad_and_shrink();
        let owned_cs = owned_cs.into_assembly();
        owned_cs.print_gate_stats();

        let (base_setup, setup, vk, setup_tree, vars_hint, wits_hint) =
            owned_cs.get_full_setup::<T>(&worker, quotient_lde_degree, cap_size);

        use crate::config::ProvingCSConfig;

        let builder_impl = CsReferenceImplementationBuilder::<F, P, ProvingCSConfig>::new(
            geometry, max_variables, max_trace_len,);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(());

        // create setup
        let now = std::time::Instant::now();
        log!("Start synthesis for proving");
        let cs = &mut owned_cs;

        let mut circuit_input = UInt32::allocate_checked(cs, n);

        let _output = fibonacci(cs, &circuit_input);
        dbg!(now.elapsed());
        log!("Synthesis for proving is done");
        // owned_cs.pad_and_shrink_using_hint(&padding_hint);
        let mut owned_cs = owned_cs.into_assembly();

        log!("Proving");
        let witness_set = owned_cs.take_witness_using_hints(&worker, &vars_hint, &wits_hint);
        log!("Witness is resolved");

        let now = std::time::Instant::now();

        let proof = owned_cs.prove_cpu_basic::<GoldilocksExt2, TR, T, NoPow>(
            &worker,
            witness_set,
            &base_setup,
            &setup,
            &setup_tree,
            &vk,
            prover_config,
            (),
        );

        log!("Proving is done, taken {:?}", now.elapsed());

        let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let verifier = builder.build(());

        let is_valid = verifier.verify::<T, TR, NoPow>((), &vk, &proof);

        assert!(is_valid);
    }

    type P = crate::field::goldilocks::MixedGL;
}