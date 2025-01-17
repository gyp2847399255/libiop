#include <cstdint>

#include <gtest/gtest.h>

#include <libff/algebra/fields/binary/gf64.hpp>
#include <libff/algebra/curves/edwards/edwards_pp.hpp>
#include "libiop/snark/aurora_snark.hpp"
#include "libiop/relations/examples/r1cs_examples.hpp"

namespace libiop {

TEST(AuroraSnarkTest, SimpleTest) {
    return;
    /* Set up R1CS */
    // typedef libff::gf64 FieldT;
    // typedef binary_hash_digest hash_type;

    // const std::size_t num_constraints = 1 << 13;
    // const std::size_t num_inputs = (1 << 5) - 1;
    // const std::size_t num_variables = (1 << 13) - 1;
    // const size_t security_parameter = 128;
    // const size_t RS_extra_dimensions = 2;
    // const size_t FRI_localization_parameter = 3;
    // const LDT_reducer_soundness_type ldt_reducer_soundness_type = LDT_reducer_soundness_type::optimistic_heuristic;
    // const FRI_soundness_type fri_soundness_type = FRI_soundness_type::heuristic;
    // const field_subset_type domain_type = affine_subspace_type;

    // r1cs_example<FieldT> r1cs_params = generate_r1cs_example<FieldT>(
    //     num_constraints, num_inputs, num_variables);
    // EXPECT_TRUE(r1cs_params.constraint_system_.is_satisfied(
    //     r1cs_params.primary_input_, r1cs_params.auxiliary_input_));

    // /* Actual SNARK test */
    // for (std::size_t i = 0; i < 2; i++) {
    //     const bool make_zk = (i == 0) ? false : true;
    //     aurora_snark_parameters<FieldT, hash_type> params(
    //         security_parameter,
    //         ldt_reducer_soundness_type,
    //         fri_soundness_type,
    //         blake2b_type,
    //         FRI_localization_parameter,
    //         RS_extra_dimensions,
    //         make_zk,
    //         domain_type,
    //         num_constraints,
    //         num_variables);
    //     const aurora_snark_argument<FieldT, hash_type> argument = aurora_snark_prover<FieldT>(
    //         r1cs_params.constraint_system_,
    //         r1cs_params.primary_input_,
    //         r1cs_params.auxiliary_input_,
    //         params);

    //     printf("iop size in bytes %lu\n", argument.IOP_size_in_bytes());
    //     printf("bcs size in bytes %lu\n", argument.BCS_size_in_bytes());
    //     printf("argument size in bytes %lu\n", argument.size_in_bytes());

    //     const bool bit = aurora_snark_verifier<FieldT, hash_type>(
    //         r1cs_params.constraint_system_,
    //         r1cs_params.primary_input_,
    //         argument,
    //         params);

    //     EXPECT_TRUE(bit) << "failed on make_zk = " << i << " test";
    // }
}

bool aurora_fixed_snark_test(size_t bit_width_dim, size_t instance_dim) {
    printf("START aurora FIXED range proof with bit width dim: %d and instance dim: %d\n", bit_width_dim, instance_dim);
    /* Set up R1CS */
    libff::edwards_pp::init_public_params();
    typedef libff::edwards_Fr FieldT;
    typedef binary_hash_digest hash_type;

    size_t bit_width = 1 << bit_width_dim;
    size_t instance_num = 1 << instance_dim;
    const size_t num_constraints = bit_width * 2 * instance_num;
    const size_t num_variables = bit_width * 2 * instance_num - 1;
    const size_t security_parameter = 120;
    const size_t RS_extra_dimensions = 3;
    const size_t FRI_localization_parameter = 3;
    const LDT_reducer_soundness_type ldt_reducer_soundness_type = LDT_reducer_soundness_type::optimistic_heuristic;
    const FRI_soundness_type fri_soundness_type = FRI_soundness_type::heuristic;
    const field_subset_type domain_type = multiplicative_coset_type;

    r1cs_example<FieldT> r1cs_params = generate_fixed_range_proof_r1cs<FieldT>(bit_width, instance_num);
    if (!r1cs_params.constraint_system_.is_satisfied(
        r1cs_params.primary_input_, r1cs_params.auxiliary_input_)) {
        return false;
    }

    /* Actual SNARK test */
    for (std::size_t i = 1; i < 2; i++) {
        const bool make_zk = i != 0;
        aurora_snark_parameters<FieldT, hash_type> params(
            security_parameter,
            ldt_reducer_soundness_type,
            fri_soundness_type,
            blake2b_type,
            FRI_localization_parameter,
            RS_extra_dimensions,
            make_zk,
            domain_type,
            num_constraints,
            num_variables);
        const aurora_snark_argument<FieldT, hash_type> argument = aurora_snark_prover<FieldT>(
            r1cs_params.constraint_system_,
            r1cs_params.primary_input_,
            r1cs_params.auxiliary_input_,
            params);

        printf("iop size in bytes %lu\n", argument.IOP_size_in_bytes());
        printf("bcs size in bytes %lu\n", argument.BCS_size_in_bytes());
        printf("argument size in bytes %lu\n", argument.size_in_bytes());
        const bool bit = aurora_snark_verifier<FieldT>(
            r1cs_params.constraint_system_,
            r1cs_params.primary_input_,
            argument,
            params);

        if (!bit) {
            return false;
        }
    }
    return true;
}

bool aurora_arbitrary_snark_test(size_t bit_width_dim, size_t instance_dim) {
    printf("START aurora ARBITRARY range proof with bit width dim: %d and instance dim: %d\n", bit_width_dim, instance_dim);
    /* Set up R1CS */
    libff::edwards_pp::init_public_params();
    typedef libff::edwards_Fr FieldT;
    typedef binary_hash_digest hash_type;

    size_t bit_width = 1 << bit_width_dim;
    size_t instance_num = 1 << instance_dim;
    const size_t num_constraints = bit_width * 16 * instance_num;
    const size_t num_variables = instance_num * bit_width * 8 - 1;
    const size_t security_parameter = 120;
    const size_t RS_extra_dimensions = 3;
    const size_t FRI_localization_parameter = 3;
    const LDT_reducer_soundness_type ldt_reducer_soundness_type = LDT_reducer_soundness_type::optimistic_heuristic;
    const FRI_soundness_type fri_soundness_type = FRI_soundness_type::heuristic;
    const field_subset_type domain_type = multiplicative_coset_type;

    r1cs_example<FieldT> r1cs_params = generate_arbitrary_range_proof_r1cs<FieldT>(bit_width, instance_num);
    if (!r1cs_params.constraint_system_.is_satisfied(
        r1cs_params.primary_input_, r1cs_params.auxiliary_input_)) {
        return false;
    }

    /* Actual SNARK test */
    for (std::size_t i = 1; i < 2; i++) {
        const bool make_zk = i != 0;
        aurora_snark_parameters<FieldT, hash_type> params(
            security_parameter,
            ldt_reducer_soundness_type,
            fri_soundness_type,
            blake2b_type,
            FRI_localization_parameter,
            RS_extra_dimensions,
            make_zk,
            domain_type,
            num_constraints,
            num_variables);
        const aurora_snark_argument<FieldT, hash_type> argument = aurora_snark_prover<FieldT>(
            r1cs_params.constraint_system_,
            r1cs_params.primary_input_,
            r1cs_params.auxiliary_input_,
            params);

        printf("iop size in bytes %lu\n", argument.IOP_size_in_bytes());
        printf("bcs size in bytes %lu\n", argument.BCS_size_in_bytes());
        printf("argument size in bytes %lu\n", argument.size_in_bytes());
        const bool bit = aurora_snark_verifier<FieldT>(
            r1cs_params.constraint_system_,
            r1cs_params.primary_input_,
            argument,
            params);

        if (!bit) {
            return false;
        }
    }
    return true;
}



TEST(AuroraSnarkMultiplicativeTest, SimpleTest) {
    size_t bit_width_dim[] = {5, 7, 9, 7, 7, 7};
    size_t instance_dim[] = {0, 0, 0, 6, 8, 10};
    EXPECT_EQ(sizeof(bit_width_dim), sizeof(instance_dim));
    // EXPECT_TRUE(aurora_arbitrary_snark_test(bit_width_dim[3], instance_dim[3]));
    EXPECT_TRUE(aurora_fixed_snark_test(bit_width_dim[3], instance_dim[3]));
}


}
