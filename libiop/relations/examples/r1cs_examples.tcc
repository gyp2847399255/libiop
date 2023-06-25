/** @file
 *****************************************************************************

 Implementation of functions to sample R1CS examples with prescribed parameters
 (according to some distribution).

 See r1cs_examples.hpp .

 *****************************************************************************
 * @author     This file is adapted from libsnark, developed by SCIPR Lab
 *             and contributors
 *             (see AUTHORS for libsnark and here for libiop).
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/

#include <cassert>
#include <stdexcept>

#include "libiop/algebra/utils.hpp"

namespace libiop {

    template<typename FieldT>
    r1cs_example<FieldT> generate_range_proof_r1cs(const size_t bit_width, const size_t instance_num) {
        size_t num_variables = bit_width * instance_num;
        size_t zero_bits = bit_width / 2;
        size_t nonzero_bits = bit_width - zero_bits;
        r1cs_constraint_system<FieldT> cs;
        cs.primary_input_size_ = 0;
        cs.auxiliary_input_size_ = num_variables;
        r1cs_variable_assignment<FieldT> variables;
        for (size_t i = 0; i < instance_num; i++) {
            for (size_t j = 0; j < nonzero_bits; j++) {
                variables.push_back(FieldT(std::rand() & 1));
            }
            for (size_t j = nonzero_bits; j < bit_width; j++) {
                variables.push_back(FieldT::zero());
            }
        }

        // constraint all variables in 0/1
        for (size_t i = 0; i < instance_num; i++) {
            for (size_t j = 0; j < nonzero_bits; j++) {
                size_t idx = i * instance_num + j;
                linear_combination<FieldT> A, B, C;
                A.add_term(idx + 1, FieldT::one());
                B.add_term(idx + 1, FieldT::one());
                B.add_term(0, FieldT::zero() - FieldT::one());
                cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
            }
        }

        for (size_t i = 0; i < instance_num; i++) {
            for (size_t j = nonzero_bits; j < bit_width; j++) {
                size_t idx = i * instance_num + j;
                linear_combination<FieldT> A, B, C;
                A.add_term(idx + 1, FieldT::one());
                cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
            }
        }

        assert(cs.num_variables() == num_variables);
        assert(cs.num_inputs() == 0);
        assert(cs.num_constraints() == num_variables);
        r1cs_primary_input<FieldT> primary_input;
        r1cs_primary_input<FieldT> auxiliary_input = variables;
        assert(cs.is_satisfied(primary_input, auxiliary_input));

        return r1cs_example<FieldT>(std::move(cs), std::move(primary_input), std::move(auxiliary_input));
    }

template<typename FieldT>
r1cs_example<FieldT> generate_r1cs_example(const size_t num_constraints,
                                           const size_t num_inputs,
                                           const size_t num_variables)
{
    if (num_inputs > num_variables)
    {
        throw std::invalid_argument("Number of inputs can't exceed number of variables.");
    }

    r1cs_constraint_system<FieldT> cs;
    cs.primary_input_size_ = num_inputs;
    cs.auxiliary_input_size_ = num_variables - num_inputs;

    const r1cs_variable_assignment<FieldT> full_variable_assignment
        = random_FieldT_vector<FieldT>(num_variables);

    for (size_t i = 0; i < num_constraints; ++i)
    {
        linear_combination<FieldT> A, B, C;

        const std::size_t A_idx = i % num_variables;
        const std::size_t B_idx = (i + 7) % num_variables;


        A.add_term(A_idx + 1, FieldT::one());
        B.add_term(B_idx + 1, FieldT::one());
        const FieldT AB_val = full_variable_assignment[A_idx] * full_variable_assignment[B_idx];

        const std::size_t C_idx = (2 * i + 1) % num_variables;
        const FieldT C_val = full_variable_assignment[C_idx];
        if (C_val.is_zero())
        {
            C.add_term(0, AB_val);
        }
        else
        {
            C.add_term(C_idx + 1, AB_val * C_val.inverse());
        }

        cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
    }

    /* split variable assignment */
    r1cs_primary_input<FieldT> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + num_inputs);
    r1cs_primary_input<FieldT> auxiliary_input(full_variable_assignment.begin() + num_inputs, full_variable_assignment.end());

    /* sanity checks */
    assert(cs.num_variables() == num_variables);
    assert(cs.num_variables() >= num_inputs);
    assert(cs.num_inputs() == num_inputs);
    assert(cs.num_constraints() == num_constraints);
    assert(cs.is_satisfied(primary_input, auxiliary_input));

    return r1cs_example<FieldT>(std::move(cs), std::move(primary_input), std::move(auxiliary_input));
}

} // libiop
