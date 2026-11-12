/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Polynomial.Basic

/-!
# Joint polynomial models from polynomial coefficient coordinates

A model can be supplied by polynomial functions of the parameters for each monomial
coefficient, instead of by a polynomial jointly in parameters and inputs.
`polynomialFromCoefficients` converts these finite coordinates into a joint polynomial tuple.
The input-degree bound is at most the supplied bound, and specializing and collecting
coefficients recovers the supplied coordinates, even when some coefficients vanish.

`polynomialRealization_polynomialFromCoefficients` identifies its realization with evaluation
of the bounded-degree polynomial tuple having the prescribed coefficients.
`polynomialCoefficientMap_polynomialFromCoefficients_coe` is the round-trip law: after forgetting
the possibly smaller inferred degree bound, extraction returns that same tuple.
For coefficient maps supplied in arbitrary finite linear coordinates, see
`TauCeti.Geometry.Neuromanifold.Polynomial.LinearPresentation`.
All statements hold over commutative semirings; faithfulness of evaluation over infinite domains
is provided separately by `MvPolynomial.tupleEvaluation_injective`.

The coefficient/function viewpoint follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
The construction uses the inverse of Mathlib's `MvPolynomial.sumAlgEquiv` and the existing
`MvPolynomial.boundedCoefficientEquiv`, rather than a new polynomial representation.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K W X J : Type*} [CommSemiring K] [Finite X] {d : ℕ}

/-- Assemble polynomial functions for the monomial coefficients into a jointly polynomial
model. The coordinates are indexed by an output and an input exponent of degree at most `d`. -/
def polynomialFromCoefficients
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) :
    J → MvPolynomial (W ⊕ X) K :=
  fun j => rename Sum.swap ((sumAlgEquiv K X W).symm
    ((boundedCoefficientEquiv X (MvPolynomial W K) J d).symm Q j))

/-- Collecting inputs after assembly recovers the polynomial tuple with the supplied
parameter-polynomial coefficients. -/
@[simp] theorem inputPolynomial_polynomialFromCoefficients
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) (j : J) :
    inputPolynomial (polynomialFromCoefficients Q) j =
      ((boundedCoefficientEquiv X (MvPolynomial W K) J d).symm Q j :
        MvPolynomial X (MvPolynomial W K)) := by
  simp [inputPolynomial_def, polynomialFromCoefficients, rename_rename]

/-- Assembly introduces no input monomials above the supplied degree bound. -/
theorem totalDegree_inputPolynomial_polynomialFromCoefficients_le
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) (j : J) :
    (inputPolynomial (polynomialFromCoefficients Q) j).totalDegree ≤ d := by
  rw [inputPolynomial_polynomialFromCoefficients]
  exact (mem_restrictTotalDegree X d _).mp
    ((boundedCoefficientEquiv X (MvPolynomial W K) J d).symm Q j).property

/-- The assembled model's uniform input-degree bound is at most the supplied bound. -/
theorem polynomialInputDegree_polynomialFromCoefficients_le [Fintype J]
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) :
    polynomialInputDegree (polynomialFromCoefficients Q) ≤ d :=
  (polynomialInputDegree_le_iff _).mpr
    (totalDegree_inputPolynomial_polynomialFromCoefficients_le Q)

/-- Specializing the collected coefficients gives the bounded-degree tuple with coordinates
obtained by evaluating the supplied coordinate polynomials at the parameters. -/
theorem map_inputPolynomial_polynomialFromCoefficients
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) (w : W → K) (j : J) :
    map (eval w) (inputPolynomial (polynomialFromCoefficients Q) j) =
      ((boundedCoefficientEquiv X K J d).symm (fun i => eval w (Q i)) j :
        MvPolynomial X K) := by
  ext a
  by_cases ha : a.degree ≤ d
  · rw [coeff_map, inputPolynomial_polynomialFromCoefficients,
      coeff_boundedCoefficientEquiv_symm_apply _ j ⟨a, ha⟩,
      coeff_boundedCoefficientEquiv_symm_apply _ j ⟨a, ha⟩]
  · rw [coeff_map, inputPolynomial_polynomialFromCoefficients,
      coeff_eq_zero_of_mem_restrictTotalDegree
        ((boundedCoefficientEquiv X (MvPolynomial W K) J d).symm Q j).property (not_le.mp ha),
      coeff_eq_zero_of_mem_restrictTotalDegree
        ((boundedCoefficientEquiv X K J d).symm (fun i => eval w (Q i)) j).property
        (not_le.mp ha), map_zero]

/-- The assembled joint model realizes evaluation of the supplied polynomial coefficient map. -/
theorem polynomialRealization_polynomialFromCoefficients
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) :
    polynomialRealization (polynomialFromCoefficients Q) =
      fun w => tupleEvaluation J (restrictTotalDegree X K d)
        ((boundedCoefficientEquiv X K J d).symm (fun i => eval w (Q i))) := by
  funext w x j
  rw [← eval₂_inputPolynomial, ← eval_map,
    map_inputPolynomial_polynomialFromCoefficients, tupleEvaluation_apply]

/-- Extraction after assembly returns the supplied coefficient tuple. The coercion forgets
only the inferred degree bound, which can be smaller than `d`. -/
theorem polynomialCoefficientMap_polynomialFromCoefficients_coe [Fintype J]
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) (w : W → K) (j : J) :
    (polynomialCoefficientMap (polynomialFromCoefficients Q) w j : MvPolynomial X K) =
      ((boundedCoefficientEquiv X K J d).symm (fun i => eval w (Q i)) j :
        MvPolynomial X K) := by
  rw [polynomialCoefficientMap_coe, map_inputPolynomial_polynomialFromCoefficients]

end TauCeti.Neuromanifold
