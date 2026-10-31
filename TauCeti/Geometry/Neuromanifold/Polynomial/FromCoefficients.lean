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
The final theorem applies this to any supplied coefficient map whose coordinates are polynomial.
All statements hold over commutative semirings; faithfulness of evaluation over infinite domains
is provided separately by `MvPolynomial.boundedEvaluation_injective`.

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
  · rw [coeff_map]
    have hleft : (inputPolynomial (polynomialFromCoefficients Q) j).coeff a = 0 :=
      coeff_eq_zero_of_totalDegree_lt (by
        rw [← Finsupp.degree_apply]
        exact (totalDegree_inputPolynomial_polynomialFromCoefficients_le Q j).trans_lt
          (not_le.mp ha))
    have hright := ((mem_restrictTotalDegree X d _).mp
      ((boundedCoefficientEquiv X K J d).symm (fun i => eval w (Q i)) j).property)
    rw [hleft, map_zero, coeff_eq_zero_of_totalDegree_lt (by
      rw [← Finsupp.degree_apply]
      exact hright.trans_lt (not_le.mp ha))]

/-- The assembled joint model realizes evaluation of the supplied polynomial coefficient map. -/
theorem polynomialRealization_polynomialFromCoefficients
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) :
    polynomialRealization (polynomialFromCoefficients Q) =
      fun w => boundedEvaluation X K J d
        ((boundedCoefficientEquiv X K J d).symm (fun i => eval w (Q i))) := by
  funext w x j
  rw [← eval₂_inputPolynomial, ← eval_map,
    map_inputPolynomial_polynomialFromCoefficients, boundedEvaluation_apply]

/-- Extraction after assembly returns the supplied coefficient tuple. The coercion forgets
only the inferred degree bound, which can be smaller than `d`. -/
theorem polynomialCoefficientMap_polynomialFromCoefficients_coe [Fintype J]
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K) (w : W → K) (j : J) :
    (polynomialCoefficientMap (polynomialFromCoefficients Q) w j : MvPolynomial X K) =
      ((boundedCoefficientEquiv X K J d).symm (fun i => eval w (Q i)) j :
        MvPolynomial X K) := by
  rw [polynomialCoefficientMap_coe, map_inputPolynomial_polynomialFromCoefficients]

/-- A supplied bounded-degree coefficient map with polynomial coordinates has a joint polynomial
presentation, and coefficient extraction recovers it in the same monomial coordinates. -/
theorem exists_polynomialRealization_of_coefficients [Fintype J]
    (c : (W → K) → J → restrictTotalDegree X K d)
    (Q : J × {a : X →₀ ℕ // a.degree ≤ d} → MvPolynomial W K)
    (hQ : ∀ w i, eval w (Q i) = boundedCoefficientEquiv X K J d (c w) i) :
    ∃ P : J → MvPolynomial (W ⊕ X) K,
      polynomialRealization P = boundedEvaluation X K J d ∘ c ∧
        ∀ w j, (polynomialCoefficientMap P w j : MvPolynomial X K) = c w j := by
  have hcoords (w : W → K) : (fun i => eval w (Q i)) =
      boundedCoefficientEquiv X K J d (c w) := funext (hQ w)
  refine ⟨polynomialFromCoefficients Q, ?_, ?_⟩
  · rw [polynomialRealization_polynomialFromCoefficients]
    funext w
    simp [hcoords]
  · intro w j
    rw [polynomialCoefficientMap_polynomialFromCoefficients_coe, hcoords,
      LinearEquiv.symm_apply_apply]

end TauCeti.Neuromanifold
