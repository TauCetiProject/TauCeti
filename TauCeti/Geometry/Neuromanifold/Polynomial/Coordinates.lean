/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Polynomial.Presentation

/-!
# Linear coordinates on polynomial coefficient presentations

The monomial coefficients of a jointly polynomial model are polynomial functions of its
parameters. Applying a linear map to its bounded-degree coefficient space gives polynomial
functions again: `polynomialCoefficientTransform` constructs these parameter polynomials.
In particular, an arbitrary linear coordinate equivalence (for example, the coordinate map of
a different basis) gives the same realization after evaluation in the new coordinates.

`boundedEvaluation_comp_polynomialCoefficientTransform` is the commuting equation for this new
presentation. Its evaluation is faithful over an infinite integral domain, so the image and
fibre comparisons in `TauCeti.Geometry.Neuromanifold.Basic` apply without any new assumptions
on the parameters. Only linear coordinate changes are considered; an arbitrary encoding need
not preserve polynomiality.

The finite coefficient-space viewpoint follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. The construction uses
`MvPolynomial.boundedCoefficientEquiv` and Mathlib's `LinearMap.pi_apply_eq_sum_univ`.
-/

public section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K W X J I : Type*} [CommSemiring K] [Fintype J] [Finite X]

/-- Parameter polynomials for the linear transform `T` of the bounded-degree coefficient map.
For a linear coordinate equivalence, these are the coefficients in the new coordinates.
The target index type need not be finite to construct each coordinate polynomial. -/
noncomputable def polynomialCoefficientTransform (P : J → MvPolynomial (W ⊕ X) K)
    (T : (J → restrictTotalDegree X K (polynomialInputDegree P)) →ₗ[K] (I → K)) :
    I → MvPolynomial W K := by
  classical
  letI := Fintype.ofFinite (J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P})
  exact fun i => ∑ a : J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P},
    C (T ((boundedCoefficientEquiv X K J _).symm (Pi.single a 1)) i) *
      (inputPolynomial P a.1).coeff a.2

/-- The transformed parameter polynomials evaluate to the linear transform of the coefficient
map, including when specialization cancels coefficients. -/
@[simp]
theorem eval_polynomialCoefficientTransform (P : J → MvPolynomial (W ⊕ X) K)
    (T : (J → restrictTotalDegree X K (polynomialInputDegree P)) →ₗ[K] (I → K))
    (w : W → K) (i : I) :
    eval w (polynomialCoefficientTransform P T i) = T (polynomialCoefficientMap P w) i := by
  classical
  let := Fintype.ofFinite (J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P})
  let g := T.comp (boundedCoefficientEquiv X K J (polynomialInputDegree P)).symm.toLinearMap
  have h := congrFun (g.pi_apply_eq_sum_univ
    (boundedCoefficientEquiv X K J _ (polynomialCoefficientMap P w))) i
  have hs (a : J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P}) :
      (fun j => if a = j then (1 : K) else 0) = Pi.single a 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  simpa [g, polynomialCoefficientTransform, coeff_map, hs, mul_comm] using h.symm

/-- The original monomial coordinates are recovered by using the monomial coefficient
equivalence as the coordinate map. -/
@[simp]
theorem polynomialCoefficientTransform_boundedCoefficientEquiv
    (P : J → MvPolynomial (W ⊕ X) K)
    (i : J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P}) :
    polynomialCoefficientTransform P (boundedCoefficientEquiv X K J _).toLinearMap i =
      (inputPolynomial P i.1).coeff i.2 := by
  classical
  let := Fintype.ofFinite (J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P})
  simp [polynomialCoefficientTransform, Pi.single_apply]

/-- Evaluating in any linearly equivalent coordinates recovers the original realization.
Thus a change of basis changes the coefficient presentation, not the realized functions. -/
theorem boundedEvaluation_comp_polynomialCoefficientTransform
    (P : J → MvPolynomial (W ⊕ X) K)
    (e : (J → restrictTotalDegree X K (polynomialInputDegree P)) ≃ₗ[K] (I → K)) :
    ((boundedEvaluation X K J _).comp e.symm.toLinearMap) ∘
        (fun w i => eval w (polynomialCoefficientTransform P e.toLinearMap i)) =
      polynomialRealization P := by
  have h (w : W → K) :
      (fun i => eval w (polynomialCoefficientTransform P e.toLinearMap i)) =
        e (polynomialCoefficientMap P w) := by
    ext i
    exact eval_polynomialCoefficientTransform P e.toLinearMap w i
  simpa only [Function.comp_def, LinearMap.comp_apply, h, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using boundedEvaluation_comp_polynomialCoefficientMap P

end TauCeti.Neuromanifold
