/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic
public import TauCeti.Geometry.Neuromanifold.Polynomial.Basic

/-!
# Faithful coefficient presentations of polynomial models

A presentation of a realization map `f : W → X → Y` is a coefficient map `c : W → V` together
with an evaluation `E : V → X → Y` satisfying `E (c w) = f w`; the comparisons for a faithful
(injective) presentation are in `TauCeti.Geometry.Neuromanifold.Basic`. This file specialises
them to jointly polynomial models.

For a jointly polynomial tuple `P`, the coefficient map `polynomialCoefficientMap P` and the
evaluation `MvPolynomial.boundedEvaluation` form a presentation of `polynomialRealization P`,
so the realized functions are the evaluations of the coefficient image. Over an infinite integral
domain this evaluation is injective, so two parameters realize the same function exactly when
they have the same input coefficients, and realization fibres are coefficient fibres.

Over a finite field evaluation can fail to be faithful, since distinct polynomials of large
degree can define the same function. A presentation by sampled outputs is not automatically
faithful.

The jointly polynomial setting and its finite ambient coefficient space follow
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
-/

public section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {W X J : Type*} [Fintype J]

/-- The functions realized by a jointly polynomial tuple are the evaluations of its coefficient
image. -/
theorem realizedFunctions_polynomialRealization {K : Type*} [CommSemiring K]
    (P : J → MvPolynomial (W ⊕ X) K) :
    realizedFunctions (polynomialRealization P) =
      boundedEvaluation X K J _ '' Set.range (polynomialCoefficientMap P) :=
  realizedFunctions_eq_image_range (congrFun (boundedEvaluation_comp_polynomialCoefficientMap P))

section Faithful

variable {K : Type*} [CommRing K] [IsDomain K] [Infinite K]

/-- Over an infinite integral domain, parameters of a jointly polynomial tuple realize the same
function exactly when they have the same input coefficients. -/
theorem polynomialCoefficientMap_eq_iff (P : J → MvPolynomial (W ⊕ X) K) {w v : W → K} :
    polynomialCoefficientMap P w = polynomialCoefficientMap P v ↔
      polynomialRealization P w = polynomialRealization P v :=
  apply_eq_apply_iff_of_injective (boundedEvaluation_injective _)
    (congrFun (boundedEvaluation_comp_polynomialCoefficientMap P))

/-- Over an infinite integral domain, the realization fibre of a jointly polynomial tuple over
the evaluation of `q` is the coefficient fibre over `q`. -/
theorem fiber_polynomialRealization_boundedEvaluation (P : J → MvPolynomial (W ⊕ X) K)
    (q : J → restrictTotalDegree X K (polynomialInputDegree P)) :
    fiber (polynomialRealization P) (boundedEvaluation X K J _ q) =
      polynomialCoefficientMap P ⁻¹' {q} :=
  fiber_apply_eq_preimage (boundedEvaluation_injective _)
    (congrFun (boundedEvaluation_comp_polynomialCoefficientMap P)) q

end Faithful

end TauCeti.Neuromanifold
