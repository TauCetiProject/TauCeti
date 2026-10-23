/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.RingTheory.RegularLocalRing.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.Derivation.Localization

/-!
# The parabola and cusp at the origin

Over any field, localize the affine plane at the origin. The equation `y - x²` is outside
the square of the maximal ideal, and its quotient is regular. The nonzero cusp equation
`y² - x³` lies in that square, so its quotient is not regular.

The origin is represented as the inverse image under the constant-coefficient map of the
field's maximal ideal, namely the ideal `(x, y)`. The argument works in every characteristic:
the partial derivative of the parabola equation with respect to `y` is one.

## Main result

* `TauCeti.IsRegularLocalRing.parabola_regular_and_cusp_not_regular`: all three assertions
  of the localized parabola/cusp comparison.

## References

* [Stacks Project, Lemma 10.106.3](https://stacks.math.columbia.edu/tag/00NQ).
-/

public section

open IsLocalRing Ideal MvPolynomial

namespace TauCeti.IsRegularLocalRing

variable {k : Type*} [Field k]

/-- At the origin of the affine plane, the parabola equation is a regular parameter and its
quotient is regular, whereas the cusp quotient is not regular. -/
theorem parabola_regular_and_cusp_not_regular :
    let origin := (maximalIdeal k).comap (constantCoeff (σ := Fin 2))
    let localRing := Localization.AtPrime origin
    let localize := algebraMap (MvPolynomial (Fin 2) k) localRing
    IsRegularLocalRing (localRing ⧸ span {localize (X 1 - X 0 ^ 2)}) ∧
      localize (X 1 - X 0 ^ 2) ∉ maximalIdeal localRing ^ 2 ∧
      ¬ IsRegularLocalRing (localRing ⧸ span {localize (X 1 ^ 2 - X 0 ^ 3)}) := by
  intro origin localRing localize
  have hvariable (index : Fin 2) : localize (X index) ∈ maximalIdeal localRing :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff localRing origin _).mpr (by simp [origin])
  have hparabola : localize (X 1 - X 0 ^ 2) ∈ maximalIdeal localRing := by
    rw [map_sub, map_pow]
    exact sub_mem (hvariable 1) (pow_mem_of_mem _ (hvariable 0) 2 (by decide))
  have hparameter : localize (X 1 - X 0 ^ 2) ∉ maximalIdeal localRing ^ 2 :=
    (pderiv 1).algebraMap_notMem_maximalIdeal_sq (by simp [origin])
  refine ⟨quotient_span_singleton hparabola hparameter, hparameter, ?_⟩
  have hcusp : localize (X 1 ^ 2 - X 0 ^ 3) ∈ maximalIdeal localRing := by
    rw [map_sub, map_pow, map_pow]
    exact sub_mem (pow_mem_of_mem _ (hvariable 1) 2 (by decide))
      (pow_mem_of_mem _ (hvariable 0) 3 (by decide))
  have hnonzero : localize (X 1 ^ 2 - X 0 ^ 3) ≠ 0 := by
    rw [Ne, IsLocalization.to_map_eq_zero_iff localRing (primeCompl_le_nonZeroDivisors origin)]
    intro heq
    have heval := congrArg (eval (fun index : Fin 2 ↦ if index = 1 then (1 : k) else 0)) heq
    simp at heval
  rw [quotient_span_singleton_iff hcusp hnonzero, not_not]
  rw [map_sub, map_pow, map_pow]
  apply sub_mem
  · exact Ideal.pow_mem_pow (hvariable 1) 2
  · rw [pow_succ (localize (X 0)) 2]
    exact mul_mem_right _ _ (Ideal.pow_mem_pow (hvariable 0) 2)

end TauCeti.IsRegularLocalRing
