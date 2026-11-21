/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# Strict positivity of positive invariant integrals

Let `A` be a complex Hopf algebra with a star structure and let `h : A → ℂ` be a nonzero
one-sided invariant integral which is positive in the algebraic sense,
`0 ≤ h (star a * a)` for every `a`. Then `h` is strictly positive: `0 < h (star a * a)` for every
`a ≠ 0`.

The Cauchy–Schwarz inequality, in the form
`TauCeti.StarPositiveFunctional.apply_star_mul_self_eq_zero_iff`, turns `h (star a * a) = 0` into
the vanishing of `h (star b * a)` and of `h (star a * b)` for all `b`. The algebraic faithfulness
of nonzero invariant integrals, `LinearMap.IsRightInvariantIntegral.eq_zero_of_forall_mul_eq_zero`
and its left counterpart, then forces `a = 0`. No norm, order or completeness on `A` is involved,
and the comultiplication need not be a star map. Strict positivity is what makes the
Haar-averaged inner products of finite-dimensional comodules definite, and the Haar GNS
construction faithful.

## Main results

* `LinearMap.IsRightInvariantIntegral.map_star_mul_self_eq_zero_iff` and
  `LinearMap.IsLeftInvariantIntegral.map_star_mul_self_eq_zero_iff`: `h (star a * a) = 0` only
  for `a = 0`.
* `LinearMap.IsRightInvariantIntegral.map_star_mul_self_pos` and
  `LinearMap.IsLeftInvariantIntegral.map_star_mul_self_pos`: `0 < h (star a * a)` for `a ≠ 0`.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 2.2.4 and
  Remark 2.2.2.
-/

public section

open ComplexOrder

namespace LinearMap

variable {A : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  {h : A →ₗ[ℂ] ℂ}

/-- A nonzero positive right invariant integral vanishes on `star a * a` only for `a = 0`. -/
theorem IsRightInvariantIntegral.map_star_mul_self_eq_zero_iff
    (hh : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A} :
    h (star a * a) = 0 ↔ a = 0 := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ by simp [ha]⟩
  let φ : TauCeti.StarPositiveFunctional A := ⟨h, hpos⟩
  have hnull := (φ.apply_star_mul_self_eq_zero_iff a).mp ha
  rw [← star_eq_zero]
  refine hh.eq_zero_of_forall_mul_eq_zero h0 fun b ↦ ?_
  have hab := φ.star_apply_star_mul a b
  rw [hnull b, star_eq_zero] at hab
  simpa [φ] using hab

/-- A nonzero positive left invariant integral vanishes on `star a * a` only for `a = 0`. -/
theorem IsLeftInvariantIntegral.map_star_mul_self_eq_zero_iff
    (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A} :
    h (star a * a) = 0 ↔ a = 0 := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ by simp [ha]⟩
  let φ : TauCeti.StarPositiveFunctional A := ⟨h, hpos⟩
  have hnull := (φ.apply_star_mul_self_eq_zero_iff a).mp ha
  exact hh.eq_zero_of_forall_mul_eq_zero h0 fun b ↦ by simpa [φ] using hnull (star b)

/-- A nonzero positive right invariant integral is strictly positive. -/
theorem IsRightInvariantIntegral.map_star_mul_self_pos
    (hh : h.IsRightInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A}
    (ha : a ≠ 0) : 0 < h (star a * a) :=
  (hpos a).lt_of_ne' ((hh.map_star_mul_self_eq_zero_iff h0 hpos).not.mpr ha)

/-- A nonzero positive left invariant integral is strictly positive. -/
theorem IsLeftInvariantIntegral.map_star_mul_self_pos
    (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) {a : A}
    (ha : a ≠ 0) : 0 < h (star a * a) :=
  (hpos a).lt_of_ne' ((hh.map_star_mul_self_eq_zero_iff h0 hpos).not.mpr ha)

end LinearMap
