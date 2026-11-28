/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Basic lemmas for normed algebras

This file collects basic constructions and lemmas for normed algebras:

* `TauCeti.normedAlgebraRatOfReal`: much of Mathlib's API for `NormedSpace.exp` (for example
  `NormedSpace.exp_continuous`) assumes a normed `ℚ`-algebra; this names the restriction of scalars
  that makes every real normed algebra a normed `ℚ`-algebra so files can enable it locally.
* `TauCeti.eq_zero_of_norm_sub_one_lt_one_of_mul_eq_neg_mul`: in a normed ring that is a real
  normed space, an element anticommuting with an element within distance `< 1` of `1` vanishes.
  `TauCeti.apply_eq_zero_of_mul_eq_neg_mul` is its form for operators on a complex normed space
  restricted to a common invariant submodule.
* `AlgEquiv.norm_map` and `AlgEquiv.isometry`: every `𝕜`-algebra equivalence `F ≃ₐ[𝕜] 𝕜` from a
  seminormed `𝕜`-algebra with `‖1‖ = 1` to its base normed field preserves the norm and is an
  isometry.
-/

public section

namespace TauCeti

variable {R : Type*} [SeminormedRing R] [NormedAlgebra ℝ R]

/-- A real normed algebra regarded as a rational normed algebra, by restricting scalars along
`ℚ → ℝ`.

This is not a global instance: algebras such as `ℂ` already carry a `ℚ`-algebra structure
(for example through Mathlib's `normedAlgebraRat`) that is not reducibly defeq to this one, so
a global instance would create a diamond. Enable it where needed with
`attribute [local instance] TauCeti.normedAlgebraRatOfReal`. -/
noncomputable abbrev normedAlgebraRatOfReal : NormedAlgebra ℚ R :=
  .restrictScalars ℚ ℝ R

/-- **An element anticommuting with an element close to `1` vanishes.** In a normed ring that is
a real normed space, such as an algebra of operators on a real or complex normed space, if
`s * a = -(a * s)` and `‖s - 1‖ < 1`, then `a = 0`: indeed
`2 • a = -((s - 1) * a + a * (s - 1))`, whose norm is at most `2 * ‖s - 1‖ * ‖a‖`. -/
theorem eq_zero_of_norm_sub_one_lt_one_of_mul_eq_neg_mul {A : Type*} [NormedRing A]
    [NormedSpace ℝ A] {s a : A} (hs : ‖s - 1‖ < 1) (h : s * a = -(a * s)) : a = 0 := by
  have key : (2 : ℝ) • a = -((s - 1) * a + a * (s - 1)) := by
    rw [two_smul, sub_mul, mul_sub, h, one_mul, mul_one]
    abel
  have hle : 2 * ‖a‖ ≤ 2 * (‖s - 1‖ * ‖a‖) := by
    calc 2 * ‖a‖ = ‖(2 : ℝ) • a‖ := by rw [norm_smul, Real.norm_two]
      _ ≤ ‖s - 1‖ * ‖a‖ + ‖a‖ * ‖s - 1‖ := by
        rw [key, norm_neg]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ = 2 * (‖s - 1‖ * ‖a‖) := by ring
  exact norm_eq_zero.mp <| le_antisymm (by nlinarith [norm_nonneg a]) (norm_nonneg a)

/-- **An operator anticommuting with one close to the identity on an invariant submodule vanishes
there.** If the bounded operators `S` and `A` on a complex normed space preserve a submodule `V`,
`S * A = -(A * S)`, and `S` moves every element of `V` by at most `δ < 1` times its norm, then
`A` vanishes on `V`: the restrictions to `V` satisfy
`TauCeti.eq_zero_of_norm_sub_one_lt_one_of_mul_eq_neg_mul`. -/
theorem apply_eq_zero_of_mul_eq_neg_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : Submodule ℂ E} {S A : E →L[ℂ] E} (hS : ∀ x ∈ V, S x ∈ V) (hA : ∀ x ∈ V, A x ∈ V)
    (h : S * A = -(A * S)) {δ : ℝ} (hδ : δ < 1) (hSV : ∀ x ∈ V, ‖S x - x‖ ≤ δ * ‖x‖) {x : E}
    (hx : x ∈ V) : A x = 0 := by
  have hcomm : S.restrict hS * A.restrict hA = -(A.restrict hA * S.restrict hS) := by
    ext y
    simpa using congrArg (fun T : E →L[ℂ] E => T y) h
  have hnear : ‖S.restrict hS - 1‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (le_max_right δ 0) fun y => ?_)
      (max_lt hδ one_pos)
    simpa using (hSV y y.property).trans
      (mul_le_mul_of_nonneg_right (le_max_left δ 0) (norm_nonneg y))
  have h0 := eq_zero_of_norm_sub_one_lt_one_of_mul_eq_neg_mul (A := V →L[ℂ] V) hnear hcomm
  simpa using congrArg (fun T : V →L[ℂ] V => (T ⟨x, hx⟩ : E)) h0

end TauCeti

namespace AlgEquiv

variable {𝕜 F : Type*} [NormedField 𝕜] [SeminormedRing F] [NormOneClass F] [NormedAlgebra 𝕜 F]

/-- Every `𝕜`-algebra equivalence from a seminormed `𝕜`-algebra `F` with `‖1‖ = 1` to its base
normed field `𝕜` preserves the norm. -/
@[simp]
theorem norm_map (e : F ≃ₐ[𝕜] 𝕜) (x : F) : ‖e x‖ = ‖x‖ := by
  have hx : algebraMap 𝕜 F (e x) = x := by
    rw [← e.symm.commutes (e x), Algebra.algebraMap_self_apply, e.symm_apply_apply]
  nth_rw 2 [← hx]
  rw [norm_algebraMap']

/-- Every `𝕜`-algebra equivalence from a seminormed `𝕜`-algebra `F` with `‖1‖ = 1` to its base
normed field `𝕜` is an isometry. -/
theorem isometry (e : F ≃ₐ[𝕜] 𝕜) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e e.norm_map

end AlgEquiv
