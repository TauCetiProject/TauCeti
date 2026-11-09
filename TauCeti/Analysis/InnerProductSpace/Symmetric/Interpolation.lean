/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth interpolation between symmetric operators

Two bounded symmetric operators `Sm` and `Sp` on a real inner product space are joined by a `C¹`
family of symmetric operators that equals `Sm` on `(-∞, -R]` and `Sp` on `[R, ∞)`, is locally
constant off `[-R, R]`, and has norm at most `‖Sm‖ + ‖Sp - Sm‖`
(`TauCeti.exists_contDiff_isSymmetric_interpolation`). The family interpolates through
`Real.smoothTransition`.
-/

public section

namespace TauCeti

open Set
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A `C¹` family of symmetric operators equal to `Sm` on `(-∞, -R]` and to `Sp` on `[R, ∞)`, with
norm at most `‖Sm‖ + ‖Sp - Sm‖`. It interpolates through `Real.smoothTransition`. -/
theorem exists_contDiff_isSymmetric_interpolation {Sm Sp : E →L[ℝ] E}
    (hSm : (Sm : E →ₗ[ℝ] E).IsSymmetric) (hSp : (Sp : E →ₗ[ℝ] E).IsSymmetric) {R : ℝ}
    (hR : 0 < R) :
    ∃ S : ℝ → E →L[ℝ] E, ContDiff ℝ 1 S ∧ (∀ s, (S s : E →ₗ[ℝ] E).IsSymmetric) ∧
      (∀ s ≤ -R, S s = Sm) ∧ (∀ s, R ≤ s → S s = Sp) ∧
      (∀ s ∉ Icc (-R) R, deriv S s = 0) ∧ ∀ s, ‖S s‖ ≤ ‖Sm‖ + ‖Sp - Sm‖ := by
  set σ : ℝ → ℝ := fun s ↦ Real.smoothTransition ((s + R) / (2 * R))
  set S : ℝ → E →L[ℝ] E := fun s ↦ Sm + σ s • (Sp - Sm)
  have hSbot (s : ℝ) (hs : s ≤ -R) : S s = Sm := by
    have : σ s = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    simp [S, this]
  have hStop (s : ℝ) (hs : R ≤ s) : S s = Sp := by
    have : σ s = 1 := Real.smoothTransition.one_of_one_le
      (by rw [le_div_iff₀ (by positivity)]; linarith)
    simp [S, this]
  refine ⟨S, contDiff_const.add
    ((Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)).smul
      contDiff_const), fun s x y ↦ ?_, hSbot, hStop, fun s hs ↦ ?_, fun s ↦ ?_⟩
  · simp only [S, ContinuousLinearMap.coe_coe, add_apply, smul_apply, sub_apply, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      hSm.apply_clm, hSp.apply_clm, RCLike.conj_to_real]
  · -- Off `[-R, R]` the family is locally constant.
    rcases lt_or_ge s (-R) with h | h
    · have : S =ᶠ[𝓝 s] fun _ ↦ Sm := by
        filter_upwards [Iio_mem_nhds h] with t ht using hSbot t ht.le
      rw [this.deriv_eq, deriv_const]
    · have h' : R < s := lt_of_not_ge fun h' ↦ hs ⟨h, h'⟩
      have : S =ᶠ[𝓝 s] fun _ ↦ Sp := by
        filter_upwards [Ioi_mem_nhds h'] with t ht using hStop t ht.le
      rw [this.deriv_eq, deriv_const]
  · refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)

end TauCeti
