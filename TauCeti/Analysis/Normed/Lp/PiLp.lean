/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Monotonicity of finite product norms

The finite `Lᵖ` norm respects coordinatewise bounds on norms, including when the two
families have different target spaces. This compares scalar evaluations of a vector
family with the vector family's `Lᵖ` norm. For constant fibres we deduce the bound for
the image of a family under a map of bounded growth, the norm of a family of multiples
of one vector, and the invariance of the norm under reindexing.
-/

public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞}
  {E F : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
  [∀ i, SeminormedAddCommGroup (F i)]

/-- Coordinatewise domination of norms implies domination of finite `Lᵖ` norms. -/
theorem norm_mono {x : PiLp p E} {y : PiLp p F}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [norm_eq_card, norm_eq_card]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    apply Set.Finite.toFinset_mono
    intro i hi hzero
    exact hi (le_antisymm (by simpa only [hzero] using h i) (norm_nonneg _))
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [norm_eq_ciSup, norm_eq_ciSup]
    exact ciSup_mono (Set.finite_range _).bddAbove h
  · simp only [norm_eq_sum (ENNReal.toReal_pos hp0 hp)]
    gcongr
    · exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    · exact h _

/-- Taking coordinate norms preserves the finite `Lᵖ` norm. -/
@[simp]
theorem norm_norm (x : PiLp p E) :
    ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ = ‖x‖ :=
  le_antisymm (norm_mono fun i ↦ by simp) (norm_mono fun i ↦ by simp)

section Constant

variable [Fact (1 ≤ p)] {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- Applying a map with `‖g v‖ ≤ C * ‖v‖` to each member of a finite family multiplies its
`Lᵖ` norm by at most `C`. -/
theorem norm_toLp_comp_le {g : E → F} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ v, ‖g v‖ ≤ C * ‖v‖)
    (x : ι → E) : ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ C * ‖WithLp.toLp p x‖ := by
  calc
    ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ ‖C • WithLp.toLp p (fun i ↦ ‖x i‖)‖ :=
      norm_mono fun i ↦ by simpa [abs_of_nonneg hC] using hg (x i)
    _ = C * ‖WithLp.toLp p x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_norm (WithLp.toLp p x)]

/-- A finite family of multiples of one vector has `Lᵖ` norm equal to the `Lᵖ` norm of the
coefficients times the norm of the vector. -/
theorem norm_toLp_smul_const {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] (a : ι → 𝕜) (y : F) :
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖WithLp.toLp p a‖ * ‖y‖ := by
  calc
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖‖y‖ • WithLp.toLp p (fun i ↦ ‖a i‖)‖ :=
      le_antisymm (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
        (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
    _ = ‖WithLp.toLp p a‖ * ‖y‖ := by
      rw [norm_smul, _root_.norm_norm, norm_norm (WithLp.toLp p a), mul_comm]

/-- Reindexing a finite family along an equivalence preserves its `Lᵖ` norm. -/
theorem norm_toLp_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (x : ι → E) :
    ‖WithLp.toLp p (x ∘ e)‖ = ‖WithLp.toLp p x‖ := by
  have he : LinearIsometryEquiv.piLpCongrLeft p ℤ E e.symm (WithLp.toLp p x) =
      WithLp.toLp p (x ∘ e) := by
    ext i
    simp [Equiv.piCongrLeft']
  rw [← he, LinearIsometryEquiv.norm_map]

end Constant

end PiLp
