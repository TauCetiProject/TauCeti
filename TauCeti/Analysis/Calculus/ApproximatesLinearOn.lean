/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# A priori estimates for maps approximating linear maps

An estimate controlling a vector by its image under a continuous linear map and an auxiliary
additive map persists under a nonlinear approximation, with a loss proportional to the
approximation constant. `ApproximatesLinearOn.one_sub_mul_norm_sub_le` records this absorption
estimate. Taking the auxiliary map to be a projection onto the kernel gives the nonlinear form
of the Peetre estimate used in local properness arguments.

Mathlib's local surjectivity and injectivity theorems also locate a unique zero of a map
approximating a linear equivalence on a closed ball:
`ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le`.
-/

public section

open Set
open scoped NNReal Pointwise

namespace ApproximatesLinearOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An a priori estimate for a linear map on `s - s` persists under a nonlinear approximation,
with its left side scaled by `1 - C * ε`. For `C * ε < 1`, this controls `‖x - y‖` by the images
under `f` and an auxiliary additive map `P`.

Taking `P` to be a projection onto the kernel recovers the nonlinear Peetre estimate; see
Wendl, *Fredholm operators*, Lemma 5.2, for the linear estimate. -/
theorem one_sub_mul_norm_sub_le {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {ε : ℝ≥0}
    (hf : ApproximatesLinearOn f f' s ε) {G 𝓕 : Type*} [SeminormedAddGroup G]
    [FunLike 𝓕 E G] [AddMonoidHomClass 𝓕 E G] {P : 𝓕} {C : ℝ} (hC : 0 ≤ C)
    (hest : ∀ z ∈ s - s, ‖z‖ ≤ C * ‖f' z‖ + ‖P z‖)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    (1 - C * (ε : ℝ)) * ‖x - y‖ ≤ C * ‖f x - f y‖ + ‖P x - P y‖ := by
  have hestxy := hest (x - y) (sub_mem_sub hx hy)
  have hnorm : ‖f' (x - y)‖ ≤ ‖f x - f y‖ + (ε : ℝ) * ‖x - y‖ :=
    (norm_le_norm_add_norm_sub (f x - f y) _).trans
      (add_le_add le_rfl (hf x hx y hy))
  have hmul := mul_le_mul_of_nonneg_left hnorm hC
  rw [map_sub P x y] at hestxy
  nlinarith

/-- A map approximating a linear equivalence `f'` on a closed ball around `b`, with constant at most
`(2 * C)⁻¹` for a bound `C` on `‖f'⁻¹‖`, has a zero within `2 * C * ‖f b‖` of `b` as soon as that
radius fits in the ball, and this zero is the only zero of the map in the ball. -/
theorem exists_eq_zero_of_two_mul_norm_le [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F}
    {b : E} {r : ℝ} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) (Metric.closedBall b r) c) {C : ℝ}
    (hC : 0 < C) (hf' : ‖(f'.symm : F →L[𝕜] E)‖ ≤ C) (hc : 2 * C * c ≤ 1)
    (hr : 2 * C * ‖f b‖ ≤ r) :
    ∃ a ∈ Metric.closedBall b (2 * C * ‖f b‖), f a = 0 ∧
      ∀ z ∈ Metric.closedBall b r, f z = 0 → z = a := by
  have hbound (v : F) : ‖f'.symm v‖ ≤ C * ‖v‖ :=
    ((f'.symm : F →L[𝕜] E).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf' (norm_nonneg v))
  -- A right inverse of `f'` with the bound `C` in place of `‖f'⁻¹‖`, which may vanish.
  let R : (f' : E →L[𝕜] F).NonlinearRightInverse :=
    { toFun := f'.symm
      nnnorm := ⟨C, hC.le⟩
      bound' := hbound
      right_inv' := f'.apply_symm_apply }
  have hsub := Metric.closedBall_subset_closedBall (x := b) hr
  have hzero : (0 : F) ∈ Metric.closedBall (f b) ((C⁻¹ - c) * (2 * C * ‖f b‖)) := by
    rw [Metric.mem_closedBall, dist_comm, dist_zero_right]
    have hCinv : C⁻¹ * C = 1 := inv_mul_cancel₀ hC.ne'
    nlinarith [norm_nonneg (f b)]
  obtain ⟨a, ha, hfa⟩ := (hf.mono_set hsub).surjOn_closedBall_of_nonlinearRightInverse R
    (by positivity) le_rfl hzero
  have hinj : InjOn f (Metric.closedBall b r) := by
    apply hf.injOn
    rcases f'.subsingleton_or_nnnorm_symm_pos with hE | hpos
    · exact Or.inl hE
    right
    refine (NNReal.lt_inv_iff_mul_lt hpos.ne').2 ?_
    rw [← NNReal.coe_lt_coe]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left hf' c.coe_nonneg
    nlinarith
  exact ⟨a, ha, hfa, fun z hz hfz ↦ hinj hz (hsub ha) (hfz.trans hfa.symm)⟩

end ApproximatesLinearOn
