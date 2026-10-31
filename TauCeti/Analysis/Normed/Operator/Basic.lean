/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Basic facts about bounded operators

For continuous semilinear maps from a seminormed space to a normed space, zero operator norm
forces the map to vanish. The corresponding normed group structure is available as an explicit
construction, including for strong duals of seminormed spaces.

This file also records a shared uniform-bound lemma for continuous linear maps between seminormed
spaces. It lets an evaluation `T i (g i)` pass to the limit when the operators `T i` are eventually
uniformly bounded, their values at the limiting argument converge, and the arguments `g i` converge.
In particular, it supplies the common continuity step for
`StronglyContinuousSemigroup.tendsto_realOperator_apply` and
`StronglyContinuousGroup.tendsto_apply`.

Finally, an operator bounded below is injective
(`ContinuousLinearMap.injective_of_forall_norm_le`), an invertible operator `A` on a normed space
cancels against its inverse (`ContinuousLinearMap.ringInverse_apply_apply`,
`ContinuousLinearMap.apply_ringInverse_apply`) and is bounded below by `‖A⁻¹‖⁻¹`
(`ContinuousLinearMap.norm_le_norm_ringInverse_mul_norm_apply`), and conversely a lower bound
`‖x‖ ≤ M ‖A x‖` bounds the norm of the inverse by `M`
(`ContinuousLinearMap.norm_ringInverse_le_of_forall_norm_le`).
-/

public section

open scoped Topology
open Filter

namespace ContinuousLinearMap

section Semilinear

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- An operator from a seminormed space to a normed space has zero norm exactly when it is zero.
This generalizes `opNorm_zero_iff` to seminormed sources. -/
@[simp]
theorem opNorm_zero_iff' (f : E →SL[σ] F) : ‖f‖ = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext x
    exact norm_le_zero_iff.mp (by simpa only [hf, zero_mul] using f.le_opNorm x)
  · rintro rfl
    exact norm_zero

/-- The nonnegative operator norm vanishes exactly at zero, even for a seminormed source. -/
@[simp]
theorem opNNNorm_eq_zero_iff (f : E →SL[σ] F) : ‖f‖₊ = 0 ↔ f = 0 := by
  simpa only [← NNReal.coe_eq_zero, coe_nnnorm] using f.opNorm_zero_iff'

/-- The extended operator norm vanishes exactly at zero, even for a seminormed source. -/
@[simp]
theorem opENorm_eq_zero_iff (f : E →SL[σ] F) : ‖f‖ₑ = 0 ↔ f = 0 := by
  simpa only [enorm_eq_nnnorm, ENNReal.coe_eq_zero] using f.opNNNorm_eq_zero_iff

/-- Continuous semilinear maps from a seminormed space to a normed space form a normed group
for the operator norm. Use this construction locally when the source is only seminormed. -/
noncomputable abbrev normedAddCommGroup : NormedAddCommGroup (E →SL[σ] F) :=
  .ofSeparation fun f ↦ f.opNorm_zero_iff'.mp

end Semilinear

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- If `T i` is eventually uniformly bounded, `T i z` tends to `w`, and `g i` tends to `z`, then
the moving evaluations `T i (g i)` tend to `w`. -/
theorem tendsto_apply_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {T : ι → X →L[𝕜] Y} {C : ℝ} {g : ι → X} {z : X} {w : Y}
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) (hz : Tendsto (fun i => T i z) l (𝓝 w))
    (hg : Tendsto g l (𝓝 z)) : Tendsto (fun i => T i (g i)) l (𝓝 w) := by
  have hmove : Tendsto (fun i => T i (g i - z)) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => C * ‖g i - z‖) ?_ ?_
    · filter_upwards [hT] with i hi
      exact (T i).le_of_opNorm_le hi _
    · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul C
  simpa only [map_sub, sub_add_cancel, zero_add] using hmove.add hz

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An operator bounded below, `‖x‖ ≤ M ‖f x‖`, is injective. -/
theorem injective_of_forall_norm_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →L[𝕜] F} {M : ℝ} (h : ∀ x, ‖x‖ ≤ M * ‖f x‖) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
  simpa [hx] using h x

/-- The inverse of an invertible operator undoes the operator. -/
@[simp]
theorem ringInverse_apply_apply {A : E →L[𝕜] E} (hA : IsUnit A) (x : E) :
    Ring.inverse A (A x) = x := by
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel A hA, one_apply_eq_self]

/-- An invertible operator undoes its inverse. -/
@[simp]
theorem apply_ringInverse_apply {A : E →L[𝕜] E} (hA : IsUnit A) (y : E) :
    A (Ring.inverse A y) = y := by
  rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel A hA, one_apply_eq_self]

/-- An invertible operator is bounded below by the reciprocal of the norm of its inverse. -/
theorem norm_le_norm_ringInverse_mul_norm_apply {A : E →L[𝕜] E} (hA : IsUnit A) (x : E) :
    ‖x‖ ≤ ‖Ring.inverse A‖ * ‖A x‖ := by
  calc
    ‖x‖ = ‖Ring.inverse A (A x)‖ := by rw [ringInverse_apply_apply hA]
    _ ≤ ‖Ring.inverse A‖ * ‖A x‖ := le_opNorm _ _

/-- An invertible operator bounded below by `M⁻¹` has an inverse of norm at most `M`. -/
theorem norm_ringInverse_le_of_forall_norm_le {A : E →L[𝕜] E} (hA : IsUnit A) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ x, ‖x‖ ≤ M * ‖A x‖) : ‖Ring.inverse A‖ ≤ M := by
  refine opNorm_le_bound _ hM fun y ↦ ?_
  simpa only [apply_ringInverse_apply hA] using h (Ring.inverse A y)

end Inverse

end ContinuousLinearMap

end
