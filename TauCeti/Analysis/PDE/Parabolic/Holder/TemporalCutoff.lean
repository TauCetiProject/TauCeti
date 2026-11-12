/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import TauCeti.Topology.MetricSpace.Holder

/-!
# Temporal cutoffs in the order-two parabolic Hölder space

A time cutoff changing from zero to one on an interval of length `δ` has time derivative
of size `δ⁻¹` and parabolic `α`-Hölder seminorm of size `δ^(-1 - α/2)`. These bounds are uniform
in the position of the transition, the spatial variable, and the containing time slab.
Unlike a compactly supported space-time cutoff, it is one on an entire later time slab.

Such cutoffs remove the initial trace when applying a closed-slab Schauder estimate away
from the initial time. The scale of their time derivative is essential in the resulting
positive-time estimates. The construction uses Mathlib's smooth transition function.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004),
  Chapter 4 (time localization for parabolic estimates).
-/

public section
noncomputable section

open Set Metric Real
open scoped NNReal ContDiff BoundedContinuousFunction

namespace TauCeti.ParabolicC2HolderSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ≥0}

-- Keep the nested operator-space instances shared by the jet constructor and its norm.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

private theorem exists_holderWith_deriv_smoothTransition (hα : α ≤ 2) :
    ∃ M : ℝ≥0, (∀ t, ‖deriv smoothTransition t‖ ≤ M) ∧
      HolderWith M (α / 2) (deriv smoothTransition) := by
  have hd : ContDiff ℝ 1 (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 2)).deriv'
  obtain ⟨K, hK⟩ := hd.lipschitzWith_of_hasCompactSupport
    smoothTransition.hasCompactSupport_deriv (by simp)
  obtain ⟨B, hB⟩ := smoothTransition.exists_forall_norm_deriv_le
  let M : ℝ≥0 := ⟨(K : ℝ) + 2 * |B|, by positivity⟩
  have hMcoe : (M : ℝ) = K + 2 * |B| := (rfl)
  have hBM : B ≤ M := by
    rw [hMcoe]
    nlinarith [le_abs_self B, abs_nonneg B, K.coe_nonneg]
  have hbnn (x : ℝ) : ‖deriv smoothTransition x‖₊ ≤ |B|.toNNReal := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (abs_nonneg B)]
    exact (hB x).trans (le_abs_self B)
  have hzero : HolderWith M 0 (deriv smoothTransition) :=
    (holderWith_zero_of_nnnorm_le hbnn).mono (by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_ofNat,
        Real.coe_toNNReal _ (abs_nonneg B), hMcoe]
      exact le_add_of_nonneg_left K.coe_nonneg)
  refine ⟨M, fun t ↦ (hB t).trans hBM, ?_⟩
  have hKM : K ≤ M := by
    exact_mod_cast (show (K : ℝ) ≤ M by
      rw [hMcoe]
      exact le_add_of_nonneg_right (by positivity))
  simpa only [max_self] using hzero.of_le_of_le (hK.weaken hKM).holderWith
    (by positivity) ((div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2 (by simpa using hα))

omit [NormedSpace ℝ E] in
private theorem holderWith_scaled_time_deriv {M : ℝ≥0}
    (hM : HolderWith M (α / 2) (deriv smoothTransition))
    {δ : ℝ} (hδ : 0 < δ) (s a b : ℝ) :
    HolderWith (M * (δ ^ (-1 - (α : ℝ) / 2)).toNNReal) α
      (fun p : ParabolicSpaceTime.slab (E := E) a b ↦
        δ⁻¹ * deriv smoothTransition (((p : ParabolicSpaceTime E).time - s) / δ)) := by
  apply holderOnWith_univ.1
  apply HolderOnWith.of_dist_le
  intro p _ q _
  have hd := hM.dist_le (((p : ParabolicSpaceTime E).time - s) / δ)
    (((q : ParabolicSpaceTime E).time - s) / δ)
  have htime := ParabolicSpaceTime.sqrt_abs_time_sub_le_dist
    (p : ParabolicSpaceTime E) (q : ParabolicSpaceTime E)
  have hpow : |(p : ParabolicSpaceTime E).time - (q : ParabolicSpaceTime E).time| ^
      ((α : ℝ) / 2) ≤ dist p q ^ (α : ℝ) := by
    rw [rpow_div_two_eq_sqrt _ (abs_nonneg _)]
    exact rpow_le_rpow (sqrt_nonneg _) htime α.coe_nonneg
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (rpow_nonneg hδ.le _)]
  simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hδ)]
  calc
    δ⁻¹ * |deriv smoothTransition (((p : ParabolicSpaceTime E).time - s) / δ) -
        deriv smoothTransition (((q : ParabolicSpaceTime E).time - s) / δ)| ≤
        δ⁻¹ * (M * (|(p : ParabolicSpaceTime E).time -
          (q : ParabolicSpaceTime E).time| / δ) ^ ((α : ℝ) / 2)) := by
      gcongr
      simpa [Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ] using hd
    _ = M * δ ^ (-1 - (α : ℝ) / 2) *
        |(p : ParabolicSpaceTime E).time - (q : ParabolicSpaceTime E).time| ^ ((α : ℝ) / 2) := by
      rw [div_rpow (abs_nonneg _) hδ.le, rpow_sub hδ, rpow_neg_one]
      ring
    _ ≤ M * δ ^ (-1 - (α : ℝ) / 2) * dist p q ^ (α : ℝ) := by gcongr

/-- **Temporal cutoffs with parabolic scaling.** For `α ≤ 2`, one constant works for every
transition interval `[s, s + δ]` and every closed time slab. The cutoff is zero before the
transition, one afterwards, has zero spatial derivatives, and its order-two norm is bounded
by `1 + M / δ + M δ^(-1 - α/2)`. In particular it is `O(δ^(-1 - α/2))` as `δ ↓ 0`. -/
theorem exists_temporal_cutoff (hα : α ≤ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {δ : ℝ}, 0 < δ → ∀ (s a b : ℝ) (hab : a < b),
      ∃ χ : ParabolicC2HolderSpace α E ℝ hab,
        (∀ p, χ p ∈ Icc 0 1) ∧
        (∀ p : ParabolicSpaceTime.slab (E := E) a b,
          (p : ParabolicSpaceTime E).time ≤ s → χ p = 0) ∧
        (∀ p : ParabolicSpaceTime.slab (E := E) a b,
          s + δ ≤ (p : ParabolicSpaceTime E).time → χ p = 1) ∧
        spatialFDerivL χ = 0 ∧ spatialSecondFDerivL χ = 0 ∧
        ‖χ‖ ≤ 1 + M / δ + M * δ ^ (-1 - (α : ℝ) / 2) := by
  obtain ⟨M, hM, hhol⟩ := exists_holderWith_deriv_smoothTransition hα
  refine ⟨M, M.coe_nonneg, fun {δ} hδ s a b hab ↦ ?_⟩
  let f : ℝ → ℝ := fun t ↦ smoothTransition ((t - s) / δ)
  have hf : ContDiff ℝ ∞ f := smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const δ)
  have hder (t : ℝ) : HasDerivAt f
      (δ⁻¹ * deriv smoothTransition ((t - s) / δ)) t := by
    simpa [f, Function.comp_def, div_eq_mul_inv, mul_comm] using
      (((smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp t
        (((hasDerivAt_id t).sub_const s).div_const δ))
  -- Bundle the value and time derivative. Their bounds depend on the transition scale,
  -- not on the containing slab; both spatial derivative fields are zero.
  let u : ParabolicSpaceTime.slab (E := E) a b →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p ↦ f (p : ParabolicSpaceTime E).time)
      (hf.continuous.comp (by fun_prop)) 1 (fun p ↦ smoothTransition.abs_le_one _)
  let ut : ParabolicSpaceTime.slab (E := E) a b →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p ↦ δ⁻¹ * deriv smoothTransition (((p : ParabolicSpaceTime E).time - s) / δ))
      (by fun_prop) (M / δ) (fun p ↦ by
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
        exact (mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 hδ.le)).trans_eq
          (by ring))
  have huthol : HolderWith (M * (δ ^ (-1 - (α : ℝ) / 2)).toNNReal) α
      (ut : ParabolicSpaceTime.slab (E := E) a b → ℝ) :=
    holderWith_scaled_time_deriv hhol hδ s a b
  let v := HolderSpace.ofBoundedContinuousFunction ut huthol.memHolder
  have hvfun : (v : ParabolicSpaceTime.slab (E := E) a b → ℝ) = ut := by
    ext p
    exact HolderSpace.ofBoundedContinuousFunction_apply _ _ p
  have hv (p) : v p = δ⁻¹ * deriv smoothTransition
      (((p : ParabolicSpaceTime E).time - s) / δ) := by simp [v, ut]
  have hx (t : Icc a b) (x : E) :
      HasFDerivAt (fun y ↦ u (ParabolicSpaceTime.slabMk y t))
        ((0 : ParabolicSpaceTime.slab (E := E) a b →ᵇ (E →L[ℝ] ℝ))
          (ParabolicSpaceTime.slabMk x t)) x := by
    simpa [u] using hasFDerivAt_const (x := x) (c := f t)
  -- Clamping agrees with the ordinary time function on the closed interval, so the
  -- derivative identity includes the one-sided derivatives at both endpoints.
  have ht (x : E) (t : Icc a b) :
      HasDerivWithinAt (timeExtension hab.le u x) (v (ParabolicSpaceTime.slabMk x t))
        (Icc a b) t := by
    rw [hv]
    simpa only [ParabolicSpaceTime.time_slabMk] using
      (hder t).hasDerivWithinAt.congr_of_mem (f₁ := timeExtension hab.le u x)
        (fun r hr ↦ by simp [timeExtension_def, u, projIcc_of_mem hab.le hr]) t.2
  have hxx (t : Icc a b) (x : E) :
      HasFDerivAt (fun y ↦ (0 : ParabolicSpaceTime.slab (E := E) a b →ᵇ (E →L[ℝ] ℝ))
        (ParabolicSpaceTime.slabMk y t))
        ((0 : HolderSpace α (ParabolicSpaceTime.slab (E := E) a b) (E →L[ℝ] E →L[ℝ] ℝ))
          (ParabolicSpaceTime.slabMk x t)) x := by
    simpa using hasFDerivAt_const (x := x) (c := (0 : E →L[ℝ] ℝ))
  let χ := mk (hab := hab) u 0 0 v hx hxx ht
  have hχ (p : ParabolicSpaceTime.slab (E := E) a b) :
      χ p = f (p : ParabolicSpaceTime E).time := by
    simp only [χ, mk_apply]
    rfl
  refine ⟨χ, ?_, ?_, ?_, by simp only [χ, spatialFDerivL_mk],
    by simp only [χ, spatialSecondFDerivL_mk], ?_⟩
  · intro p
    rw [hχ]
    exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · intro p hp
    rw [hχ]
    exact smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  · intro p hp
    rw [hχ]
    exact smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith))
  · -- The norm is the value supremum plus the time-derivative Hölder norm.
    -- Scaling time by δ produces δ⁻¹ in the supremum and δ^(-1-α/2) in the seminorm.
    have hu : ‖u‖ ≤ 1 := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _
    have hut : ‖ut‖ ≤ M / δ :=
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _
    have hvnorm : ‖v‖ ≤ M / δ + M * δ ^ (-1 - (α : ℝ) / 2) := by
      have h := HolderSpace.norm_le_of_norm_le_of_holderWith (f := v)
        (M := (M : ℝ) / δ) (by positivity)
        (fun p ↦ by rw [hvfun]; exact (ut.norm_coe_le_norm p).trans hut)
        (by rw [hvfun]; exact huthol)
      simpa only [NNReal.coe_mul, Real.coe_toNNReal _ (rpow_nonneg hδ.le _)] using h
    simp only [χ, norm_eq, valueL_mk, spatialFDerivL_mk,
      spatialSecondFDerivL_mk, timeDerivL_mk]
    have hz : ‖(0 : ParabolicSpaceTime.slab (E := E) a b →ᵇ (E →L[ℝ] ℝ))‖ = 0 := norm_zero
    rw [hz]
    simp only [norm_zero, zero_add, add_zero]
    linarith

end TauCeti.ParabolicC2HolderSpace
