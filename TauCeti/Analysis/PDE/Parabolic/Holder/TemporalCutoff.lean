/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Temporal cutoffs in the order-two parabolic Hölder space

The time derivative of a cutoff changing from zero to one on an interval of length `δ`
has supremum of size `δ⁻¹` and parabolic `α`-Hölder seminorm of size `δ^(-1 - α/2)`.
These bounds are uniform in the position of the transition, the spatial variable,
and the containing time slab.
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

omit [NormedSpace ℝ E] in
private theorem holderWith_scaled_time_deriv {M : ℝ≥0}
    (hM : HolderWith M (α / 2) (deriv smoothTransition))
    {δ : ℝ} (hδ : 0 < δ) (s a b : ℝ) :
    HolderWith (M * (δ ^ (-1 - (α : ℝ) / 2)).toNNReal) α
      (fun p : ParabolicSpaceTime.slab (E := E) a b ↦
        δ⁻¹ * deriv smoothTransition (((p : ParabolicSpaceTime E).time - s) / δ)) := by
  suffices hscaled : HolderWith (M * (δ ^ (-1 - (α : ℝ) / 2)).toNNReal) (α / 2)
      (fun t : ℝ ↦ δ⁻¹ * deriv smoothTransition ((t - s) / δ)) from
    (hscaled.holderOnWith (Icc a b)).comp_parabolicTime_slab
  apply holderOnWith_univ.1
  apply HolderOnWith.of_dist_le
  intro t _ r _
  have hd := hM.dist_le ((t - s) / δ) ((r - s) / δ)
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (rpow_nonneg hδ.le _), NNReal.coe_div,
    NNReal.coe_ofNat]
  simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hδ)]
  calc
    δ⁻¹ * |deriv smoothTransition ((t - s) / δ) -
        deriv smoothTransition ((r - s) / δ)| ≤
        δ⁻¹ * (M * (|t - r| / δ) ^ ((α : ℝ) / 2)) := by
      gcongr
      simpa [Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ] using hd
    _ = M * δ ^ (-1 - (α : ℝ) / 2) * |t - r| ^ ((α : ℝ) / 2) := by
      rw [div_rpow (abs_nonneg _) hδ.le, rpow_sub hδ, rpow_neg_one]
      ring

omit [NormedSpace ℝ E] in
private theorem exists_scaled_time_deriv {M : ℝ≥0}
    (hM : ∀ t, ‖deriv smoothTransition t‖ ≤ M)
    (hhol : HolderWith M (α / 2) (deriv smoothTransition))
    {δ : ℝ} (hδ : 0 < δ) (s a b : ℝ) :
    ∃ v : HolderSpace α (ParabolicSpaceTime.slab (E := E) a b) ℝ,
      (∀ p, v p = δ⁻¹ * deriv smoothTransition
        (((p : ParabolicSpaceTime E).time - s) / δ)) ∧
      ‖v.toBoundedContinuousFunction‖ ≤ M / δ ∧
      (nnHolderNorm α (v : ParabolicSpaceTime.slab (E := E) a b → ℝ) : ℝ) ≤
        M * δ ^ (-1 - (α : ℝ) / 2) ∧
      ‖v‖ ≤ M / δ + M * δ ^ (-1 - (α : ℝ) / 2) := by
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
  have hut : ‖ut‖ ≤ M / δ :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _
  refine ⟨v, fun p ↦ by simp [v, ut], ?_, ?_, ?_⟩
  · simpa only [v, HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction] using hut
  · have hsemi : nnHolderNorm α (ut : ParabolicSpaceTime.slab (E := E) a b → ℝ) ≤
        M * (δ ^ (-1 - (α : ℝ) / 2)).toNNReal := by
      exact_mod_cast coe_nnHolderNorm_le_eHolderNorm.trans huthol.eHolderNorm_le
    rw [hvfun]
    simpa only [NNReal.coe_mul, Real.coe_toNNReal _ (rpow_nonneg hδ.le _)] using
      (NNReal.coe_le_coe.2 hsemi)
  · have h := HolderSpace.norm_le_of_norm_le_of_holderWith (f := v)
      (M := (M : ℝ) / δ) (by positivity)
      (fun p ↦ by rw [hvfun]; exact (ut.norm_coe_le_norm p).trans hut)
      (by rw [hvfun]; exact huthol)
    simpa only [NNReal.coe_mul, Real.coe_toNNReal _ (rpow_nonneg hδ.le _)] using h

/-- **Temporal cutoffs with parabolic scaling.** For `α ≤ 2`, one constant works for every
transition interval `[s, s + δ]` and every closed time slab. The cutoff is zero before the
transition, one afterwards, has zero spatial derivatives, and its order-two norm is bounded
by `1 + M / δ + M δ^(-1 - α/2)`. Its value and time derivative are given explicitly by the
rescaled smooth transition and its derivative. The derivative's supremum and parabolic
Hölder seminorm are bounded separately by `M / δ` and `M δ^(-1 - α/2)`.
In particular the norm is `O(δ^(-1 - α/2))` as `δ ↓ 0`. -/
theorem exists_temporal_cutoff (hα : α ≤ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {δ : ℝ}, 0 < δ → ∀ (s a b : ℝ) (hab : a < b),
      ∃ χ : ParabolicC2HolderSpace α E ℝ hab,
        (∀ p, χ p = smoothTransition (((p : ParabolicSpaceTime E).time - s) / δ)) ∧
        (∀ p, timeDerivL χ p =
          δ⁻¹ * deriv smoothTransition (((p : ParabolicSpaceTime E).time - s) / δ)) ∧
        (∀ p, χ p ∈ Icc 0 1) ∧
        (∀ p : ParabolicSpaceTime.slab (E := E) a b,
          (p : ParabolicSpaceTime E).time ≤ s → χ p = 0) ∧
        (∀ p : ParabolicSpaceTime.slab (E := E) a b,
          s + δ ≤ (p : ParabolicSpaceTime E).time → χ p = 1) ∧
        spatialFDerivL χ = 0 ∧ spatialSecondFDerivL χ = 0 ∧
        ‖(timeDerivL χ).toBoundedContinuousFunction‖ ≤ M / δ ∧
        (nnHolderNorm α (timeDerivL χ : ParabolicSpaceTime.slab (E := E) a b → ℝ) : ℝ) ≤
          M * δ ^ (-1 - (α : ℝ) / 2) ∧
        ‖χ‖ ≤ 1 + M / δ + M * δ ^ (-1 - (α : ℝ) / 2) := by
  have hd : ContDiff ℝ 1 (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 2)).deriv'
  obtain ⟨M, hhol, hM⟩ := hd.exists_holderWith_and_norm_le_of_hasCompactSupport
    smoothTransition.hasCompactSupport_deriv
    ((div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2 (by simpa using hα))
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
  obtain ⟨v, hv, hvsup, hvsemi, hvnorm⟩ := exists_scaled_time_deriv (E := E) hM hhol hδ s a b
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
    simp only [χ, mk_apply, u, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  refine ⟨χ, hχ, ?_, ?_, ?_, ?_, by simp only [χ, spatialFDerivL_mk],
    by simp only [χ, spatialSecondFDerivL_mk], ?_, ?_, ?_⟩
  · simpa only [χ, timeDerivL_mk] using hv
  · intro p
    rw [hχ]
    exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · intro p hp
    rw [hχ]
    exact smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  · intro p hp
    rw [hχ]
    exact smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith))
  · simpa only [χ, timeDerivL_mk] using hvsup
  · simpa only [χ, timeDerivL_mk] using hvsemi
  · -- The norm is the value supremum plus the time-derivative Hölder norm.
    -- Scaling time by δ produces δ⁻¹ in the supremum and δ^(-1-α/2) in the seminorm.
    have hu : ‖u‖ ≤ 1 := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _
    simp only [χ, norm_eq, valueL_mk, spatialFDerivL_mk,
      spatialSecondFDerivL_mk, timeDerivL_mk]
    have hz : ‖(0 : ParabolicSpaceTime.slab (E := E) a b →ᵇ (E →L[ℝ] ℝ))‖ = 0 := norm_zero
    rw [hz]
    simp only [norm_zero, zero_add, add_zero]
    linarith

end TauCeti.ParabolicC2HolderSpace
