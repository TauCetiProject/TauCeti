/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Critical inverse-norm and radial singularities in local Sobolev classes

On a finite-dimensional real inner product space of dimension `d ≥ 2`, the normalized radial map
`NormedSpace.normalize : E → E` (`x ↦ ‖x‖⁻¹ • x`) belongs to `TauCeti.MemWkpLoc p U 1` near the
origin if and only if `p < d` (`TauCeti.memWkpLoc_one_normalize_iff`), matching the critical local
`Lᵖ` threshold for `x ↦ ‖x‖⁻¹` from `TauCeti.MeasureTheory.Function.MemLpLoc.NormInv`.

## Main declarations

* `TauCeti.memWkpLoc_one_normalize`: `NormedSpace.normalize` is in `W^{1,p}_loc` everywhere for
  `p < dim E` when `1 < dim E`.
* `TauCeti.not_memWkpLoc_one_normalize`: `NormedSpace.normalize` is not in `W^{1,p}_loc` near `0`
  for `dim E ≤ p` when `1 < dim E`.
* `TauCeti.memWkpLoc_one_normalize_iff`: characterization `MemWkpLoc p U 1 NormedSpace.normalize ↔
  p < dim E` near the origin for `1 < dim E`.
-/

public noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology RealInnerProductSpace

namespace TauCeti

section RadialSingularity

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {p : ENNReal} {U : Set E}

/-- In dimension `d ≥ 2`, the normalized radial map `NormedSpace.normalize` (`x ↦ ‖x‖⁻¹ • x`)
lies in `MemWkpLoc p U 1` on every set whenever `p < d`. -/
theorem memWkpLoc_one_normalize (hd : 1 < Module.finrank ℝ E) (hp : p < Module.finrank ℝ E) :
    MemWkpLoc p U 1 (NormedSpace.normalize : E → E) := by
  have hs : -(Module.finrank ℝ E : ℝ) < -1 := by
    have : (1 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
    linarith
  have hfun : (NormedSpace.normalize : E → E) = fun x : E => ‖x‖ ^ (-1 : ℝ) • x :=
    funext fun x => by rw [NormedSpace.normalize, Real.rpow_neg_one]
  let D : E → E →L[ℝ] E := fun x => ‖x‖ ^ (-1 : ℝ) • ContinuousLinearMap.id ℝ E +
    ((-1 * ‖x‖ ^ ((-1 : ℝ) - 2)) • innerSL ℝ x).smulRight x
  refine memWkpLoc_one_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, D, ?_,
      memLpLoc_iff.2 fun K _ hK => ?_⟩
  · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    refine MemLp.of_bound
      (by unfold NormedSpace.normalize; fun_prop :
        Measurable (NormedSpace.normalize : E → E)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [NormedSpace.norm_normalize hx]
  · rw [hfun]
    have hd' : -max 1 (Module.finrank ℝ E : ℝ) < -1 :=
      neg_lt_neg ((by exact_mod_cast hd : (1 : ℝ) < Module.finrank ℝ E).trans_le
        (le_max_right _ _))
    exact hasWeakFDerivOn_norm_rpow_smul_self hd' (Opens.interior U)
  · have hker : MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict K) :=
      hK.isBounded.memLp_norm_inv_restrict hp
    refine (hker.const_mul (1 + |(-1 : ℝ)|)).of_le
      (locallyIntegrable_rpow_smul_id_add_smulRight (μ := volume) hs).aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
    exact norm_rpow_smul_id_add_smulRight_le (-1) x

/-- In dimension `d ≥ 2`, the normalized radial map `NormedSpace.normalize` is not in
`MemWkpLoc p U 1` for any `p ≥ d` when `0 ∈ interior U`. -/
theorem not_memWkpLoc_one_normalize (hd : 1 < Module.finrank ℝ E)
    (hp : Module.finrank ℝ E ≤ p) (h0 : (0 : E) ∈ interior U) :
    ¬ MemWkpLoc p U 1 (NormedSpace.normalize : E → E) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (zero_lt_one.trans hd)
  intro h
  obtain ⟨-, D, hD, hDLp⟩ := memWkpLoc_one_iff.1 h
  set Ω' : Opens E := Opens.interior U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hsmooth : ContDiffOn ℝ 1 (NormedSpace.normalize : E → E) (Ω' : Set E) := fun x hx =>
    (((contDiffAt_norm ℝ hx.2 : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x).inv
      (norm_ne_zero_iff.2 hx.2)).smul contDiffAt_id).contDiffWithinAt
  have hfu := hsmooth.hasWeakFDerivOn_fderiv (μ := volume)
  have hae : D =ᵐ[volume.restrict Ω'] fderiv ℝ (NormedSpace.normalize : E → E) :=
    (hD.mono inf_le_left).ae_eq hfu
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hK : closedBall (0 : E) (r / 2) ⊆ interior U :=
    (closedBall_subset_ball (by linarith)).trans hrU
  have hDK : MemLp D p (volume.restrict (closedBall (0 : E) (r / 2))) :=
    memLpLoc_iff.1 hDLp _ (hK.trans interior_subset) (isCompact_closedBall 0 _)
  have hinvK :
      MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict (closedBall (0 : E) (r / 2))) := by
    refine hDK.of_le (by fun_prop : Measurable fun x : E => ‖x‖⁻¹).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_closedBall]
    have h1 := (ae_restrict_iff' Ω'.isOpen.measurableSet).1 hae
    have hnull : ∀ᵐ x ∂(volume : Measure E), x ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [h1, hnull] with x hx hx0 hxb
    rw [hx ⟨hK hxb, hx0⟩, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x))]
    exact inv_norm_le_norm_fderiv_normalize_of_one_lt_finrank hd hx0
  exact not_memLp_norm_inv_closedBall (half_pos hr) hp hinvK

/-- **Critical exponent for `NormedSpace.normalize`.** On a finite-dimensional real inner product
space of dimension `d ≥ 2`, `NormedSpace.normalize` lies in `MemWkpLoc p U 1` on any set whose
interior contains the origin iff `p < d`. -/
theorem memWkpLoc_one_normalize_iff (hd : 1 < Module.finrank ℝ E) (h0 : (0 : E) ∈ interior U) :
    MemWkpLoc p U 1 (NormedSpace.normalize : E → E) ↔ p < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_one_normalize hd hp h0 h,
    fun hp => memWkpLoc_one_normalize hd hp⟩

end Normalize

end RadialSingularity

end TauCeti
