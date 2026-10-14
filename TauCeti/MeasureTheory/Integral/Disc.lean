/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Radial differentiation of disc integrals

For an integrable density on a disc, continuous away from its centre, the derivative of
its integral with respect to the radius is the boundary integral, parametrized by
`circleMap`. The density may have an integrable singularity at the centre. In particular,
this formula applies to finite energy on a punctured disc before an extension is known.

The annular polar formula is `TauCeti.integral_annulus_eq_integral_circleMap`; the derivative
uses Mathlib's fundamental theorem of calculus on a compact annulus around the radius.
The target may be any real Banach space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (the radial energy calculation).
-/

public section

open Complex MeasureTheory Metric Set Filter
open scoped Real Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Boundary density integrals of a continuous density on a closed annulus depend continuously
on the radius. Continuity at the centre is not required. -/
theorem ContinuousOn.smul_integral_comp_circleMap [CompleteSpace F]
    {f : ℂ → F} {z₀ : ℂ} {a b : ℝ}
    (hf : ContinuousOn f {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}) (ha : 0 ≤ a) :
    ContinuousOn (fun r ↦ r • ∫ θ in -π..π, f (circleMap z₀ r θ)) (Icc a b) := by
  let A := {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have hcompact : IsCompact A := (isCompact_closedBall z₀ b).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const))
    (fun z hz ↦ by simpa only [mem_closedBall, dist_eq_norm] using hz.2)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hf
  have hmem (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) : circleMap z₀ r θ ∈ A := by
    simpa only [A, mem_ofPred_eq, circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg (ha.trans hr.1)] using (mem_Icc.mp hr)
  have hcont (r : ℝ) (hr : r ∈ Icc a b) :
      ContinuousOn (fun θ ↦ f (circleMap z₀ r θ)) (Icc (-π) π) :=
    hf.comp (by unfold circleMap; fun_prop : Continuous (circleMap z₀ r)).continuousOn
      (fun θ _ ↦ hmem r hr θ)
  have heq (r : ℝ) (hr : r ∈ Icc a b) :
      (∫ θ in -π..π, r • f (circleMap z₀ r θ)) =
        r • ∫ θ in -π..π, f (circleMap z₀ r θ) :=
    (r • ContinuousLinearMap.id ℝ F).intervalIntegral_comp_comm
      (by
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -π ≤ π)] using hcont r hr)
  refine ContinuousOn.congr ?_ (fun r hr ↦ (heq r hr).symm)
  simp_rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]
  refine continuousOn_of_dominated (bound := fun _ ↦ b * C) (fun r hr ↦ ?_)
    (fun r hr ↦ ae_of_all _ fun θ ↦ ?_) (integrableOn_const (by simp))
    (ae_of_all _ fun θ ↦ ?_)
  · exact ((hcont r hr).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc |>.const_smul r
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha.trans hr.1)]
    exact mul_le_mul hr.2 (hC _ (hmem r hr θ)) (norm_nonneg _)
      (ha.trans (hr.1.trans hr.2))
  · exact continuous_id.continuousOn.smul
      (hf.comp (by simp only [circleMap]; fun_prop) (fun r hr ↦ hmem r hr θ))

variable [CompleteSpace F]

namespace MeasureTheory.IntegrableOn

/-- The radial derivative of a disc integral is its boundary density integral. The density
need only be continuous on the punctured disc and integrable on the whole disc, so the
formula does not assume a removable singularity at the centre. -/
theorem hasDerivAt_integral_ball {f : ℂ → F} {z₀ : ℂ} {R r : ℝ}
    (hint : IntegrableOn f (ball z₀ R))
    (hf : ContinuousOn f (ball z₀ R \ {z₀})) (hr : r ∈ Ioo 0 R) :
    HasDerivAt (fun t ↦ ∫ z in ball z₀ t, f z)
      (r • ∫ θ in -π..π, f (circleMap z₀ r θ)) r := by
  -- Work on an annulus containing the radius, where the boundary density is continuous.
  let a := r / 2
  let b := (r + R) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hr.1]
  have har : a < r := by dsimp [a]; linarith [hr.1]
  have hrb : r < b := by dsimp [b]; linarith [hr.2]
  have hbR : b < R := by dsimp [b]; linarith [hr.2]
  have hsub : {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} ⊆ ball z₀ R \ {z₀} := by
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm] using hz.2.trans_lt hbR
    · rintro rfl
      have : a ≤ 0 := by simpa using hz.1
      linarith
  let G (t : ℝ) := t • ∫ θ in -π..π, f (circleMap z₀ t θ)
  have hG : ContinuousOn G (Icc a b) :=
    (hf.mono hsub).smul_integral_comp_circleMap ha.le
  have hGc : ContinuousAt G r := hG.continuousAt (Icc_mem_nhds har hrb)
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Icc a b)) :=
    hG.aestronglyMeasurable measurableSet_Icc
  have hGr : IntervalIntegrable G volume a r :=
    (hG.mono (by rw [uIcc_of_le har.le]; exact Icc_subset_Icc le_rfl hrb.le)).intervalIntegrable
  have hd := intervalIntegral.integral_hasDerivAt_right hGr
    (_root_.AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hGmeas
      (Icc_mem_nhds har hrb)) hGc
  -- Locally the disc integral differs from this radial primitive by a fixed inner disc.
  have heq : (fun t ↦ ∫ z in ball z₀ t, f z) =ᶠ[𝓝 r]
      (fun t ↦ (∫ z in ball z₀ a, f z) + ∫ s in a..t, G s) := by
    filter_upwards [Ioo_mem_nhds har hrb] with t ht
    have hclosed := volume.addHaar_closedBall_ae_eq_ball z₀ t
    have hA : {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ t} = closedBall z₀ t \ ball z₀ a := by
      ext z
      simp only [mem_ofPred_eq, Set.mem_sdiff, mem_closedBall, mem_ball, dist_eq_norm, not_lt]
      exact and_comm
    have hpolar := TauCeti.integral_annulus_eq_integral_circleMap ha ht.1.le
      ((hf.mono hsub).mono (fun z hz ↦ ⟨hz.1, hz.2.trans ht.2.le⟩))
    rw [hA, setIntegral_congr_set (ae_eq_set_sdiff hclosed Filter.EventuallyEq.rfl),
      setIntegral_sdiff measurableSet_ball (hint.mono_set (ball_subset_ball
        (ht.2.trans hbR).le)) (ball_subset_ball ht.1.le)] at hpolar
    dsimp only [G]
    rw [← hpolar]
    abel
  exact (hd.const_add (∫ z in ball z₀ a, f z)).congr_of_eventuallyEq heq

end MeasureTheory.IntegrableOn
