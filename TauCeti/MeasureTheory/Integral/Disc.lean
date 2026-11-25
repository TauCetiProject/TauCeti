/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Topology.MetricSpace.Annulus
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial differentiation of disc integrals

For an integrable density on a disc, continuous away from its centre, the derivative of
its integral with respect to the radius is the boundary integral, parametrized by
`circleMap`. The density may have an integrable singularity at the centre. In particular,
this formula applies to finite energy on a punctured disc before an extension is known.

The same holds for the half-disc `{z | z₀.im ≤ z.im} ∩ ball z₀ r` about a point `z₀`, with the
boundary integral taken over the half-circle `θ ∈ [0, π]`
(`MeasureTheory.IntegrableOn.hasDerivAt_integral_inter_ball`). This is the radial energy
calculation at a boundary puncture, where the domain of a holomorphic curve is a half-disc about a
point of the real axis.

The annular polar formulas are `TauCeti.integral_annulus_eq_integral_circleMap` and
`TauCeti.integral_upperHalfAnnulus_eq_integral_circleMap`; the derivative uses the fundamental
theorem of calculus (`ContinuousOn.hasDerivAt_of_eq_add_integral`) on a compact annulus or
half-annulus around the radius, where the arc density integrals depend continuously on the radius
(`ContinuousOn.smul_integral_comp_circleMap_of_isCompact`). The target may be any real Banach space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (the radial energy calculation).
-/

public section

open Complex MeasureTheory Metric Set Filter
open scoped Real Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Arc density integrals of a density continuous on a compact set `A` depend continuously on the
radius, as long as the arcs `θ ↦ circleMap z₀ r θ`, `θ ∈ [α, β]`, of radii `r ∈ [a, b]` lie in
`A`. Continuity at the centre is not required when `A` avoids it. -/
theorem ContinuousOn.smul_integral_comp_circleMap_of_isCompact [CompleteSpace F]
    {f : ℂ → F} {z₀ : ℂ} {a b α β : ℝ} {A : Set ℂ} (hf : ContinuousOn f A) (hA : IsCompact A)
    (ha : 0 ≤ a) (hαβ : α ≤ β) (hmem : ∀ r ∈ Icc a b, ∀ θ ∈ Icc α β, circleMap z₀ r θ ∈ A) :
    ContinuousOn (fun r ↦ r • ∫ θ in α..β, f (circleMap z₀ r θ)) (Icc a b) := by
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hf
  have hcont (r : ℝ) (hr : r ∈ Icc a b) :
      ContinuousOn (fun θ ↦ f (circleMap z₀ r θ)) (Icc α β) :=
    hf.comp (by unfold circleMap; fun_prop : Continuous (circleMap z₀ r)).continuousOn
      (hmem r hr)
  have heq (r : ℝ) (hr : r ∈ Icc a b) :
      (∫ θ in α..β, r • f (circleMap z₀ r θ)) = r • ∫ θ in α..β, f (circleMap z₀ r θ) :=
    (r • ContinuousLinearMap.id ℝ F).intervalIntegral_comp_comm
      (by
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le hαβ] using hcont r hr)
  refine ContinuousOn.congr ?_ (fun r hr ↦ (heq r hr).symm)
  simp_rw [intervalIntegral.integral_of_le hαβ]
  refine continuousOn_of_dominated (bound := fun _ ↦ b * C) (fun r hr ↦ ?_)
    (fun r hr ↦ (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun θ hθ ↦ ?_))
    (integrableOn_const (by simp)) ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun θ hθ ↦ ?_))
  · exact ((hcont r hr).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc |>.const_smul r
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha.trans hr.1)]
    exact mul_le_mul hr.2 (hC _ (hmem r hr θ (Ioc_subset_Icc_self hθ))) (norm_nonneg _)
      (ha.trans (hr.1.trans hr.2))
  · exact continuous_id.continuousOn.smul
      (hf.comp (by simp only [circleMap]; fun_prop)
        (fun r hr ↦ hmem r hr θ (Ioc_subset_Icc_self hθ)))

/-- Boundary density integrals of a continuous density on a closed annulus depend continuously
on the radius. Continuity at the centre is not required. -/
theorem ContinuousOn.smul_integral_comp_circleMap [CompleteSpace F]
    {f : ℂ → F} {z₀ : ℂ} {a b : ℝ}
    (hf : ContinuousOn f {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}) (ha : 0 ≤ a) :
    ContinuousOn (fun r ↦ r • ∫ θ in -π..π, f (circleMap z₀ r θ)) (Icc a b) :=
  hf.smul_integral_comp_circleMap_of_isCompact (TauCeti.isCompact_setOf_le_norm_sub_le z₀ a b) ha
    (by linarith [Real.pi_pos]) fun r hr θ _ ↦ TauCeti.circleMap_mem_setOf_le_norm_sub_le ha hr θ

/-- Boundary density integrals over half-circles of a continuous density on the closed upper half
of an annulus depend continuously on the radius. Continuity at the centre is not required. -/
theorem ContinuousOn.smul_integral_comp_circleMap_zero_pi [CompleteSpace F]
    {f : ℂ → F} {z₀ : ℂ} {a b : ℝ}
    (hf : ContinuousOn f {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}) (ha : 0 ≤ a) :
    ContinuousOn (fun r ↦ r • ∫ θ in 0..π, f (circleMap z₀ r θ)) (Icc a b) :=
  hf.smul_integral_comp_circleMap_of_isCompact
    ((TauCeti.isCompact_setOf_le_norm_sub_le z₀ a b).of_isClosed_subset
      (TauCeti.isClosed_upperHalfAnnulus z₀ a b) fun _ hz ↦ hz.2)
    ha Real.pi_pos.le fun _ hr _ hθ ↦ TauCeti.circleMap_mem_upperHalfAnnulus ha hr hθ

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
  obtain ⟨a, ha, har⟩ := exists_between hr.1
  obtain ⟨b, hrb, hbR⟩ := exists_between hr.2
  have hsub : {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} ⊆ ball z₀ R \ {z₀} :=
    TauCeti.setOf_le_norm_sub_le_subset_ball_sdiff_singleton ha hbR
  refine ((hf.mono hsub).smul_integral_comp_circleMap ha.le).hasDerivAt_of_eq_add_integral
    ⟨har, hrb⟩ fun t ht ↦ ?_
  -- The disc integral differs from the radial primitive by the fixed inner disc.
  have hclosed := volume.addHaar_closedBall_ae_eq_ball z₀ t
  have hA : {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ t} = closedBall z₀ t \ ball z₀ a := by
    ext z
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_closedBall, mem_ball, dist_eq_norm, not_lt]
    exact and_comm
  have hpolar := TauCeti.integral_annulus_eq_integral_circleMap ha.le ht.1.le
    (hint.mono_set fun z hz ↦ (hsub ⟨hz.1, hz.2.trans ht.2.le⟩).1)
  rw [hA, setIntegral_congr_set (ae_eq_set_sdiff hclosed Filter.EventuallyEqSet.rfl),
    setIntegral_sdiff measurableSet_ball (hint.mono_set (ball_subset_ball
      (ht.2.trans hbR).le)) (ball_subset_ball ht.1.le)] at hpolar
  rw [← hpolar]
  abel

/-- The radial derivative of a half-disc integral is its boundary density integral over the
half-circle. Here the half-disc of radius `t` about `z₀` is `{z | z₀.im ≤ z.im} ∩ ball z₀ t`. The
density need only be continuous on the punctured half-disc and integrable on the whole half-disc,
so the formula does not assume a removable singularity at the centre. -/
theorem hasDerivAt_integral_inter_ball {f : ℂ → F} {z₀ : ℂ} {R r : ℝ}
    (hint : IntegrableOn f ({z | z₀.im ≤ z.im} ∩ ball z₀ R))
    (hf : ContinuousOn f ({z | z₀.im ≤ z.im} ∩ (ball z₀ R \ {z₀}))) (hr : r ∈ Ioo 0 R) :
    HasDerivAt (fun t ↦ ∫ z in {z | z₀.im ≤ z.im} ∩ ball z₀ t, f z)
      (r • ∫ θ in 0..π, f (circleMap z₀ r θ)) r := by
  set H : Set ℂ := {z | z₀.im ≤ z.im}
  have hH : MeasurableSet H := (isClosed_le continuous_const Complex.continuous_im).measurableSet
  -- Work on a half-annulus containing the radius, where the boundary density is continuous.
  obtain ⟨a, ha, har⟩ := exists_between hr.1
  obtain ⟨b, hrb, hbR⟩ := exists_between hr.2
  have hsub : {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} ⊆ H ∩ (ball z₀ R \ {z₀}) :=
    fun _ hz ↦ ⟨hz.1, TauCeti.setOf_le_norm_sub_le_subset_ball_sdiff_singleton ha hbR hz.2⟩
  refine ((hf.mono hsub).smul_integral_comp_circleMap_zero_pi ha.le).hasDerivAt_of_eq_add_integral
    ⟨har, hrb⟩ fun t ht ↦ ?_
  -- The half-disc integral differs from the radial primitive by the fixed inner half-disc.
  have hclosed : H ∩ closedBall z₀ t =ᵐ[volume] H ∩ ball z₀ t :=
    Filter.EventuallyEqSet.rfl.inter (volume.addHaar_closedBall_ae_eq_ball z₀ t)
  have hA : {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ t} =
      (H ∩ closedBall z₀ t) \ (H ∩ ball z₀ a) := by
    ext z
    simp only [H, mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff, mem_closedBall, mem_ball,
      dist_eq_norm, not_and, not_lt]
    tauto
  have hpolar := TauCeti.integral_upperHalfAnnulus_eq_integral_circleMap ha.le ht.1.le
    (hint.mono_set fun z hz ↦ ⟨(hsub ⟨hz.1, hz.2.1, hz.2.2.trans ht.2.le⟩).1,
      (hsub ⟨hz.1, hz.2.1, hz.2.2.trans ht.2.le⟩).2.1⟩)
  rw [hA, setIntegral_congr_set (ae_eq_set_sdiff hclosed Filter.EventuallyEqSet.rfl),
    setIntegral_sdiff (hH.inter measurableSet_ball) (hint.mono_set (inter_subset_inter_right _
      (ball_subset_ball (ht.2.trans hbR).le)))
      (inter_subset_inter_right _ (ball_subset_ball ht.1.le))] at hpolar
  rw [← hpolar]
  abel

end MeasureTheory.IntegrableOn
