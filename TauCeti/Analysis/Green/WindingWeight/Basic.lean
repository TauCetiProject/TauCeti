/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.UnboundedComponent
public import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Contour.Winding.Continuity
import TauCeti.Analysis.Complex.CauchyKernel
import TauCeti.MeasureTheory.Integral.KernelPotential
import TauCeti.MeasureTheory.Integral.NormRpow
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Winding weights of planar curves

The area weight is the real part of the existing contour winding number off the trace and zero on
the trace. This convention makes the weight independent of any principal-value interpretation on
the trace. For a closed absolutely continuous curve it is measurable, compactly supported, and
area-integrable. The integrability proof dominates the weight by the inverse-distance potential
of the curve's integrable speed; the planar inverse-distance kernel is locally integrable.

-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped Topology

namespace TauCeti.Green

open scoped Classical in
/-- The real winding weight, set to zero on the curve trace. -/
def windingWeight (γ : ℝ → ℂ) (a b : ℝ) (z : ℂ) : ℝ :=
  if z ∈ γ '' uIcc a b then 0 else (Contour.windingNumber γ a b z).re

variable {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}

/-- On the trace the area weight is zero. -/
theorem windingWeight_eq_zero_of_mem (hz : z ∈ γ '' uIcc a b) :
    windingWeight γ a b z = 0 := by simp [windingWeight, hz]

/-- Off the trace the area weight is the real part of the existing winding number. -/
theorem windingWeight_eq_of_notMem (hz : z ∉ γ '' uIcc a b) :
    windingWeight γ a b z = (Contour.windingNumber γ a b z).re := by simp [windingWeight, hz]

/-- A constant curve has zero winding weight everywhere. -/
@[simp]
theorem windingWeight_const (w : ℂ) (a b : ℝ) (z : ℂ) :
    windingWeight (fun _ : ℝ ↦ w) a b z = 0 := by
  simp [windingWeight]

/-- The winding weight is constant on a neighborhood of any point off the trace of a closed
absolutely continuous curve. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingWeight_eventuallyEq_of_notMem
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hz : z ∉ γ '' uIcc a b) :
    windingWeight γ a b =ᶠ[nhds z] fun _ ↦ windingWeight γ a b z := by
  have hK := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  have hc := AbsolutelyContinuousOnInterval.isLocallyConstant_windingNumber
    hγ hclosed
  have hopen : IsOpen ((Subtype.val : ↥((γ '' uIcc a b)ᶜ) → ℂ) ''
      {w | Contour.windingNumber γ a b w.1 = Contour.windingNumber γ a b z}) :=
    hK.isClosed.isOpen_compl.isOpenMap_subtype_val _ (hc.isOpen_fiber _)
  have hmem : z ∈ (Subtype.val : ↥((γ '' uIcc a b)ᶜ) → ℂ) ''
      {w | Contour.windingNumber γ a b w.1 = Contour.windingNumber γ a b z} :=
    ⟨⟨z, hz⟩, rfl, rfl⟩
  filter_upwards [hopen.mem_nhds hmem] with w hw
  obtain ⟨w, hw, rfl⟩ := hw
  rw [windingWeight_eq_of_notMem w.2, hw, windingWeight_eq_of_notMem hz]

/-- The winding weight of an absolutely continuous curve is measurable. -/
theorem _root_.AbsolutelyContinuousOnInterval.measurable_windingWeight
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    Measurable (windingWeight γ a b) := by
  classical
  have hK : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  have hcont : ContinuousOn (fun z : ℂ ↦ (Contour.windingNumber γ a b z).re)
      (γ '' uIcc a b)ᶜ := by
    intro z hz
    exact Complex.continuous_re.continuousAt.comp
      (Contour.continuousAt_windingNumber_of_avoidance hγ.continuousOn
        (fun t ht heq ↦ hz ⟨t, ht, heq⟩)
        (hγ.intervalIntegrable_inv_sub_mul_deriv hz))
      |>.continuousWithinAt
  exact continuousOn_const.measurable_piecewise hcont hK.measurableSet

/-- Every value of a closed absolutely continuous curve's winding weight is an integer. -/
theorem _root_.AbsolutelyContinuousOnInterval.exists_int_windingWeight
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (z : ℂ) : ∃ n : ℤ, windingWeight γ a b z = n := by
  by_cases hz : z ∈ γ '' uIcc a b
  · exact ⟨0, by rw [windingWeight_eq_zero_of_mem hz]; simp⟩
  obtain ⟨n, hn⟩ := AbsolutelyContinuousOnInterval.exists_int_windingNumber
    hγ hclosed hz
  exact ⟨n, by rw [windingWeight_eq_of_notMem hz, hn]; simp⟩

/-- The winding weight vanishes outside the filled hull of the trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingWeight_eq_zero_of_notMem_filledHull
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hz : z ∉ filledHull (γ '' uIcc a b)) :
    windingWeight γ a b z = 0 := by
  have hzK : z ∉ γ '' uIcc a b := fun h ↦ hz (subset_filledHull h)
  rw [windingWeight_eq_of_notMem hzK,
    AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component
      hγ hclosed (fun h ↦ hz (mem_filledHull_iff.mpr h)), Complex.zero_re]

/-- Index one throughout the bounded complementary region makes the winding weight its indicator. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingWeight_eq_indicator_of_index_one
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hindex : ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      Contour.windingNumber γ a b z = 1) :
    windingWeight γ a b =
      (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  ext z
  by_cases hz : z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)
  · rw [indicator_of_mem hz, windingWeight_eq_of_notMem hz.2, hindex z hz]
    exact Complex.one_re
  · rw [indicator_of_notMem hz]
    by_cases ht : z ∈ γ '' uIcc a b
    · exact windingWeight_eq_zero_of_mem ht
    · exact hγ.windingWeight_eq_zero_of_notMem_filledHull hclosed
        (fun h ↦ hz ⟨h, ht⟩)

/-- The support of the winding weight lies in the intrinsic planar inside. -/
theorem _root_.AbsolutelyContinuousOnInterval.support_windingWeight_subset
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) :
    Function.support (windingWeight γ a b) ⊆ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) := by
  intro z hz
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hz (hγ.windingWeight_eq_zero_of_notMem_filledHull hclosed h)
  · intro h
    exact hz (windingWeight_eq_zero_of_mem h)

/-- A ball containing a closed absolutely continuous curve also contains its winding support. -/
theorem _root_.AbsolutelyContinuousOnInterval.support_windingWeight_subset_closedBall
    {c : ℂ} {R : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hR : ∀ t ∈ uIcc a b, γ t ∈ closedBall c R) :
    Function.support (windingWeight γ a b) ⊆ closedBall c R :=
  ((hγ.support_windingWeight_subset hclosed).trans sdiff_subset).trans
    ((filledHull_subset_closedConvexHull (K := γ '' uIcc a b)
        ⟨γ a, a, left_mem_uIcc, rfl⟩).trans
      (closedConvexHull_min (by rintro _ ⟨t, ht, rfl⟩; exact hR t ht)
        (convex_closedBall c R) isClosed_closedBall))

/-- The winding weight of a closed absolutely continuous curve has compact support. -/
theorem _root_.AbsolutelyContinuousOnInterval.hasCompactSupport_windingWeight
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) : HasCompactSupport (windingWeight γ a b) := by
  have hK : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  have hH : IsCompact (filledHull (γ '' uIcc a b)) :=
    Metric.isCompact_of_isClosed_isBounded (IsClosed.isClosed_filledHull hK.isClosed)
      (isBounded_filledHull.mpr hK.isBounded)
  exact HasCompactSupport.of_support_subset_isCompact hH
    ((hγ.support_windingWeight_subset hclosed).trans sdiff_subset)

/-- Integrating translated integrable kernels against the speed gives an integrable potential. -/
private theorem integrable_speedPotential (hγ : AbsolutelyContinuousOnInterval γ a b)
    {k : ℂ → ℝ} (hk : Integrable k) (hkm : Measurable k) :
    Integrable (fun z : ℂ ↦ ∫ t in uIoc a b, k (z - γ t) * ‖deriv γ t‖) :=
  (hk.integrable_prod_comp_sub_mul hkm
    ((hγ.continuousOn.mono uIoc_subset_uIcc).aemeasurable measurableSet_uIoc)
    hγ.intervalIntegrable_deriv_of_finiteDimensional.def'.norm).integral_prod_right

/-- The winding weight of a closed absolutely continuous planar curve is area-integrable.
The proof dominates it by an integrable inverse-distance potential of the curve's speed. -/
theorem _root_.AbsolutelyContinuousOnInterval.integrable_windingWeight
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) : Integrable (windingWeight γ a b) := by
  have hK : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  obtain ⟨R, -, hR⟩ :=
    (isBounded_filledHull.mpr hK.isBounded).exists_pos_norm_lt
  let k : ℂ → ℝ := (Metric.closedBall 0 (2 * R)).indicator (fun z ↦ ‖z‖⁻¹)
  have hkm : Measurable k := measurable_id.norm.inv.indicator isClosed_closedBall.measurableSet
  have hk : Integrable k :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (by simpa only [Real.rpow_neg_one, zero_sub, norm_neg] using
        (TauCeti.locallyIntegrable_norm_sub_rpow (mu := volume)
          (s := -1) (by simp [Complex.finrank_real_complex]) (0 : ℂ)).integrableOn_isCompact
            (isCompact_closedBall (0 : ℂ) (2 * R)))
  let F : ℂ → ℝ := fun z ↦ ∫ t in uIoc a b, k (z - γ t) * ‖deriv γ t‖
  have hF : Integrable F := integrable_speedPotential hγ hk hkm
  have hkpos : ∀ z, 0 ≤ k z := by
    intro z
    exact Set.indicator_nonneg (fun _ _ ↦ inv_nonneg.mpr (norm_nonneg _)) z
  have hFpos : ∀ z, 0 ≤ F z := fun z ↦
    integral_nonneg fun t ↦ mul_nonneg (hkpos _) (norm_nonneg _)
  let C := ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖
  apply (hF.const_mul C).mono' (hγ.measurable_windingWeight).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  by_cases hzK : z ∈ γ '' uIcc a b
  · rw [windingWeight_eq_zero_of_mem hzK, norm_zero]
    exact mul_nonneg (norm_nonneg _) (hFpos z)
  by_cases hzH : z ∈ filledHull (γ '' uIcc a b)
  · have heq : (∫ t in uIoc a b, ‖(γ t - z)⁻¹ * deriv γ t‖) = F z := by
      apply setIntegral_congr_fun measurableSet_uIoc
      intro t ht
      have hγR := hR (γ t) (subset_filledHull ⟨t, uIoc_subset_uIcc ht, rfl⟩)
      have hzR := hR z hzH
      have hball : z - γ t ∈ Metric.closedBall 0 (2 * R) :=
        mem_closedBall_zero_iff.mpr
          ((norm_sub_le z (γ t)).trans (by linarith))
      simp only [k, Set.indicator_of_mem hball, norm_mul, norm_inv, norm_sub_rev]
    calc
      ‖windingWeight γ a b z‖ = |(Contour.windingNumber γ a b z).re| := by
        rw [windingWeight_eq_of_notMem hzK, Real.norm_eq_abs]
      _ ≤ ‖Contour.windingNumber γ a b z‖ := Complex.abs_re_le_norm _
      _ = C * ‖∫ t in a..b, (γ t - z)⁻¹ * deriv γ t‖ := by
        rw [hγ.windingNumber_eq_integral hzK, norm_mul]
      _ ≤ C * (∫ t in uIoc a b, ‖(γ t - z)⁻¹ * deriv γ t‖) :=
        mul_le_mul_of_nonneg_left intervalIntegral.norm_integral_le_integral_norm_uIoc
          (norm_nonneg _)
      _ = C * F z := congrArg (C * ·) heq
  · rw [hγ.windingWeight_eq_zero_of_notMem_filledHull hclosed hzH, norm_zero]
    exact mul_nonneg (norm_nonneg _) (hFpos z)

end TauCeti.Green
