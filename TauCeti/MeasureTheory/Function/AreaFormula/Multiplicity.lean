/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import TauCeti.MeasureTheory.Function.Jacobian.Decomposition
import TauCeti.Topology.Algebra.InfiniteSum.Extend
import TauCeti.MeasureTheory.Function.AreaFormula.Integral
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# The area formula with multiplicity

The weighted area formula integrates the geometric Jacobian on the parameter space and
sums the weights over each fiber in the target. Fiber sums take values in `ℝ≥0∞`:
in particular an infinite fiber has infinite multiplicity, not multiplicity zero.
The target measure is normalized Euclidean Hausdorff measure.

We sum the injective area formula over measurable bi-Lipschitz pieces of the regular
locus. The remaining points have null image, by Rademacher's theorem and the null-image
result for zero Jacobians.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.3 (the area formula).
-/

public section

open Set Function MeasureTheory Measure Module
open scoped NNReal ENNReal symmDiff

namespace TauCeti

/-- Weighted fiber sums for a map with injective derivative are measurable. Such a map
need not itself be injective or globally Lipschitz. -/
theorem measurable_tsum_fiber_of_injective_fderiv
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [SecondCountableTopology V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {g : U → ℝ≥0∞}
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hg : Measurable g) :
    Measurable (fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), g x) := by
  classical
  obtain ⟨p, L, K, hpm, hpd, hcover, hp⟩ :=
    exists_partition_lipschitz_antilipschitz_of_hasFDerivWithinAt hs
      (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt) hinj
  have he (n : ℕ) : MeasurableEmbedding ((p n).domRestrict f) :=
    ContinuousOn.measurableEmbedding (hpm n)
      (continuousOn_iff_continuous_domRestrict.2 (hp n).1.continuous)
      (fun x hx y hy hxy ↦ congrArg Subtype.val
        ((hp n).2.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
  have hsum (n : ℕ) (y : V) : (∑' x : ↥(p n ∩ f ⁻¹' {y}), g x) =
      extend ((p n).domRestrict f) (fun x ↦ g x) 0 y := by
    let e : ↥(p n ∩ f ⁻¹' {y}) ≃ ((p n).domRestrict f ⁻¹' {y}) :=
      { toFun := fun x ↦ ⟨⟨x, x.property.1⟩, x.property.2⟩
        invFun := fun x ↦ ⟨x.val.val, x.val.property, x.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact (e.tsum_eq (fun x ↦ g x.val.val)).trans
      ((he n).injective.tsum_fiber_eq_extend (fun x ↦ g x) y)
  have hfiber (y : V) : (∑' x : ↥(s ∩ f ⁻¹' {y}), g x) =
      ∑' n, extend ((p n).domRestrict f) (fun x ↦ g x) 0 y := by
    rw [← hcover, iUnion_inter, ENNReal.tsum_iUnion]
    · exact tsum_congr fun n ↦ hsum n y
    · intro i _ j _ hij
      exact (hpd hij).mono inter_subset_left inter_subset_left
  simp_rw [hfiber]
  exact Measurable.tsum fun n ↦
    (he n).measurable_extend (hg.comp measurable_subtype_coe) measurable_const

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {g : U → ℝ≥0∞}

/-- The weighted area formula on a measurable set of points with injective derivative,
without any injectivity assumption on the parametrization itself. -/
theorem lintegral_normDet_fderiv_mul_eq_lintegral_tsum_of_injective_fderiv
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hg : Measurable g) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * g x =
      ∫⁻ y, ∑' x : ↥(s ∩ f ⁻¹' {y}), g x ∂μHE[finrank ℝ U] := by
  classical
  obtain ⟨p, L, K, hpm, hpd, hcover, hp⟩ :=
    exists_partition_lipschitz_antilipschitz_of_hasFDerivWithinAt hs
      (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt) hinj
  have hps (n : ℕ) : p n ⊆ s := by rw [← hcover]; exact subset_iUnion p n
  have hpi (n : ℕ) : InjOn f (p n) := fun x hx y hy hxy ↦
    congrArg Subtype.val ((hp n).2.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hmeas (n : ℕ) : Measurable (fun y ↦ ∑' x : ↥(p n ∩ f ⁻¹' {y}), g x) :=
    measurable_tsum_fiber_of_injective_fderiv (hpm n)
      (fun x hx ↦ hd x (hps n hx)) (fun x hx ↦ hinj x (hps n hx)) hg
  have hpiece (n : ℕ) :
      (∫⁻ x in p n, ENNReal.ofReal (fderiv ℝ f x).normDet * g x) =
        ∫⁻ y, ∑' x : ↥(p n ∩ f ⁻¹' {y}), g x ∂μHE[finrank ℝ U] := by
    have hvalue (x : U) (hx : x ∈ p n) :
        (∑' z : ↥(p n ∩ f ⁻¹' {f x}), g z) = g x := by
      exact tsum_eq_single (⟨x, hx, rfl⟩ : ↥(p n ∩ f ⁻¹' {f x})) fun z hz ↦ by
        exfalso
        exact hz (Subtype.ext (hpi n z.property.1 hx z.property.2))
    have hsupp : (fun y ↦ ∑' x : ↥(p n ∩ f ⁻¹' {y}), g x).support ⊆ f '' p n := by
      intro y hy
      by_contra h
      have : IsEmpty ↥(p n ∩ f ⁻¹' {y}) :=
        ⟨fun x ↦ h ⟨x, x.property.1, x.property.2⟩⟩
      exact hy tsum_empty
    rw [← setLIntegral_eq_of_support_subset hsupp,
      lintegral_image_eq_lintegral_normDet_fderiv_mul (hpm n)
        (fun x hx ↦ hd x (hps n hx)) (fun x hx ↦ hinj x (hps n hx)) (hpi n)]
    exact setLIntegral_congr_fun (hpm n) fun x hx ↦ by rw [hvalue x hx]
  rw [← hcover, lintegral_iUnion hpm hpd]
  simp_rw [hpiece]
  rw [← lintegral_tsum (fun n ↦ (hmeas n).aemeasurable)]
  apply lintegral_congr
  intro y
  rw [iUnion_inter, ENNReal.tsum_iUnion]
  intro i _ j _ hij
  exact (hpd hij).mono inter_subset_left inter_subset_left

/-- Restricting the parameters of a Lipschitz map to its differentiability points with
nonzero Jacobian preserves weighted fiber sums almost everywhere for normalized Hausdorff
measure. Neither the parameter set nor the weight needs to be measurable. -/
theorem tsum_fiber_inter_setOf_regular_ae_eq (s : Set U) (g : U → ℝ≥0∞)
    {K : ℝ≥0} (hf : LipschitzWith K f) :
    (fun y ↦ ∑' x : ↥((s ∩ {x | DifferentiableAt ℝ f x ∧
      (fderiv ℝ f x).normDet ≠ 0}) ∩ f ⁻¹' {y}), g x) =ᵐ[μHE[finrank ℝ U]]
      fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), g x := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    hf.euclideanHausdorffMeasure_image_compl_setOf_regular] with y hy
  apply tsum_congr_set_coe g
  ext x
  have hx : f x = y → DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0 :=
    fun h ↦ not_not.1 fun hx ↦ hy ⟨x, hx, h⟩
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  aesop

end TauCeti

namespace LipschitzWith

open TauCeti

/-- Changing the parameter set on a Lebesgue-null set changes its weighted fiber sums
only on a Hausdorff-null set. No measurability of the weight or the sets is needed. -/
theorem tsum_fiber_congr_ae
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [EMetricSpace V] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {K : ℝ≥0} (hf : LipschitzWith K f) {s t : Set U}
    (hst : s =ᵐ[volume] t) (g : U → ℝ≥0∞) :
    (fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), g x) =ᵐ[μHE[finrank ℝ U]]
      fun y ↦ ∑' x : ↥(t ∩ f ⁻¹' {y}), g x := by
  have hnull : μHE[finrank ℝ U] (f '' (s ∆ t)) = 0 := by
    have hzero := measure_symmDiff_eq_zero_iff.mpr hst
    have hle := hf.lipschitzOnWith.euclideanHausdorffMeasure_image_le (s := s ∆ t)
      (finrank ℝ U)
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, hzero, mul_zero,
      nonpos_iff_eq_zero] using hle
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  apply tsum_congr_set_coe g
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  have hx : f x = y → (x ∈ s ↔ x ∈ t) := by
    intro hxy
    have hnot : x ∉ s ∆ t := fun hx ↦ hy ⟨x, hx, hxy⟩
    simpa only [mem_symmDiff, not_or, not_and, not_not, iff_def] using hnot
  aesop

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {g : U → ℝ≥0∞} {K : ℝ≥0}

/-- Weighted fiber sums of a Lipschitz map on a Lebesgue-measurable set are almost
everywhere measurable for normalized Hausdorff measure, including infinite fibers. -/
theorem aemeasurable_tsum_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume)
    (hg : Measurable g) :
    AEMeasurable (fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), g x) μHE[finrank ℝ U] := by
  let t := toMeasurable volume s
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  suffices h : AEMeasurable (fun y ↦ ∑' x : ↥(t ∩ f ⁻¹' {y}), g x)
      μHE[finrank ℝ U] from
    h.congr (hf.tsum_fiber_congr_ae hs.toMeasurable_ae_eq g)
  let G := {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}
  have hG : MeasurableSet G := (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ f)) measurable_const).compl
  have hinj (x : U) (hx : x ∈ G) : Injective (fderiv ℝ f x) :=
    LinearMap.ker_eq_bot.1
      (not_not.1 fun h ↦ hx.2 (LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 h))
  exact (measurable_tsum_fiber_of_injective_fderiv (ht.inter hG)
    (fun x hx ↦ hx.2.1) (fun x hx ↦ hinj x hx.2) hg).aemeasurable.congr
      (tsum_fiber_inter_setOf_regular_ae_eq t g hf)

/-- **The weighted area formula with multiplicity.** Integrating the geometric Jacobian
of a Lipschitz map against a nonnegative measurable weight equals the normalized Hausdorff
integral of the sum of the weights over each fiber. The parameter set may be Lebesgue
measurable rather than Borel, and infinite fibers use extended sums. -/
theorem lintegral_normDet_fderiv_mul_eq_lintegral_tsum (hf : LipschitzWith K f)
    (hs : NullMeasurableSet s volume) (hg : Measurable g) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * g x =
      ∫⁻ y, ∑' x : ↥(s ∩ f ⁻¹' {y}), g x ∂μHE[finrank ℝ U] := by
  let t := toMeasurable volume s
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  suffices h : (∫⁻ x in t, ENNReal.ofReal (fderiv ℝ f x).normDet * g x) =
      ∫⁻ y, ∑' x : ↥(t ∩ f ⁻¹' {y}), g x ∂μHE[finrank ℝ U] from
    (setLIntegral_congr hs.toMeasurable_ae_eq.symm).trans
      (h.trans (lintegral_congr_ae (hf.tsum_fiber_congr_ae hs.toMeasurable_ae_eq g)))
  let G := {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}
  have hG : MeasurableSet G := (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ f)) measurable_const).compl
  have hzero : ∫⁻ x in t \ G, ENNReal.ofReal (fderiv ℝ f x).normDet * g x = 0 := by
    refine (setLIntegral_congr_fun_ae (ht.diff hG) ?_).trans lintegral_zero
    filter_upwards [hf.ae_differentiableAt] with x hx hxs
    rw [not_not.1 fun h ↦ hxs.2 ⟨hx, h⟩, ENNReal.ofReal_zero, zero_mul]
  rw [← lintegral_inter_add_sdiff _ t hG, hzero, add_zero,
    lintegral_normDet_fderiv_mul_eq_lintegral_tsum_of_injective_fderiv (ht.inter hG)
      (fun x hx ↦ hx.2.1) (fun x hx ↦ ?_) hg]
  · exact lintegral_congr_ae (tsum_fiber_inter_setOf_regular_ae_eq t g hf)
  · exact LinearMap.ker_eq_bot.1
      (not_not.1 fun h ↦ hx.2.2 (LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 h))

/-- The unweighted area formula: multiplicity is the extended cardinality of the fiber,
so infinite fibers are counted as infinity. -/
theorem lintegral_normDet_fderiv_eq_lintegral_encard (hf : LipschitzWith K f)
    (hs : NullMeasurableSet s volume) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet =
      ∫⁻ y, ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[finrank ℝ U] := by
  simpa only [mul_one, ENNReal.tsum_set_one] using
    hf.lintegral_normDet_fderiv_mul_eq_lintegral_tsum hs (g := fun _ ↦ 1) measurable_const

end LipschitzWith
