/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.Analysis.Calculus.Deriv.CountableLevels
import TauCeti.MeasureTheory.Function.Gluing
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Locality of weak derivatives on equality sets in one dimension

For functions on an open subset of the real line, weak derivatives agree almost everywhere
where the functions agree, for any additive Haar measure. In particular, a weak derivative
vanishes almost everywhere on the preimage of any countable set of values. Weak directional
derivatives can be taken in any real direction. Neither continuity of the given representatives
nor measurability of their equality set is required. The codomain can be any real Banach
space; no finite-dimensionality or Radon–Nikodým assumption is used.

The interval fundamental theorem supplies continuous representatives with the prescribed
classical derivative almost everywhere. The classical level-set result in
`TauCeti.Analysis.Calculus.Deriv.CountableLevels` then applies. Localizing to compact intervals
inside the open domain removes any global integrability requirement. This is the
one-dimensional locality statement used in slicing arguments for weak derivatives.

## References

* G. Leoni, *A First Course in Sobolev Spaces*, the absolute-continuity characterization of
  one-dimensional Sobolev functions and locality of weak derivatives.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens ℝ} {u v u' v' : ℝ → F}

/-- On an interval with integrable weak derivative, the derivative vanishes almost everywhere
on the preimage of a countable set of values, even for a discontinuous representative. -/
private theorem HasWeakLineDerivOn.ae_eq_zero_on_preimage_Ioo {a b : ℝ}
    (hu : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo a b)) {C : Set F} (hC : C.Countable) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), u t ∈ C → u' t = 0 := by
  rcases le_or_gt b a with hba | hab
  · simp [Ioo_eq_empty_of_le hba]
  obtain ⟨w, hw, huw⟩ := hu.exists_continuousOn_ae_eq hu'
  have hd := hu.ae_hasDerivAt (hw.mono Ioo_subset_Icc_self) huw hab.le
  filter_upwards [huw, ae_restrict_of_ae hd,
    ae_restrict_of_ae (hC.ae_deriv_eq_zero_on_preimage w volume),
    ae_restrict_mem measurableSet_Ioo] with t ht hdt hCt htI hval
  have hderiv := hdt (uIoc_of_le hab.le ▸ Ioo_subset_Ioc_self htI)
  exact hderiv.deriv.symm.trans (hCt (ht ▸ hval))

/-- Localize countable-preimage vanishing for direction `1` and Lebesgue measure to intervals
whose closures are contained in the domain. -/
private theorem HasWeakLineDerivOn.ae_eq_zero_on_preimage_volume_one
    (hu : HasWeakLineDerivOn volume Ω u u' 1) {C : Set F} (hC : C.Countable) :
    ∀ᵐ t ∂volume.restrict Ω, u t ∈ C → u' t = 0 := by
  refine ae_restrict_of_subset_iUnion_isOpen
    (t := fun p : {p : ℝ × ℝ // Icc p.1 p.2 ⊆ Ω} ↦ Ioo p.1.1 p.1.2)
    (fun _ ↦ isOpen_Ioo) ?_ ?_
  · intro x hx
    obtain ⟨a, b, -, hIx, hI⟩ := exists_Icc_mem_subset_of_mem_nhds (Ω.isOpen.mem_nhds hx)
    apply mem_iUnion.2 ⟨⟨(a, b), hI⟩, ?_⟩
    simpa only [interior_Icc] using mem_interior_iff_mem_nhds.2 hIx
  · rintro ⟨⟨a, b⟩, hI⟩
    have hsub : Ioo a b ⊆ Ω := Ioo_subset_Icc_self.trans hI
    have huint := hu.locallyIntegrableOn_deriv.integrableOn_compact_subset hI isCompact_Icc
    exact (hu.mono (Ω' := ⟨Ioo a b, isOpen_Ioo⟩) hsub).ae_eq_zero_on_preimage_Ioo
      (huint.mono_set Ioo_subset_Icc_self) hC

variable {μ : Measure ℝ} [μ.IsAddHaarMeasure] {d : ℝ}

/-- A weak directional derivative on an open subset of the real line vanishes almost everywhere
on the preimage of any countable set. The exceptional set may depend on that set of values. -/
theorem HasWeakLineDerivOn.ae_eq_zero_on_preimage_real
    (hu : HasWeakLineDerivOn μ Ω u u' d) {C : Set F} (hC : C.Countable) :
    ∀ᵐ t ∂μ.restrict Ω, u t ∈ C → u' t = 0 := by
  by_cases hd : d = 0
  · subst d
    have := hu.completeSpace
    filter_upwards [hu.ae_eq (hasWeakLineDerivOn_zero_direction hu.locallyIntegrableOn)] with t ht
    exact fun _ ↦ ht
  -- Rescaling the Haar measure multiplies both sides of the test function identity equally.
  have huvol : HasWeakLineDerivOn volume Ω u u' d :=
    hasWeakLineDerivOn_iff_testFunction.2 ⟨hu.completeSpace,
      hu.locallyIntegrableOn.of_isAddHaarMeasure volume,
      hu.locallyIntegrableOn_deriv.of_isAddHaarMeasure volume, fun φ ↦ by
        rw [Measure.isAddLeftInvariant_eq_smul (volume : Measure ℝ) μ]
        simp only [integral_smul_nnreal_measure,
          hu.integral_lineDeriv_smul_eq_neg_integral_smul φ, smul_neg]⟩
  have hunit : HasWeakLineDerivOn volume Ω u (d⁻¹ • u') 1 := by
    simpa only [smul_eq_mul, inv_mul_cancel₀ hd] using huvol.smul_direction d⁻¹
  have hμ := (Measure.absolutelyContinuous_isAddHaarMeasure μ volume).restrict (Ω : Set ℝ)
  filter_upwards [hμ.ae_le (hunit.ae_eq_zero_on_preimage_volume_one hC)] with t ht hval
  exact (smul_eq_zero.mp (ht hval)).resolve_left (inv_ne_zero hd)

/-- Weak directional derivatives on an open subset of the real line agree almost everywhere
where the original functions agree. The equality set need not be open or measurable. -/
theorem HasWeakLineDerivOn.ae_eq_on_eq_real
    (hu : HasWeakLineDerivOn μ Ω u u' d) (hv : HasWeakLineDerivOn μ Ω v v' d) :
    ∀ᵐ t ∂μ.restrict Ω, u t = v t → u' t = v' t := by
  have hzero := (hu.sub hv).ae_eq_zero_on_preimage_real (countable_singleton (0 : F))
  filter_upwards [hzero] with t ht heq
  exact sub_eq_zero.mp (ht (by simp [heq]))

/-- For a real source, a weak Fréchet derivative vanishes almost everywhere on the preimage
of any countable set. The exceptional set may depend on that set of values. -/
theorem HasWeakFDerivOn.ae_eq_zero_on_preimage_real {Du : ℝ → ℝ →L[ℝ] F}
    (hu : HasWeakFDerivOn μ Ω u Du) {C : Set F} (hC : C.Countable) :
    ∀ᵐ t ∂μ.restrict Ω, u t ∈ C → Du t = 0 := by
  filter_upwards [(hu.hasWeakLineDerivOn 1).ae_eq_zero_on_preimage_real hC] with t ht hval
  exact ContinuousLinearMap.ext_ring (by simpa only [zero_apply] using ht hval)

/-- For a real source, weak Fréchet derivatives agree almost everywhere on the equality set
of the functions. The equality set need not be open or measurable. -/
theorem HasWeakFDerivOn.ae_eq_on_eq_real {Du Dv : ℝ → ℝ →L[ℝ] F}
    (hu : HasWeakFDerivOn μ Ω u Du) (hv : HasWeakFDerivOn μ Ω v Dv) :
    ∀ᵐ t ∂μ.restrict Ω, u t = v t → Du t = Dv t := by
  have hzero := (hu.sub hv).ae_eq_zero_on_preimage_real (countable_singleton (0 : F))
  filter_upwards [hzero] with t ht heq
  exact sub_eq_zero.mp (ht (by simp [heq]))

end TauCeti
