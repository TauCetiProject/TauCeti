/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.Analysis.Calculus.Deriv.CountableLevels

/-!
# Locality of weak derivatives on equality sets in one dimension

For functions on an open subset of the real line, weak derivatives agree almost everywhere
where the functions agree. In particular, a weak derivative vanishes almost everywhere on
the preimage of any countable set of values. Neither continuity of the given representatives
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

open MeasureTheory Set Filter TopologicalSpace
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

/-- A weak derivative on an open subset of the real line vanishes almost everywhere on the
preimage of any countable set. The exceptional set may depend on that set of values. -/
theorem HasWeakLineDerivOn.ae_eq_zero_on_preimage
    (hu : HasWeakLineDerivOn volume Ω u u' 1) {C : Set F} (hC : C.Countable) :
    ∀ᵐ t ∂volume.restrict Ω, u t ∈ C → u' t = 0 := by
  apply (ae_restrict_iff' Ω.isOpen.measurableSet).2
  rw [ae_iff]
  apply measure_null_of_locally_null
  intro x hx
  have hxΩ : x ∈ Ω := by
    by_contra hn
    exact hx (fun hxΩ ↦ (hn hxΩ).elim)
  obtain ⟨a, b, -, hIx, hI⟩ := exists_Icc_mem_subset_of_mem_nhds (Ω.isOpen.mem_nhds hxΩ)
  have hxI : x ∈ Ioo a b := by
    simpa only [interior_Icc] using mem_interior_iff_mem_nhds.2 hIx
  have hsub : Ioo a b ⊆ Ω := Ioo_subset_Icc_self.trans hI
  have huint := hu.locallyIntegrableOn_deriv.integrableOn_compact_subset hI isCompact_Icc
  have hzero := (hu.mono (Ω' := ⟨Ioo a b, isOpen_Ioo⟩) hsub).ae_eq_zero_on_preimage_Ioo
    (huint.mono_set Ioo_subset_Icc_self) hC
  refine ⟨{t | ¬(t ∈ Ω → u t ∈ C → u' t = 0)} ∩ Ioo a b,
    inter_mem_nhdsWithin _ (Ioo_mem_nhds hxI.1 hxI.2), ?_⟩
  have hlocal := (ae_restrict_iff' measurableSet_Ioo).1 hzero
  rw [ae_iff] at hlocal
  apply measure_mono_null _ hlocal
  rintro t ⟨ht, htI⟩
  simp only [mem_ofPred_eq, not_imp] at ht ⊢
  exact ⟨htI, ht.2⟩

/-- Weak derivatives on an open subset of the real line agree almost everywhere on the set
where the original functions agree. The equality set need not be open or measurable. -/
theorem HasWeakLineDerivOn.ae_eq_on_eq_set
    (hu : HasWeakLineDerivOn volume Ω u u' 1)
    (hv : HasWeakLineDerivOn volume Ω v v' 1) :
    ∀ᵐ t ∂volume.restrict Ω, u t = v t → u' t = v' t := by
  have hzero := (hu.sub hv).ae_eq_zero_on_preimage (countable_singleton (0 : F))
  filter_upwards [hzero] with t ht heq
  exact sub_eq_zero.mp (ht (by simp [heq]))

/-- For a real source, weak Fréchet derivatives agree almost everywhere on the equality set
of the functions. Equality of their values on the vector `1` determines the linear maps. -/
theorem HasWeakFDerivOn.ae_eq_on_eq_set_real {Du Dv : ℝ → ℝ →L[ℝ] F}
    (hu : HasWeakFDerivOn volume Ω u Du) (hv : HasWeakFDerivOn volume Ω v Dv) :
    ∀ᵐ t ∂volume.restrict Ω, u t = v t → Du t = Dv t := by
  filter_upwards [(hu.hasWeakLineDerivOn 1).ae_eq_on_eq_set (hv.hasWeakLineDerivOn 1)]
    with t ht heq
  exact ContinuousLinearMap.ext_ring (ht heq)

end TauCeti
