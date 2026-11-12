/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity
public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Null sets of a projection-valued measure

A projection-valued measure `P` has a diagonal scalar measure `P.diag ξ` for each vector `ξ`.
The filter `P.ae` records sets that are conull for *every* diagonal measure. A measurable set
is null for this filter precisely when its spectral projection vanishes.

The null measurable sets are closed under taking measurable subsets and countable unions.
This is the shared almost-everywhere interface needed for the bounded Borel spectral integral.

## Provenance

The finite diagonal scalar measures and projection identities are from the maintained
AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization
(`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean`).
The filter packages those existing results with Mathlib's native almost-everywhere API.
-/

public section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The filter of sets conull for every diagonal measure of the PVM. -/
noncomputable def ae (P : ProjValMeasure X H) : Filter X :=
  ⨆ ξ : H, MeasureTheory.ae (P.diag ξ)

/-- PVM-almost-everywhere predicates hold for every diagonal scalar measure. -/
theorem eventually_ae_iff (P : ProjValMeasure X H) (R : X → Prop) :
    (∀ᶠ x in P.ae, R x) ↔ ∀ ξ : H, ∀ᵐ x ∂(P.diag ξ), R x := by
  simp only [Filter.Eventually, ae, Filter.mem_iSup]

/-- The almost-everywhere filter of each diagonal measure lies below the PVM filter. -/
theorem ae_diag_le_ae (P : ProjValMeasure X H) (ξ : H) :
    MeasureTheory.ae (P.diag ξ) ≤ P.ae := by
  simpa only [ae] using (le_iSup (fun η : H => MeasureTheory.ae (P.diag η)) ξ)

/-- A PVM-almost-everywhere statement holds for an individual diagonal measure. -/
theorem ae_diag_of_ae (P : ProjValMeasure X H) (ξ : H) {R : X → Prop}
    (hR : ∀ᶠ x in P.ae, R x) : ∀ᵐ x ∂(P.diag ξ), R x := by
  exact (P.ae_diag_le_ae ξ) hR

/-- Membership in the PVM's almost-everywhere filter is simultaneous conullity
for all its diagonal scalar measures. -/
@[simp]
theorem mem_ae_iff (P : ProjValMeasure X H) (s : Set X) :
    s ∈ P.ae ↔ ∀ ξ : H, (P.diag ξ) sᶜ = 0 := by
  simp only [ae, Filter.mem_iSup, MeasureTheory.mem_ae_iff]

/-- A set is null for the PVM iff each diagonal measure vanishes on it. -/
theorem compl_mem_ae_iff (P : ProjValMeasure X H) (s : Set X) :
    sᶜ ∈ P.ae ↔ ∀ ξ : H, (P.diag ξ) s = 0 := by
  simpa only [compl_compl] using P.mem_ae_iff sᶜ

/-- A measurable spectral projection is zero exactly when every diagonal measure
assigns its set zero mass. -/
theorem proj_eq_zero_iff_forall_diag_apply_eq_zero (P : ProjValMeasure X H)
    (s : Set X) (hs : MeasurableSet s) :
    P.proj s hs = 0 ↔ ∀ ξ : H, (P.diag ξ) s = 0 := by
  constructor
  · intro h ξ
    rw [← P.enorm_sq_proj_apply s hs ξ, h]
    simp
  · intro h
    apply ContinuousLinearMap.eq_of_diagonal
    intro ξ
    rw [P.inner_proj s hs ξ, h ξ]
    simp

/-- A measurable set is PVM-null iff its orthogonal projection vanishes. -/
theorem proj_eq_zero_iff_compl_mem_ae (P : ProjValMeasure X H)
    (s : Set X) (hs : MeasurableSet s) :
    P.proj s hs = 0 ↔ sᶜ ∈ P.ae := by
  rw [P.proj_eq_zero_iff_forall_diag_apply_eq_zero s hs, P.compl_mem_ae_iff]

/-- PVM-null measurable sets are downward closed. -/
theorem proj_eq_zero_of_subset (P : ProjValMeasure X H)
    {s t : Set X} (hst : s ⊆ t) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : P.proj t ht = 0) :
    P.proj s hs = 0 := by
  apply (P.proj_eq_zero_iff_forall_diag_apply_eq_zero s hs).2
  intro ξ
  exact measure_mono_null hst ((P.proj_eq_zero_iff_forall_diag_apply_eq_zero t ht).1 h ξ)

/-- PVM-null measurable sets are closed under countable unions. -/
theorem proj_iUnion_eq_zero (P : ProjValMeasure X H) {ι : Type*} [Countable ι]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (h : ∀ i, P.proj (s i) (hs i) = 0) :
    P.proj (⋃ i, s i) (MeasurableSet.iUnion hs) = 0 := by
  apply (P.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _).2
  intro ξ
  exact measure_iUnion_null fun i =>
    (P.proj_eq_zero_iff_forall_diag_apply_eq_zero (s i) (hs i)).1 (h i) ξ

end ProjValMeasure
end TauCeti
