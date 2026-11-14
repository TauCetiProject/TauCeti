/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Topology.Separation.Regular
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Locality of the local Lebesgue and Sobolev classes

The classes `TauCeti.MemLpLoc p U`, `TauCeti.MemW1pLoc p Ω`, and `TauCeti.MemWkpLoc p U k` have
the sheaf property: membership can be checked near each point, and membership on every member of an
open cover gives membership on the union.

* For `MemLpLoc p U` on a regular topological measure space `E`, membership on an arbitrary set `U`
  holds if and only if every point of `U` has a relative neighbourhood on which it holds
  (`TauCeti.memLpLoc_iff_locally`), and can be checked on the traces `U ∩ O i` of any open cover
  (`TauCeti.memLpLoc_iff_forall_inter`, `TauCeti.memLpLoc_iSup_iff`).
* For `MemW1pLoc p Ω` on an open subset of a finite-dimensional real normed space `E` carrying a
  Borel measure, membership on `⨆ i, V i` holds if and only if it holds on each `V i`
  (`TauCeti.memW1pLoc_iSup_iff`), and holds on `Ω` if and only if it holds on an open neighbourhood
  of each point (`TauCeti.memW1pLoc_iff_locally`).
* For `MemWkpLoc p U k` on an arbitrary subset `U ⊆ ℂ` (such as a half-disc reaching the real
  axis), membership holds if and only if it holds on a relative neighbourhood of each point
  (`TauCeti.memWkpLoc_iff_locally`, `TauCeti.memWkpLoc_iff_forall_inter`,
  `TauCeti.memWkpLoc_iSup_iff`).

For positive order the codomain is assumed complete: an empty cover carries no weak derivative to
supply the completeness that `TauCeti.HasWeakFDerivOn` demands.

## Implementation notes

Local `Lᵖ` membership on a compact set is assembled from finitely many compact pieces by
`IsCompact.induction_on`, cutting by closed neighbourhoods from `closed_nhds_basis`. At positive
order the local weak derivatives agree almost everywhere on overlaps by uniqueness and are glued by
`TauCeti.exists_hasWeakFDerivOn_iSup`. For `MemWkpLoc` on a non-open set `U`, the glued derivative
field is set to zero off `interior U` so that `Lᵖ` bounds up to the boundary of `U` are preserved.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299, §2.
-/

public section

open MeasureTheory Set TopologicalSpace Filter
open scoped Topology

namespace TauCeti

section MemLpLoc

variable {E F : Type*} [TopologicalSpace E] [RegularSpace E] [MeasureSpace E]
  [NormedAddCommGroup F] {p : ENNReal} {U : Set E} {f : E → F}

/-- Local `Lᵖ` membership is a local property: it holds on `U` exactly when every point of `U`
has a neighbourhood within `U` on which it holds. -/
theorem memLpLoc_iff_locally :
    MemLpLoc p U f ↔ ∀ x ∈ U, ∃ V ∈ 𝓝[U] x, MemLpLoc p V f := by
  refine ⟨fun hf _ _ => ⟨U, self_mem_nhdsWithin, hf⟩,
    fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  refine hK.induction_on (p := fun s => MemLp f p (volume.restrict s)) (by simp)
    (fun s t hst ht => ht.mono_measure (Measure.restrict_mono hst le_rfl))
    (fun s t hs ht => (hs.add_measure ht).mono_measure (Measure.restrict_union_le s t))
    fun x hx => ?_
  obtain ⟨V, hV, hfV⟩ := h x (hKU hx)
  obtain ⟨O, hO, hOV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  obtain ⟨C, ⟨hCnhds, hCcl⟩, hCO⟩ := (closed_nhds_basis x).mem_iff.1 hO
  exact ⟨K ∩ C, inter_mem_nhdsWithin K hCnhds,
    memLpLoc_iff.1 hfV _ (fun y hy => hOV ⟨hCO hy.2, hKU hy.1⟩) (hK.inter_right hCcl)⟩

/-- Local `Lᵖ` membership on `U` can be checked on the traces `U ∩ O i` of an open cover. -/
theorem memLpLoc_iff_forall_inter {ι : Type*} (O : ι → Opens E) (hU : U ⊆ ⋃ i, (O i : Set E)) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p (U ∩ O i) f := by
  refine ⟨fun hf i => hf.mono_set inter_subset_left, fun h => memLpLoc_iff_locally.2 ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hU hx)
  exact ⟨U ∩ O i, inter_mem_nhdsWithin U ((O i).isOpen.mem_nhds hi), h i⟩

/-- Local `Lᵖ` membership on the union of open sets is membership on each of them. -/
theorem memLpLoc_iSup_iff {ι : Type*} (V : ι → Opens E) :
    MemLpLoc p (⨆ i, V i : Opens E) f ↔ ∀ i, MemLpLoc p (V i) f := by
  rw [memLpLoc_iff_forall_inter V (by simp)]
  simp only [Opens.coe_iSup, inter_eq_right.2 (subset_iUnion (fun i => (V i : Set E)) _)]

end MemLpLoc

section MemW1pLoc

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ENNReal}

/-- `MemW1pLoc` has the sheaf property for open covers: membership on `⨆ i, V i` holds if and
only if it holds on each open set `V i` of the cover. Local weak derivatives agree almost
everywhere on overlaps by uniqueness and glue via `TauCeti.exists_hasWeakFDerivOn_iSup`. -/
theorem memW1pLoc_iSup_iff {ι : Type*} (V : ι → Opens E) {u : E → F} :
    MemW1pLoc p (⨆ i, V i) u ↔ ∀ i, MemW1pLoc p (V i) u := by
  refine ⟨fun hu i => hu.mono (le_iSup V i), fun h => ?_⟩
  choose D hD hDLp using fun i => (h i).exists_hasWeakFDerivOn
  obtain ⟨Du, hDu, hDuD⟩ := exists_hasWeakFDerivOn_iSup V D hD
  exact memW1pLoc_iff.2 ⟨(memLpLoc_iSup_iff V).2 fun i => (h i).memLpLoc, Du, hDu,
    (memLpLoc_iSup_iff V).2 fun i => (hDLp i).congr_ae (hDuD i).symm⟩

/-- `MemW1pLoc` is a local property on open sets: membership on `Ω` holds if and only if every
point of `Ω` has an open neighbourhood on which it holds. -/
theorem memW1pLoc_iff_locally {Ω : Opens E} {u : E → F} :
    MemW1pLoc p Ω u ↔ ∀ x ∈ Ω, ∃ V : Opens E, x ∈ V ∧ MemW1pLoc p V u := by
  refine ⟨fun hu x hx => ⟨Ω, hx, hu⟩, fun h => ?_⟩
  choose V hxV hV using fun x : Ω => h x x.2
  have hΩ : Ω ≤ ⨆ x : Ω, V x := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  exact ((memW1pLoc_iSup_iff V).2 hV).mono hΩ

end MemW1pLoc

section MemWkpLoc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set ℂ} {f : ℂ → F}

/-- Zeroing a function off the interior of `U` keeps it in its local Sobolev class: the weak
derivatives only see the interior, and the `Lᵖ` bounds only improve. -/
private theorem MemWkpLoc.indicator_interior {k : ℕ} (hf : MemWkpLoc p U k f) :
    MemWkpLoc p U k ((interior U).indicator f) := by
  have hLp : MemLpLoc p U ((interior U).indicator f) := memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 hf.memLpLoc K hK hc).indicator measurableSet_interior.nullMeasurableSet
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 hLp
  | succ k =>
    obtain ⟨D, hD, hk⟩ := hf.exists_weakFDeriv
    exact memWkpLoc_succ_iff.2 ⟨hLp, D, hD.congr_ae (indicator_ae_eq_restrict
      measurableSet_interior.nullMeasurableSet).symm, hk⟩

/-- Positive-order local Sobolev membership on `U` can be checked on the traces `U ∩ O i` of an
open cover. The local weak derivatives need not agree; they are glued on the interior of `U`.
Completeness of the codomain is needed for an empty cover. -/
theorem memWkpLoc_iff_forall_inter [CompleteSpace F] {ι : Type*} (O : ι → Opens ℂ)
    (hU : U ⊆ ⋃ i, (O i : Set ℂ)) {k : ℕ} :
    MemWkpLoc p U k f ↔ ∀ i, MemWkpLoc p (U ∩ O i) k f := by
  refine ⟨fun hf i => hf.mono inter_subset_left, fun h => ?_⟩
  induction k generalizing F with
  | zero =>
    exact memWkpLoc_zero_iff.2 <| (memLpLoc_iff_forall_inter O hU).2 fun i => (h i).memLpLoc
  | succ k ih =>
    choose D hD hDk using fun i => (h i).exists_weakFDeriv
    obtain ⟨G, hG, hGD⟩ := exists_hasWeakFDerivOn_iSup _ D hD
    have hint : ∀ i, interior (U ∩ O i) = interior U ∩ O i := fun i => by
      rw [interior_inter, (O i).isOpen.interior_eq]
    have hsup : (⨆ i, Opens.interior (U ∩ O i)) = Opens.interior U := by
      ext z
      simp only [Opens.coe_iSup, Opens.coe_interior, hint, ← inter_iUnion]
      exact ⟨fun hz => hz.1, fun hz => ⟨hz, hU (interior_subset hz)⟩⟩
    refine memWkpLoc_succ_iff.2 ⟨(memLpLoc_iff_forall_inter O hU).2 fun i => (h i).memLpLoc,
      (interior U).indicator G, ?_, ih fun i => ?_⟩
    · rw [hsup] at hG
      exact hG.congr_ae_deriv
        (indicator_ae_eq_restrict measurableSet_interior.nullMeasurableSet).symm
    · refine (hDk i).indicator_interior.congr_ae ?_
      have hGDi := (ae_restrict_iff' measurableSet_interior).1 (hGD i)
      filter_upwards [ae_restrict_of_ae hGDi, ae_restrict_of_ae_restrict_of_subset
        inter_subset_right (ae_restrict_mem (O i).isOpen.measurableSet)] with z hz hzO
      by_cases hzU : z ∈ interior U
      · have hzi : z ∈ interior (U ∩ O i) := (hint i).symm ▸ ⟨hzU, hzO⟩
        simp only [indicator_of_mem hzi, indicator_of_mem hzU, hz hzi]
      · have hzi : z ∉ interior (U ∩ O i) := fun hzi => hzU ((hint i ▸ hzi).1)
        simp only [indicator_of_notMem hzi, indicator_of_notMem hzU]

/-- Local Sobolev membership on the union of open sets is membership on each of them. -/
theorem memWkpLoc_iSup_iff [CompleteSpace F] {ι : Type*} (V : ι → Opens ℂ) {k : ℕ} :
    MemWkpLoc p (⨆ i, V i : Opens ℂ) k f ↔ ∀ i, MemWkpLoc p (V i) k f := by
  rw [memWkpLoc_iff_forall_inter V (by simp)]
  simp only [Opens.coe_iSup, inter_eq_right.2 (subset_iUnion (fun i => (V i : Set ℂ)) _)]

/-- Local Sobolev membership is a local property: it holds on `U` exactly when every point of
`U` has a neighbourhood within `U` on which it holds. -/
theorem memWkpLoc_iff_locally [CompleteSpace F] {k : ℕ} :
    MemWkpLoc p U k f ↔ ∀ x ∈ U, ∃ V ∈ 𝓝[U] x, MemWkpLoc p V k f := by
  refine ⟨fun hf _ _ => ⟨U, self_mem_nhdsWithin, hf⟩, fun h => ?_⟩
  have hO : ∀ x : U, ∃ O : Opens ℂ, (x : ℂ) ∈ O ∧ MemWkpLoc p (U ∩ O) k f := fun x => by
    obtain ⟨V, hV, hfV⟩ := h x x.2
    obtain ⟨O, hO, hxO, hOV⟩ := mem_nhdsWithin.1 hV
    exact ⟨⟨O, hO⟩, hxO, hfV.mono fun z hz => hOV ⟨hz.2, hz.1⟩⟩
  choose O hxO hfO using hO
  exact (memWkpLoc_iff_forall_inter O fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩).2 hfO

end MemWkpLoc

end TauCeti
