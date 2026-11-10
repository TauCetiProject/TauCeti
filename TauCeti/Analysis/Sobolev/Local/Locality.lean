/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Locality of the local Sobolev classes

The classes `TauCeti.MemLpLoc p U` and `TauCeti.MemWkpLoc p U k` have the sheaf property:
membership can be checked near each point, and membership on every member of an open cover
gives membership on the union. Concretely, for an arbitrary set `U ⊆ ℂ`, a function lies in
the class on `U` exactly when every point of `U` has a neighbourhood within `U` on which it
lies in the class. The set `U` need not be open: for a set reaching the real axis, such as a
relatively open subset of the closed upper half-plane, the neighbourhoods are relative ones and
the `Lᵖ` bounds reach the boundary, as in the definition.

This is what lets regularity statements be proved one point at a time, for instance in
elliptic bootstrapping, and lets membership in coordinates be assembled from charts.

## Main results

* `TauCeti.memLpLoc_iff_locally` and `TauCeti.memWkpLoc_iff_locally`: membership holds exactly
  when it holds on a relative neighbourhood of each point.
* `TauCeti.memLpLoc_iff_forall_inter` and `TauCeti.memWkpLoc_iff_forall_inter`: membership on
  `U` is membership on `U ∩ O i` for every member of an open cover `O` of `U`.
* `TauCeti.memLpLoc_iSup_iff` and `TauCeti.memWkpLoc_iSup_iff`: the sheaf property for open
  covers of an open set.

For positive order the codomain is assumed complete: an empty cover carries no weak
derivative to supply the completeness that the weak-derivative predicate demands.

## Implementation notes

Local `Lᵖ` membership on a compact set is assembled from finitely many compact pieces by
`IsCompact.induction_on`. At positive order the local weak derivatives are glued by
`TauCeti.exists_hasWeakFDerivOn_iSup` on the interior of `U`, which is covered by the
interiors of the sets `U ∩ O i`. The glued field is only determined almost everywhere on that
interior, and the class on `U` also bounds it on the part of `U` outside its interior, which
may have positive measure. The glued field is therefore set to zero off the interior of `U`;
each local field may be replaced in the same way without leaving its class.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces).
-/

public section

open MeasureTheory Set TopologicalSpace Filter Metric
open scoped Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] {p : ENNReal} {U : Set ℂ} {f : ℂ → F}

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
  obtain ⟨r, hr, hrO⟩ := nhds_basis_closedBall.mem_iff.1 hO
  exact ⟨K ∩ closedBall x r, inter_mem_nhdsWithin K (closedBall_mem_nhds x hr),
    memLpLoc_iff.1 hfV _ (fun z hz => hOV ⟨hrO hz.2, hKU hz.1⟩)
      (hK.inter_right isClosed_closedBall)⟩

/-- Local `Lᵖ` membership on `U` can be checked on the traces `U ∩ O i` of an open cover. -/
theorem memLpLoc_iff_forall_inter {ι : Type*} (O : ι → Opens ℂ) (hU : U ⊆ ⋃ i, (O i : Set ℂ)) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p (U ∩ O i) f := by
  refine ⟨fun hf i => hf.mono_set inter_subset_left, fun h => memLpLoc_iff_locally.2 ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hU hx)
  exact ⟨U ∩ O i, inter_mem_nhdsWithin U ((O i).isOpen.mem_nhds hi), h i⟩

/-- Local `Lᵖ` membership on the union of open sets is membership on each of them. -/
theorem memLpLoc_iSup_iff {ι : Type*} (V : ι → Opens ℂ) :
    MemLpLoc p (⨆ i, V i : Opens ℂ) f ↔ ∀ i, MemLpLoc p (V i) f := by
  rw [memLpLoc_iff_forall_inter V (by simp)]
  simp only [Opens.coe_iSup, inter_eq_right.2 (subset_iUnion (fun i => (V i : Set ℂ)) _)]

variable [NormedSpace ℝ F]

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

end TauCeti
