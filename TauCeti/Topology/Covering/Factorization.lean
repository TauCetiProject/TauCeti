/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Covering.Basic
import TauCeti.Topology.FiberBundle.Trivialization

/-!
# A map of covering spaces with locally connected target is a covering map

Let `p : E → X` and `q : F → X` be covering maps and let `g : E → F` be a continuous map over
`X`, that is, `q ∘ g = p`. This file proves that `g` is itself a covering map as soon as `F` is
locally connected.

The proof is the standard sheet comparison. Around a point `f₀` of `F`, choose a connected open
neighbourhood in `F` whose image `V` lies inside the intersection of evenly covered
neighbourhoods for `p` and `q`, and trivialize both projections over `V`. A sheet of `p` over `V`
is the image of `V` under
`v ↦ tp.symm (v, i)`, so it is connected, and the sheet index of its image under `g` is a
continuous map from `V` to a discrete space, hence constant. So `g` carries each sheet of `p`
over `V` onto a single sheet of `q`, and injectively, because `p = q ∘ g` is injective on it.
The sheet `W` of `q` through `f₀` is therefore evenly covered by `g`, with fibre the set of
sheets of `p` that land in `W`.

Local connectedness of `F` produces the connected neighbourhood whose open, connected image is
`V`. It is used exactly once, to make the sheet index locally constant.

Neither total space is assumed connected and `g` is not assumed surjective. That is consistent
because `IsCoveringMap` allows empty fibres: over a sheet of `q` missed by `g` the fibre of `g`
is empty.

## Main declarations

* `IsCoveringMap.of_comp_eq`: **a continuous map between covering spaces, with locally connected
  target and commuting with the projections, is a covering map.**
-/

public section

namespace TauCeti

open Bundle Set Topology

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {g : E → F}

/-- The evenly covered neighbourhood of `f₀` for a map `g` over `X` between two trivialized
projections, cut out by a connected open set `V` of the base lying inside both base sets.

The neighbourhood is the sheet of `q` over `V` through `f₀`, and the fibre over it is the set of
sheet indices of `p` that `g` sends into that sheet. -/
private theorem isEvenlyCovered_of_trivialization (hq : Continuous q) (hg : Continuous g)
    (hqg : ∀ e, q (g e) = p e) {I J : Type*} [TopologicalSpace I] [DiscreteTopology I]
    [TopologicalSpace J] [DiscreteTopology J] (tp : Trivialization I p) (tq : Trivialization J q)
    (f₀ : F) {V : Set X} (hVopen : IsOpen V) (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) (hf₀V : q f₀ ∈ V) :
    IsEvenlyCovered g f₀ (g ⁻¹' {f₀}) := by
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := {i : I // (tq (g (tp.toOpenPartialHomeomorph.symm (q f₀, i)))).2 = (tq f₀).2}) ?_
  set j₀ : J := (tq f₀).2 with _₀
  set W : Set F := {f | q f ∈ V ∧ (tq f).2 = j₀}
  have hWopen : IsOpen W := tq.isOpen_sheet hq hVopen (fun v hv => (hVsub hv).2) j₀
  have hgW := tp.map_mem_sheet_iff hg hqg tq hVconn hVsub hf₀V j₀
  refine ⟨inferInstance, W, ⟨hf₀V, rfl⟩, hWopen, hWopen.preimage hg,
    { toFun := fun e => (⟨g e.1, e.2⟩, ⟨(tp e.1).2, (hgW e.1).mp e.2 |>.2⟩)
      invFun := fun wi => ⟨tp.toOpenPartialHomeomorph.symm (q wi.1.1, wi.2.1), by
        refine (hgW _).mpr ⟨?_, ?_⟩
        · rw [tp.proj_symm_apply' (hVsub wi.1.2.1).1]
          exact wi.1.2.1
        · rw [tp.apply_symm_apply' (hVsub wi.1.2.1).1]
          exact wi.2.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        refine Subtype.ext ?_
        dsimp only
        rw [hqg e]
        exact tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub ((hgW e).mp he).1).1)
      right_inv := by
        rintro ⟨⟨w, hw⟩, ⟨i, hi⟩⟩
        dsimp only
        refine Prod.ext (Subtype.ext
          (tp.map_symm_eq_of_mem_sheet hg hqg tq hVconn hVsub hf₀V hw hi)) (Subtype.ext ?_)
        dsimp only
        rw [tp.apply_symm_apply' (hVsub hw.1).1]
      continuous_toFun := by
        refine Continuous.prodMk (Continuous.subtype_mk (hg.comp continuous_subtype_val) _)
          (Continuous.subtype_mk ?_ _)
        refine continuous_snd.comp_continuousOn tp.continuousOn_toFun
          |>.comp_continuous continuous_subtype_val fun e => ?_
        exact tp.mem_source.mpr (hVsub ((hgW e.1).mp e.2).1).1
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        refine tp.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous ?_ fun wi => ?_
        · exact ((hq.comp continuous_subtype_val).comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd)
        · exact tp.mem_target.mpr (hVsub wi.1.2.1).1 },
    fun _ => rfl⟩

/-- **A map of covering spaces with locally connected target is a covering map.** If `p : E → X`
and `q : F → X` are covering maps and `g : E → F` is continuous with `q ∘ g = p`, then `g` is a
covering map provided `F` is locally connected.

Neither total space needs to be connected and `g` need not be surjective; the fibre of `g` over
a point outside its range is empty, which `IsCoveringMap` permits. -/
theorem _root_.IsCoveringMap.of_comp_eq [LocallyConnectedSpace F] (hp : IsCoveringMap p)
    (hq : IsCoveringMap q) (hg : Continuous g) (hgp : q ∘ g = p) : IsCoveringMap g := by
  have hqg : ∀ e, q (g e) = p e := congrFun hgp
  intro f₀
  rcases isEmpty_or_nonempty (p ⁻¹' {q f₀} : Set E) with hemp | hne
  · -- `p` misses `q f₀`, so `g` misses a whole evenly covered neighbourhood of `f₀`.
    obtain ⟨-, U, hxU, hU, -, Hp, -⟩ := hp (q f₀)
    have hgU : g ⁻¹' (q ⁻¹' U) = ∅ := by
      rw [← preimage_comp, hgp]
      exact isEmpty_coe_sort.mp (Function.isEmpty Hp)
    have : IsEmpty (g ⁻¹' {f₀}) := isEmpty_coe_sort.mpr <|
      subset_empty_iff.mp (hgU ▸ preimage_mono (singleton_subset_iff.mpr hxU))
    exact IsEvenlyCovered.of_preimage_eq_empty _ ((hU.preimage hq.continuous).mem_nhds hxU) hgU
  · have : Nonempty (q ⁻¹' {q f₀} : Set F) := ⟨⟨f₀, rfl⟩⟩
    have := (hp (q f₀)).discreteTopology_fiber
    have := (hq (q f₀)).discreteTopology_fiber
    set tp := (hp (q f₀)).toTrivialization
    set tq := (hq (q f₀)).toTrivialization
    obtain ⟨W, hWsub, hWopen, hf₀W, hWconn⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp ‹LocallyConnectedSpace F› f₀
        (q ⁻¹' (tp.baseSet ∩ tq.baseSet))
        ((tp.open_baseSet.inter tq.open_baseSet).preimage hq.continuous |>.mem_nhds
          ⟨(hp (q f₀)).mem_toTrivialization_baseSet,
            (hq (q f₀)).mem_toTrivialization_baseSet⟩)
    exact isEvenlyCovered_of_trivialization hq.continuous hg hqg tp tq f₀
      (hq.isOpenMap W hWopen) (hWconn.isPreconnected.image q hq.continuous.continuousOn)
      (fun x ⟨f, hf, hfx⟩ => hfx ▸ hWsub hf) ⟨f₀, hf₀W, rfl⟩

end TauCeti
