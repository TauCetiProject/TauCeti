/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Covering.Basic

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

/-- A point of a sheet of `p` over a set `V` inside both base sets is sent by `g` into the source
of `tq`, so its sheet index for `q` is defined. -/
private theorem symm_mem_source_of_comp_eq (hqg : ∀ e, q (g e) = p e) {I J : Type*}
    [TopologicalSpace I] [TopologicalSpace J] (tp : Trivialization I p) (tq : Trivialization J q)
    {V : Set X} (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) (i : I) {v : X} (hv : v ∈ V) :
    g (tp.toOpenPartialHomeomorph.symm (v, i)) ∈ tq.source := by
  rw [tq.mem_source, hqg, tp.proj_symm_apply' (hVsub hv).1]
  exact (hVsub hv).2

/-- The `q`-sheet index of the image under `g` of a point of a `p`-sheet over a preconnected set
`V` is constant along the sheet, because the index is continuous and `J` is discrete. -/
private theorem sheetIndex_symm_eq (hg : Continuous g) (hqg : ∀ e, q (g e) = p e) {I J : Type*}
    [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J] (tp : Trivialization I p)
    (tq : Trivialization J q) {V : Set X} (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) (i : I) {v x₀ : X} (hv : v ∈ V) (hx₀ : x₀ ∈ V) :
    (tq (g (tp.toOpenPartialHomeomorph.symm (v, i)))).2 =
      (tq (g (tp.toOpenPartialHomeomorph.symm (x₀, i)))).2 := by
  have hsnd : ContinuousOn (fun f : F => (tq f).2) tq.source :=
    continuous_snd.comp_continuousOn tq.continuousOn_toFun
  have h1 : ContinuousOn (fun v => g (tp.toOpenPartialHomeomorph.symm (v, i))) V :=
    hg.comp_continuousOn (tp.continuousOn_symm_prodMk_left.mono fun v hv => (hVsub hv).1)
  exact hVconn.constant (hsnd.comp h1 fun v hv => symm_mem_source_of_comp_eq hqg tp tq hVsub i hv)
    hv hx₀

/-- The `q`-sheet of index `j` over an open set `V` inside the base set of `tq` is open. -/
private theorem isOpen_sheet (hq : Continuous q) {J : Type*} [TopologicalSpace J]
    [DiscreteTopology J] (tq : Trivialization J q) {V : Set X} (hVopen : IsOpen V)
    (hVsub : V ⊆ tq.baseSet) (j : J) : IsOpen {f : F | q f ∈ V ∧ (tq f).2 = j} := by
  have hW : {f : F | q f ∈ V ∧ (tq f).2 = j} =
      q ⁻¹' V ∩ (tq.source ∩ (fun f => (tq f).2) ⁻¹' {j}) := by
    ext f
    exact ⟨fun h => ⟨h.1, tq.mem_source.mpr (hVsub h.1), h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [hW]
  exact (hVopen.preimage hq).inter
    ((continuous_snd.comp_continuousOn tq.continuousOn_toFun).isOpen_inter_preimage
      tq.open_source (isOpen_discrete {j}))

/-- Whether `g e` lies in the `q`-sheet of index `j` over `V` is read off the sheet index of `p`
at `e`. -/
private theorem comp_mem_sheet_iff (hg : Continuous g) (hqg : ∀ e, q (g e) = p e) {I J : Type*}
    [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J] (tp : Trivialization I p)
    (tq : Trivialization J q) {V : Set X} (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) {x₀ : X} (hx₀ : x₀ ∈ V) (j : J) (e : E) :
    (q (g e) ∈ V ∧ (tq (g e)).2 = j) ↔
      p e ∈ V ∧ (tq (g (tp.toOpenPartialHomeomorph.symm (x₀, (tp e).2)))).2 = j := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [hqg] at h1
    refine ⟨h1, ?_⟩
    rw [← sheetIndex_symm_eq hg hqg tp tq hVconn hVsub (tp e).2 h1 hx₀,
      tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub h1).1), h2]
  · rintro ⟨h1, h2⟩
    have h3 := sheetIndex_symm_eq hg hqg tp tq hVconn hVsub (tp e).2 h1 hx₀
    rw [tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub h1).1)] at h3
    exact ⟨by rw [hqg]; exact h1, by rw [h3, h2]⟩

/-- The `p`-sheet of index `i` through a point `w` of a `q`-sheet is carried by `g` onto `w`
when it lands in that `q`-sheet. -/
private theorem comp_symm_eq_of_mem_sheet (hg : Continuous g) (hqg : ∀ e, q (g e) = p e)
    {I J : Type*} [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J]
    (tp : Trivialization I p) (tq : Trivialization J q) {V : Set X} (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) {x₀ : X} (hx₀ : x₀ ∈ V) {j : J} {w : F} {i : I}
    (hw : q w ∈ V ∧ (tq w).2 = j) (hi : (tq (g (tp.toOpenPartialHomeomorph.symm (x₀, i)))).2 = j) :
    g (tp.toOpenPartialHomeomorph.symm (q w, i)) = w := by
  have h1 : q (g (tp.toOpenPartialHomeomorph.symm (q w, i))) = q w := by
    rw [hqg, tp.proj_symm_apply' (hVsub hw.1).1]
  refine tq.injOn (symm_mem_source_of_comp_eq hqg tp tq hVsub i hw.1)
    (tq.mem_source.mpr (hVsub hw.1).2) (Prod.ext ?_ ?_)
  · simp only [Trivialization.coe_coe]
    rw [tq.coe_fst (symm_mem_source_of_comp_eq hqg tp tq hVsub i hw.1),
      tq.coe_fst (tq.mem_source.mpr (hVsub hw.1).2), h1]
  · simp only [Trivialization.coe_coe]
    rw [sheetIndex_symm_eq hg hqg tp tq hVconn hVsub i hw.1 hx₀, hi, hw.2]

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
  have hWopen : IsOpen W := isOpen_sheet hq tq hVopen (fun v hv => (hVsub hv).2) j₀
  have hgW := comp_mem_sheet_iff hg hqg tp tq hVconn hVsub hf₀V j₀
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
          (comp_symm_eq_of_mem_sheet hg hqg tp tq hVconn hVsub hf₀V hw hi)) (Subtype.ext ?_)
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
    have hpU : p ⁻¹' U = ∅ := Set.isEmpty_coe_sort.mp (Function.isEmpty ⇑Hp)
    have hgU : g ⁻¹' (q ⁻¹' U) = ∅ := by
      rw [← Set.preimage_comp, hgp]
      exact hpU
    have : IsEmpty (g ⁻¹' {f₀} : Set E) := by
      refine Set.isEmpty_coe_sort.mpr (Set.eq_empty_of_subset_empty ?_)
      rw [← hgU]
      rintro e he
      rw [Set.mem_preimage, Set.mem_singleton_iff] at he
      simpa only [Set.mem_preimage, he] using hxU
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
