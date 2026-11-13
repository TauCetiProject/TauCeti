/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Preferred trivializations and disjoint unions of trivializations

Near a point `v₀` of the total space of a fibre bundle, every point lies over the base set of the
preferred trivialization at the base point `v₀.proj`, so it can be read in that trivialization.
A compact subset of the total space lies over finitely many preferred trivializing base sets.
An arbitrary family of trivializations over pairwise disjoint open base sets glues to one
trivialization over their union, with the same forward and inverse maps on each constituent.
The coordinate change between two trivializations is jointly continuous in the base point and the
fibre coordinate over the overlap of their base sets, which makes the transition functions of a
fibre bundle continuous.
A map is continuous as soon as every point of the base lies in the base set of a trivialization,
and the trivializations at the points of the base of a fibre bundle make its projection such a
locally trivial map.
Finally, the inverse of a trivialization undoes a coordinate change into it, and over a point
of its base set a trivialization is an equivalence between the fibre and the model fibre.

## Main results

* `Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`: near `v₀`, points lie over
  the base set of the trivialization at `v₀.proj`.
* `IsCompact.exists_finset_subset_preimage_biUnion_baseSet`: a compact subset of the total
  space lies over a finite union of preferred trivializing base sets.
* `TauCeti.continuous_of_forall_exists_trivialization`: a locally trivial map is continuous.
* `FiberBundle.exists_trivialization_mem_baseSet`: the projection of a fibre bundle is locally
  trivial.
* `Bundle.Trivialization.continuousOn_coordChange`: coordinate changes are jointly continuous over
  the overlap of the base sets.
* `Bundle.Trivialization.symm_mk_coordChange`: the inverse of `e₂` undoes the coordinate change
  from `e₁` to `e₂`, landing on the point with the original fibre coordinate in `e₁`.
* `Bundle.Trivialization.equivAt`: a trivialization as an equivalence between the fibre over a
  point of its base set and the model fibre.
* `Bundle.Trivialization.isOpen_sheet`: for a trivialization with discrete fibre of a map,
  the sheet of a given index over an open subset of the base set is open.
* `Bundle.Trivialization.map_mem_sheet_iff`, `Bundle.Trivialization.map_symm_eq_of_mem_sheet`:
  a continuous map `g` over the base, between two trivialized maps with discrete target fibre,
  carries the sheets of `p` over a preconnected set onto sheets of `q`.
-/

public section

open Bundle Filter Set
open scoped Topology

namespace Bundle.TotalSpace

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- Near a point `v₀` of the total space, every point lies over the base set of the
trivialization at `v₀.proj`. -/
theorem eventually_proj_mem_baseSet_trivializationAt (v₀ : TotalSpace F E) :
    ∀ᶠ v in 𝓝 v₀, v.proj ∈ (trivializationAt F E v₀.proj).baseSet :=
  (FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
    ((trivializationAt F E v₀.proj).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' v₀.proj))

end Bundle.TotalSpace

namespace Bundle.Trivialization

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  {proj : Z → B}

/-- The coordinate change `(b, v) ↦ e₁.coordChange e₂ b v` between two trivializations is jointly
continuous over the overlap of their base sets. -/
theorem continuousOn_coordChange (e₁ e₂ : Trivialization F proj) :
    ContinuousOn (fun p : B × F ↦ e₁.coordChange e₂ p.1 p.2)
      ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ) := by
  -- Over the overlap, the coordinate change is the second coordinate of `e₂ ∘ e₁⁻¹`.
  have hsymm : ContinuousOn e₁.toOpenPartialHomeomorph.symm
      ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ) :=
    e₁.toOpenPartialHomeomorph.continuousOn_symm.mono fun _ hp ↦ e₁.mem_target.2 hp.1.1
  have hmaps : MapsTo e₁.toOpenPartialHomeomorph.symm ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ)
      e₂.toOpenPartialHomeomorph.source := fun _ hp ↦
    e₂.mem_source.2 (by rw [e₁.proj_symm_apply' hp.1.1]; exact hp.1.2)
  refine (continuous_snd.comp_continuousOn
    (e₂.toOpenPartialHomeomorph.continuousOn.comp hsymm hmaps)).congr
    fun p hp ↦ ?_
  simp only [Function.comp_apply, e₂.coe_coe, ← e₁.mk_coordChange e₂ hp.1.1 hp.1.2 p.2]

end Bundle.Trivialization

namespace TauCeti

/-- A locally trivial map, one for which every point of the base lies in the base set of a
trivialization, is continuous. -/
theorem continuous_of_forall_exists_trivialization {B F Z : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace Z] {p : Z → B}
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) : Continuous p :=
  continuous_iff_continuousAt.2 fun z ↦ by
    obtain ⟨e, he⟩ := h (p z)
    exact e.continuousAt_proj (e.mem_source.2 he)

end TauCeti

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (F E) in
/-- The projection of a fibre bundle is locally trivial, through the trivializations at the points
of the base. -/
theorem exists_trivialization_mem_baseSet (b : B) :
    ∃ e : Trivialization F (π F E), b ∈ e.baseSet :=
  ⟨trivializationAt F E b, mem_baseSet_trivializationAt F E b⟩

end FiberBundle

/-- A compact subset of a fibre bundle's total space lies over a finite union of the
chosen trivializing base sets. -/
theorem IsCompact.exists_finset_subset_preimage_biUnion_baseSet
    {B : Type*} [TopologicalSpace B] {F : Type*} [TopologicalSpace F]
    {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {K : Set (TotalSpace F E)} (hK : IsCompact K) :
    ∃ s : Finset B, K ⊆ π F E ⁻¹' ⋃ b ∈ s, (trivializationAt F E b).baseSet := by
  obtain ⟨s, hs⟩ := (hK.image (FiberBundle.continuous_proj F E)).elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩)
  exact ⟨s, fun p hp ↦ hs (mem_image_of_mem _ hp)⟩

namespace Bundle.Trivialization

section DisjointUnion

variable {ι B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [Nonempty F] [∀ b, Nonempty (E b)]
  (e : ι → Trivialization F (π F E))
  (hd : Pairwise fun i j ↦ Disjoint (e i).baseSet (e j).baseSet)

open Classical in
private noncomputable def iUnionFun (p : TotalSpace F E) : B × F :=
  if h : ∃ i, p.proj ∈ (e i).baseSet then e h.choose p
  else (p.proj, Classical.choice ‹Nonempty F›)

open Classical in
private noncomputable def iUnionInv (p : B × F) : TotalSpace F E :=
  if h : ∃ i, p.1 ∈ (e i).baseSet then (e h.choose).toOpenPartialHomeomorph.symm p
  else ⟨p.1, Classical.choice (inferInstance : Nonempty (E p.1))⟩

omit [Nonempty F] [∀ b, Nonempty (E b)] in
include hd in
private theorem iUnion_index_eq {b : B} {i : ι} (hi : b ∈ (e i).baseSet)
    (h : ∃ j, b ∈ (e j).baseSet) : h.choose = i := by
  by_contra hne
  exact Set.disjoint_left.1 (hd hne) h.choose_spec hi

omit [∀ b, Nonempty (E b)] in
include hd in
private theorem iUnionFun_eq {i : ι} {p : TotalSpace F E}
    (hp : p.proj ∈ (e i).baseSet) : iUnionFun e p = e i p := by
  rw [iUnionFun, dite_eq_left ⟨i, hp⟩, iUnion_index_eq e hd hp]

omit [Nonempty F] in
include hd in
private theorem iUnionInv_eq {i : ι} {p : B × F}
    (hp : p.1 ∈ (e i).baseSet) :
    iUnionInv e p = (e i).toOpenPartialHomeomorph.symm p := by
  rw [iUnionInv, dite_eq_left ⟨i, hp⟩, iUnion_index_eq e hd hp]

/-- Glue an arbitrary family of trivializations with pairwise disjoint base sets. The base set
is their union. No local finiteness is required: every base set is open. The nonempty fibers
supply arbitrary values outside the source and target, where a trivialization has no meaning. -/
noncomputable def iUnion : Trivialization F (π F E) where
  toFun := iUnionFun e
  invFun := iUnionInv e
  source := ⋃ i, (e i).source
  target := ⋃ i, (e i).target
  map_source' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionFun_eq e hd ((e i).mem_source.1 hi)]
    exact Set.mem_iUnion.2 ⟨i, (e i).map_source hi⟩
  map_target' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionInv_eq e hd ((e i).mem_target.1 hi)]
    exact Set.mem_iUnion.2 ⟨i, (e i).map_target hi⟩
  left_inv' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionFun_eq e hd ((e i).mem_source.1 hi),
      iUnionInv_eq e hd (p := e i p) ((e i).mem_target.1 ((e i).map_source hi))]
    exact (e i).left_inv hi
  right_inv' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionInv_eq e hd ((e i).mem_target.1 hi),
      iUnionFun_eq e hd ((e i).mem_source.1 ((e i).map_target hi))]
    exact (e i).right_inv hi
  open_source := isOpen_iUnion fun i ↦ (e i).open_source
  open_target := isOpen_iUnion fun i ↦ (e i).open_target
  continuousOn_toFun := ContinuousOn.iUnion_of_isOpen (fun i ↦
    (e i).continuousOn.congr fun p hp ↦ iUnionFun_eq e hd ((e i).mem_source.1 hp))
    fun i ↦ (e i).open_source
  continuousOn_invFun := ContinuousOn.iUnion_of_isOpen (fun i ↦
    (e i).toOpenPartialHomeomorph.symm.continuousOn.congr fun p hp ↦
      iUnionInv_eq e hd ((e i).mem_target.1 hp))
    fun i ↦ (e i).open_target
  baseSet := ⋃ i, (e i).baseSet
  open_baseSet := isOpen_iUnion fun i ↦ (e i).open_baseSet
  source_eq := by simp only [source_eq, Set.preimage_iUnion]
  target_eq := by simp only [target_eq, Set.iUnion_prod_const]
  proj_toFun p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    exact (congrArg Prod.fst (iUnionFun_eq e hd ((e i).mem_source.1 hi))).trans
      ((e i).coe_fst hi)

@[simp]
theorem iUnion_baseSet : (iUnion e hd).baseSet = ⋃ i, (e i).baseSet :=
  (rfl)

include hd in
/-- The glued trivialization agrees with a constituent over its base set. -/
theorem iUnion_apply {i : ι} {p : TotalSpace F E} (hp : p.proj ∈ (e i).baseSet) :
    iUnion e hd p = e i p :=
  iUnionFun_eq e hd hp

include hd in
/-- The inverse of the glued trivialization agrees with the corresponding local inverse. -/
theorem iUnion_symm_apply {i : ι} {p : B × F} (hp : p.1 ∈ (e i).baseSet) :
    (iUnion e hd).toOpenPartialHomeomorph.symm p =
      (e i).toOpenPartialHomeomorph.symm p :=
  iUnionInv_eq e hd hp

end DisjointUnion

section CoordChange

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, Nonempty (E x)]

/-- Reading a coordinate change from `e₁` to `e₂` back through `e₂` gives the point of the fibre
that `e₁` sends to the original fibre coordinate. -/
theorem symm_mk_coordChange (e₁ e₂ : Trivialization F (π F E)) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (v : F) :
    e₂.toOpenPartialHomeomorph.symm (b, e₁.coordChange e₂ b v) = ⟨b, e₁.symm b v⟩ := by
  rw [e₁.mk_coordChange e₂ h₁ h₂, e₂.symm_apply_apply
    (e₂.mem_source.2 (by rwa [e₁.proj_symm_apply' h₁])), e₁.mk_symm h₁]

/-- The equivalence between the fibre over a point of the base set of a trivialization and the
model fibre, given by the trivialization. Compare `Bundle.Trivialization.linearEquivAt`. -/
noncomputable def equivAt (e : Trivialization F (π F E)) (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ F where
  toFun p := (e ⟨b, p⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp [e.apply_mk_symm hb]

@[simp]
theorem equivAt_apply (e : Trivialization F (π F E)) (b : B) (hb : b ∈ e.baseSet) (p : E b) :
    e.equivAt b hb p = (e ⟨b, p⟩).2 :=
  (rfl)

@[simp]
theorem equivAt_symm_apply (e : Trivialization F (π F E)) (b : B) (hb : b ∈ e.baseSet) (v : F) :
    (e.equivAt b hb).symm v = e.symm b v :=
  (rfl)

end CoordChange

end Bundle.Trivialization

namespace Bundle.Trivialization

/-- For a trivialization `tq` of a map `q` with discrete fibre, the sheet of index `j`
over an open set `V` inside the base set, the set of points lying over `V` with fibre coordinate
`j`, is open. -/
theorem isOpen_sheet {Z B J : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    [TopologicalSpace J] [DiscreteTopology J] {q : Z → B} (tq : Trivialization J q)
    {V : Set B} (hVopen : IsOpen V) (hVsub : V ⊆ tq.baseSet) (j : J) :
    IsOpen {f : Z | q f ∈ V ∧ (tq f).2 = j} := by
  have hW : {f : Z | q f ∈ V ∧ (tq f).2 = j} = tq.source ∩ tq ⁻¹' (V ×ˢ {j}) := by
    ext f
    refine ⟨fun h => ⟨tq.mem_source.mpr (hVsub h.1), ?_⟩, fun h => ?_⟩
    · simpa [tq.coe_fst (tq.mem_source.mpr (hVsub h.1))] using And.intro h.1 h.2
    · have := h.2
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff] at this
      exact ⟨by simpa [tq.coe_fst h.1] using this.1, this.2⟩
  rw [hW]
  exact tq.continuousOn_toFun.isOpen_inter_preimage tq.open_source
    (hVopen.prod (isOpen_discrete {j}))

section SheetComparison

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {g : E → F}

/-- A point of a sheet of `p` over a set `V` inside both base sets is sent by `g` into the source
of `tq`, so its sheet index for `q` is defined. -/
theorem map_symm_mem_source (hqg : ∀ e, q (g e) = p e) {I J : Type*}
    [TopologicalSpace I] [TopologicalSpace J] (tp : Trivialization I p) (tq : Trivialization J q)
    {V : Set X} (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) (i : I) {v : X} (hv : v ∈ V) :
    g (tp.toOpenPartialHomeomorph.symm (v, i)) ∈ tq.source := by
  rw [tq.mem_source, hqg, tp.proj_symm_apply' (hVsub hv).1]
  exact (hVsub hv).2

/-- The `q`-sheet index of the image under `g` of a point of a `p`-sheet over a preconnected set
`V` is constant along the sheet, because the index is continuous and `J` is discrete. -/
theorem snd_map_symm_eq (hg : Continuous g) (hqg : ∀ e, q (g e) = p e) {I J : Type*}
    [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J] (tp : Trivialization I p)
    (tq : Trivialization J q) {V : Set X} (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) (i : I) {v x₀ : X} (hv : v ∈ V) (hx₀ : x₀ ∈ V) :
    (tq (g (tp.toOpenPartialHomeomorph.symm (v, i)))).2 =
      (tq (g (tp.toOpenPartialHomeomorph.symm (x₀, i)))).2 := by
  have hsnd : ContinuousOn (fun f : F => (tq f).2) tq.source :=
    continuous_snd.comp_continuousOn tq.continuousOn_toFun
  have h1 : ContinuousOn (fun v => g (tp.toOpenPartialHomeomorph.symm (v, i))) V :=
    hg.comp_continuousOn (tp.continuousOn_symm_prodMk_left.mono fun v hv => (hVsub hv).1)
  exact hVconn.constant (hsnd.comp h1 fun v hv => tp.map_symm_mem_source hqg tq hVsub i hv)
    hv hx₀

/-- Whether `g e` lies in the `q`-sheet of index `j` over `V` is read off the sheet index of `p`
at `e`. -/
theorem map_mem_sheet_iff (hg : Continuous g) (hqg : ∀ e, q (g e) = p e) {I J : Type*}
    [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J] (tp : Trivialization I p)
    (tq : Trivialization J q) {V : Set X} (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) {x₀ : X} (hx₀ : x₀ ∈ V) (j : J) (e : E) :
    (q (g e) ∈ V ∧ (tq (g e)).2 = j) ↔
      p e ∈ V ∧ (tq (g (tp.toOpenPartialHomeomorph.symm (x₀, (tp e).2)))).2 = j := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [hqg] at h1
    refine ⟨h1, ?_⟩
    rw [← tp.snd_map_symm_eq hg hqg tq hVconn hVsub (tp e).2 h1 hx₀,
      tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub h1).1), h2]
  · rintro ⟨h1, h2⟩
    have h3 := tp.snd_map_symm_eq hg hqg tq hVconn hVsub (tp e).2 h1 hx₀
    rw [tp.symm_apply_mk_proj (tp.mem_source.mpr (hVsub h1).1)] at h3
    exact ⟨by rw [hqg]; exact h1, by rw [h3, h2]⟩

/-- The point `tp.symm (q w, i)` of the `p`-sheet of index `i` lying over `q w` is mapped by `g`
to `w`, provided `q w` lies in a preconnected set `V` contained in both base sets and `w` is in the
`q`-sheet of index `j`, and
the image under `g` of the point of that `p`-sheet over the reference base point `x₀ ∈ V` lies in
the same `q`-sheet of index `j`. -/
theorem map_symm_eq_of_mem_sheet (hg : Continuous g) (hqg : ∀ e, q (g e) = p e)
    {I J : Type*} [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J]
    (tp : Trivialization I p) (tq : Trivialization J q) {V : Set X} (hVconn : IsPreconnected V)
    (hVsub : V ⊆ tp.baseSet ∩ tq.baseSet) {x₀ : X} (hx₀ : x₀ ∈ V) {j : J} {w : F} {i : I}
    (hw : q w ∈ V ∧ (tq w).2 = j) (hi : (tq (g (tp.toOpenPartialHomeomorph.symm (x₀, i)))).2 = j) :
    g (tp.toOpenPartialHomeomorph.symm (q w, i)) = w := by
  have h1 : q (g (tp.toOpenPartialHomeomorph.symm (q w, i))) = q w := by
    rw [hqg, tp.proj_symm_apply' (hVsub hw.1).1]
  refine tq.injOn (tp.map_symm_mem_source hqg tq hVsub i hw.1)
    (tq.mem_source.mpr (hVsub hw.1).2) (Prod.ext ?_ ?_)
  · simp only [Trivialization.coe_coe]
    rw [tq.coe_fst (tp.map_symm_mem_source hqg tq hVsub i hw.1),
      tq.coe_fst (tq.mem_source.mpr (hVsub hw.1).2), h1]
  · simp only [Trivialization.coe_coe]
    rw [tp.snd_map_symm_eq hg hqg tq hVconn hVsub i hw.1 hx₀, hi, hw.2]

end SheetComparison

end Bundle.Trivialization
