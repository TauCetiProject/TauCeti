/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension

/-!
# Krull dimension of topological spaces: open covers and closed points

This file records facts about the topological Krull dimension and the codimension of points.

The Krull dimension of a space is the supremum of the Krull dimensions of the members of an open
cover: an irreducible closed subset meeting an open subset `U` is the closure of its trace on `U`,
so every chain of irreducible closed subsets of the whole space restricts to a chain of the same
length in any open subset containing a point of its smallest member. For schemes this is what
reduces dimension computations to affine opens. Similarly, the preimage of a set under an
embedding has the Krull dimension of the part of the set lying in the range.

For the specialization preorder, defined on any topological space, the codimension
`Order.coheight x` of a point is the supremum of the lengths of the chains of proper
generalizations of `x`. On a T₀ space the specialization preorder is a partial order; there, on a
space all of whose points have codimension at most one, a point of codimension exactly one is
closed, since a proper specialization of such a point would have codimension at least two.

## Main declarations

* `TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding`: the Krull dimension of a space
  covered by the ranges of open embeddings is the supremum of the Krull dimensions of their
  domains.
* `Topology.IsEmbedding.topologicalKrullDim_preimage`: the preimage of a set under an embedding
  has the Krull dimension of the part of the set in the range.
* `TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one`: on a T₀ space all
  of whose points have codimension at most one for the specialization order, a point of
  codimension one is closed.
* `TauCeti.coheight_le_topologicalKrullDim`: the codimension of a point for the specialization
  preorder is at most the Krull dimension of the space.
* `TauCeti.topologicalKrullDim_eq_iSup_coheight`: on a quasi-sober space, the Krull dimension is
  the supremum of the codimensions of the points for the specialization preorder.
* `TauCeti.height_eq_topologicalKrullDim_closure_singleton`: on a quasi-sober space, the height
  of a point for the specialization preorder is the Krull dimension of its closure.
* `TauCeti.topologicalKrullDim_closure_singleton_le_of_not_isMax`: on a quasi-sober space all
  of whose points have codimension at most `d + 1`, the closure of a point that is not the generic
  point of an irreducible component has dimension at most `d`.
* `GeneralizingMap.coheight_apply_le_coheight`: a continuous generalizing map cannot increase
  the codimension of a point.
* `GeneralizingMap.topologicalKrullDim_le_of_surjective`: the target of a continuous, surjective,
  generalizing map to a quasi-sober space has dimension at most its source.
-/

public section

open Order Topology TopologicalSpace

namespace TauCeti

/-- The Krull dimension of a space covered by the ranges of a family of open embeddings is the
supremum of the Krull dimensions of their domains. -/
theorem topologicalKrullDim_eq_iSup_of_isOpenEmbedding {X ι : Type*} [TopologicalSpace X]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcover : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  refine le_antisymm (iSup_le fun p ↦ ?_) (iSup_le fun i ↦ (hf i).isInducing.topologicalKrullDim_le)
  -- A point `f i y` of the smallest member of the chain `p` lies in every member, so `p` is a
  -- chain of irreducible closed sets meeting the range of `f i`, hence comes from `Y i`.
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨i, y, rfl⟩ := hcover x
  let q : LTSeries {V : IrreducibleCloseds X | ((f i) ⁻¹' V).Nonempty} :=
    ⟨p.length, fun j ↦ ⟨p j, y, p.monotone (Fin.zero_le j) hx⟩, fun j ↦ p.step j⟩
  exact le_iSup_of_le i (q.map _
    (IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)).symm.strictMono).length_le_krullDim

attribute [local instance] specializationOrder in
/-- On a T₀ topological space all of whose points have codimension at most one for the
specialization order, a point of codimension one is closed. -/
theorem isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one {α : Type*}
    [TopologicalSpace α] [T0Space α]
    (hdim : ∀ y : α, coheight y ≤ 1) {x : α} (hx : coheight x = 1) :
    IsClosed ({x} : Set α) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) subset_closure
  -- `y ∈ closure {x}` says `x ⤳ y`, which is exactly `y ≤ x` in the specialization order; a
  -- strict such `y` would be a proper specialization of `x`, hence of codimension at least two.
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  rcases eq_or_ne y x with rfl | hne
  · exact Set.mem_singleton _
  refine absurd (hdim y) (not_le.mpr ?_)
  simpa [hx] using Order.coheight_strictAnti (lt_of_le_of_ne hyx hne) (by simp [hx])

attribute [local instance] specializationPreorder in
/-- The codimension of a point for the specialization preorder is at most the Krull dimension of
the space. -/
theorem coheight_le_topologicalKrullDim {α : Type*} [TopologicalSpace α] (x : α) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim α := by
  -- A chain of proper specializations `y₀ ⤳ … ⤳ yₙ` gives the chain of irreducible closed sets
  -- `closure {yₙ} ⊆ … ⊆ closure {y₀}`, strictly increasing since the specializations are proper.
  let c : α → IrreducibleCloseds α :=
    fun y ↦ ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hc : StrictMono c := fun y z hyz ↦
    lt_of_le_of_ne (specializes_iff_closure_subset.mp hyz.le) fun h ↦ hyz.not_ge
      (specializes_iff_closure_subset.mpr (congrArg SetLike.coe h).ge)
  exact (coheight_le_krullDim x).trans (krullDim_le_of_strictMono c hc)

attribute [local instance] specializationPreorder in
/-- On a quasi-sober topological space, the Krull dimension is the supremum of the codimensions of
the points for the specialization preorder: generic points of a chain of irreducible closed
subsets form a chain of proper generalizations. -/
theorem topologicalKrullDim_eq_iSup_coheight (α : Type*) [TopologicalSpace α] [QuasiSober α] :
    topologicalKrullDim α = ⨆ x : α, (coheight x : WithBot ℕ∞) := by
  refine le_antisymm ?_ (iSup_le coheight_le_topologicalKrullDim)
  -- Choosing a generic point of each irreducible closed subset is strictly monotone.
  let g : IrreducibleCloseds α → α := fun s ↦ s.isIrreducible.genericPoint
  have hg (s : IrreducibleCloseds α) : closure {g s} = s :=
    s.isIrreducible.closure_genericPoint s.isClosed
  have hmono : StrictMono g := fun s t hst ↦ lt_of_le_not_ge
    (specializes_iff_closure_subset.mpr (by rw [hg, hg]; exact hst.le)) fun h ↦
      hst.not_ge (by simpa only [hg, SetLike.coe_subset_coe] using
        specializes_iff_closure_subset.mp h)
  rw [← krullDim_eq_iSup_coheight]
  exact krullDim_le_of_strictMono g hmono

attribute [local instance] specializationPreorder in
/-- On a quasi-sober topological space, the height of a point for the specialization preorder
(`x ≤ y ↔ y ⤳ x`) is the Krull dimension of its closure: the points below `x` are the points of
`closure {x}`, and chains of them correspond to chains of irreducible closed subsets of it. -/
theorem height_eq_topologicalKrullDim_closure_singleton {α : Type*} [TopologicalSpace α]
    [QuasiSober α] (x : α) :
    (height x : WithBot ℕ∞) = topologicalKrullDim (closure ({x} : Set α)) := by
  have : QuasiSober (closure ({x} : Set α)) :=
    isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  have hle {y : α} (hy : y ≤ x) : y ∈ closure ({x} : Set α) := specializes_iff_mem_closure.mp hy
  rw [height_eq_krullDim_Iic, topologicalKrullDim]
  refine le_antisymm ?_ ?_
  · -- A chain of points below `x` gives the chain of closures of these points inside the closure.
    let q : Set.Iic x → closure ({x} : Set α) := fun y ↦ ⟨y.1, hle y.2⟩
    refine krullDim_le_of_strictMono (fun y ↦ (⟨closure {q y}, isIrreducible_singleton.closure,
      isClosed_closure⟩ : IrreducibleCloseds (closure ({x} : Set α)))) fun y z hyz ↦ ?_
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp ?_) fun h ↦ hyz.not_ge ?_
    · exact (IsInducing.subtypeVal.specializes_iff (x := q z) (y := q y)).mp hyz.le
    · exact (IsInducing.subtypeVal.specializes_iff (x := q y) (y := q z)).mpr
        (specializes_iff_closure_subset.mpr (congrArg SetLike.coe h).ge)
  · -- Generic points of a chain of irreducible closed subsets of the closure lie below `x`.
    let g : IrreducibleCloseds (closure ({x} : Set α)) → closure ({x} : Set α) := fun s ↦
      s.isIrreducible.genericPoint
    have hg (s : IrreducibleCloseds (closure ({x} : Set α))) : closure {g s} = s :=
      s.isIrreducible.closure_genericPoint s.isClosed
    refine krullDim_le_of_strictMono
      (fun s ↦ (⟨(g s : α), specializes_iff_mem_closure.mpr (g s).2⟩ : Set.Iic x))
      fun s t hst ↦ lt_of_le_not_ge ?_ fun h ↦ hst.not_ge ?_
    · exact (IsInducing.subtypeVal.specializes_iff (x := g t) (y := g s)).mpr
        (specializes_iff_closure_subset.mpr (by rw [hg, hg]; exact hst.le))
    · have := (IsInducing.subtypeVal.specializes_iff (x := g s) (y := g t)).mp h
      simpa only [hg, SetLike.coe_subset_coe] using specializes_iff_closure_subset.mp this

attribute [local instance] specializationPreorder in
/-- On a quasi-sober topological space all of whose points have codimension at most `d + 1`
for the specialization preorder, the closure of a point `x` which is not maximal, that is, not
the generic point of an irreducible component, has Krull dimension at most `d`: a chain of
specializations of `x` extends by a proper generalization of `x`. For instance, a prime divisor on
a scheme of dimension at most two is a curve. -/
theorem topologicalKrullDim_closure_singleton_le_of_not_isMax {α : Type*} [TopologicalSpace α]
    [QuasiSober α] {d : ℕ} (hdim : ∀ y : α, coheight y ≤ d + 1) {x : α}
    (hx : ¬IsMax x) : topologicalKrullDim (closure ({x} : Set α)) ≤ d := by
  rw [← height_eq_topologicalKrullDim_closure_singleton]
  obtain ⟨y, hxy⟩ := not_isMax_iff.mp hx
  refine WithBot.coe_le_coe.mpr (height_le_iff'.mpr fun p hp ↦ ?_)
  -- Extending a chain of specializations ending at `x` by `y` gives a longer chain.
  have := (length_le_coheight_head (p := p.snoc y (hp ▸ hxy))).trans (hdim _)
  simp only [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one] at this
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this

end TauCeti

attribute [local instance] specializationPreorder in
/-- A continuous generalizing map cannot increase the coheight of a point for the specialization
preorders: chains of proper generalizations lift along the map. -/
theorem GeneralizingMap.coheight_apply_le_coheight {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : GeneralizingMap f) (hcont : Continuous f) (x : X) :
    coheight (f x) ≤ coheight x := by
  refine coheight_le_iff'.mpr fun p hp ↦ ?_
  induction p using RelSeries.inductionOn generalizing x with
  | singleton y => simp
  | cons p y hy ih =>
    simp only [RelSeries.head_cons] at hp
    have hlt : f x < p.head := hp ▸ hy
    obtain ⟨x', hx', hfx'⟩ := hf hlt.le
    have hx : x < x' := lt_of_le_not_ge hx' fun h ↦
      hlt.not_ge (by simpa [hfx'] using hcont.specialization_monotone h)
    grw [RelSeries.cons_length, Nat.cast_add, Nat.cast_one, ih x' hfx'.symm]
    exact coheight_add_one_le hx

attribute [local instance] specializationPreorder in
/-- The target of a continuous, surjective, generalizing map to a quasi-sober space has Krull
dimension at most that of the source. -/
theorem GeneralizingMap.topologicalKrullDim_le_of_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober Y]
    {f : X → Y} (hf : GeneralizingMap f) (hcont : Continuous f)
    (hsurj : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rw [TauCeti.topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact (WithBot.coe_le_coe.mpr (hf.coheight_apply_le_coheight hcont x)).trans
    (TauCeti.coheight_le_topologicalKrullDim x)

attribute [local instance] specializationPreorder in
/-- Along an open embedding `f`, the coheight of a point `x` of a subset `T` of the source, in the
specialization order of `T`, is the coheight of `f x` in a subset `F` of the target with
`v ∈ T ↔ f v ∈ F`: open sets are closed under generization, so chains of generizations in `F` lift
to `T`. For `T = f ⁻¹' F` this is the subset version of `Topology.IsOpenEmbedding.coheight_eq`. -/
theorem Topology.IsOpenEmbedding.coheight_subtype_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenEmbedding f) {T : Set X} {F : Set Y}
    (hTF : ∀ v, v ∈ T ↔ f v ∈ F) {x : X} (hx : x ∈ T) :
    coheight (⟨x, hx⟩ : T) = coheight (⟨f x, (hTF x).1 hx⟩ : F) := by
  have hlt {a b : X} : f a < f b ↔ a < b :=
    and_congr hf.isInducing.specializes_iff (not_congr hf.isInducing.specializes_iff)
  refine coheight_eq_of_strictMono (fun v : T ↦ (⟨f v, (hTF v).1 v.2⟩ : F))
    (fun _ _ h ↦ Subtype.coe_lt_coe.mp (hlt.mpr h)) (fun v b h ↦ ?_) _
  obtain ⟨v', hv'⟩ : (b : Y) ∈ Set.range f :=
    h.le.mem_open hf.isOpen_range ⟨v, rfl⟩
  exact ⟨⟨v', (hTF v').2 (hv' ▸ b.2)⟩, hlt.mp (by rw [hv']; exact h), Subtype.ext hv'⟩

namespace Topology.IsEmbedding

/-- The preimage of a set `Z` under an embedding `e` is homeomorphic to the part of `Z` in the
range of `e`, so the two have the same Krull dimension. -/
theorem topologicalKrullDim_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : Y → X} (he : IsEmbedding e) (Z : Set X) :
    topologicalKrullDim ↥(e ⁻¹' Z) = topologicalKrullDim ↥(Z ∩ Set.range e) := by
  rw [← Set.preimage_inter_range]
  exact (he.homeomorphOfSubsetRange Set.inter_subset_right).isHomeomorph.topologicalKrullDim_eq

end Topology.IsEmbedding
