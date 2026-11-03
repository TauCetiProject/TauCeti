/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.ShrinkingLemma

/-!
# Small cofinal systems of open covers

Point-neighborhood covers of a space `X : Type u` form a `u`-small system: their index type
is `X` itself. Every `u`-small open cover admits a refinement of this form, and pointwise
intersection supplies common refinements. On a compact space, the `u`-small system of covers
indexed by `ULift (Fin n)` is also cofinal. Compactness alone suffices; no separation axiom
is needed.

On a normal space, for a finite open cover `U` and a choice of a neighborhood `N x` of each point
`x`, there is a point-neighborhood cover `W` with `W x ⊆ U (r x) ∩ N x` whose overlaps are
controlled by `U`: `x ∈ U (r z)` whenever `W x` meets `W z`. This is the shrinking argument used to
kill Čech cochains of locally zero presheaves by refinement.

Both systems are preorders ordered towards finer covers. The relation remembers only the
existence of a refinement, whereas an actual refinement is a native `FormalCoproduct` morphism.
Consequently these preorders are filtered, hence connected, categories, without asserting
filteredness of the category of actual refinement functions. They provide small indexing
categories for colimits of cover-dependent invariants whose transition maps are independent of
refinement functions.
Finite covers retain repeated members and include the empty cover of the empty space.

The cover-refinement description follows the Stacks Project, Cohomology of Sheaves, §20.15
(tag 09UY). Finite cofinality is the compactness argument of J. Pardon, arXiv:1309.2370v6,
Appendix A, Lemma A.4.4, here without separation or local compactness assumptions.
-/

public section

open CategoryTheory Limits TopologicalSpace Topology

universe u

namespace TauCeti.Topology

/-- An open neighborhood of each point, regarded as a cover indexed by the points themselves. -/
@[ext]
structure PointOpenCover (X : Type u) [TopologicalSpace X] where
  /-- The open neighborhood assigned to a point. -/
  opens : X → Opens X
  /-- Each point belongs to its assigned open. -/
  mem_opens (x : X) : x ∈ opens x

namespace PointOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- The native family underlying a point-neighborhood cover. -/
@[simps]
abbrev toFormalCoproduct (U : PointOpenCover X) : FormalCoproduct.{u} (Opens X) :=
  ⟨X, U.opens⟩

/-- The assigned neighborhoods cover the whole space. -/
theorem isOpenCover (U : PointOpenCover X) : IsOpenCover U.opens :=
  top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, U.mem_opens x⟩

/-- The refinement preorder points towards finer covers; it forgets the refinement function. -/
instance : Preorder (PointOpenCover X) where
  le U V := Nonempty (V.toFormalCoproduct ⟶ U.toFormalCoproduct)
  le_refl U := ⟨𝟙 _⟩
  le_trans _ _ _ hUV hVW := ⟨hVW.some ≫ hUV.some⟩

/-- Comparison of point-neighborhood covers means existence of an actual refinement. -/
theorem le_iff (U V : PointOpenCover X) :
    U ≤ V ↔ Nonempty (V.toFormalCoproduct ⟶ U.toFormalCoproduct) := Iff.rfl

/-- Intersecting the neighborhoods at each point gives a common refinement. -/
def inter (U V : PointOpenCover X) : PointOpenCover X where
  opens x := U.opens x ⊓ V.opens x
  mem_opens x := ⟨U.mem_opens x, V.mem_opens x⟩

@[simp]
theorem inter_opens (U V : PointOpenCover X) (x : X) :
    (U.inter V).opens x = U.opens x ⊓ V.opens x := (rfl)

/-- The pointwise intersection refines the first cover. -/
theorem le_inter_left (U V : PointOpenCover X) : U ≤ U.inter V :=
  ⟨⟨id, fun _ ↦ homOfLE inf_le_left⟩⟩

/-- The pointwise intersection refines the second cover. -/
theorem le_inter_right (U V : PointOpenCover X) : V ≤ U.inter V :=
  ⟨⟨id, fun _ ↦ homOfLE inf_le_right⟩⟩

instance : IsDirectedOrder (PointOpenCover X) where
  directed U V := ⟨U.inter V, U.le_inter_left V, U.le_inter_right V⟩

instance : Inhabited (PointOpenCover X) := ⟨⟨fun _ ↦ ⊤, fun _ ↦ trivial⟩⟩

/-- As a nonempty directed preorder, the point-neighborhood covers form a connected category. -/
instance : IsConnected (PointOpenCover X) := IsFiltered.isConnected _

/-- Every small open cover admits a point-neighborhood refinement. This also applies to the
empty cover of the empty space: no nonempty index type is required. -/
theorem exists_refinement {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) :
    ∃ V : PointOpenCover X,
      Nonempty (V.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) := by
  classical
  choose a ha using hU.exists_mem
  exact ⟨⟨fun x ↦ U (a x), ha⟩, ⟨⟨a, fun _ ↦ 𝟙 _⟩⟩⟩

/-- **Point-neighborhood refinements with controlled overlaps.** On a normal space, for a finite
open cover `U` and a neighborhood `N x` of each point `x`, there is a point-neighborhood cover `W`,
with `W x ⊆ U (r x)` and `W x ⊆ N x`, such that `x ∈ U (r z)` whenever `W x` and `W z` meet. Thus a
nonempty intersection `W x₀ ∩ ⋯ ∩ W xₙ` lies in `W x₀`, whose point `x₀` lies in each `U (r xₖ)`. -/
theorem exists_refinement_mem_of_mem_of_mem [NormalSpace X] {ι : Type*} [Finite ι]
    (U : ι → Opens X) (hU : IsOpenCover U) {N : X → Set X} (hN : ∀ x, N x ∈ 𝓝 x) :
    ∃ (W : PointOpenCover X) (r : X → ι), (∀ x, W.opens x ≤ U (r x) ∧ ↑(W.opens x) ⊆ N x) ∧
      ∀ x y z, y ∈ W.opens x → y ∈ W.opens z → x ∈ U (r z) := by
  -- shrink `U` to opens `v i` with `closure (v i) ⊆ U i`, and choose `x ∈ v (r x)`
  obtain ⟨v, hvU, hvo, hvc⟩ := exists_iUnion_eq_closure_subset (u := fun i ↦ (U i : Set X))
    (fun i ↦ (U i).isOpen) (fun _ ↦ Set.toFinite _) hU.iSup_set_eq_univ
  choose r hr using fun x : X ↦ Set.mem_iUnion.1 (hvU ▸ Set.mem_univ x)
  -- `W x` lies in `v (r x)` and in `N x`, and misses every `closure (v i)` not containing `x`
  have key (x : X) : ∃ W : Opens X, x ∈ W ∧ ∀ y ∈ W, y ∈ v (r x) ∧ y ∈ N x ∧
      ∀ i, x ∉ closure (v i) → y ∉ closure (v i) := by
    have h : ∀ᶠ y in 𝓝 x, ∀ i, x ∉ closure (v i) → y ∉ closure (v i) :=
      Filter.eventually_all.2 fun i ↦ Filter.eventually_imp_distrib_left.2
        (isClosed_closure.isOpen_compl.mem_nhds ·)
    obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 <|
      Filter.inter_mem ((hvo _).mem_nhds (hr x)) (Filter.inter_mem (hN x) h)
    exact ⟨⟨t, hto⟩, hxt, ht⟩
  choose W hxW hW using key
  refine ⟨⟨W, hxW⟩, r, fun x ↦ ⟨fun y hy ↦ hvc _ (subset_closure (hW x y hy).1),
    fun y hy ↦ (hW x y hy).2.1⟩, fun x y z hx hz ↦ hvc _ ?_⟩
  -- `y ∈ v (r z)` lies in `closure (v (r z))`, which `W x` would miss unless it contains `x`
  by_contra h
  exact (hW x y hx).2.2 _ h (subset_closure (hW z y hz).1)

end PointOpenCover

/-- A finite indexed open cover. The lifted index type lives in the universe of `X`, so the
collection of all these covers is small in that same universe. Repetitions are allowed. -/
@[ext]
structure FiniteOpenCover (X : Type u) [TopologicalSpace X] where
  /-- The number of indexed members, possibly zero. -/
  n : ℕ
  /-- The indexed opens; different indices may name the same open. -/
  opens : ULift.{u} (Fin n) → Opens X
  /-- The members cover the whole space. -/
  isOpenCover : IsOpenCover opens

namespace FiniteOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- The native family underlying a finite indexed cover. -/
@[simps]
abbrev toFormalCoproduct (U : FiniteOpenCover X) : FormalCoproduct.{u} (Opens X) :=
  ⟨ULift (Fin U.n), U.opens⟩

/-- Finite covers are ordered towards finer covers, forgetting the refinement function. -/
instance : Preorder (FiniteOpenCover X) where
  le U V := Nonempty (V.toFormalCoproduct ⟶ U.toFormalCoproduct)
  le_refl U := ⟨𝟙 _⟩
  le_trans _ _ _ hUV hVW := ⟨hVW.some ≫ hUV.some⟩

/-- Comparison of finite indexed covers means existence of an actual refinement. -/
theorem le_iff (U V : FiniteOpenCover X) :
    U ≤ V ↔ Nonempty (V.toFormalCoproduct ⟶ U.toFormalCoproduct) := Iff.rfl

instance : Inhabited (FiniteOpenCover X) :=
  ⟨⟨1, fun _ ↦ ⊤, by simp [IsOpenCover]⟩⟩

/-- Any cover with a finite index type can be enumerated by a lifted `Fin n`, preserving the
entire indexed family up to a native formal-coproduct isomorphism. -/
theorem exists_iso {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : IsOpenCover U) :
    ∃ V : FiniteOpenCover X,
      Nonempty (V.toFormalCoproduct ≅ FormalCoproduct.mk ι U) := by
  classical
  let := Fintype.ofFinite ι
  let e : ULift.{u} (Fin (Fintype.card ι)) ≃ ι :=
    Equiv.ulift.trans (Fintype.equivFin ι).symm
  let V : FiniteOpenCover X :=
    ⟨Fintype.card ι, fun i ↦ U (e i), e.iSup_comp.trans hU.iSup_eq_top⟩
  exact ⟨V, ⟨FormalCoproduct.isoOfComponents e (fun _ ↦ Iso.refl _)⟩⟩

/-- On a compact space every small open cover admits a finite indexed refinement. The finite
subcover is enumerated without excluding the empty subcover. -/
theorem exists_refinement [CompactSpace X] {ι : Type u} (U : ι → Opens X)
    (hU : IsOpenCover U) :
    ∃ V : FiniteOpenCover X,
      Nonempty (V.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) := by
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  obtain ⟨V, ⟨e⟩⟩ := exists_iso (fun i : s ↦ U i) hs
  exact ⟨V, ⟨e.hom ≫ ⟨Subtype.val, fun _ ↦ 𝟙 _⟩⟩⟩

/-- Any two finite covers have a common finite refinement, without a compactness hypothesis. -/
instance : IsDirectedOrder (FiniteOpenCover X) where
  directed U V := by
    let W (i : ULift.{u} (Fin U.n) × ULift.{u} (Fin V.n)) := U.opens i.1 ⊓ V.opens i.2
    have hW : ⨆ i, W i = ⊤ := by
      dsimp [W]
      rw [← iSup_inf_iSup, U.isOpenCover.iSup_eq_top, V.isOpenCover.iSup_eq_top, inf_top_eq]
    obtain ⟨T, ⟨e⟩⟩ := exists_iso W hW
    exact ⟨T, ⟨e.hom ≫ ⟨Prod.fst, fun _ ↦ homOfLE inf_le_left⟩⟩,
      ⟨e.hom ≫ ⟨Prod.snd, fun _ ↦ homOfLE inf_le_right⟩⟩⟩

/-- As a nonempty directed preorder, the finite covers form a connected category. -/
instance : IsConnected (FiniteOpenCover X) := IsFiltered.isConnected _

/-- The empty indexed family is a cover of the empty space. -/
def empty [IsEmpty X] : FiniteOpenCover X where
  n := 0
  opens i := Fin.elim0 i.down
  isOpenCover := Subsingleton.elim _ _

@[simp]
theorem empty_n [IsEmpty X] : (empty : FiniteOpenCover X).n = 0 := (rfl)

/-- The empty cover refines every cover of the empty space, so it is a greatest element in the
refinement preorder. This permits colimits to detect vanishing even for presheaves nonzero on
the empty open. -/
theorem le_empty [IsEmpty X] (U : FiniteOpenCover X) : U ≤ empty :=
  ⟨⟨fun i ↦ Fin.elim0 i.down, fun i ↦ Fin.elim0 i.down⟩⟩

end FiniteOpenCover

end TauCeti.Topology
