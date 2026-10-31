/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Dedup

/-!
# Functors on finite subsets from edge maps with commuting square faces

A commutative cube indexed by a type `ι` in a category `C` is a functor `Finset ι ⥤ C` on the
finite subsets of `ι`, ordered by inclusion. In practice such a cube is given by its edges: an
object `X S` for every vertex `S` and a morphism `X S ⟶ X T` for every covering relation `S ⋖ T`,
that is, for `T = insert a S` with `a ∉ S`. The only condition is that every square face commutes:
the two routes `S ⋖ T₁ ⋖ U` and `S ⋖ T₂ ⋖ U` give the same composite. This file constructs the
functor `CategoryTheory.Functor.ofCubeEdges` from such data. Its morphism for `S ⊆ T` composes the
edges along a maximal chain from `S` to `T`; the square condition makes this independent of the
chain, since any two orderings of the elements of `T \ S` are related by adjacent transpositions.

Morphisms of cubes are checked on edges too, by `CategoryTheory.NatTrans.ofCovBy` in
`TauCeti.CategoryTheory.Category.Preorder`.

This is the form in which the cube of resolutions of a link diagram is defined: the edge maps are
the merge and split maps of the two smoothings at one crossing, and the commuting faces are the
associativity, coassociativity and Frobenius relations. The resulting functor is the input of the
signed totalization `CategoryTheory.Functor.cubeComplex`.

## Main definitions

* `CategoryTheory.Functor.ofCubeEdges`: the functor `Finset ι ⥤ C` with prescribed covering edges,
  characterised by `Functor.ofCubeEdges_obj`, `Functor.ofCubeEdges_map` and
  `Functor.ofCubeEdges_map_homOfLE_of_covBy`.

## References

The construction follows the pattern of Mathlib's `CategoryTheory.Functor.ofSequence` (Joël Riou,
`Mathlib.CategoryTheory.Functor.OfSequence`), which builds a functor on `ℕ` from its successor maps.

* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

open Finset

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {ι : Type w} [DecidableEq ι]

namespace Functor

namespace OfCubeEdges

/-- `IsChain S T l` says that inserting the elements of `l` into `S` one at a time, each new,
reaches `T`. -/
private def IsChain : Finset ι → Finset ι → List ι → Prop
  | S, T, [] => S = T
  | S, T, a :: l => a ∉ S ∧ IsChain (insert a S) T l

private theorem isChain_nil_iff {S T : Finset ι} : IsChain S T [] ↔ S = T := Iff.rfl

private theorem isChain_iff {S T : Finset ι} {l : List ι} :
    IsChain S T l ↔ l.Nodup ∧ (∀ a ∈ l, a ∉ S) ∧ S ∪ l.toFinset = T := by
  induction l generalizing S with
  | nil => simp [isChain_nil_iff]
  | cons a l ih =>
    simp only [IsChain, ih, List.nodup_cons, List.mem_cons, List.toFinset_cons, mem_insert,
      not_or, forall_eq_or_imp, insert_union, union_insert]
    constructor
    · rintro ⟨ha, hl, hS, rfl⟩
      exact ⟨⟨fun h ↦ (hS a h).1 rfl, hl⟩, ⟨ha, fun b hb ↦ (hS b hb).2⟩, rfl⟩
    · rintro ⟨⟨ha, hl⟩, ⟨haS, hS⟩, rfl⟩
      exact ⟨haS, hl, fun b hb ↦ ⟨fun h ↦ ha (h ▸ hb), hS b hb⟩, rfl⟩

private theorem isChain_nil (S : Finset ι) : IsChain S S [] := isChain_nil_iff.2 rfl

private theorem isChain_singleton {S : Finset ι} {a : ι} (ha : a ∉ S) :
    IsChain S (insert a S) [a] :=
  ⟨ha, rfl⟩

private theorem isChain_toList_sdiff {S T : Finset ι} (h : S ⊆ T) :
    IsChain S T (T \ S).toList :=
  isChain_iff.2 ⟨nodup_toList _, fun a ha ↦ (mem_sdiff.1 (mem_toList.1 ha)).2, by
    rw [toList_toFinset, union_sdiff_of_subset h]⟩

private theorem isChain_append {S T U : Finset ι} {l l' : List ι} (h : IsChain S T l)
    (h' : IsChain T U l') : IsChain S U (l ++ l') := by
  induction l generalizing S with
  | nil => exact isChain_nil_iff.1 h ▸ h'
  | cons a l ih => exact ⟨h.1, ih h.2⟩

/-- Any two chains from `S` to `T` are permutations of each other. -/
private theorem IsChain.perm {S T : Finset ι} {l l' : List ι} (h : IsChain S T l)
    (h' : IsChain S T l') : l.Perm l' := by
  obtain ⟨hl, hlS, rfl⟩ := isChain_iff.1 h
  obtain ⟨hl', hlS', e⟩ := isChain_iff.1 h'
  refine List.perm_of_nodup_nodup_toFinset_eq hl hl' ?_
  rw [← union_sdiff_cancel_left (disjoint_left.2 fun a haS ha ↦ hlS a (List.mem_toFinset.1 ha)
    haS), ← e, union_sdiff_cancel_left (disjoint_left.2 fun a haS ha ↦
    hlS' a (List.mem_toFinset.1 ha) haS)]

private theorem isChain_of_perm {S T : Finset ι} {l l' : List ι} (hl : l.Perm l')
    (h : IsChain S T l) : IsChain S T l' := by
  obtain ⟨hn, hS, e⟩ := isChain_iff.1 h
  exact isChain_iff.2 ⟨hl.nodup_iff.1 hn, fun a ha ↦ hS a (hl.mem_iff.2 ha),
    List.toFinset_eq_of_perm _ _ hl ▸ e⟩

variable (X : Finset ι → C) (d : ∀ ⦃S T : Finset ι⦄, S ⋖ T → (X S ⟶ X T))

/-- The composite of the edges `d` along a chain from `S` to `T`. -/
private def chainMap : ∀ (S T : Finset ι) (l : List ι), IsChain S T l → (X S ⟶ X T)
  | _, _, [], h => eqToHom (congrArg X h)
  | S, T, a :: l, h => d (covBy_insert h.1) ≫ chainMap (insert a S) T l h.2

private theorem chainMap_append {S T U : Finset ι} (l l' : List ι) (h : IsChain S T l)
    (h' : IsChain T U l') :
    chainMap X d S T l h ≫ chainMap X d T U l' h' =
      chainMap X d S U (l ++ l') (isChain_append h h') := by
  induction l generalizing S with
  | nil =>
    obtain rfl := isChain_nil_iff.1 h
    simp [chainMap]
  | cons a l ih => simp [chainMap, ih]

private theorem chainMap_congr {S T : Finset ι} {l l' : List ι} (e : l = l') (h : IsChain S T l)
    (h' : IsChain S T l') : chainMap X d S T l h = chainMap X d S T l' h' := by
  subst e
  rfl

private theorem chainMap_eq_eqToHom_comp {S S' T : Finset ι} (e : S = S') (l : List ι)
    (h : IsChain S T l) (h' : IsChain S' T l) :
    chainMap X d S T l h = eqToHom (congrArg X e) ≫ chainMap X d S' T l h' := by
  subst e
  simp

omit [DecidableEq ι] in
private theorem edge_eq_comp_eqToHom {S T T' : Finset ι} (h : S ⋖ T) (h' : S ⋖ T') (e : T = T') :
    d h' = d h ≫ eqToHom (congrArg X e) := by
  subst e
  simp

variable {X d}

/-- If every square face of edges commutes, the composite along a chain from `S` to `T` does not
depend on the chain. -/
private theorem chainMap_eq
    (comm : ∀ ⦃S T₁ T₂ U : Finset ι⦄ (h₁ : S ⋖ T₁) (h₁' : T₁ ⋖ U) (h₂ : S ⋖ T₂) (h₂' : T₂ ⋖ U),
      d h₁ ≫ d h₁' = d h₂ ≫ d h₂')
    {S T : Finset ι} {l l' : List ι} (h : IsChain S T l) (h' : IsChain S T l') :
    chainMap X d S T l h = chainMap X d S T l' h' := by
  induction h.perm h' generalizing S with
  | nil => rfl
  | cons a _ ih => simp only [chainMap, ih h.2 h'.2]
  | swap a b l =>
    obtain ⟨hb, ha, hl⟩ := h
    obtain ⟨ha', hb', hl'⟩ := h'
    have e : insert b (insert a S) = insert a (insert b S) := insert_comm b a S
    -- Reindex the route through `insert a S` so that both routes end at the same vertex; then the
    -- two first edges form a square face.
    have edge : d (covBy_insert hb') ≫ eqToHom (congrArg X e) = d (e ▸ covBy_insert hb') :=
      (edge_eq_comp_eqToHom X d _ _ e).symm
    have square := comm (covBy_insert hb) (covBy_insert ha) (covBy_insert ha')
      (e ▸ covBy_insert hb')
    simp only [chainMap, chainMap_eq_eqToHom_comp X d e l hl' hl, reassoc_of% edge,
      reassoc_of% square]
  | trans p₁ _ ih₁ ih₂ =>
    have h₂ := isChain_of_perm p₁ h
    exact (ih₁ h h₂).trans (ih₂ h₂ h')

variable (X d) in
/-- The morphism `X S ⟶ X T` for `S ⊆ T` composing the edges `d` along a maximal chain from `S`
to `T`, inserting the elements of `T \ S` one at a time. This is the morphism of
`Functor.ofCubeEdges`. -/
def map {S T : Finset ι} (h : S ⊆ T) : X S ⟶ X T :=
  chainMap X d S T (T \ S).toList (isChain_toList_sdiff h)

/-- The composite along the empty chain is the identity. -/
theorem map_id (S : Finset ι) : map X d (subset_refl S) = 𝟙 (X S) :=
  (chainMap_congr X d (by simp) _ (isChain_nil S)).trans (eqToHom_refl _ _)

/-- The composite along a covering relation is its edge. -/
theorem map_of_covBy {S T : Finset ι} (h : S ⋖ T) : map X d h.le = d h := by
  obtain ⟨a, ha, rfl⟩ := covBy_iff_exists_insert.1 h
  exact (chainMap_congr X d (by simp [insert_sdiff_of_notMem _ ha]) _
    (isChain_singleton ha)).trans (Category.comp_id _)

/-- If every square face of edges commutes, the composite of the edges along a maximal chain is
functorial. -/
theorem map_comp
    (comm : ∀ ⦃S T₁ T₂ U : Finset ι⦄ (h₁ : S ⋖ T₁) (h₁' : T₁ ⋖ U) (h₂ : S ⋖ T₂) (h₂' : T₂ ⋖ U),
      d h₁ ≫ d h₁' = d h₂ ≫ d h₂')
    {S T U : Finset ι} (h : S ⊆ T) (h' : T ⊆ U) : map X d h ≫ map X d h' = map X d (h.trans h') :=
  (chainMap_append X d _ _ _ _).trans (chainMap_eq comm _ _)

end OfCubeEdges

variable (X : Finset ι → C) (d : ∀ ⦃S T : Finset ι⦄, S ⋖ T → (X S ⟶ X T))
  (comm : ∀ ⦃S T₁ T₂ U : Finset ι⦄ (h₁ : S ⋖ T₁) (h₁' : T₁ ⋖ U) (h₂ : S ⋖ T₂) (h₂' : T₂ ⋖ U),
    d h₁ ≫ d h₁' = d h₂ ≫ d h₂')

/-- The commutative cube `Finset ι ⥤ C` with vertices `X S` and edge maps `d h : X S ⟶ X T` for
the covering relations `h : S ⋖ T`, assuming every square face of edges commutes. The morphism
for `S ⊆ T` composes the edges along any maximal chain from `S` to `T`. -/
-- Exposed so that `(ofCubeEdges X d comm).obj S` is definitionally `X S` for importers: the edge
-- lemma `ofCubeEdges_map_homOfLE_of_covBy` and every use of the cube on its edges rely on it.
@[expose, simps obj]
def ofCubeEdges : Finset ι ⥤ C where
  obj := X
  map f := OfCubeEdges.map X d (leOfHom f)
  map_id S := OfCubeEdges.map_id S
  map_comp f g := (OfCubeEdges.map_comp comm (leOfHom f) (leOfHom g)).symm

/-- The cube `Functor.ofCubeEdges` sends `S ⊆ T` to the composite of the edges along a maximal
chain from `S` to `T`. -/
theorem ofCubeEdges_map {S T : Finset ι} (f : S ⟶ T) :
    (ofCubeEdges X d comm).map f = OfCubeEdges.map X d (leOfHom f) :=
  rfl

/-- The cube `Functor.ofCubeEdges` sends each covering relation to its prescribed edge map. -/
@[simp]
theorem ofCubeEdges_map_homOfLE_of_covBy {S T : Finset ι} (h : S ⋖ T) :
    (ofCubeEdges X d comm).map (homOfLE h.le) = d h :=
  OfCubeEdges.map_of_covBy h

end Functor

end CategoryTheory
