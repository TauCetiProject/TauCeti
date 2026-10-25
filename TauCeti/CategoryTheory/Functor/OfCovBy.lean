/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Data.Finset.Grade

/-!
# Functors on finite subsets from their edge maps

A functor `F : Finset ι ⥤ C` out of the finite subsets of `ι`, ordered by inclusion, is a
commutative cube: a vertex `F(S)` for every finite subset `S`, an edge map `F(S) ⟶ F(T)` for
every covering pair `S ⋖ T` (that is, `T = S ∪ {a}` with `a ∉ S`), and commuting square faces.
This file shows that this data presents the functor: the edge maps can be prescribed freely,
subject only to the commutativity of the square faces, and they determine everything else.

In the cubes of resolutions of link diagrams the edge maps are merges and splits of circles,
which are only specified along edges; the constructions here turn such edge data, together with
the commutativity of the faces, into a functor to which the signed totalization
`CategoryTheory.Functor.cubeComplex` applies. Maps of cubes are likewise specified on vertices
and checked along edges.

## Main definitions

* `CategoryTheory.Functor.ofCovBy f comm`: the functor `Finset ι ⥤ C` with vertices `X` and edge
  maps `f`, given that the two routes `S ⋖ T ⋖ U` and `S ⋖ T' ⋖ U` around every square face
  agree (`comm`). The map along `S ⊆ T` composes the edge maps along any maximal chain from `S`
  to `T`.
* `CategoryTheory.NatTrans.ofCovBy app naturality`: a natural transformation between functors
  `Finset ι ⥤ C`, from its components and naturality along the edges only.

## Main results

* `CategoryTheory.Functor.ofCovBy_map_of_covBy`, `CategoryTheory.Functor.ofCovBy_map_insert`:
  the edge maps of `Functor.ofCovBy f comm` are those of `f`.
* `CategoryTheory.Functor.ext_of_covBy`: two functors `Finset ι ⥤ C` agreeing on vertices and
  edge maps are equal, so `Functor.ofCovBy f comm` is the only functor with vertices `X` and edge
  maps `f`.

The analogous constructions for functors out of `ℕ` are `CategoryTheory.Functor.ofSequence` and
`CategoryTheory.NatTrans.ofSequence`.
-/

public section

open Finset

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {ι : Type*}

section DecidableEq

variable [DecidableEq ι]

/-- Removing an element `a ∈ T \ S` lowers the number of elements of `T` outside `S` by one. -/
private theorem card_sdiff_insert_add_one {S T : Finset ι} {a : ι} (ha : a ∈ T \ S) :
    #(T \ insert a S) + 1 = #(T \ S) := by
  rw [sdiff_insert, card_erase_add_one ha]

/-- Downward induction on `S ⊆ T`: a property holding at `T`, and passing from `S ∪ {a}` to `S`,
holds for every `S ⊆ T`. -/
private theorem subset_induction {T : Finset ι} {P : ∀ S, S ⊆ T → Prop}
    (self : P T Subset.rfl)
    (step : ∀ S a, a ∉ S → ∀ h : insert a S ⊆ T,
      P (insert a S) h → P S ((S.subset_insert a).trans h)) (S : Finset ι) (h : S ⊆ T) :
    P S h := by
  induction hk : #(T \ S) generalizing S with
  | zero =>
    obtain rfl := Subset.antisymm h (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hk))
    exact self
  | succ k ih =>
    obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < #(T \ S))
    have h' : insert a S ⊆ T := insert_subset (mem_sdiff.1 ha).1 h
    exact step S a (mem_sdiff.1 ha).2 h'
      (ih _ h' (by have := card_sdiff_insert_add_one ha; omega))

end DecidableEq

namespace Functor

namespace OfCovBy

variable {X : Finset ι → C} (f : ∀ ⦃S T : Finset ι⦄, S ⋖ T → (X S ⟶ X T))

section DecidableEq

variable [DecidableEq ι]

/-- The composite of the edge maps `f` along a chain of covers from `S` to `T`, by recursion on
the number `k` of elements of `T` outside `S`; each step adds a chosen element of `T \ S`. -/
private noncomputable def chain :
    ∀ (k : ℕ) (S T : Finset ι), S ⊆ T → #(T \ S) = k → (X S ⟶ X T)
  | 0, S, T, h, hk =>
    eqToHom (congrArg X (Subset.antisymm h (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hk))))
  | k + 1, S, T, h, hk =>
    have hne : ∃ a, a ∈ T \ S := card_pos.1 (by omega)
    f (covBy_insert (mem_sdiff.1 (Classical.choose_spec hne)).2) ≫
      chain k (insert (Classical.choose hne) S) T
        (insert_subset (mem_sdiff.1 (Classical.choose_spec hne)).1 h)
        (by have := card_sdiff_insert_add_one (Classical.choose_spec hne); omega)

private theorem chain_congr {k : ℕ} {S S' T : Finset ι} (e : S = S') (h : S ⊆ T) (h' : S' ⊆ T)
    (hk : #(T \ S) = k) (hk' : #(T \ S') = k) {A : Finset ι} (g : X A ⟶ X S)
    (g' : X A ⟶ X S') (hg : g ≫ eqToHom (congrArg X e) = g') :
    g ≫ chain f k S T h hk = g' ≫ chain f k S' T h' hk' := by
  subst e
  rw [eqToHom_refl, comp_id] at hg
  rw [hg]

omit [DecidableEq ι] in
private theorem comp_eqToHom {S T T' : Finset ι} (h : S ⋖ T) (e : T = T') :
    f h ≫ eqToHom (congrArg X e) = f (e ▸ h) := by
  subst e
  simp

private theorem comp_chain_zero {S T : Finset ι} {A : Finset ι} (h : A ⋖ T)
    (h' : A ⋖ S) (hS : S ⊆ T) (hk : #(T \ S) = 0) : f h' ≫ chain f 0 S T hS hk = f h := by
  obtain rfl := Subset.antisymm hS (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hk))
  simp [chain]

end DecidableEq

/-- The map `X S ⟶ X T` along `S ⊆ T` obtained by composing the edge maps `f` along a maximal
chain of covers from `S` to `T`. When the square faces commute, it does not depend on the
chain, and it is the action of `Functor.ofCovBy` on morphisms. -/
noncomputable def map {S T : Finset ι} (h : S ⊆ T) : X S ⟶ X T :=
  open Classical in chain f #(T \ S) S T h rfl

section DecidableEq

variable [DecidableEq ι]

private theorem map_eq_chain {k : ℕ} {S T : Finset ι} (h : S ⊆ T) (hk : #(T \ S) = k) :
    map f h = chain f k S T h hk := by
  obtain rfl : ‹DecidableEq ι› = fun a b ↦ Classical.propDecidable (a = b) :=
    Subsingleton.elim _ _
  subst hk
  rfl

omit [DecidableEq ι] in
/-- The map along `S ⊆ S` is the identity. -/
theorem map_id (S : Finset ι) : map f (Subset.refl S) = 𝟙 (X S) := by
  classical
  rw [map_eq_chain f _ (by simp : #(S \ S) = 0), chain, eqToHom_refl]

omit [DecidableEq ι] in
private theorem map_of_covBy {S T : Finset ι} (h : S ⋖ T) : map f h.le = f h := by
  classical
  rw [map_eq_chain f _ (covBy_iff_card_sdiff_eq_one.1 h).2, chain, comp_chain_zero f h]

variable {f} (comm : ∀ ⦃S T T' U : Finset ι⦄ (h₁ : S ⋖ T) (h₂ : T ⋖ U) (h₁' : S ⋖ T')
  (h₂' : T' ⋖ U), f h₁ ≫ f h₂ = f h₁' ≫ f h₂')
include comm

/-- The chain may start with any element `a` of `T \ S`, not only the chosen one. -/
private theorem chain_succ_eq (k : ℕ) {S T : Finset ι} (h : S ⊆ T) (hk : #(T \ S) = k + 1)
    {a : ι} (ha : a ∈ T \ S) :
    chain f (k + 1) S T h hk = f (covBy_insert (mem_sdiff.1 ha).2) ≫
      chain f k (insert a S) T (insert_subset (mem_sdiff.1 ha).1 h)
        (by have := card_sdiff_insert_add_one ha; omega) := by
  induction k generalizing S a with
  | zero =>
    -- Here `S ⋖ T`, and both sides are the edge map `S ⟶ T`.
    have hST : S ⋖ T := covBy_iff_card_sdiff_eq_one.2 ⟨h, hk⟩
    rw [comp_chain_zero f hST, chain, comp_chain_zero f hST]
  | succ k ih =>
    rw [chain]
    have hne : ∃ a, a ∈ T \ S := card_pos.1 (by omega)
    set m := Classical.choose hne
    have hm : m ∈ T \ S := Classical.choose_spec hne
    rw [mem_sdiff] at ha hm
    by_cases ham : a = m
    · subst ham
      exact chain_congr f rfl _ _ _ _ _ _ (by simp)
    -- Otherwise both chains continue through `S ∪ {a, m}`, and the square face at `S` commutes.
    have ha' : a ∈ T \ insert m S := by simp [ha, ham]
    have hm' : m ∈ T \ insert a S := by simp [hm, Ne.symm ham]
    rw [ih _ _ ha', ih _ _ hm', ← assoc, ← assoc]
    exact chain_congr f (insert_comm a m S) _ _ _ _ _ _
      (by rw [assoc, comp_eqToHom f _ (insert_comm a m S), comm])

/-- Along `S ⊆ T`, the map first follows the edge `S ⋖ S ∪ {a}` for any `a ∈ T \ S`. -/
private theorem map_eq_comp {S T : Finset ι} (h : S ⊆ T) {a : ι} (ha : a ∈ T \ S) :
    map f h = f (covBy_insert (mem_sdiff.1 ha).2) ≫ map f (insert_subset (mem_sdiff.1 ha).1 h) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (card_ne_zero_of_mem ha)
  rw [map_eq_chain f h hk, chain_succ_eq comm k h hk ha,
    map_eq_chain f (k := k) _ (by have := card_sdiff_insert_add_one ha; omega)]

omit [DecidableEq ι] in
/-- The maps along `S ⊆ T` and `T ⊆ U` compose to the map along `S ⊆ U`. -/
theorem map_comp {S T U : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ U) :
    map f (h₁.trans h₂) = map f h₁ ≫ map f h₂ := by
  classical
  induction S, h₁ using subset_induction with
  | self => rw [map_id, id_comp]
  | step S a ha h ih =>
    rw [map_eq_comp comm _ (mem_sdiff.2 ⟨h₂ (h (mem_insert_self a S)), ha⟩), ih,
      map_eq_comp comm _ (mem_sdiff.2 ⟨h (mem_insert_self a S), ha⟩), assoc]

end DecidableEq

end OfCovBy

variable {X : Finset ι → C} (f : ∀ ⦃S T : Finset ι⦄, S ⋖ T → (X S ⟶ X T))
  (comm : ∀ ⦃S T T' U : Finset ι⦄ (h₁ : S ⋖ T) (h₂ : T ⋖ U) (h₁' : S ⋖ T') (h₂' : T' ⋖ U),
    f h₁ ≫ f h₂ = f h₁' ≫ f h₂')

/-- The functor `Finset ι ⥤ C` with vertices `X` and edge maps `f` along the covers `S ⋖ T`,
given that the two routes around every square face `S ⋖ T ⋖ U`, `S ⋖ T' ⋖ U` agree. The map
along `S ⊆ T` is the composite of the edge maps along any maximal chain from `S` to `T`. -/
@[expose]
noncomputable def ofCovBy : Finset ι ⥤ C where
  obj := X
  map φ := OfCovBy.map f (leOfHom φ)
  map_id S := OfCovBy.map_id f S
  map_comp φ ψ := OfCovBy.map_comp comm (leOfHom φ) (leOfHom ψ)

/-- The vertices of `Functor.ofCovBy f comm` are those prescribed by `X`. -/
@[simp]
theorem ofCovBy_obj (S : Finset ι) : (ofCovBy f comm).obj S = X S :=
  rfl

/-- The edge maps of `Functor.ofCovBy f comm` are those prescribed by `f`. -/
theorem ofCovBy_map_of_covBy {S T : Finset ι} (h : S ⋖ T) (φ : S ⟶ T) :
    (ofCovBy f comm).map φ = f h := by
  classical
  exact OfCovBy.map_of_covBy f h

/-- The edge map of `Functor.ofCovBy f comm` from `S` to `S ∪ {a}`. -/
@[simp]
theorem ofCovBy_map_insert [DecidableEq ι] {S : Finset ι} {a : ι} (ha : a ∉ S)
    (φ : S ⟶ insert a S) : (ofCovBy f comm).map φ = f (covBy_insert ha) :=
  ofCovBy_map_of_covBy f comm _ φ

/-- Two functors `Finset ι ⥤ C` with the same vertices and the same edge maps are equal. -/
theorem ext_of_covBy {F G : Finset ι ⥤ C} (h_obj : ∀ S, F.obj S = G.obj S)
    (h_map : ∀ ⦃S T : Finset ι⦄ (h : S ⋖ T), F.map (homOfLE h.le) =
      eqToHom (h_obj S) ≫ G.map (homOfLE h.le) ≫ eqToHom (h_obj T).symm) : F = G := by
  classical
  refine Functor.ext h_obj fun S T φ ↦ ?_
  suffices ∀ S (h : S ⊆ T), F.map (homOfLE h) =
      eqToHom (h_obj S) ≫ G.map (homOfLE h) ≫ eqToHom (h_obj T).symm from this S (leOfHom φ)
  intro S h
  induction S, h using subset_induction with
  | self => simp
  | step S a ha h ih =>
    rw [← homOfLE_comp (S.subset_insert a) h, F.map_comp, G.map_comp, ih,
      h_map (covBy_insert ha)]
    simp

end Functor

namespace NatTrans

variable {F G : Finset ι ⥤ C} (app : ∀ S, F.obj S ⟶ G.obj S)
  (naturality : ∀ ⦃S T : Finset ι⦄ (h : S ⋖ T),
    F.map (homOfLE h.le) ≫ app T = app S ≫ G.map (homOfLE h.le))

/-- The natural transformation between functors `Finset ι ⥤ C` with components `app`, which
need only be natural along the edges `S ⋖ T`. -/
@[expose]
def ofCovBy : F ⟶ G where
  app := app
  naturality S T φ := by
    classical
    suffices ∀ S (h : S ⊆ T), F.map (homOfLE h) ≫ app T = app S ≫ G.map (homOfLE h) from
      this S (leOfHom φ)
    intro S h
    induction S, h using subset_induction with
    | self => simp
    | step S a ha h ih =>
      rw [← homOfLE_comp (S.subset_insert a) h, F.map_comp, G.map_comp, assoc, ih,
        reassoc_of% naturality (covBy_insert ha)]

/-- The components of `NatTrans.ofCovBy app naturality` are `app`. -/
@[simp]
theorem ofCovBy_app (S : Finset ι) : (ofCovBy app naturality).app S = app S :=
  rfl

end NatTrans

end CategoryTheory
