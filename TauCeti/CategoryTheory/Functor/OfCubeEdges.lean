/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Finset.Grade
public import Mathlib.Order.ModularLattice

/-!
# Commutative cubes from their edge maps

A commutative cube indexed by a type `ι` in a category `C` is a functor `Finset ι ⥤ C` on the
finite subsets of `ι`, ordered by inclusion. Such a cube is usually given by its edges only: an
object `X S` at every vertex, a map `X S ⟶ X T` along every edge, that is, whenever `T` covers
`S` (`S ⋖ T`, so `T = insert a S` with `a ∉ S`), and the condition that every square face
commutes. This file builds the cube from these data, `CategoryTheory.Functor.ofCubeEdges`: the
map along an inclusion `S ⊆ T` is the composite of edge maps along any maximal chain from `S` to
`T`, and the commuting faces make it independent of the chain.

Likewise a map of cubes only needs to commute with the edge maps:
`CategoryTheory.NatTrans.ofCubeEdges` builds a natural transformation between functors
`Finset ι ⥤ C` from components that are natural along every edge.

These are the analogues for the Boolean cube of `CategoryTheory.Functor.ofSequence` and
`CategoryTheory.NatTrans.ofSequence` for the ordered set `ℕ`. The cube of resolutions of a link
diagram, whose vertices are the circle tensors of the smoothings and whose edge maps are the
saddle maps, is a cube of this kind; its signed totalization
`CategoryTheory.Functor.cubeComplex` is the Khovanov complex.

## Main definitions

* `CategoryTheory.Functor.ofCubeEdges d hd`: the commutative cube with edge maps `d`, whose
  square faces commute by `hd`.
* `CategoryTheory.NatTrans.ofCubeEdges app naturality`: the map of cubes with components `app`,
  natural along every edge.

## Main results

* `CategoryTheory.Functor.ofCubeEdges_map_of_covBy`: along an edge the cube has the given edge
  map.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

universe w v u

namespace CategoryTheory

open Category Finset

variable {C : Type u} [Category.{v} C] {ι : Type w}

namespace Functor

namespace OfCubeEdges

variable {X : Finset ι → C} (d : ∀ ⦃S T : Finset ι⦄, S ⋖ T → (X S ⟶ X T))

open scoped Classical in
/-- The composite of edge maps from `X S` to `X T` along a maximal chain from `S` to `T`, whose
first step is chosen arbitrarily; it does not depend on this choice once the square faces of
edge maps commute. This is the map along `S ⊆ T` of `CategoryTheory.Functor.ofCubeEdges`. -/
def map (S T : Finset ι) (h : S ⊆ T) : X S ⟶ X T :=
  if hST : S = T then eqToHom (congrArg X hST)
  else
    have hU := exists_covBy_le_of_lt (h.lt_of_ne hST)
    d hU.choose_spec.1 ≫ map hU.choose T hU.choose_spec.2
termination_by #T - #S
decreasing_by
  exact Nat.sub_lt_sub_left (card_lt_card (h.lt_of_ne hST))
    (card_lt_card hU.choose_spec.1.lt)

/-- The empty chain from `S` to itself gives the identity. -/
theorem map_self (S : Finset ι) (h : S ⊆ S) : map d S S h = 𝟙 _ := by
  rw [map, dite_eq_left rfl, eqToHom_refl]

private lemma exists_map_eq_comp {S T : Finset ι} (h : S ⊆ T) (hST : S ≠ T) :
    ∃ U, ∃ (hSU : S ⋖ U) (hUT : U ⊆ T), map d S T h = d hSU ≫ map d U T hUT :=
  ⟨(exists_covBy_le_of_lt (h.lt_of_ne hST)).choose,
    (exists_covBy_le_of_lt (h.lt_of_ne hST)).choose_spec.1,
    (exists_covBy_le_of_lt (h.lt_of_ne hST)).choose_spec.2, by rw [map, dite_eq_right hST]⟩

variable {d}
  (hd : ∀ ⦃S T₁ T₂ U : Finset ι⦄ (h₁ : S ⋖ T₁) (h₁' : T₁ ⋖ U) (h₂ : S ⋖ T₂) (h₂' : T₂ ⋖ U),
    d h₁ ≫ d h₁' = d h₂ ≫ d h₂')
include hd

/-- The composite of edge maps from `X S` to `X T` may start along any edge: this is where the
commuting faces are used. -/
private lemma map_eq_comp {S U T : Finset ι} (hSU : S ⋖ U) (hUT : U ⊆ T) (h : S ⊆ T) :
    map d S T h = d hSU ≫ map d U T hUT := by
  classical
  induction hk : #T - #S using Nat.strong_induction_on generalizing S U with
  | _ k ih =>
  have hST : S ≠ T := by
    rintro rfl
    exact hSU.lt.not_ge hUT
  obtain ⟨V, hSV, hVT, e⟩ := exists_map_eq_comp d h hST
  rw [e]
  obtain rfl | hUV := eq_or_ne U V
  · rfl
  -- Both routes continue to `U ⊔ V`, and the square face through `U` and `V` commutes.
  have hUV' : U ⊓ V = S := hSU.wcovBy.inf_eq hSV.wcovBy hUV
  have hUW : U ⋖ U ⊔ V := covBy_sup_of_inf_covBy_right (hUV' ▸ hSV)
  have hVW : V ⋖ U ⊔ V := covBy_sup_of_inf_covBy_left (hUV' ▸ hSU)
  have hWT : U ⊔ V ⊆ T := sup_le hUT hVT
  rw [ih _ (hk ▸ Nat.sub_lt_sub_left (card_lt_card (h.lt_of_ne hST)) (card_lt_card hSU.lt))
      hUW hWT hUT rfl,
    ih _ (hk ▸ Nat.sub_lt_sub_left (card_lt_card (h.lt_of_ne hST)) (card_lt_card hSV.lt))
      hVW hWT hVT rfl,
    ← assoc, ← assoc, hd hSV hVW hSU hUW]

/-- Once the square faces commute, the composites of edge maps along chains compose. -/
theorem map_comp {S T U : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ U) :
    map d S T h₁ ≫ map d T U h₂ = map d S U (h₁.trans h₂) := by
  induction hk : #T - #S using Nat.strong_induction_on generalizing S with
  | _ k ih =>
  obtain rfl | hST := eq_or_ne S T
  · rw [map_self, id_comp]
  obtain ⟨V, hSV, hVT, e⟩ := exists_map_eq_comp d h₁ hST
  rw [e, map_eq_comp hd hSV (hVT.trans h₂), assoc,
    ih _ (hk ▸ Nat.sub_lt_sub_left (card_lt_card (h₁.lt_of_ne hST)) (card_lt_card hSV.lt)) hVT rfl]

end OfCubeEdges

variable {X : Finset ι → C} (d : ∀ ⦃S T : Finset ι⦄, S ⋖ T → (X S ⟶ X T))
  (hd : ∀ ⦃S T₁ T₂ U : Finset ι⦄ (h₁ : S ⋖ T₁) (h₁' : T₁ ⋖ U) (h₂ : S ⋖ T₂) (h₂' : T₂ ⋖ U),
    d h₁ ≫ d h₁' = d h₂ ≫ d h₂')

/-- The commutative cube `Finset ι ⥤ C` with vertices `X S` and with the edge map `d h` along
every edge `h : S ⋖ T`, given that every square face of edge maps commutes (`hd`). Along an
inclusion `S ⊆ T` it is the composite of the edge maps along any maximal chain from `S` to
`T`. -/
@[expose, simps obj]
def ofCubeEdges : Finset ι ⥤ C where
  obj := X
  map {S T} f := OfCubeEdges.map d S T (leOfHom f)
  map_id S := OfCubeEdges.map_self d S _
  map_comp f g := (OfCubeEdges.map_comp hd (leOfHom f) (leOfHom g)).symm

/-- Along an edge `S ⋖ T`, the cube `ofCubeEdges d hd` is the edge map `d`. -/
theorem ofCubeEdges_map_of_covBy {S T : Finset ι} (f : S ⟶ T) (h : S ⋖ T) :
    (ofCubeEdges d hd).map f = d h := by
  -- By definition, `ofCubeEdges` sends `f` to the composite of edge maps along `leOfHom f`.
  change OfCubeEdges.map d S T (leOfHom f) = d h
  rw [OfCubeEdges.map_eq_comp hd h subset_rfl, OfCubeEdges.map_self, comp_id]

/-- Along the edge from `S` to `insert a S`, for `a ∉ S`, the cube `ofCubeEdges d hd` is the edge
map `d`. -/
@[simp]
theorem ofCubeEdges_map_homOfLE_insert [DecidableEq ι] {S : Finset ι} {a : ι} (ha : a ∉ S) :
    (ofCubeEdges d hd).map (homOfLE (subset_insert a S)) = d (covBy_insert ha) :=
  ofCubeEdges_map_of_covBy d hd _ _

end Functor

namespace NatTrans

variable {F G : Finset ι ⥤ C} (app : ∀ S, F.obj S ⟶ G.obj S)
  (naturality : ∀ ⦃S T : Finset ι⦄ (h : S ⋖ T),
    F.map (homOfLE h.le) ≫ app T = app S ≫ G.map (homOfLE h.le))

include naturality in
/-- Components that are natural along every edge of the cube are natural along every
inclusion. -/
private lemma naturality_homOfLE {S T : Finset ι} (h : S ⊆ T) :
    F.map (homOfLE h) ≫ app T = app S ≫ G.map (homOfLE h) := by
  induction hk : #T - #S using Nat.strong_induction_on generalizing S with
  | _ k ih =>
  obtain rfl | hST := eq_or_ne S T
  · simp
  obtain ⟨U, hSU, hUT⟩ := exists_covBy_le_of_lt (h.lt_of_ne hST)
  rw [← homOfLE_comp hSU.le hUT, F.map_comp, G.map_comp, assoc,
    ih _ (hk ▸ Nat.sub_lt_sub_left (card_lt_card (h.lt_of_ne hST)) (card_lt_card hSU.lt)) hUT rfl,
    ← assoc, naturality hSU, assoc]

/-- The map of cubes `F ⟶ G` with components `app`, which need only be natural along the edges
`S ⋖ T` of the cube. -/
def ofCubeEdges : F ⟶ G where
  app := app
  naturality S T f := by
    rw [Subsingleton.elim f (homOfLE (leOfHom f))]
    exact naturality_homOfLE app naturality (leOfHom f)

/-- The components of `NatTrans.ofCubeEdges app naturality` are `app`. -/
@[simp]
theorem ofCubeEdges_app (S : Finset ι) : (ofCubeEdges app naturality).app S = app S := (rfl)

end NatTrans

end CategoryTheory
