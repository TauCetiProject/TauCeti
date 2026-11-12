/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Fibres of morphisms in `TopCat`

The fibre `TopCat.Hom.fiber p b` of a morphism `p : E ⟶ B` over a point `b` is the preimage
`p ⁻¹' {b}` with the subspace topology, and `TopCat.Hom.fiberι p b` is its inclusion into `E`.
A commutative square from `p` to `p'`, such as a map of fibrations, induces maps between the
fibres (`CategoryTheory.CommSq.fiberMap`), functorially in horizontal composition of squares.
Over a fixed base `B`, a map `f : E ⟶ E'` from `p` to `p'` more generally maps the part `p ⁻¹' S`
of `E` over any subset `S` of `B` to the part of `E'` over `S` (`TopCat.Hom.preimageMap`); over a
point it is the map of fibres of the square with the identity of `B`
(`CategoryTheory.CommSq.fiberMap_eq_preimageMap`).

The names and the dot-notation shape follow Mathlib's scheme-theoretic fibres
`AlgebraicGeometry.Scheme.Hom.fiber` and `AlgebraicGeometry.Scheme.Hom.fiberι`.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.TopCat

variable {E B E' : _root_.TopCat.{u}}

/-- A map `f : E ⟶ E'` over `B`, from `p` to `p'`, carries the part `p ⁻¹' S` of `E` over a
subset `S` of `B` into the part `p' ⁻¹' S` of `E'`. -/
lemma mapsTo_preimage_of_comp_eq {p : E ⟶ B} {p' : E' ⟶ B} {f : E ⟶ E'} (hf : f ≫ p' = p)
    (S : Set B) : Set.MapsTo f (p ⁻¹' S) (p' ⁻¹' S) :=
  fun e he ↦ by rwa [Set.mem_preimage, ← ConcreteCategory.comp_apply, hf]

end TauCeti.TopCat

namespace TopCat.Hom

open TauCeti.TopCat (mapsTo_preimage_of_comp_eq)

variable {E B : TopCat.{u}}

/-- The fibre `p ⁻¹' {b}` of a morphism `p : E ⟶ B` over a point `b`, with the subspace
topology. -/
abbrev fiber (p : E ⟶ B) (b : B) : TopCat.{u} := TopCat.of (p ⁻¹' {b})

/-- The inclusion of the fibre of `p` over `b` into `E`. -/
def fiberι (p : E ⟶ B) (b : B) : p.fiber b ⟶ E := TopCat.ofHom ⟨Subtype.val, by fun_prop⟩

@[simp]
lemma fiberι_apply (p : E ⟶ B) (b : B) (x : p.fiber b) : p.fiberι b x = x.1 := (rfl)

/-- The morphism `p` sends every point of its fibre over `b` to `b`. -/
@[simp]
lemma apply_coe_fiber (p : E ⟶ B) (b : B) (x : p.fiber b) : p x.1 = b :=
  x.2

@[reassoc (attr := simp)]
lemma fiberι_comp (p : E ⟶ B) (b : B) : p.fiberι b ≫ p = TopCat.const b := by
  ext x
  exact x.2

variable {E' : TopCat.{u}}

/-- The map `p ⁻¹' S ⟶ p' ⁻¹' S` between the parts over a subset `S` of the base induced by a map
`f : E ⟶ E'` over the base, from `p` to `p'`. Over a point it is the map of fibres
`CategoryTheory.CommSq.fiberMap` of the square with the identity of `B`
(`CategoryTheory.CommSq.fiberMap_eq_preimageMap`); over a skeleton of a CW base it maps one stage
of the skeletal filtration of `p` to that of `p'`. -/
def preimageMap (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B} (hf : f ≫ p' = p)
    (S : Set B) : TopCat.of (p ⁻¹' S) ⟶ TopCat.of (p' ⁻¹' S) :=
  TopCat.ofHom ⟨(mapsTo_preimage_of_comp_eq hf S).restrict,
    f.hom.continuous.restrict (mapsTo_preimage_of_comp_eq hf S)⟩

@[simp]
lemma preimageMap_apply_coe (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B} (hf : f ≫ p' = p)
    (S : Set B) (x : p ⁻¹' S) : (preimageMap f hf S x : E') = f x.1 :=
  (rfl)

/-- The map induced on the parts over `S` commutes with the inclusions of these parts. -/
@[reassoc (attr := simp)]
lemma preimageMap_comp_ofHom_val (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B} (hf : f ≫ p' = p)
    (S : Set B) :
    preimageMap f hf S ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ =
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ f :=
  (rfl)

/-- The map induced on the fibres over `b` commutes with the inclusions of the fibres. -/
@[reassoc (attr := simp)]
lemma preimageMap_comp_fiberι (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B} (hf : f ≫ p' = p)
    (b : B) : preimageMap f hf {b} ≫ p'.fiberι b = p.fiberι b ≫ f :=
  (rfl)

/-- The maps induced on the parts over nested subsets `S ⊆ T` commute with the inclusions. -/
@[reassoc]
lemma preimageMap_comp_ofHom_inclusion (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B}
    (hf : f ≫ p' = p) {S T : Set B} (h : S ⊆ T) :
    preimageMap f hf S ≫ TopCat.ofHom (ContinuousMap.inclusion (Set.preimage_mono h)) =
      TopCat.ofHom (ContinuousMap.inclusion (Set.preimage_mono h)) ≫ preimageMap f hf T :=
  (rfl)

/-- The identity induces the identity on the parts over `S`. -/
@[simp]
lemma preimageMap_id (p : E ⟶ B) (S : Set B) :
    preimageMap (𝟙 E) (Category.id_comp p) S = 𝟙 _ :=
  (rfl)

/-- The maps induced on the parts over `S` compose. -/
@[reassoc (attr := simp)]
lemma preimageMap_comp_preimageMap {E'' : TopCat.{u}} (f : E ⟶ E') (f' : E' ⟶ E'')
    {p : E ⟶ B} {p' : E' ⟶ B} {p'' : E'' ⟶ B} (hf : f ≫ p' = p) (hf' : f' ≫ p'' = p')
    (S : Set B) :
    preimageMap f hf S ≫ preimageMap f' hf' S =
      preimageMap (f ≫ f') (by rw [Category.assoc, hf', hf]) S :=
  (rfl)

/-- The composite of two maps with finite fibres has finite fibres. -/
theorem finite_fibers_comp {E B X : TopCat.{u}} (p : E ⟶ B) (q : B ⟶ X)
    (hfinp : ∀ b, Finite ↥(p ⁻¹' {b})) (hfinq : ∀ x, Finite ↥(q ⁻¹' {x})) :
    ∀ x, Finite ↥((p ≫ q) ⁻¹' {x}) := fun x => by
  rw [TopCat.coe_comp, Set.preimage_comp]
  exact ((Set.finite_coe_iff.mp (hfinq x)).preimage' fun b _ =>
    Set.finite_coe_iff.mp (hfinp b)).to_subtype

end TopCat.Hom

namespace CategoryTheory.CommSq

variable {E B E' B' E'' B'' : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B'} {p'' : E'' ⟶ B''}
  {f : E ⟶ E'} {g : B ⟶ B'} {f' : E' ⟶ E''} {g' : B' ⟶ B''}

/-- A map of fibrations, that is, a commutative square from `p` to `p'`, maps the fibre of `p`
over `b` to the fibre of `p'` over `g b`. -/
def fiberMap (sq : CommSq f p p' g) (b : B) : p.fiber b ⟶ p'.fiber (g b) :=
  TopCat.ofHom
    { toFun x := ⟨f x.1, by simpa using ConcreteCategory.congr_hom sq.w x.1⟩
      continuous_toFun := by fun_prop }

@[simp]
lemma fiberMap_apply_coe (sq : CommSq f p p' g) (b : B) (x : p.fiber b) :
    (sq.fiberMap b x : E') = f x.1 := (rfl)

@[reassoc (attr := simp)]
lemma fiberMap_comp_fiberι (sq : CommSq f p p' g) (b : B) :
    sq.fiberMap b ≫ p'.fiberι (g b) = p.fiberι b ≫ f := (rfl)

/-- The identity square induces the identity on fibres. -/
@[simp]
lemma fiberMap_id (sq : CommSq (𝟙 E) p p (𝟙 B)) (b : B) : sq.fiberMap b = 𝟙 _ := (rfl)

/-- The composite of the maps on fibres induced by two squares is the map on fibres induced by
their horizontal composite.  It is stated in this direction so that `simp` can use it: the
middle map `p'` cannot be recovered from the composite square, as for `eqToHom_trans`. -/
@[reassoc (attr := simp)]
lemma fiberMap_comp_fiberMap (sq : CommSq f p p' g) (sq' : CommSq f' p' p'' g') (b : B) :
    sq.fiberMap b ≫ sq'.fiberMap (g b) = (sq.horiz_comp sq').fiberMap b := (rfl)

/-- Over the identity of the base, the map of fibres over `b` is the map
`TopCat.Hom.preimageMap` induced on the parts over `{b}`. -/
lemma fiberMap_eq_preimageMap {f : E ⟶ E'} {p : E ⟶ B} {p' : E' ⟶ B}
    (sq : CommSq f p p' (𝟙 B)) (b : B) :
    sq.fiberMap b = TopCat.Hom.preimageMap f (sq.w.trans (Category.comp_id p)) {b} :=
  (rfl)

end CategoryTheory.CommSq
