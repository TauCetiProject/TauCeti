/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Topology.ContinuousMap.RestrictPreimage

/-!
# Fibres of morphisms in `TopCat`

The fibre `TopCat.Hom.fiber p b` of a morphism `p : E ⟶ B` over a point `b` is the preimage
`p ⁻¹' {b}` with the subspace topology, and `TopCat.Hom.fiberι p b` is its inclusion into `E`.
A commutative square from `p` to `p'`, such as a map of fibrations, induces maps between the
fibres (`CategoryTheory.CommSq.fiberMap`), functorially in horizontal composition of squares.
More generally, a map `f` over `B` restricts to maps between the parts over any subset of `B`
(`TopCat.Hom.preimageMap`), and a map over `s : B' ⟶ B` restricts to a map from the part over `T`
to the part over any subset into which `s` maps `T` (`TopCat.Hom.preimageMapOver`). For a
continuous map `p : E → B` and a point `y` of a subset `Y` of `B`,
`ContinuousMap.preimageInclusion` is the inclusion `p⁻¹(y) → p⁻¹(Y)`, which is the fibre inclusion
of the restriction `p⁻¹(Y) → Y` (`ContinuousMap.preimageInclusion_eq`) and is natural in maps over
the base (`ContinuousMap.preimageInclusion_comp_ofHom_restrictPreimageMap`,
`TopCat.Hom.preimageMapOver_comp_preimageInclusion`).

The names and the dot-notation shape follow Mathlib's scheme-theoretic fibres
`AlgebraicGeometry.Scheme.Hom.fiber` and `AlgebraicGeometry.Scheme.Hom.fiberι`.
-/

public section

open CategoryTheory

universe u

namespace TopCat.Hom

variable {E B : TopCat.{u}}

/-- The fibre `p ⁻¹' {b}` of a morphism `p : E ⟶ B` over a point `b`, with the subspace
topology. -/
abbrev fiber (p : E ⟶ B) (b : B) : TopCat.{u} := TopCat.of (p ⁻¹' {b})

/-- The inclusion of the fibre of `p` over `b` into `E`. -/
def fiberι (p : E ⟶ B) (b : B) : p.fiber b ⟶ E := TopCat.ofHom ⟨Subtype.val, by fun_prop⟩

@[simp]
lemma fiberι_apply (p : E ⟶ B) (b : B) (x : p.fiber b) : p.fiberι b x = x.val := (rfl)

/-- The morphism `p` sends every point of its fibre over `b` to `b`. -/
@[simp]
lemma apply_coe_fiber (p : E ⟶ B) (b : B) (x : p.fiber b) : p x.val = b :=
  x.property

@[reassoc (attr := simp)]
lemma fiberι_comp (p : E ⟶ B) (b : B) : p.fiberι b ≫ p = TopCat.const b := by
  ext x
  exact x.property

/-- A map `f` over `B`, that is with `f ≫ p' = p`, carries the part of `E` over a subset of `B`
into the part of `E'` over it. -/
lemma mapsTo_preimage_of_comp_eq {E' : TopCat.{u}} (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B}
    (hf : f ≫ p' = p) (S : Set B) : Set.MapsTo f (p ⁻¹' S) (p' ⁻¹' S) := fun e he ↦ by
  rw [Set.mem_preimage, ← ConcreteCategory.comp_apply, hf]
  exact he

/-- A map `g` over `s`, that is with `g ≫ p = p' ≫ s`, carries the part of `E'` over a subset `T`
of `B'` into the part of `E` over any subset `U` of `B` into which `s` maps `T`. -/
lemma mapsTo_preimage_of_comp_eq_comp {E' B' : TopCat.{u}} (g : E' ⟶ E) {p : E ⟶ B}
    {p' : E' ⟶ B'} {s : B' ⟶ B} (hg : g ≫ p = p' ≫ s) {T : Set B'} {U : Set B}
    (hs : Set.MapsTo s T U) : Set.MapsTo g (p' ⁻¹' T) (p ⁻¹' U) := fun x hx ↦ by
  rw [Set.mem_preimage, ← ConcreteCategory.comp_apply, hg, ConcreteCategory.comp_apply]
  exact hs hx

/-- The restriction `p'⁻¹(T) ⟶ p⁻¹(U)` of a map `g` over `s`, that is with `g ≫ p = p' ≫ s`, where
`s` maps `T` into `U` (`TopCat.Hom.mapsTo_preimage_of_comp_eq_comp`). -/
def preimageMapOver {E' B' : TopCat.{u}} (g : E' ⟶ E) {p : E ⟶ B} {p' : E' ⟶ B'} {s : B' ⟶ B}
    (hg : g ≫ p = p' ≫ s) {T : Set B'} {U : Set B} (hs : Set.MapsTo s T U) :
    TopCat.of (p' ⁻¹' T) ⟶ TopCat.of (p ⁻¹' U) :=
  TopCat.ofHom ⟨(g.mapsTo_preimage_of_comp_eq_comp hg hs).restrict, g.hom.continuous.restrict _⟩

@[simp]
lemma coe_preimageMapOver_apply {E' B' : TopCat.{u}} (g : E' ⟶ E) {p : E ⟶ B} {p' : E' ⟶ B'}
    {s : B' ⟶ B} (hg : g ≫ p = p' ≫ s) {T : Set B'} {U : Set B} (hs : Set.MapsTo s T U)
    (x : TopCat.of (p' ⁻¹' T)) : (g.preimageMapOver hg hs x : E) = g x :=
  (rfl)

/-- The restriction `p⁻¹(S) ⟶ p'⁻¹(S)` of a map `f` over `B`, that is with `f ≫ p' = p`, to the
parts over a subset `S` of `B`: the morphism of `TauCeti.restrictPreimageMap`. -/
def preimageMap {E' : TopCat.{u}} (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B}
    (hf : f ≫ p' = p) (S : Set B) : TopCat.of (p ⁻¹' S) ⟶ TopCat.of (p' ⁻¹' S) :=
  TopCat.ofHom (TauCeti.restrictPreimageMap S (congrArg TopCat.Hom.hom hf))

@[simp]
lemma coe_preimageMap_apply {E' : TopCat.{u}} (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B}
    (hf : f ≫ p' = p) (S : Set B) (x : TopCat.of (p ⁻¹' S)) : (f.preimageMap hf S x : E') = f x :=
  TauCeti.coe_restrictPreimageMap S _ x

@[simp]
lemma preimageMap_id {p : E ⟶ B} (hf : 𝟙 E ≫ p = p) (S : Set B) :
    preimageMap (𝟙 E) hf S = 𝟙 _ :=
  congrArg TopCat.ofHom (TauCeti.restrictPreimageMap_id S)

/-- Restrictions of maps over `B` compose. It is stated in this direction so that `simp` can use
it: the middle map `p'` cannot be recovered from the composite. -/
@[reassoc (attr := simp)]
lemma preimageMap_comp_preimageMap {E' E'' : TopCat.{u}} (f : E ⟶ E') (f' : E' ⟶ E'')
    {p : E ⟶ B} {p' : E' ⟶ B} {p'' : E'' ⟶ B} (hf : f ≫ p' = p) (hf' : f' ≫ p'' = p')
    (S : Set B) :
    f.preimageMap hf S ≫ f'.preimageMap hf' S =
      preimageMap (f ≫ f') (by rw [Category.assoc, hf', hf]) S :=
  congrArg TopCat.ofHom (TauCeti.restrictPreimageMap_comp S _ _)

/-- On fibres, the restriction of a map `f` over `B` commutes with the inclusions of the fibres. -/
@[reassoc (attr := simp)]
lemma preimageMap_comp_fiberι {E' : TopCat.{u}} (f : E ⟶ E') {p : E ⟶ B} {p' : E' ⟶ B}
    (hf : f ≫ p' = p) (b : B) : f.preimageMap hf {b} ≫ p'.fiberι b = p.fiberι b ≫ f :=
  TopCat.ext (f.coe_preimageMap_apply hf {b})

/-- The composite of two maps with finite fibres has finite fibres. -/
theorem finite_fibers_comp {E B X : TopCat.{u}} (p : E ⟶ B) (q : B ⟶ X)
    (hfinp : ∀ b, Finite ↥(p ⁻¹' {b})) (hfinq : ∀ x, Finite ↥(q ⁻¹' {x})) :
    ∀ x, Finite ↥((p ≫ q) ⁻¹' {x}) := fun x => by
  rw [TopCat.coe_comp, Set.preimage_comp]
  exact ((Set.finite_coe_iff.mp (hfinq x)).preimage' fun b _ =>
    Set.finite_coe_iff.mp (hfinp b)).to_subtype

end TopCat.Hom

/-! ### The fibre inside the part over a subset -/

namespace ContinuousMap

variable {E' B' : Type u} [TopologicalSpace E'] [TopologicalSpace B'] {Y : Set B'} {y : B'}

/-- The inclusion `p⁻¹(y) → p⁻¹(Y)` of the fibre over a point `y ∈ Y` into the preimage of `Y`. -/
def preimageInclusion (p : C(E', B')) (hy : y ∈ Y) :
    TopCat.of (p ⁻¹' {y}) ⟶ TopCat.of (p ⁻¹' Y) :=
  TopCat.ofHom (ContinuousMap.inclusion (Set.preimage_mono (Set.singleton_subset_iff.2 hy)))

@[simp]
theorem hom_preimageInclusion (p : C(E', B')) (hy : y ∈ Y) :
    (p.preimageInclusion hy).hom =
      ContinuousMap.inclusion (Set.preimage_mono (Set.singleton_subset_iff.2 hy)) :=
  (rfl)

theorem coe_preimageInclusion_apply (p : C(E', B')) (hy : y ∈ Y) (x : p ⁻¹' {y}) :
    ((p.preimageInclusion hy).hom x : E') = x :=
  (rfl)

/-- The inclusion `p⁻¹(y) → p⁻¹(Y)` is natural in maps over the base: it commutes with the
restrictions of a map `f` over `B` to the preimages of `{y}` and of `Y`. -/
@[reassoc (attr := simp)]
theorem preimageInclusion_comp_ofHom_restrictPreimageMap {E'' : Type u} [TopologicalSpace E'']
    {p : C(E', B')} {q : C(E'', B')} {f : C(E', E'')} (hf : q.comp f = p) (hy : y ∈ Y) :
    p.preimageInclusion hy ≫ TopCat.ofHom (TauCeti.restrictPreimageMap Y hf) =
      TopCat.ofHom (TauCeti.restrictPreimageMap {y} hf) ≫ q.preimageInclusion hy :=
  TopCat.ext fun _ ↦ Subtype.ext <| by simp

/-- The fibre `p⁻¹(y)` is the fibre over `y` of the restriction `p⁻¹(Y) → Y`. -/
def preimageSingletonHomeomorphFiber (p : C(E', B')) (hy : y ∈ Y) :
    (p ⁻¹' {y}) ≃ₜ (p.restrictPreimage Y ⁻¹' {⟨y, hy⟩}) where
  toFun e := ⟨⟨e.val, Set.mem_preimage.2 ((Set.mem_singleton_iff.1 e.property).symm ▸ hy)⟩,
    Subtype.ext e.property⟩
  invFun e := ⟨e.val.val, congrArg Subtype.val e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem coe_coe_preimageSingletonHomeomorphFiber_apply (p : C(E', B')) (hy : y ∈ Y)
    (e : p ⁻¹' {y}) : ((p.preimageSingletonHomeomorphFiber hy e).val : E') = e :=
  (rfl)

@[simp]
theorem coe_preimageSingletonHomeomorphFiber_symm_apply (p : C(E', B')) (hy : y ∈ Y)
    (e : p.restrictPreimage Y ⁻¹' {⟨y, hy⟩}) :
    ((p.preimageSingletonHomeomorphFiber hy).symm e : E') = e.val.val :=
  (rfl)

/-- The inclusion `p⁻¹(y) → p⁻¹(Y)` is the fibre inclusion of the restriction `p⁻¹(Y) → Y`, up to
`ContinuousMap.preimageSingletonHomeomorphFiber`. -/
theorem preimageInclusion_eq (p : C(E', B')) (hy : y ∈ Y) :
    p.preimageInclusion hy =
      (TopCat.isoOfHomeo (p.preimageSingletonHomeomorphFiber hy)).hom ≫
        (TopCat.ofHom (p.restrictPreimage Y)).fiberι ⟨y, hy⟩ :=
  TopCat.ext fun x ↦ by
    rw [ConcreteCategory.comp_apply, TopCat.Hom.fiberι_apply]
    exact Subtype.ext (p.coe_coe_preimageSingletonHomeomorphFiber_apply hy x).symm

end ContinuousMap

namespace TopCat.Hom

/-- The restriction of a map `g` over `s` to the parts over `T` and over a point `y ∈ Y`, followed
by the inclusion `p⁻¹(y) → p⁻¹(Y)`, is the restriction of `g` to the parts over `T` and `Y`. -/
@[reassoc (attr := simp)]
lemma preimageMapOver_comp_preimageInclusion {E B E' B' : TopCat.{u}} (g : E' ⟶ E) {p : E ⟶ B}
    {p' : E' ⟶ B'} {s : B' ⟶ B} (hg : g ≫ p = p' ≫ s) {T : Set B'} {Y : Set B} {y : B}
    (hs : Set.MapsTo s T {y}) (hy : y ∈ Y) :
    g.preimageMapOver hg hs ≫ p.hom.preimageInclusion hy =
      g.preimageMapOver hg (hs.mono_right (Set.singleton_subset_iff.2 hy)) :=
  (rfl)

end TopCat.Hom

namespace CategoryTheory.CommSq

variable {E B E' B' E'' B'' : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B'} {p'' : E'' ⟶ B''}
  {f : E ⟶ E'} {g : B ⟶ B'} {f' : E' ⟶ E''} {g' : B' ⟶ B''}

/-- A map of fibrations, that is, a commutative square from `p` to `p'`, maps the fibre of `p`
over `b` to the fibre of `p'` over `g b`. -/
def fiberMap (sq : CommSq f p p' g) (b : B) : p.fiber b ⟶ p'.fiber (g b) :=
  TopCat.ofHom
    { toFun x := ⟨f x.val, by simpa using ConcreteCategory.congr_hom sq.w x.val⟩
      continuous_toFun := by fun_prop }

@[simp]
lemma fiberMap_apply_coe (sq : CommSq f p p' g) (b : B) (x : p.fiber b) :
    (sq.fiberMap b x : E') = f x.val := (rfl)

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

/-- Underlying `ContinuousMap` commutativity `p'.hom.comp f.hom = g.hom.comp p.hom` of a
commutative square `sq : CommSq f p p' g` in `TopCat`. -/
theorem hom_comp_eq (sq : CommSq f p p' g) : p'.hom.comp f.hom = g.hom.comp p.hom := by
  rw [← TopCat.hom_comp, ← TopCat.hom_comp, sq.w]

end CategoryTheory.CommSq
