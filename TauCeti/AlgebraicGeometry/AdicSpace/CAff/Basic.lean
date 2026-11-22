/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair

import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.RingTheory.Huber.RingOfDefinition

/-!
# The category of complete Hausdorff Huber pairs

This file bundles complete Hausdorff Huber pairs `(A, A⁺)` into a category `TauCeti.CAff.{u}` whose
morphisms `X ⟶ Y` are continuous ring homomorphisms `X.ring →+* Y.ring` carrying `X.pair.plus` into
`Y.pair.plus`. Its opposite category `CAff.{u}ᵒᵖ` is the category of affinoid adic spaces in the
wide sense — prior to imposing any sheafiness hypothesis on `(A, A⁺)` — on which the rational
covering site and Yoneda-adic spaces are built.

## Main definitions

* `TauCeti.CAff`: the category of complete Hausdorff Huber pairs `(A, A⁺)`.
* `TauCeti.CAff.of`: construct an object of `CAff` from a `Huber.Pair` on a complete `T0Space`
  Huber ring.
* `TauCeti.CAff.discrete`: any commutative ring `R` as an object `(R, R)` of `CAff` with the
  discrete uniformity.
* `TauCeti.CAff.pairOfDefinition`: a chosen pair of definition of `X.ring` whose ring of definition
  is contained in `X.pair.plus`.
* `TauCeti.CAff.spa`: the adic spectrum functor `CAff.{u}ᵒᵖ ⥤ TopCat.{u}` sending `op (A, A⁺)` to
  `Spa(A, A⁺)` and `op φ` to `φ.spaComap`.
* `TauCeti.CAff.globalSections` and `TauCeti.CAff.ringPresheaf`: the global-ring presheaf
  `op (A, A⁺) ↦ A` on `CAff.{u}ᵒᵖ`, valued respectively in `Type u` and `CommRingCat.{u}`.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §2–3.
* P. Scholze and J. Weinstein, *Berkeley Lectures on `p`-adic Geometry*, Annals of Mathematics
  Studies 207, Princeton University Press (2020), Lectures 2–4.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.3–7.5.
-/

public section

open CategoryTheory Opposite Topology TauCeti.Huber TauCeti.ValuationSpectrum

universe u

namespace TauCeti

/-- An object of `CAff.{u}` is a complete Hausdorff Huber pair `(A, A⁺)` in universe `u`. The
separation axiom is stored as `T0Space`, from which `T2Space` follows automatically via
`IsUniformAddGroup`. -/
structure CAff : Type (u + 1) where
  /-- The underlying commutative ring `A`. -/
  ring : Type u
  [commRing : CommRing ring]
  [uniformSpace : UniformSpace ring]
  [isUniformAddGroup : IsUniformAddGroup ring]
  [isTopologicalRing : IsTopologicalRing ring]
  [isHuberRing : IsHuberRing ring]
  [completeSpace : CompleteSpace ring]
  [t0Space : T0Space ring]
  /-- The Huber pair `(A, A⁺)` specifying the ring of integral elements `A⁺ ⊆ A`. -/
  pair : Pair ring

attribute [instance] CAff.commRing CAff.uniformSpace CAff.isUniformAddGroup CAff.isTopologicalRing
  CAff.isHuberRing CAff.completeSpace CAff.t0Space

namespace CAff

/-- Bundle a `Huber.Pair` on a complete separated Huber ring as an object of `CAff.{u}`. -/
abbrev of {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsHuberRing A] [CompleteSpace A] [T0Space A] (S : Pair A) : CAff.{u} :=
  { ring := A, pair := S }

/-- Equip an arbitrary commutative ring `R` with the discrete uniformity and `R⁺ = R` to obtain an
object `(R, R)` of `CAff.{u}`. -/
@[expose]
def discrete (R : Type u) [CommRing R] : CAff.{u} :=
  letI : UniformSpace R := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  haveI : DiscreteTopology R := ⟨rfl⟩
  { ring := R
    pair := Pair.discrete R }

@[simp]
theorem discrete_ring (R : Type u) [CommRing R] : (discrete R).ring = R :=
  (rfl)

instance instDiscreteTopologyDiscreteRing (R : Type u) [CommRing R] :
    DiscreteTopology (discrete R).ring :=
  ⟨rfl⟩

@[simp]
theorem discrete_plus (R : Type u) [CommRing R] : (discrete R).pair.plus = ⊤ :=
  Pair.discrete_plus

/-- Every `X : CAff` admits a pair of definition whose ring of definition lies in `X.pair.plus`. -/
noncomputable def pairOfDefinition (X : CAff.{u}) : PairOfDefinition X.ring :=
  (exists_pairOfDefinition_ringOfDefinition_le X.pair.isRingOfIntegralElements.isOpen).choose

/-- The ring of definition of `X.pairOfDefinition` is contained in `X.pair.plus`. -/
theorem ringOfDefinition_le_plus (X : CAff.{u}) :
    X.pairOfDefinition.ringOfDefinition ≤ X.pair.plus :=
  (exists_pairOfDefinition_ringOfDefinition_le X.pair.isRingOfIntegralElements.isOpen).choose_spec

/-! ### Category structure on `CAff` -/

instance : Category.{u} CAff.{u} where
  Hom X Y := Pair.Hom X.pair Y.pair
  id X := Pair.Hom.id X.pair
  comp f g := g.comp f
  id_comp f := Pair.Hom.comp_id f
  comp_id f := Pair.Hom.id_comp f
  assoc f g h := (Pair.Hom.comp_assoc h g f).symm

@[simp]
theorem id_toRingHom (X : CAff.{u}) : (𝟙 X : X ⟶ X).toRingHom = RingHom.id X.ring :=
  Pair.Hom.toRingHom_id X.pair

@[simp]
theorem comp_toRingHom {X Y Z : CAff.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRingHom = g.toRingHom.comp f.toRingHom :=
  Pair.Hom.toRingHom_comp g f

@[simp]
theorem id_spaComap (X : CAff.{u}) : (𝟙 X : X ⟶ X).spaComap = id :=
  Pair.Hom.spaComap_id X.pair

@[simp]
theorem comp_spaComap {X Y Z : CAff.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).spaComap = f.spaComap ∘ g.spaComap :=
  Pair.Hom.spaComap_comp g f

/-- Construct an isomorphism in `CAff` from a homeomorphic ring isomorphism carrying one plus ring
onto the other. -/
def isoMk {X Y : CAff.{u}} (e : X.ring ≃+* Y.ring) (he : Continuous e) (he' : Continuous e.symm)
    (hplus : ∀ a, a ∈ X.pair.plus ↔ e a ∈ Y.pair.plus) : X ≅ Y where
  hom :=
    { toRingHom := e.toRingHom
      continuous_toRingHom := he
      map_mem_plus _ ha := (hplus _).mp ha }
  inv :=
    { toRingHom := e.symm.toRingHom
      continuous_toRingHom := he'
      map_mem_plus b hb := (hplus (e.symm b)).mpr (by simpa using hb) }
  hom_inv_id := Pair.Hom.ext (by ext x; simp)
  inv_hom_id := Pair.Hom.ext (by ext y; simp)

@[simp]
theorem isoMk_hom_toRingHom {X Y : CAff.{u}} (e : X.ring ≃+* Y.ring) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : ∀ a, a ∈ X.pair.plus ↔ e a ∈ Y.pair.plus) :
    (isoMk e he he' hplus).hom.toRingHom = e.toRingHom :=
  (rfl)

@[simp]
theorem isoMk_inv_toRingHom {X Y : CAff.{u}} (e : X.ring ≃+* Y.ring) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : ∀ a, a ∈ X.pair.plus ↔ e a ∈ Y.pair.plus) :
    (isoMk e he he' hplus).inv.toRingHom = e.symm.toRingHom :=
  (rfl)

/-! ### The adic spectrum functor `CAffᵒᵖ ⥤ TopCat` -/

/-- The functor sending `op (A, A⁺)` to the topological space `Spa(A, A⁺)` and `op φ` to the
pullback map `φ.spaComap : Spa(B, B⁺) → Spa(A, A⁺)`. -/
@[expose]
def spa : CAff.{u}ᵒᵖ ⥤ TopCat.{u} where
  obj X := TopCat.of ↥(ValuationSpectrum.spa (unop X).pair.plus)
  map f := TopCat.ofHom ⟨f.unop.spaComap, f.unop.continuous_spaComap⟩
  map_id X := TopCat.ext fun v ↦ congrFun (Pair.Hom.spaComap_id (unop X).pair) v
  map_comp f g := TopCat.ext fun v ↦ congrFun (Pair.Hom.spaComap_comp f.unop g.unop) v

@[simp]
theorem spa_obj (X : CAff.{u}) :
    (spa.obj (op X) : Type u) = ↥(ValuationSpectrum.spa X.pair.plus) :=
  (rfl)

@[simp]
theorem coe_spa_map {X Y : CAff.{u}} (f : X ⟶ Y) :
    ⇑(spa.map f.op) = f.spaComap :=
  (rfl)

/-- **Wedhorn Proposition 7.52 in `CAff`**: the adic spectrum of a complete Hausdorff Huber pair
`X : CAff` is empty if and only if `X.ring` is trivial. -/
theorem isEmpty_spa_iff (X : CAff.{u}) :
    IsEmpty (spa.obj (op X)) ↔ Subsingleton X.ring := by
  rw [spa_obj, Set.isEmpty_coe_sort,
    spa_eq_empty_iff_subsingleton X.pair.plus X.pair.isRingOfIntegralElements]

/-! ### The global-ring presheaves on `CAffᵒᵖ` -/

/-- The presheaf of commutative rings on `CAff.{u}ᵒᵖ` sending `op (A, A⁺)` to `A` and `op φ`
(for `φ : X ⟶ Y`) to `φ.toRingHom : X.ring →+* Y.ring`. -/
-- exposed so that its objects are definitionally `CommRingCat.of X.ring`
@[expose]
def ringPresheaf : (CAff.{u}ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (unop (unop X)).ring
  map f := CommRingCat.ofHom f.unop.unop.toRingHom
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

/-- The presheaf of sets on `CAff.{u}ᵒᵖ` sending `op (A, A⁺)` to the underlying ring `A` and a
morphism `op Y ⟶ op X` (given by `φ : X ⟶ Y`) to `φ.toRingHom : X.ring → Y.ring`. -/
-- exposed so that `globalSections.obj (op (op X))` is definitionally `X.ring`
@[expose]
def globalSections : (CAff.{u}ᵒᵖ)ᵒᵖ ⥤ Type u :=
  ringPresheaf ⋙ forget CommRingCat

@[simp]
theorem globalSections_obj (X : CAff.{u}) : globalSections.obj (op (op X)) = X.ring :=
  (rfl)

@[simp]
theorem globalSections_map_apply {X Y : CAff.{u}} (f : X ⟶ Y) (a : X.ring) :
    globalSections.map f.op.op a = f.toRingHom a :=
  (rfl)

@[simp]
theorem ringPresheaf_comp_forget :
    ringPresheaf.{u} ⋙ forget CommRingCat.{u} = globalSections.{u} :=
  (rfl)

end CAff

end TauCeti

end
