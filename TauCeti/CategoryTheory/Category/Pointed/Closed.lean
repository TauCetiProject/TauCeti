/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import TauCeti.CategoryTheory.Category.Pointed.Smash

/-!
# The smash product of pointed types is closed

The pointed maps `X ⟶ Y`, pointed at the constant map to the basepoint of `Y`, form a pointed
type, and a pointed map `X ∧ Y ⟶ Z` is the same as a pointed map `Y ⟶ (X ⟶ Z)` by currying:
`y` goes to the map `x ↦ f (x ∧ y)`. This makes the smash product monoidal structure on
`Pointed` closed. Consequently tensoring with a fixed pointed type on either side preserves all
colimits.

We also identify `Pointed` with the category of types under the one-point type, so that
`Pointed` has all limits and colimits. Since colimits of diagrams of pointed types are then
computed pointwise, closedness implies that the degreewise smash product of such diagrams, for
instance of simplicial pointed types, preserves colimits in each variable.

## Main definitions

* `Pointed.ihom X`: the functor `Y ↦ (X ⟶ Y)` of pointed maps out of `X`.
* `Pointed.tensorHomEquiv X Y Z : (X ⊗ Y ⟶ Z) ≃ (Y ⟶ (Pointed.ihom X).obj Z)`, currying.
* The instance `MonoidalClosed Pointed`.
* `Pointed.equivUnderPUnit`: the equivalence of `Pointed` with types under `PUnit`.
* The instances `HasLimitsOfSize.{w, w} Pointed.{u}` and `HasColimitsOfSize.{w, w} Pointed.{u}`
  whenever `UnivLE.{w, u}`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1 (the closed symmetric monoidal smash product of pointed simplicial sets).
-/

public section

universe w u

open CategoryTheory Limits MonoidalCategory

namespace Pointed

variable {X Y Y' Z : Pointed.{u}}

/-- The internal hom for the smash product: the functor sending `Y` to the pointed maps
`X ⟶ Y`, pointed at the constant map to the basepoint of `Y`. A pointed map `Y ⟶ Y'` acts by
postcomposition.

The body is exposed so that elements of `(Pointed.ihom X).obj Y`, and hence of
`(ihom X).obj Y`, can be used as pointed maps `X ⟶ Y`. -/
@[expose]
protected def ihom (X : Pointed.{u}) : Pointed.{u} ⥤ Pointed.{u} where
  obj Y := of (⟨fun _ ↦ Y.point, rfl⟩ : X ⟶ Y)
  map g := ⟨fun f ↦ f ≫ g, by ext; exact g.map_point⟩

/-- Currying: a pointed map `X ∧ Y ⟶ Z` corresponds to the pointed map `Y ⟶ (X ⟶ Z)` sending
`y` to `x ↦ f (x ∧ y)`. -/
def tensorHomEquiv (X Y Z : Pointed.{u}) : (X ⊗ Y ⟶ Z) ≃ (Y ⟶ (Pointed.ihom X).obj Z) where
  toFun f :=
    { toFun y :=
        { toFun x := f.toFun (smash.mk x y)
          map_point := (congrArg f.toFun (smash.mk_point_left y)).trans f.map_point }
      map_point := Hom.ext <| funext fun x ↦
        (congrArg f.toFun (smash.mk_point_right x)).trans f.map_point }
  invFun g := smash.lift (fun x y ↦ (g.toFun y).toFun x) (fun y ↦ (g.toFun y).map_point)
    (fun x ↦ congrArg (Hom.toFun · x) g.map_point)
  left_inv _ := tensor_ext fun _ _ ↦ smash.lift_mk ..
  right_inv _ := Hom.ext <| funext fun _ ↦ Hom.ext <| funext fun _ ↦ smash.lift_mk ..

@[simp]
lemma tensorHomEquiv_apply_apply_apply (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    ((tensorHomEquiv X Y Z f).toFun y).toFun x = f.toFun (smash.mk x y) :=
  (rfl)

@[simp]
lemma tensorHomEquiv_symm_apply_mk (g : Y ⟶ (Pointed.ihom X).obj Z) (x : X) (y : Y) :
    ((tensorHomEquiv X Y Z).symm g).toFun (smash.mk x y) = (g.toFun y).toFun x :=
  smash.lift_mk ..

/-- Currying is natural in the source: precomposition with `f` corresponds to precomposition
with `X ◁ f`. -/
lemma tensorHomEquiv_symm_comp {Y'' : Pointed.{u}} (f : Y'' ⟶ Y)
    (g : Y ⟶ (Pointed.ihom X).obj Z) :
    (tensorHomEquiv X Y'' Z).symm (f ≫ g) = X ◁ f ≫ (tensorHomEquiv X Y Z).symm g :=
  tensor_ext fun _ _ ↦ by simp

/-- Currying is natural in the target: postcomposition with `g` corresponds to postcomposition
with `(Pointed.ihom X).map g`. -/
lemma tensorHomEquiv_comp {Z' : Pointed.{u}} (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    tensorHomEquiv X Y Z' (f ≫ g) = tensorHomEquiv X Y Z f ≫ (Pointed.ihom X).map g :=
  (rfl)

/-- The smash product of pointed types is closed: `X ∧ -` is left adjoint to the functor of
pointed maps out of `X`. -/
instance monoidalClosed : MonoidalClosed Pointed.{u} where
  closed X :=
    { rightAdj := Pointed.ihom X
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := tensorHomEquiv X
          homEquiv_naturality_left_symm := tensorHomEquiv_symm_comp
          homEquiv_naturality_right := tensorHomEquiv_comp } }

/-- The hom-set bijection of the smash–hom adjunction is `Pointed.tensorHomEquiv`. -/
lemma homEquiv_def (X Y Z : Pointed.{u}) :
    (ihom.adjunction X).homEquiv Y Z = tensorHomEquiv X Y Z :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

/-- The basepoint of `X ⟶ Y` is the constant map to the basepoint of `Y`. -/
@[simp]
lemma ihom_obj_point_apply (x : X) : ((ihom X).obj Y).point.toFun x = Y.point := (rfl)

/-- The internal hom acts on pointed maps by postcomposition. -/
@[simp]
lemma ihom_map_apply_apply (g : Y ⟶ Y') (f : (ihom X).obj Y) (x : X) :
    (((ihom X).map g).toFun f).toFun x = g.toFun (f.toFun x) := (rfl)

@[simp]
lemma curry_apply_apply (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    ((MonoidalClosed.curry f).toFun y).toFun x = f.toFun (smash.mk x y) :=
  (rfl)

@[simp]
lemma uncurry_mk (g : Y ⟶ (ihom X).obj Z) (x : X) (y : Y) :
    (MonoidalClosed.uncurry g).toFun (smash.mk x y) = (g.toFun y).toFun x := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, homEquiv_def]
  exact tensorHomEquiv_symm_apply_mk g x y

/-- The evaluation map `X ∧ (X ⟶ Y) ⟶ Y` applies a pointed map to a point. -/
@[simp]
lemma ihom_ev_app_mk (x : X) (f : (ihom X).obj Y) :
    ((ihom.ev X).app Y).toFun (smash.mk x f) = f.toFun x := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_mk]
  rfl

/-- The coevaluation map `Y ⟶ (X ⟶ X ∧ Y)` sends `y` to `x ↦ x ∧ y`. -/
@[simp]
lemma ihom_coev_app_apply_apply (y : Y) (x : X) :
    (((ihom.coev X).app Y).toFun y).toFun x = smash.mk x y :=
  (rfl)

/-- Pointed types are the same as types under the one-point type: a pointed type `X`
corresponds to the map `PUnit → X` picking out its basepoint. -/
def equivUnderPUnit : Pointed.{u} ≌ Under (PUnit.{u + 1} : Type u) where
  functor :=
    { obj X := Under.mk (TypeCat.ofHom fun _ ↦ X.point)
      map f := Under.homMk (TypeCat.ofHom f.toFun) (by ext; exact f.map_point) }
  inverse :=
    { obj A := of (A.hom PUnit.unit)
      map g := ⟨g.right, ConcreteCategory.congr_hom (Under.w g) PUnit.unit⟩ }
  unitIso := NatIso.ofComponents fun X ↦ Iso.refl X
  counitIso := NatIso.ofComponents fun A ↦
    Under.isoMk (Iso.refl A.right) (by ext; rfl)

instance [UnivLE.{w, u}] : HasColimitsOfSize.{w, w} Pointed.{u} :=
  Adjunction.has_colimits_of_equivalence equivUnderPUnit.functor

instance [UnivLE.{w, u}] : HasLimitsOfSize.{w, w} Pointed.{u} :=
  have : HasLimitsOfSize.{w, w} (Under (PUnit.{u + 1} : Type u)) := ⟨fun _ _ ↦ inferInstance⟩
  Adjunction.has_limits_of_equivalence equivUnderPUnit.functor

end Pointed
