/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Evaluation
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic

/-!
# The free rigid monoidal category on a duality signature

A *duality signature* (`TauCeti.DualitySignature`) specifies generating objects and generating
morphisms (*coupons*) whose source and target boundaries are formal rigid object expressions
(`TauCeti.RigidObject`), embedding dual-free signatures via `TensorSignature.toDualitySignature`.

The free rigid category `DualitySignature.FreeRigid S` has `RigidObject S.Obj` as objects and
formal composites, tensors, and whiskerings of monoidal structure morphisms, right/left
(co)evaluations, and coupons quotiented by `FreeRigid.HomEquiv` (monoidal axioms and the four
`ExactPairing` zigzag equations, with no pivotal or coupon equations).

Universal property: `TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Universal`;
non-pivotality: `TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.NonPivotal`.

## Main definitions and results

* `TauCeti.DualitySignature`, `TauCeti.TensorSignature.toDualitySignature`: duality signatures and
  inclusion of tensor signatures.
* `TauCeti.DualitySignature.FreeRigid S`: free rigid monoidal category on `S` (`Category`,
  `MonoidalCategory`, `RightRigidCategory`, `LeftRigidCategory`, `RigidCategory`, `FreeRigid.of`,
  `FreeRigid.coupon`, `FreeRigid.Hom.inductionOn`, `TensorSignature.FreeMonoidal.toFreeRigid`).

## Design notes and attribution

Parallels `TauCeti.TensorSignature.FreeMonoidal` (modeled on Markus Himmel's
`Mathlib/CategoryTheory/Monoidal/Free/Basic.lean`), extended with right/left (co)evaluations and
Jakob von Raumer's `CategoryTheory.ExactPairing`
(`Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`).

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991).
* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, unpublished manuscript (1988).
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §4.
-/

public section

universe u v

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti

/-- A duality signature: a type `Obj` of generating objects and a type `Coupon` of generating
morphisms, each coupon having a source and a target formal rigid object expression in `Obj`. -/
structure DualitySignature where
  /-- The generating objects. -/
  Obj : Type u
  /-- The generating morphisms (coupons). -/
  Coupon : Type v
  /-- The source rigid object expression of a coupon. -/
  src : Coupon → RigidObject Obj
  /-- The target rigid object expression of a coupon. -/
  tgt : Coupon → RigidObject Obj

/-- View an ordinary dual-free tensor signature as a duality signature by embedding its formal
tensor-word boundaries into `RigidObject`. -/
@[expose] def TensorSignature.toDualitySignature (S : TensorSignature.{u, v}) :
    DualitySignature.{u, v} where
  Obj := S.Obj
  Coupon := S.Coupon
  src g := (S.src g).toRigidObject
  tgt g := (S.tgt g).toRigidObject

@[simp] theorem TensorSignature.toDualitySignature_obj (S : TensorSignature.{u, v}) :
    S.toDualitySignature.Obj = S.Obj := rfl
@[simp] theorem TensorSignature.toDualitySignature_coupon (S : TensorSignature.{u, v}) :
    S.toDualitySignature.Coupon = S.Coupon := rfl
@[simp] theorem TensorSignature.toDualitySignature_src (S : TensorSignature.{u, v}) (g : S.Coupon) :
    S.toDualitySignature.src g = (S.src g).toRigidObject := rfl
@[simp] theorem TensorSignature.toDualitySignature_tgt (S : TensorSignature.{u, v}) (g : S.Coupon) :
    S.toDualitySignature.tgt g = (S.tgt g).toRigidObject := rfl

namespace DualitySignature

variable (S : DualitySignature.{u, v})

/-- The free rigid monoidal category on a duality signature `S`. Its objects are the formal rigid
object expressions `RigidObject S.Obj`. -/
@[ext]
structure FreeRigid where
  /-- The formal rigid object expression underlying an object of `S.FreeRigid`. -/
  as : RigidObject S.Obj

namespace FreeRigid

variable {S}

/-- The object of `S.FreeRigid` given by a single generating object. -/
@[expose] def of (a : S.Obj) : S.FreeRigid := ⟨.of a⟩

/-- Formal morphism expressions of the free rigid category on `S`: identities, associators, unitors,
right and left coevaluations and evaluations, and coupons, closed under composition, whiskering and
tensor product. -/
inductive Hom : RigidObject S.Obj → RigidObject S.Obj → Type (max u v)
  | id (X : RigidObject S.Obj) : Hom X X
  | α_hom (X Y Z : RigidObject S.Obj) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : RigidObject S.Obj) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X : RigidObject S.Obj) : Hom (RigidObject.unit.tensor X) X
  | l_inv (X : RigidObject S.Obj) : Hom X (RigidObject.unit.tensor X)
  | ρ_hom (X : RigidObject S.Obj) : Hom (X.tensor RigidObject.unit) X
  | ρ_inv (X : RigidObject S.Obj) : Hom X (X.tensor RigidObject.unit)
  | rightCoevaluation (X : RigidObject S.Obj) : Hom RigidObject.unit (X.tensor X.rightDual)
  | rightEvaluation (X : RigidObject S.Obj) : Hom (X.rightDual.tensor X) RigidObject.unit
  | leftCoevaluation (X : RigidObject S.Obj) : Hom RigidObject.unit (X.leftDual.tensor X)
  | leftEvaluation (X : RigidObject S.Obj) : Hom (X.tensor X.leftDual) RigidObject.unit
  | coupon (g : S.Coupon) : Hom (S.src g) (S.tgt g)
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : RigidObject S.Obj) {Y₁ Y₂} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : RigidObject S.Obj) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)

/-- The congruence on formal morphism expressions generated by the axioms of a monoidal category and
the four zigzag equations of right and left duality. No pivotal relation or coupon equation is
imposed. -/
inductive HomEquiv : ∀ {X Y : RigidObject S.Obj}, Hom X Y → Hom X Y → Prop
  | refl {X Y} (f : Hom X Y) : HomEquiv f f
  | symm {X Y} (f g : Hom X Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : Hom X Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : Hom X Y} {g g' : Hom Y Z} : HomEquiv f f' → HomEquiv g g' →
      HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Hom Y Z) : HomEquiv f f' →
      HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Hom Y Z) (X) : HomEquiv f f' →
      HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : Hom W X} {g g' : Hom Y Z} : HomEquiv f f' → HomEquiv g g' →
      HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : Hom X₁ Y₁) (g : Hom X₂ Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : Hom X Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : Hom X Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V} (f : Hom X U) (g : Hom U V) (h : Hom V Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂)
      (g₁ : Hom Y₁ Z₁) (g₂ : Hom Y₂ Z₂) :
      HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂) (f₃ : Hom X₃ Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : Hom X Y) :
      HomEquiv ((f.whiskerRight .unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : Hom X Y) :
      HomEquiv ((f.whiskerLeft .unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} : HomEquiv (((Hom.α_hom W X Y).whiskerRight Z).comp
      ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
      ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} : HomEquiv ((Hom.α_hom X .unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
      ((Hom.ρ_hom X).whiskerRight Y)
  | right_coevaluation_evaluation (X : RigidObject S.Obj) : HomEquiv
      (((Hom.rightCoevaluation X).whiskerLeft X.rightDual).comp
        ((Hom.α_inv X.rightDual X X.rightDual).comp
          ((Hom.rightEvaluation X).whiskerRight X.rightDual)))
      ((Hom.ρ_hom X.rightDual).comp (Hom.l_inv X.rightDual))
  | right_evaluation_coevaluation (X : RigidObject S.Obj) : HomEquiv
      (((Hom.rightCoevaluation X).whiskerRight X).comp
        ((Hom.α_hom X X.rightDual X).comp ((Hom.rightEvaluation X).whiskerLeft X)))
      ((Hom.l_hom X).comp (Hom.ρ_inv X))
  | left_coevaluation_evaluation (X : RigidObject S.Obj) : HomEquiv
      (((Hom.leftCoevaluation X).whiskerLeft X).comp
        ((Hom.α_inv X X.leftDual X).comp ((Hom.leftEvaluation X).whiskerRight X)))
      ((Hom.ρ_hom X).comp (Hom.l_inv X))
  | left_evaluation_coevaluation (X : RigidObject S.Obj) : HomEquiv
      (((Hom.leftCoevaluation X).whiskerRight X.leftDual).comp
        ((Hom.α_hom X.leftDual X X.leftDual).comp
          ((Hom.leftEvaluation X).whiskerLeft X.leftDual)))
      ((Hom.l_hom X.leftDual).comp (Hom.ρ_inv X.leftDual))

/-- Formal morphism expressions are identified when the monoidal and zigzag axioms equate them. -/
instance setoidHom (X Y : RigidObject S.Obj) : Setoid (Hom X Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

section Instances

open HomEquiv

instance : Category.{max u v} S.FreeRigid where
  Hom X Y := Quotient (setoidHom X.as Y.as)
  id X := ⟦Hom.id X.as⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
  id_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound (id_comp f)
  comp_id := by rintro _ _ ⟨f⟩; exact Quotient.sound (comp_id f)
  assoc := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact Quotient.sound (assoc f g h)

instance : MonoidalCategory S.FreeRigid where
  tensorObj X Y := ⟨X.as.tensor Y.as⟩
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f :=
    Quot.map (fun f ↦ Hom.whiskerLeft X.as f) (fun f f' ↦ .whiskerLeft _ f f') f
  whiskerRight f Y :=
    Quot.map (fun f ↦ Hom.whiskerRight f Y.as) (fun f f' ↦ .whiskerRight f f' _) f
  tensorHom_def := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩; exact Quotient.sound (tensorHom_def _ _)
  id_tensorHom_id _ _ := Quot.sound id_tensorHom_id
  tensorHom_comp_tensorHom := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩; exact Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X.as Y.as)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X.as Y.as)
  tensorUnit := ⟨.unit⟩
  associator X Y Z :=
    ⟨⟦Hom.α_hom X.as Y.as Z.as⟧, ⟦Hom.α_inv X.as Y.as Z.as⟧, Quotient.sound α_hom_inv,
      Quotient.sound α_inv_hom⟩
  associator_naturality := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩; exact Quotient.sound (associator_naturality _ _ _)
  leftUnitor X :=
    ⟨⟦Hom.l_hom X.as⟧, ⟦Hom.l_inv X.as⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  leftUnitor_naturality := by rintro _ _ ⟨f⟩; exact Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X.as⟧, ⟦Hom.ρ_inv X.as⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality := by rintro _ _ ⟨f⟩; exact Quotient.sound (ρ_naturality _)
  pentagon _ _ _ _ := Quotient.sound pentagon
  triangle _ _ := Quotient.sound triangle

instance : RightRigidCategory S.FreeRigid where
  rightDual X :=
    { rightDual := ⟨X.as.rightDual⟩
      exact :=
        { coevaluation' := ⟦Hom.rightCoevaluation X.as⟧, evaluation' := ⟦Hom.rightEvaluation X.as⟧
          coevaluation_evaluation' := Quotient.sound (right_coevaluation_evaluation X.as)
          evaluation_coevaluation' := Quotient.sound (right_evaluation_coevaluation X.as) } }

instance : LeftRigidCategory S.FreeRigid where
  leftDual X :=
    { leftDual := ⟨X.as.leftDual⟩
      exact :=
        { coevaluation' := ⟦Hom.leftCoevaluation X.as⟧, evaluation' := ⟦Hom.leftEvaluation X.as⟧
          coevaluation_evaluation' := Quotient.sound (left_coevaluation_evaluation X.as)
          evaluation_coevaluation' := Quotient.sound (left_evaluation_coevaluation X.as) } }

instance : RigidCategory S.FreeRigid where

end Instances

theorem as_of (a : S.Obj) : (of a).as = .of a := rfl
theorem as_tensorUnit : (𝟙_ S.FreeRigid).as = .unit := rfl
theorem as_tensor (X Y : S.FreeRigid) : (X ⊗ Y).as = X.as.tensor Y.as := rfl
theorem as_rightDual (X : S.FreeRigid) : (Xᘁ).as = X.as.rightDual := rfl
theorem as_leftDual (X : S.FreeRigid) : (ᘁX).as = X.as.leftDual := rfl

/-- Interpreting a formal rigid object expression via the generating objects of `S.FreeRigid`
recovers the object wrapping that expression. -/
@[simp] theorem eval_of_eq (X : RigidObject S.Obj) :
    RigidObject.eval (of (S := S)) X = ⟨X⟩ := by
  induction X with
  | of _ | unit => rfl
  | tensor _ _ ihX ihY => dsimp only [RigidObject.eval]; rw [ihX, ihY]; rfl
  | rightDual _ ih | leftDual _ ih => dsimp only [RigidObject.eval]; rw [ih]; rfl

/-- The morphism of `S.FreeRigid` represented by a formal morphism expression. -/
abbrev homMk {X Y : S.FreeRigid} (f : Hom X.as Y.as) : X ⟶ Y := ⟦f⟧

/-- The generating morphism given by a coupon, from its source rigid expression to its target rigid
expression. -/
@[expose] def coupon (g : S.Coupon) : (⟨S.src g⟩ : S.FreeRigid) ⟶ ⟨S.tgt g⟩ :=
  homMk (Hom.coupon g)

@[simp] theorem homMk_id (X : S.FreeRigid) : homMk (Hom.id X.as) = 𝟙 X := rfl
@[simp] theorem homMk_comp {X Y Z : S.FreeRigid} (f : Hom X.as Y.as) (g : Hom Y.as Z.as) :
    homMk (Y := Z) (f.comp g) = homMk f ≫ homMk g := rfl
@[simp] theorem homMk_tensor {X₁ Y₁ X₂ Y₂ : S.FreeRigid} (f : Hom X₁.as Y₁.as)
    (g : Hom X₂.as Y₂.as) :
    homMk (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (f.tensor g) = homMk f ⊗ₘ homMk g := rfl
@[simp] theorem homMk_whiskerLeft (X : S.FreeRigid) {Y₁ Y₂ : S.FreeRigid} (f : Hom Y₁.as Y₂.as) :
    homMk (X := X ⊗ Y₁) (Y := X ⊗ Y₂) (f.whiskerLeft X.as) = X ◁ homMk f := rfl
@[simp] theorem homMk_whiskerRight {X₁ X₂ : S.FreeRigid} (f : Hom X₁.as X₂.as) (Y : S.FreeRigid) :
    homMk (X := X₁ ⊗ Y) (Y := X₂ ⊗ Y) (f.whiskerRight Y.as) = homMk f ▷ Y := rfl
@[simp] theorem homMk_α_hom (X Y Z : S.FreeRigid) :
    homMk (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (Hom.α_hom X.as Y.as Z.as) = (α_ X Y Z).hom := rfl
@[simp] theorem homMk_α_inv (X Y Z : S.FreeRigid) :
    homMk (X := X ⊗ (Y ⊗ Z)) (Y := (X ⊗ Y) ⊗ Z) (Hom.α_inv X.as Y.as Z.as) = (α_ X Y Z).inv := rfl
@[simp] theorem homMk_l_hom (X : S.FreeRigid) :
    homMk (X := 𝟙_ _ ⊗ X) (Hom.l_hom X.as) = (λ_ X).hom := rfl
@[simp] theorem homMk_l_inv (X : S.FreeRigid) :
    homMk (Y := 𝟙_ _ ⊗ X) (Hom.l_inv X.as) = (λ_ X).inv := rfl
@[simp] theorem homMk_ρ_hom (X : S.FreeRigid) :
    homMk (X := X ⊗ 𝟙_ _) (Hom.ρ_hom X.as) = (ρ_ X).hom := rfl
@[simp] theorem homMk_ρ_inv (X : S.FreeRigid) :
    homMk (Y := X ⊗ 𝟙_ _) (Hom.ρ_inv X.as) = (ρ_ X).inv := rfl
@[simp] theorem homMk_rightCoevaluation (X : S.FreeRigid) :
    homMk (X := 𝟙_ _) (Y := X ⊗ Xᘁ) (Hom.rightCoevaluation X.as) = η_ X (Xᘁ) := rfl
@[simp] theorem homMk_rightEvaluation (X : S.FreeRigid) :
    homMk (X := Xᘁ ⊗ X) (Y := 𝟙_ _) (Hom.rightEvaluation X.as) = ε_ X (Xᘁ) := rfl
@[simp] theorem homMk_leftCoevaluation (X : S.FreeRigid) :
    homMk (X := 𝟙_ _) (Y := (ᘁX) ⊗ X) (Hom.leftCoevaluation X.as) = η_ (ᘁX) X := rfl
@[simp] theorem homMk_leftEvaluation (X : S.FreeRigid) :
    homMk (X := X ⊗ (ᘁX)) (Y := 𝟙_ _) (Hom.leftEvaluation X.as) = ε_ (ᘁX) X := rfl
@[simp] theorem homMk_coupon (g : S.Coupon) :
    homMk (X := ⟨S.src g⟩) (Y := ⟨S.tgt g⟩) (Hom.coupon g) = coupon g := rfl

/-- Induction principle for morphisms of the free rigid category: a property of morphisms holding
for identities, associators, unitors, right and left coevaluations and evaluations, and coupons,
and stable under composition and whiskering on either side, holds for every morphism. -/
theorem Hom.inductionOn {motive : {X Y : S.FreeRigid} → (X ⟶ Y) → Prop} {X Y : S.FreeRigid}
    (t : X ⟶ Y)
    (id : (X : S.FreeRigid) → motive (𝟙 X))
    (α_hom : (X Y Z : S.FreeRigid) → motive (α_ X Y Z).hom)
    (α_inv : (X Y Z : S.FreeRigid) → motive (α_ X Y Z).inv)
    (l_hom : (X : S.FreeRigid) → motive (λ_ X).hom)
    (l_inv : (X : S.FreeRigid) → motive (λ_ X).inv)
    (ρ_hom : (X : S.FreeRigid) → motive (ρ_ X).hom)
    (ρ_inv : (X : S.FreeRigid) → motive (ρ_ X).inv)
    (rightCoevaluation : (X : S.FreeRigid) → motive (η_ X (Xᘁ)))
    (rightEvaluation : (X : S.FreeRigid) → motive (ε_ X (Xᘁ)))
    (leftCoevaluation : (X : S.FreeRigid) → motive (η_ (ᘁX) X))
    (leftEvaluation : (X : S.FreeRigid) → motive (ε_ (ᘁX) X))
    (coupon : (g : S.Coupon) → motive (FreeRigid.coupon g))
    (comp : {X Y Z : S.FreeRigid} → (f : X ⟶ Y) → (g : Y ⟶ Z) → motive f → motive g →
      motive (f ≫ g))
    (whiskerLeft : (X : S.FreeRigid) → {Y Z : S.FreeRigid} → (f : Y ⟶ Z) → motive f →
      motive (X ◁ f))
    (whiskerRight : {X Y : S.FreeRigid} → (f : X ⟶ Y) → (Z : S.FreeRigid) → motive f →
      motive (f ▷ Z)) :
    motive t := by
  suffices H : ∀ {X Y : RigidObject S.Obj} (f : Hom X Y),
      motive (homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) by
    induction t using Quotient.inductionOn with | _ f => exact H f
  intro X Y f; induction f with
  | id X => exact id ⟨X⟩
  | α_hom X Y Z => exact α_hom ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact α_inv ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact l_hom ⟨X⟩
  | l_inv X => exact l_inv ⟨X⟩
  | ρ_hom X => exact ρ_hom ⟨X⟩
  | ρ_inv X => exact ρ_inv ⟨X⟩
  | rightCoevaluation X => exact rightCoevaluation ⟨X⟩
  | rightEvaluation X => exact rightEvaluation ⟨X⟩
  | leftCoevaluation X => exact leftCoevaluation ⟨X⟩
  | leftEvaluation X => exact leftEvaluation ⟨X⟩
  | coupon g => exact coupon g
  | comp _ _ hf hg => exact comp _ _ hf hg
  | whiskerLeft X _ hf => exact whiskerLeft ⟨X⟩ _ hf
  | whiskerRight _ X hf => exact whiskerRight _ ⟨X⟩ hf
  | @tensor W X Y Z f g hf hg =>
    rw [show (homMk (f.tensor g) : (⟨W.tensor X⟩ : S.FreeRigid) ⟶ ⟨Y.tensor Z⟩) =
        homMk (X := ⟨W⟩) (Y := ⟨Y⟩) f ▷ (⟨X⟩ : S.FreeRigid) ≫
          (⟨Y⟩ : S.FreeRigid) ◁ homMk (X := ⟨X⟩) (Y := ⟨Z⟩) g from
      Quotient.sound (.tensorHom_def f g)]
    exact comp _ _ (whiskerRight _ _ hf) (whiskerLeft _ _ hg)

end FreeRigid

end DualitySignature

namespace TensorSignature.FreeMonoidal

variable (S : TensorSignature.{u, v})

/-- Interpreting a dual-free monoidal word via the generating objects of
`S.toDualitySignature.FreeRigid` produces the object whose underlying `RigidObject` is
`W.toRigidObject`. -/
@[simp] theorem projectObj_of_eq (W : FreeMonoidalCategory S.Obj) :
    FreeMonoidalCategory.projectObj (fun a : S.Obj ↦
      DualitySignature.FreeRigid.of (S := S.toDualitySignature) a) W = ⟨W.toRigidObject⟩ := by
  induction W with
  | of _ | unit => simp [FreeMonoidalCategory.projectObj]; rfl
  | tensor _ _ ihX ihY => simp [FreeMonoidalCategory.projectObj, ihX, ihY]; rfl

/-- The canonical strong monoidal functor from the free monoidal category on a tensor signature
`S` to the free rigid category on `S.toDualitySignature`, obtained by the universal lift of
`FreeMonoidal`. -/
@[expose] def toFreeRigid : S.FreeMonoidal ⥤ S.toDualitySignature.FreeRigid :=
  FreeMonoidal.lift (fun a : S.Obj ↦ DualitySignature.FreeRigid.of (S := S.toDualitySignature) a)
    fun g ↦ eqToHom (projectObj_of_eq S (S.src g)) ≫
      DualitySignature.FreeRigid.coupon (S := S.toDualitySignature) g ≫
      eqToHom (projectObj_of_eq S (S.tgt g)).symm

instance : (toFreeRigid S).Monoidal := by delta toFreeRigid; infer_instance

@[simp] theorem toFreeRigid_obj (X : S.FreeMonoidal) :
    (toFreeRigid S).obj X = ⟨X.as.toRigidObject⟩ := projectObj_of_eq S X.as
@[simp] theorem toFreeRigid_obj_of (a : S.Obj) :
    (toFreeRigid S).obj (of a) = DualitySignature.FreeRigid.of a := rfl

theorem toFreeRigid_map_coupon (g : S.Coupon) : (toFreeRigid S).map (coupon g) =
    eqToHom (toFreeRigid_obj S ⟨S.src g⟩) ≫
      DualitySignature.FreeRigid.coupon (S := S.toDualitySignature) g ≫
      eqToHom (toFreeRigid_obj S ⟨S.tgt g⟩).symm := FreeMonoidal.lift_map_coupon _ _ g

@[simp] theorem toFreeRigid_ε :
    Functor.LaxMonoidal.ε (toFreeRigid S) = 𝟙 _ := FreeMonoidal.lift_ε _ _
@[simp] theorem toFreeRigid_η :
    Functor.OplaxMonoidal.η (toFreeRigid S) = 𝟙 _ := FreeMonoidal.lift_η _ _
@[simp] theorem toFreeRigid_μ (X Y : S.FreeMonoidal) :
    Functor.LaxMonoidal.μ (toFreeRigid S) X Y = 𝟙 _ := FreeMonoidal.lift_μ _ _ X Y
@[simp] theorem toFreeRigid_δ (X Y : S.FreeMonoidal) :
    Functor.OplaxMonoidal.δ (toFreeRigid S) X Y = 𝟙 _ := FreeMonoidal.lift_δ _ _ X Y

end TensorSignature.FreeMonoidal

end TauCeti
