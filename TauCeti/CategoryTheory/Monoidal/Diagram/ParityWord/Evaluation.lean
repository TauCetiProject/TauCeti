/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.ParityWord.Substitution
public import TauCeti.CategoryTheory.Monoidal.TensorList.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Basic

/-!
# Categorical evaluation of parity boundary words

This file evaluates `ParityWord α = List (α × ZMod 2)` in right rigid and pivotal monoidal
categories using `TauCeti.tensorList`.

* `TauCeti.parityDual`: `ZMod 2`-indexed chosen right duality (`0 ↦ X`, `1 ↦ Xᘁ`) in any
  `[RightRigidCategory C]`.
* `TauCeti.ParityWord.evalObj`: right-associated tensor evaluation of `ParityWord α` in
  `[RightRigidCategory C]`, together with `ParityWord.evalObjSingletonIso` and
  `ParityWord.evalObjAppendIso` (constructed without `eqToHom`).
* `TauCeti.parityDualRightDualIso`, `TauCeti.ParityWord.evalObjDualIso`,
  `TauCeti.ParityWord.evalObjDualPowIso`, and `TauCeti.ParityWord.evalObjSubstIso`: pivotal
  duality, `ZMod 2` dual-power, and multi-port substitution comparisons on evaluated parity words
  in `[RigidCategory C] [PivotalCategory C]`, all constructed without `eqToHom`.

## References

* [P. Freyd and D. Yetter, *Braided compact closed categories with applications to low dimensional
  topology*][freydyetter1989]
* [A. Joyal and R. Street, *Planar diagrams and tensor algebra*][joyalStreet1988]
* [P. Selinger, *A survey of graphical languages for monoidal categories*][selinger2011], §4.4
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Parity-indexed duality and evaluation of parity words -/

section RightRigid

variable [RightRigidCategory C]

/-- `ZMod 2`-indexed chosen right dual of `X`: parity `0` is `X` and parity `1` is the chosen right
dual `(RightRigidCategory.rightDual X).rightDual`. -/
@[expose]
def parityDual (X : C) : ZMod 2 → C
  | ⟨0, _⟩ => X
  | ⟨1, _⟩ => (RightRigidCategory.rightDual X).rightDual

@[simp]
theorem parityDual_zero (X : C) : parityDual X 0 = X := by rfl

@[simp]
theorem parityDual_one (X : C) :
    parityDual X 1 = (RightRigidCategory.rightDual X).rightDual := by rfl

end RightRigid

namespace ParityWord

section RightRigid

variable [RightRigidCategory C]

/-- Evaluate `L : ParityWord α` in a right rigid monoidal category `C` as the right-associated
tensor product of `parityDual (f p.1) p.2`. -/
@[expose]
def evalObj {α : Type*} (f : α → C) (L : ParityWord α) : C :=
  tensorList (fun p : α × ZMod 2 ↦ parityDual (f p.1) p.2) L

@[simp]
theorem evalObj_nil {α : Type*} (f : α → C) :
    evalObj f ([] : ParityWord α) = 𝟙_ C := by rfl

@[simp]
theorem evalObj_cons {α : Type*} (f : α → C) (p : α × ZMod 2) (L : ParityWord α) :
    evalObj f (p :: L) = parityDual (f p.1) p.2 ⊗ evalObj f L := by rfl

/-- Right-unitor isomorphism `evalObj f [p] ≅ parityDual (f p.1) p.2` on a single port. -/
def evalObjSingletonIso {α : Type*} (f : α → C) (p : α × ZMod 2) :
    evalObj f [p] ≅ parityDual (f p.1) p.2 :=
  tensorListSingletonIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2) p

/-- Concatenation comparison `evalObj f L ⊗ evalObj f M ≅ evalObj f (L ++ M)` built without
`eqToHom`. -/
def evalObjAppendIso {α : Type*} (f : α → C) (L M : ParityWord α) :
    evalObj f L ⊗ evalObj f M ≅ evalObj f (L ++ M) :=
  tensorListAppendIso (fun p : α × ZMod 2 ↦ parityDual (f p.1) p.2) L M

@[simp]
theorem evalObjAppendIso_nil {α : Type*} (f : α → C) (M : ParityWord α) :
    evalObjAppendIso f [] M = λ_ (evalObj f M) :=
  tensorListAppendIso_nil _ M

/-- Recursive step of `ParityWord.evalObjAppendIso` on `p :: L`. -/
theorem evalObjAppendIso_cons_hom {α : Type*} (f : α → C) (p : α × ZMod 2) (L M : ParityWord α) :
    (evalObjAppendIso f (p :: L) M).hom =
      (α_ (parityDual (f p.1) p.2) (evalObj f L) (evalObj f M)).hom ≫
        parityDual (f p.1) p.2 ◁ (evalObjAppendIso f L M).hom :=
  tensorListAppendIso_cons_hom _ p L M

end RightRigid

end ParityWord

/-! ### Pivotal boundary duality on parity words -/

section PivotalParity

variable [RigidCategory C] [PivotalCategory C]

/-- Pivotal comparison `(parityDual X ε)ᘁ ≅ parityDual X (ε + 1)` built without `eqToHom`:
at parity `0` it is `Iso.refl Xᘁ`, and at parity `1` it is `(pivotalIsoApp X).symm : Xᘁᘁ ≅ X`. -/
@[expose]
noncomputable def parityDualRightDualIso (X : C) :
    (ε : ZMod 2) → (RightRigidCategory.rightDual (parityDual X ε)).rightDual ≅ parityDual X (ε + 1)
  | ⟨0, _⟩ => Iso.refl _
  | ⟨1, _⟩ => (pivotalIsoApp X).symm

@[simp]
theorem parityDualRightDualIso_zero (X : C) :
    parityDualRightDualIso X 0 = Iso.refl (RightRigidCategory.rightDual X).rightDual := by rfl

@[simp]
theorem parityDualRightDualIso_one (X : C) :
    parityDualRightDualIso X 1 = (pivotalIsoApp X).symm := by rfl

namespace ParityWord

/-- `eqToHom`-free pivotal comparison `(evalObj f L)ᘁ ≅ evalObj f L.dual`, reversing the tensor
factors via `(rightDualFunctor C).opMopTensorListIso` and flipping parities via
`parityDualRightDualIso`. -/
noncomputable def evalObjDualIso {α : Type*} (f : α → C) (L : ParityWord α) :
    (RightRigidCategory.rightDual (evalObj f L)).rightDual ≅ evalObj f L.dual :=
  (rightDualFunctor C).opMopTensorListIso (fun p : α × ZMod 2 ↦ parityDual (f p.1) p.2) L ≪≫
    tensorListCongrIso (fun p : α × ZMod 2 ↦ parityDualRightDualIso (f p.1) p.2) L.reverse ≪≫
    tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
      (fun p : α × ZMod 2 ↦ (p.1, p.2 + 1)) L.reverse

/-- Explicit forward morphism of `ParityWord.evalObjDualIso`. -/
theorem evalObjDualIso_hom {α : Type*} (f : α → C) (L : ParityWord α) :
    (evalObjDualIso f L).hom =
      ((rightDualFunctor C).opMopTensorListIso
          (fun p : α × ZMod 2 ↦ parityDual (f p.1) p.2) L).hom ≫
        tensorListCongrHom (fun p : α × ZMod 2 ↦ (parityDualRightDualIso (f p.1) p.2).hom)
          L.reverse ≫
        (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
          (fun p : α × ZMod 2 ↦ (p.1, p.2 + 1)) L.reverse).hom := by
  exact congrArg (fun g ↦ _ ≫ g ≫ _) (tensorListCongrIso_hom _ _)

/-- `eqToHom`-free `ZMod 2` dual-power comparison
`parityDual (evalObj f L) ε ≅ evalObj f (L.dualPow ε)`. -/
noncomputable def evalObjDualPowIso {α : Type*} (f : α → C) :
    (ε : ZMod 2) → (L : ParityWord α) → parityDual (evalObj f L) ε ≅ evalObj f (L.dualPow ε)
  | ⟨0, _⟩, L => Iso.refl (evalObj f L)
  | ⟨1, _⟩, L => evalObjDualIso f L

@[simp]
theorem evalObjDualPowIso_zero {α : Type*} (f : α → C) (L : ParityWord α) :
    evalObjDualPowIso f 0 L = Iso.refl (evalObj f L) := by rfl

@[simp]
theorem evalObjDualPowIso_one {α : Type*} (f : α → C) (L : ParityWord α) :
    evalObjDualPowIso f 1 L = evalObjDualIso f L := by rfl

/-- `eqToHom`-free substitution comparison
`evalObj (fun a ↦ evalObj f (σ a)) L ≅ evalObj f (L.subst σ)`. -/
noncomputable def evalObjSubstIso {α β : Type*} (f : β → C) (σ : α → ParityWord β)
    (L : ParityWord α) :
    evalObj (fun a ↦ evalObj f (σ a)) L ≅ evalObj f (L.subst σ) :=
  tensorListCongrIso (fun p : α × ZMod 2 ↦ evalObjDualPowIso f p.2 (σ p.1)) L ≪≫
    tensorListFlatMapIso (fun q : β × ZMod 2 ↦ parityDual (f q.1) q.2)
      (fun p : α × ZMod 2 ↦ (σ p.1).dualPow p.2) L

end ParityWord

end PivotalParity

end TauCeti
