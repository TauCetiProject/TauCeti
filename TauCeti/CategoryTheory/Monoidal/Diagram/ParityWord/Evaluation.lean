/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.ParityWord.Substitution
public import TauCeti.CategoryTheory.Monoidal.TensorList.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Categorical evaluation of parity boundary words

Evaluating a parity boundary word `ParityWord α = List (α × ZMod 2)` on objects requires only
`[RightRigidCategory C]`, assigning `X` at parity `0` and the chosen right dual `Xᘁ` at parity `1`
(`TauCeti.parityDual`, `TauCeti.ParityWord.eval`). By contrast, promoting boundary duality
(`ParityWord.dual`) and multi-port substitution (`ParityWord.subst`) to categorical comparison
isomorphisms requires identifying `Xᘁᘁ` with `X` via a pivotal structure `[PivotalCategory C]`.
These structural comparisons mirror `WindingWord.eval`, `WindingWord.evalAppendIso`,
`WindingWord.evalRightDualIso`, `WindingWord.evalDualPowIso`, and `WindingWord.evalSubstIso`, and
feed the pivotal boundary reduction in `TauCeti.CategoryTheory.Monoidal.Diagram.ParityWord.Pivotal`.

## Main declarations

* `TauCeti.parityDual`, `TauCeti.parityDualMapIso`, and `TauCeti.ParityWord.eval`:
  `ZMod 2`-indexed chosen right duality (`0 ↦ X`, `1 ↦ Xᘁ`), its action on isomorphisms, and
  right-associated word evaluation in `[RightRigidCategory C]`, with `ParityWord.evalAppendIso` and
  `ParityWord.evalCongrIso`;
* `TauCeti.parityDualRightDualIso`, `TauCeti.ParityWord.evalDualIso`,
  `TauCeti.ParityWord.evalDualPowIso`, and `TauCeti.ParityWord.evalSubstIso`: pivotal duality,
  `ZMod 2` dual-power, and multi-port substitution comparisons in
  `[RigidCategory C] [PivotalCategory C]`.

## References

* P. Freyd and D. Yetter, *Coherence theorems via knot theory*, J. Pure Appl. Algebra 78 (1992),
  49–76, §4.
* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, §2.
* P. Selinger, *A survey of graphical languages for monoidal categories*, §4.2.
-/

public section

open CategoryTheory MonoidalCategory
open scoped CharTwo

namespace TauCeti

universe v u w w'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section RightRigid

variable [RightRigidCategory C]

/-- `ZMod 2`-indexed chosen right dual of `X`: parity `0` is `X` and parity `1` is `Xᘁ`. -/
@[expose]
def parityDual : ZMod 2 → C → C
  | ⟨0, _⟩, X => X
  | ⟨1, _⟩, X => Xᘁ

@[simp] theorem parityDual_zero (X : C) : parityDual 0 X = X := (rfl)

@[simp] theorem parityDual_one (X : C) : parityDual 1 X = Xᘁ := (rfl)

/-- Action of `parityDual ε` on an isomorphism `e : X ≅ Y`: covariant at parity `0` (`e`) and via
`e.symm.rightAdjointMate` at parity `1`. -/
def parityDualMapIso : (ε : ZMod 2) → {X Y : C} → (X ≅ Y) → (parityDual ε X ≅ parityDual ε Y)
  | ⟨0, _⟩, _, _, e => e
  | ⟨1, _⟩, _, _, e => e.symm.rightAdjointMate

@[simp] theorem parityDualMapIso_zero {X Y : C} (e : X ≅ Y) :
    parityDualMapIso 0 e = e := (rfl)

@[simp] theorem parityDualMapIso_one {X Y : C} (e : X ≅ Y) :
    parityDualMapIso 1 e = e.symm.rightAdjointMate := (rfl)

namespace ParityWord

variable {α : Type w}

/-- Evaluate `L : ParityWord α` in a right rigid monoidal category: the port `(a, ε)` becomes
`parityDual ε (f a)`, and the word is the right-associated tensor product of its ports ending in
`𝟙_ C`. -/
@[expose]
def eval (f : α → C) : ParityWord α → C
  | [] => 𝟙_ C
  | p :: L => parityDual p.2 (f p.1) ⊗ eval f L

@[simp] theorem eval_nil (f : α → C) : eval f ([] : ParityWord α) = 𝟙_ C := (rfl)

@[simp] theorem eval_cons (f : α → C) (p : α × ZMod 2) (L : ParityWord α) :
    eval f (p :: L) = parityDual p.2 (f p.1) ⊗ eval f L := (rfl)

/-- `ParityWord.eval` agrees with `TauCeti.tensorList` applied to `parityDual`. -/
theorem eval_eq_tensorList (f : α → C) (L : ParityWord α) :
    eval f L = tensorList (fun p : α × ZMod 2 ↦ parityDual p.2 (f p.1)) L := by
  induction L with
  | nil => rfl
  | cons p L ih => exact congrArg (parityDual p.2 (f p.1) ⊗ ·) ih

/-- The evaluation of a concatenation of parity words is the tensor product of their evaluations. -/
def evalAppendIso (f : α → C) : (L M : ParityWord α) → eval f (L ++ M) ≅ eval f L ⊗ eval f M
  | [], M => (λ_ (eval f M)).symm
  | p :: L, M => whiskerLeftIso (parityDual p.2 (f p.1)) (evalAppendIso f L M) ≪≫ (α_ _ _ _).symm

@[simp] theorem evalAppendIso_nil (f : α → C) (M : ParityWord α) :
    evalAppendIso f [] M = (λ_ (eval f M)).symm := (rfl)

@[simp] theorem evalAppendIso_cons (f : α → C) (p : α × ZMod 2) (L M : ParityWord α) :
    evalAppendIso f (p :: L) M =
      whiskerLeftIso (parityDual p.2 (f p.1)) (evalAppendIso f L M) ≪≫ (α_ _ _ _).symm := (rfl)

/-- Associativity of `evalAppendIso` across triple concatenations `(L ++ M) ++ N`. -/
@[reassoc]
theorem evalAppendIso_assoc_hom (f : α → C) (L M N : ParityWord α) :
    eqToHom (congrArg (eval f) (List.append_assoc L M N).symm) ≫
        (evalAppendIso f (L ++ M) N).hom ≫ ((evalAppendIso f L M).hom ▷ eval f N) =
      (evalAppendIso f L (M ++ N)).hom ≫ (eval f L ◁ (evalAppendIso f M N).hom) ≫
        (α_ (eval f L) (eval f M) (eval f N)).inv := by
  induction L with
  | nil =>
    dsimp only [List.nil_append, eval]
    simp [leftUnitor_inv_whiskerRight]
  | cons p L ih =>
    have heq : eqToHom (congrArg (eval f) (List.append_assoc (p :: L) M N).symm) =
        parityDual p.2 (f p.1) ◁ eqToHom (congrArg (eval f) (List.append_assoc L M N).symm) :=
      (MonoidalCategory.whiskerLeft_eqToHom (parityDual p.2 (f p.1))
        (congrArg (eval f) (List.append_assoc L M N).symm)).symm
    rw [heq]
    dsimp only [List.cons_append, eval]
    simp only [evalAppendIso_cons, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom]
    calc _ = (parityDual p.2 (f p.1) ◁
            (eqToHom (congrArg (eval f) (List.append_assoc L M N).symm) ≫
              (evalAppendIso f (L ++ M) N).hom ≫ ((evalAppendIso f L M).hom ▷ eval f N))) ≫
          ((α_ (parityDual p.2 (f p.1)) (eval f L ⊗ eval f M) (eval f N)).inv ≫
            ((α_ (parityDual p.2 (f p.1)) (eval f L) (eval f M)).inv ▷ eval f N)) := by
          simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
          monoidal
      _ = _ := by
          rw [ih]
          simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
          monoidal

/-- Pointwise isomorphisms `e a : f₁ a ≅ f₂ a` of generator valuations induce an isomorphism
`eval f₁ L ≅ eval f₂ L`. -/
def evalCongrIso {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) :
    (L : ParityWord α) → eval f₁ L ≅ eval f₂ L
  | [] => Iso.refl (𝟙_ C)
  | p :: L => parityDualMapIso p.2 (e p.1) ⊗ᵢ evalCongrIso e L

@[simp] theorem evalCongrIso_nil {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) :
    evalCongrIso e [] = Iso.refl (𝟙_ C) := (rfl)

@[simp] theorem evalCongrIso_cons {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (p : α × ZMod 2)
    (L : ParityWord α) :
    evalCongrIso e (p :: L) = parityDualMapIso p.2 (e p.1) ⊗ᵢ evalCongrIso e L := (rfl)

/-- `evalAppendIso` is natural with respect to `evalCongrIso`. -/
@[reassoc]
theorem evalAppendIso_hom_naturality {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a)
    (L M : ParityWord α) :
    (evalCongrIso e (L ++ M)).hom ≫ (evalAppendIso f₂ L M).hom =
      (evalAppendIso f₁ L M).hom ≫ ((evalCongrIso e L).hom ⊗ₘ (evalCongrIso e M).hom) := by
  induction L with
  | nil =>
    dsimp only [List.nil_append, eval]
    simp
  | cons p L ih =>
    dsimp only [List.cons_append, eval]
    simp only [evalCongrIso_cons, evalAppendIso_cons, tensorIso_hom, Iso.trans_hom,
      whiskerLeftIso_hom, Iso.symm_hom, Category.assoc]
    rw [tensorHom_def'_assoc, ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ih, MonoidalCategory.whiskerLeft_comp_assoc, ← tensorHom_def'_assoc,
      associator_inv_naturality]

end ParityWord

end RightRigid

section PivotalParity

variable [RigidCategory C] [PivotalCategory C]

/-- Pivotal comparison `(parityDual ε X)ᘁ ≅ parityDual (ε + 1) X`: `Iso.refl Xᘁ` at parity `0` and
`(pivotalIsoApp X).symm : Xᘁᘁ ≅ X` at parity `1`. -/
noncomputable def parityDualRightDualIso :
    (ε : ZMod 2) → (X : C) → (parityDual ε X)ᘁ ≅ parityDual (ε + 1) X
  | ⟨0, _⟩, X => Iso.refl Xᘁ
  | ⟨1, _⟩, X => (pivotalIsoApp X).symm

@[simp] theorem parityDualRightDualIso_zero (X : C) :
    parityDualRightDualIso 0 X = Iso.refl Xᘁ := (rfl)

@[simp] theorem parityDualRightDualIso_one (X : C) :
    parityDualRightDualIso 1 X = (pivotalIsoApp X).symm := (rfl)

/-- Naturality of `parityDualRightDualIso ε` with respect to an isomorphism `e : X ≅ Y`. -/
@[reassoc]
theorem parityDualRightDualIso_hom_naturality :
    (ε : ZMod 2) → {X Y : C} → (e : X ≅ Y) →
      (parityDualMapIso ε e).invᘁ ≫ (parityDualRightDualIso ε Y).hom =
        (parityDualRightDualIso ε X).hom ≫ (parityDualMapIso (ε + 1) e).hom
  | ⟨0, _⟩, _, _, e =>
    (Category.comp_id _).trans ((Category.id_comp _).symm.trans
      (congrArg (𝟙 _ ≫ ·) (Iso.rightAdjointMate_hom e.symm).symm))
  | ⟨1, _⟩, X, Y, e =>
    (congrArg (fun f : Yᘁ ⟶ Xᘁ ↦ fᘁ ≫ (pivotalIsoApp Y).inv)
      (Iso.rightAdjointMate_inv e.symm)).trans (pivotalIsoApp_inv_naturality e.hom)

namespace ParityWord

variable {α : Type w} {β : Type w'}

/-- Pivotal comparison `(eval f L)ᘁ ≅ eval f L.dual`: the tensor order reverses, the dual of the
unit is identified with the unit, and each port's parity flips via `parityDualRightDualIso`. -/
noncomputable def evalDualIso (f : α → C) :
    (L : ParityWord α) → (eval f L)ᘁ ≅ eval f (dual L)
  | [] => rightDualUnitIso C ≪≫ eqToIso (by simp)
  | p :: L =>
    rightDualTensorIso _ _ ≪≫
      (evalDualIso f L ⊗ᵢ (parityDualRightDualIso p.2 (f p.1) ≪≫ (ρ_ _).symm)) ≪≫
      (evalAppendIso f (dual L) [(p.1, p.2 + 1)]).symm ≪≫
      eqToIso (congrArg (eval f) (dual_cons p L).symm)

@[simp] theorem evalDualIso_nil (f : α → C) :
    evalDualIso f [] = rightDualUnitIso C ≪≫ eqToIso (by simp) := (rfl)

@[simp] theorem evalDualIso_cons (f : α → C) (p : α × ZMod 2) (L : ParityWord α) :
    evalDualIso f (p :: L) =
      rightDualTensorIso _ _ ≪≫
        (evalDualIso f L ⊗ᵢ (parityDualRightDualIso p.2 (f p.1) ≪≫ (ρ_ _).symm)) ≪≫
        (evalAppendIso f (dual L) [(p.1, p.2 + 1)]).symm ≪≫
        eqToIso (congrArg (eval f) (dual_cons p L).symm) := (rfl)

/-- `ZMod 2` dual-power comparison `eval f (dualPow ε L) ≅ parityDual ε (eval f L)`, matching the
direction of `WindingWord.evalDualPowIso`. -/
noncomputable def evalDualPowIso (f : α → C) :
    (ε : ZMod 2) → (L : ParityWord α) → eval f (dualPow ε L) ≅ parityDual ε (eval f L)
  | ⟨0, h⟩, L =>
      eqToIso (by rw [show (⟨0, h⟩ : ZMod 2) = (0 : ZMod 2) from rfl]; simp)
  | ⟨1, h⟩, L =>
      eqToIso (by rw [show (⟨1, h⟩ : ZMod 2) = (1 : ZMod 2) from rfl]; simp) ≪≫
        (evalDualIso f L).symm

@[simp] theorem evalDualPowIso_zero (f : α → C) (L : ParityWord α) :
    evalDualPowIso f 0 L = eqToIso (by simp) := (rfl)

@[simp] theorem evalDualPowIso_one (f : α → C) (L : ParityWord α) :
    evalDualPowIso f 1 L = eqToIso (by simp) ≪≫ (evalDualIso f L).symm := (rfl)

/-- Multi-port substitution comparison `eval g (subst F L) ≅ eval (fun a ↦ eval g (F a)) L`,
matching the recursive form of `WindingWord.evalSubstIso`. -/
noncomputable def evalSubstIso (g : β → C) (F : α → ParityWord β) :
    (L : ParityWord α) → eval g (subst F L) ≅ eval (fun a ↦ eval g (F a)) L
  | [] => eqToIso (by simp)
  | p :: L =>
    eqToIso (congrArg (eval g) (subst_cons F p L)) ≪≫
      evalAppendIso g (dualPow p.2 (F p.1)) (subst F L) ≪≫
      (evalDualPowIso g p.2 (F p.1) ⊗ᵢ evalSubstIso g F L)

@[simp] theorem evalSubstIso_nil (g : β → C) (F : α → ParityWord β) :
    evalSubstIso g F [] = eqToIso (by simp) := (rfl)

@[simp] theorem evalSubstIso_cons (g : β → C) (F : α → ParityWord β) (p : α × ZMod 2)
    (L : ParityWord α) :
    evalSubstIso g F (p :: L) =
      eqToIso (congrArg (eval g) (subst_cons F p L)) ≪≫
        evalAppendIso g (dualPow p.2 (F p.1)) (subst F L) ≪≫
        (evalDualPowIso g p.2 (F p.1) ⊗ᵢ evalSubstIso g F L) := (rfl)

/-- `evalSubstIso` respects concatenation of parity words via `evalAppendIso`. -/
@[reassoc]
theorem evalSubstIso_append_hom (g : β → C) (F : α → ParityWord β) (L M : ParityWord α) :
    (evalSubstIso g F (L ++ M)).hom ≫
        (evalAppendIso (fun a ↦ eval g (F a)) L M).hom =
      eqToHom (congrArg (eval g) (subst_append F L M)) ≫
        (evalAppendIso g (subst F L) (subst F M)).hom ≫
        ((evalSubstIso g F L).hom ⊗ₘ (evalSubstIso g F M).hom) := by
  induction L with
  | nil =>
    have hNil : ∀ {W : ParityWord β} (_ : W = []) (hm : subst F M = W ++ subst F M)
        (hwEval : eval g W = 𝟙_ C),
        eqToHom (congrArg (eval g) hm) ≫
          (evalAppendIso g W (subst F M)).hom ≫
          (eqToHom hwEval ⊗ₘ (evalSubstIso g F M).hom) =
        (evalSubstIso g F M).hom ≫ (λ_ (eval (fun a ↦ eval g (F a)) M)).inv := by
      rintro _ rfl hm hwEval
      have h1 : eqToHom (congrArg (eval g) hm) = 𝟙 (eval g (subst F M)) := eqToHom_refl _ _
      have h2 : eqToHom hwEval = 𝟙 (𝟙_ C) := eqToHom_refl _ _
      rw [evalAppendIso_nil, Iso.symm_hom, h1, h2]
      dsimp only [List.nil_append, eval]
      rw [Category.id_comp, id_tensorHom, leftUnitor_inv_naturality]
    rw [evalSubstIso_nil, evalAppendIso_nil]
    dsimp only [List.nil_append, Iso.symm_hom, eqToIso.hom]
    exact (hNil (subst_nil F) (subst_append F [] M) (by simp)).symm
  | cons p L ih =>
    have hAppAssoc := evalAppendIso_assoc_hom g (dualPow p.2 (F p.1)) (subst F L) (subst F M)
    have hSlide : ∀ {U V : ParityWord β} (hu : U = dualPow p.2 (F p.1) ++ subst F L)
        (huv : dualPow p.2 (F p.1) ++ (subst F L ++ V) = U ++ V),
        eqToHom (congrArg (eval g) huv) ≫
          (evalAppendIso g U V).hom ≫
          (eqToHom (congrArg (eval g) hu) ▷ eval g V) =
        eqToHom (congrArg (eval g)
            (List.append_assoc (dualPow p.2 (F p.1)) (subst F L) V).symm) ≫
          (evalAppendIso g (dualPow p.2 (F p.1) ++ subst F L) V).hom := by
      intro U V hu huv
      subst hu
      simp
    have hNatApp : ∀ {W₁ W₂ : ParityWord β} (hw : W₁ = W₂),
        (evalAppendIso g (dualPow p.2 (F p.1)) W₁).hom ≫
          (eval g (dualPow p.2 (F p.1)) ◁ eqToHom (congrArg (eval g) hw)) =
        eqToHom (congrArg (eval g) (congrArg (dualPow p.2 (F p.1) ++ ·) hw)) ≫
          (evalAppendIso g (dualPow p.2 (F p.1)) W₂).hom := by
      intro W₁ W₂ hw; subst hw; simp
    dsimp only [List.cons_append]
    rw [evalSubstIso_cons, evalSubstIso_cons, evalAppendIso_cons]
    dsimp only [List.cons_append, eval]
    simp only [Iso.trans_hom, eqToIso.hom, tensorIso_hom, whiskerLeftIso_hom, Iso.symm_hom,
      Category.assoc]
    calc _ = eqToHom (congrArg (eval g) (subst_cons F p (L ++ M))) ≫
            (evalAppendIso g (dualPow p.2 (F p.1)) (subst F (L ++ M))).hom ≫
            ((evalDualPowIso g p.2 (F p.1)).hom ⊗ₘ
              ((evalSubstIso g F (L ++ M)).hom ≫
                (evalAppendIso (fun a ↦ eval g (F a)) L M).hom)) ≫
            (α_ (parityDual p.2 (eval g (F p.1)))
              (eval (fun a ↦ eval g (F a)) L)
              (eval (fun a ↦ eval g (F a)) M)).inv := by
          simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
          rw [← whisker_exchange_assoc]
      _ = _ := by
          rw [ih]
          have hSplitR : ∀ {X₁ X₂ Y₁ Y₂ Y₃ Y₄ : C} (u : X₁ ⟶ X₂)
              (v₁ : Y₁ ⟶ Y₂) (v₂ : Y₂ ⟶ Y₃) (v₃ : Y₃ ⟶ Y₄),
              u ⊗ₘ (v₁ ≫ v₂ ≫ v₃) =
                (X₁ ◁ v₁) ≫ (X₁ ◁ v₂) ≫ (u ⊗ₘ v₃) := by
            intros; simp [tensorHom_def']
          rw [hSplitR]
          simp only [Category.assoc]
          rw [associator_inv_naturality,
            reassoc_of% (hNatApp (subst_append F L M)),
            ← reassoc_of% hAppAssoc]
          have hLeft : eqToHom (congrArg (eval g) (subst_cons F p (L ++ M))) ≫
              eqToHom (congrArg (eval g)
                (congrArg (dualPow p.2 (F p.1) ++ ·) (subst_append F L M))) ≫
              eqToHom (congrArg (eval g)
                (List.append_assoc (dualPow p.2 (F p.1)) (subst F L) (subst F M)).symm) ≫
              (evalAppendIso g (dualPow p.2 (F p.1) ++ subst F L) (subst F M)).hom =
            eqToHom (congrArg (eval g) (subst_append F (p :: L) M)) ≫
              (evalAppendIso g (subst F (p :: L)) (subst F M)).hom ≫
              (eqToHom (congrArg (eval g) (subst_cons F p L)) ▷ eval g (subst F M)) := by
            rw [← hSlide (subst_cons F p L)
              (by rw [subst_cons, List.append_assoc])]
            simp only [eqToHom_trans_assoc]
          rw [reassoc_of% hLeft]
          simp only [tensorHom_def', comp_whiskerRight]
          rw [whisker_exchange_assoc
              (eqToHom (congrArg (eval g) (subst_cons F p L)))
              (evalSubstIso g F M).hom,
            whisker_exchange_assoc
              (evalAppendIso g (dualPow p.2 (F p.1)) (subst F L)).hom
              (evalSubstIso g F M).hom]

end ParityWord

end PivotalParity

end TauCeti
