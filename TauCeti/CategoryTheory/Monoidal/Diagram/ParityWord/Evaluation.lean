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

/-- Evaluate `L : ParityWord α` in a right rigid monoidal category as the right-associated list
tensor product (`TauCeti.tensorList`) assigning `parityDual ε (f a)` to each port `(a, ε)` and
ending in `𝟙_ C`. -/
@[expose, reducible]
def eval (f : α → C) (L : ParityWord α) : C :=
  tensorList (fun p : α × ZMod 2 ↦ parityDual p.2 (f p.1)) L

theorem eval_def (f : α → C) (L : ParityWord α) :
    eval f L = tensorList (fun p : α × ZMod 2 ↦ parityDual p.2 (f p.1)) L := (rfl)

theorem eval_nil (f : α → C) : eval f ([] : ParityWord α) = 𝟙_ C := (rfl)

theorem eval_cons (f : α → C) (p : α × ZMod 2) (L : ParityWord α) :
    eval f (p :: L) = parityDual p.2 (f p.1) ⊗ eval f L := (rfl)

/-- The evaluation of a concatenation of parity words is the tensor product of their evaluations,
implemented as the inverse of `TauCeti.tensorListAppendIso`. -/
def evalAppendIso (f : α → C) (L M : ParityWord α) : eval f (L ++ M) ≅ eval f L ⊗ eval f M :=
  (tensorListAppendIso (fun p : α × ZMod 2 ↦ parityDual p.2 (f p.1)) L M).symm

theorem evalAppendIso_def (f : α → C) (L M : ParityWord α) :
    evalAppendIso f L M =
      (tensorListAppendIso (fun p : α × ZMod 2 ↦ parityDual p.2 (f p.1)) L M).symm := (rfl)

@[simp] theorem evalAppendIso_nil (f : α → C) (M : ParityWord α) :
    evalAppendIso f [] M = (λ_ (eval f M)).symm :=
  congrArg Iso.symm (tensorListAppendIso_nil _ M)

@[simp] theorem evalAppendIso_cons (f : α → C) (p : α × ZMod 2) (L M : ParityWord α) :
    evalAppendIso f (p :: L) M =
      whiskerLeftIso (parityDual p.2 (f p.1)) (evalAppendIso f L M) ≪≫ (α_ _ _ _).symm := by
  ext
  exact tensorListAppendIso_cons_inv (fun q : α × ZMod 2 ↦ parityDual q.2 (f q.1)) p L M

/-- Associativity of `evalAppendIso` across triple concatenations `(L ++ M) ++ N`, derived from
`TauCeti.tensorListAppendIso_assoc`. -/
@[reassoc]
theorem evalAppendIso_assoc_hom (f : α → C) (L M N : ParityWord α) :
    eqToHom (congrArg (eval f) (List.append_assoc L M N).symm) ≫
        (evalAppendIso f (L ++ M) N).hom ≫ ((evalAppendIso f L M).hom ▷ eval f N) =
      (evalAppendIso f L (M ++ N)).hom ≫ (eval f L ◁ (evalAppendIso f M N).hom) ≫
        (α_ (eval f L) (eval f M) (eval f N)).inv := by
  let g : α × ZMod 2 → C := fun p ↦ parityDual p.2 (f p.1)
  rw [← cancel_mono (whiskerRightIso (tensorListAppendIso g L M) (eval f N)).hom]
  dsimp only [eval, g]
  simp only [evalAppendIso_def, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
  rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id,
    ← cancel_mono (tensorListAppendIso g (L ++ M) N).hom]
  dsimp only [g]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorListAppendIso_assoc g L M N]
  dsimp only [g]
  rw [Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id_assoc]

/-- Pointwise isomorphisms `e a : f₁ a ≅ f₂ a` of generator valuations induce an isomorphism
`eval f₁ L ≅ eval f₂ L`, implemented via `TauCeti.tensorListCongrIso` and `parityDualMapIso`. -/
def evalCongrIso {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : ParityWord α) :
    eval f₁ L ≅ eval f₂ L :=
  tensorListCongrIso (fun p : α × ZMod 2 ↦ parityDualMapIso p.2 (e p.1)) L

theorem evalCongrIso_def {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (L : ParityWord α) :
    evalCongrIso e L =
      tensorListCongrIso (fun p : α × ZMod 2 ↦ parityDualMapIso p.2 (e p.1)) L := (rfl)

@[simp] theorem evalCongrIso_nil {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) :
    evalCongrIso e [] = Iso.refl (𝟙_ C) := by
  ext
  simp [evalCongrIso_def]

@[simp] theorem evalCongrIso_cons {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a) (p : α × ZMod 2)
    (L : ParityWord α) :
    evalCongrIso e (p :: L) = parityDualMapIso p.2 (e p.1) ⊗ᵢ evalCongrIso e L := by
  ext
  simp [evalCongrIso_def]

/-- `evalAppendIso` is natural with respect to `evalCongrIso`, derived from
`TauCeti.tensorListAppendIso_hom_naturality`. -/
@[reassoc]
theorem evalAppendIso_hom_naturality {f₁ f₂ : α → C} (e : ∀ a, f₁ a ≅ f₂ a)
    (L M : ParityWord α) :
    (evalCongrIso e (L ++ M)).hom ≫ (evalAppendIso f₂ L M).hom =
      (evalAppendIso f₁ L M).hom ≫ ((evalCongrIso e L).hom ⊗ₘ (evalCongrIso e M).hom) := by
  rw [evalCongrIso_def, evalCongrIso_def, evalCongrIso_def, evalAppendIso_def, evalAppendIso_def,
    Iso.symm_hom, Iso.symm_hom, tensorListCongrIso_hom, tensorListCongrIso_hom,
    tensorListCongrIso_hom, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (tensorListAppendIso_hom_naturality
    (fun p : α × ZMod 2 ↦ (parityDualMapIso p.2 (e p.1)).hom) L M).symm

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

/-- Applying `parityDualRightDualIso` twice recovers `(pivotalIsoApp (parityDual ε X)).inv` up to
`ε + 1 + 1 = ε` in `ZMod 2`. -/
@[reassoc]
theorem parityDualRightDualIso_rightDual_hom :
    (ε : ZMod 2) → (X : C) →
      ((parityDualRightDualIso ε X).inv)ᘁ ≫ (parityDualRightDualIso (ε + 1) X).hom ≫
          eqToHom (congrArg (parityDual · X)
            (by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])) =
        (pivotalIsoApp (parityDual ε X)).inv
  | ⟨0, _⟩, X => by
    rw [eqToHom_refl, Category.comp_id]
    exact (@rightAdjointMate_id C _ _ Xᘁ _ =≫ _).trans (Category.id_comp _)
  | ⟨1, _⟩, X => by
    rw [eqToHom_refl, Category.comp_id]
    exact (Category.comp_id _).trans (pivotalIsoApp_rightDual_inv X).symm

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

omit [PivotalCategory C] in
private theorem rightDualTensorIso_evalAppendIso_cons (f : α → C) (p : α × ZMod 2)
    (L M : ParityWord α) :
    (rightDualTensorIso (parityDual p.2 (f p.1)) (eval f (L ++ M))).hom ≫
        ((((evalAppendIso f L M).inv)ᘁ ≫ (rightDualTensorIso (eval f L) (eval f M)).hom) ▷
          (parityDual p.2 (f p.1))ᘁ) =
      ((evalAppendIso f (p :: L) M).inv)ᘁ ≫
        (rightDualTensorIso (parityDual p.2 (f p.1) ⊗ eval f L) (eval f M)).hom ≫
        ((eval f M)ᘁ ◁ (rightDualTensorIso (parityDual p.2 (f p.1)) (eval f L)).hom) ≫
        (α_ (eval f M)ᘁ (eval f L)ᘁ (parityDual p.2 (f p.1))ᘁ).inv := by
  let g : α × ZMod 2 → C := fun q ↦ parityDual q.2 (f q.1)
  have hAppInv : (evalAppendIso f (p :: L) M).inv =
      (α_ (parityDual p.2 (f p.1)) (eval f L) (eval f M)).hom ≫
        (parityDual p.2 (f p.1) ◁ (evalAppendIso f L M).inv) :=
    tensorListAppendIso_cons_hom g p L M
  rw [hAppInv, comp_rightAdjointMate, comp_whiskerRight,
    ← Category.assoc (rightDualTensorIso (parityDual p.2 (f p.1)) (eval f (L ++ M))).hom]
  have hNat :=
    (rightDualTensorIso_hom_naturality (𝟙 (parityDual p.2 (f p.1))) (evalAppendIso f L M).inv).symm
  rw [rightAdjointMate_id, tensorHom_id, id_tensorHom] at hNat
  rw [hNat, Category.assoc,
    ← cancel_mono (α_ (eval f M)ᘁ (eval f L)ᘁ (parityDual p.2 (f p.1))ᘁ).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1
  exact (rightDualTensorIso_associativity (parityDual p.2 (f p.1)) (eval f L) (eval f M)).symm

omit [PivotalCategory C] in
private theorem evalDualIso_append_assoc_tail (f : α → C) (p : α × ZMod 2) (L M : ParityWord α) :
    ((evalAppendIso f (dual M) (dual L)).inv ▷ eval f [(p.1, p.2 + 1)]) ≫
        (eqToHom (congrArg (eval f) (dual_append L M).symm) ▷ eval f [(p.1, p.2 + 1)]) ≫
        (evalAppendIso f (dual (L ++ M)) [(p.1, p.2 + 1)]).inv ≫
        eqToHom (congrArg (eval f) (dual_cons p (L ++ M)).symm) =
      (α_ (eval f (dual M)) (eval f (dual L)) (eval f [(p.1, p.2 + 1)])).hom ≫
        (eval f (dual M) ◁ (evalAppendIso f (dual L) [(p.1, p.2 + 1)]).inv) ≫
        (eval f (dual M) ◁ eqToHom (congrArg (eval f) (dual_cons p L).symm)) ≫
        (evalAppendIso f (dual M) (dual (p :: L))).inv ≫
        eqToHom (congrArg (eval f) (dual_append (p :: L) M).symm) := by
  let g : α × ZMod 2 → C := fun q ↦ parityDual q.2 (f q.1)
  have hWhiskerR : ∀ {U V : ParityWord α} (h : U = V),
      (eqToHom (congrArg (eval f) h) ▷ eval f [(p.1, p.2 + 1)]) ≫
        (evalAppendIso f V [(p.1, p.2 + 1)]).inv =
      (evalAppendIso f U [(p.1, p.2 + 1)]).inv ≫
        eqToHom (congrArg (eval f) (congrArg (· ++ [(p.1, p.2 + 1)]) h)) := by
    rintro U _ rfl; simp
  have hWhiskerL : ∀ {U V : ParityWord α} (h : U = V),
      (eval f (dual M) ◁ eqToHom (congrArg (eval f) h)) ≫
        (evalAppendIso f (dual M) V).inv =
      (evalAppendIso f (dual M) U).inv ≫
        eqToHom (congrArg (eval f) (congrArg (dual M ++ ·) h)) := by
    rintro U _ rfl; simp
  rw [reassoc_of% (hWhiskerR (dual_append L M).symm),
    reassoc_of% (hWhiskerL (dual_cons p L).symm)]
  simp only [evalAppendIso_def, Iso.symm_inv, eqToHom_trans]
  rw [tensorListAppendIso_assoc_assoc g (dual M) (dual L) [(p.1, p.2 + 1)]]
  simp only [eqToHom_trans]
  rfl

/-- `evalDualIso` reverses concatenations via `evalAppendIso` and `rightDualTensorIso`. -/
@[reassoc]
theorem evalDualIso_append_hom (f : α → C) (L M : ParityWord α) :
    (evalDualIso f (L ++ M)).hom =
      ((evalAppendIso f L M).inv)ᘁ ≫ (rightDualTensorIso (eval f L) (eval f M)).hom ≫
        ((evalDualIso f M).hom ⊗ₘ (evalDualIso f L).hom) ≫
        (evalAppendIso f (dual M) (dual L)).inv ≫
        eqToHom (congrArg (eval f) (dual_append L M).symm) := by
  induction L with
  | nil =>
    dsimp only [List.nil_append]
    rw [evalAppendIso_nil, Iso.symm_inv, evalDualIso_nil]
    simp only [Iso.trans_hom, eqToIso.hom]
    have hUnitR : ∀ {R : ParityWord α} (_ : R = []) (h0 : 𝟙_ C = eval f R)
        (hDual : dual M = dual M ++ R),
        (eval f (dual M) ◁ eqToHom h0) ≫ (evalAppendIso f (dual M) R).inv ≫
          eqToHom (congrArg (eval f) hDual.symm) = (ρ_ (eval f (dual M))).hom := by
      rintro _ rfl h0 hDual
      simp [evalAppendIso_def, tensorListAppendIso_nil_right_hom]
    rw [tensorHom_def']
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerLeft_comp_assoc,
      whisker_exchange_assoc (evalDualIso f M).hom (eqToHom _),
      hUnitR dual_nil _ (dual_append ([] : ParityWord α) M), rightDualUnitIso_hom,
      reassoc_of% (@rightDualTensorIso_leftUnitality C _ _ (eval f M) _
        (RightRigidCategory.rightDual (𝟙_ C)) _).symm,
      ← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  | cons p L ih =>
    dsimp only [List.cons_append]
    rw [evalDualIso_cons]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, eqToIso.hom]
    rw [ih]
    have hSplit1 : ∀ {A₁ A₂ A₃ A₄ B₁ B₂ : C} (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
        (b : B₁ ⟶ B₂),
        ((a₁ ≫ a₂ ≫ a₃) ⊗ₘ b) = (a₁ ▷ B₁) ≫ (a₂ ▷ B₁) ≫ (a₃ ⊗ₘ b) := by
      intros; simp [tensorHom_def]
    rw [hSplit1 (((evalAppendIso f L M).inv)ᘁ) (rightDualTensorIso (eval f L) (eval f M)).hom,
      ← comp_whiskerRight_assoc]
    simp only [Category.assoc]
    rw [reassoc_of% (rightDualTensorIso_evalAppendIso_cons f p L M)]
    congr 2
    rw [evalDualIso_cons]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, eqToIso.hom]
    let u : (parityDual p.2 (f p.1))ᘁ ⟶ eval f [(p.1, p.2 + 1)] :=
      (parityDualRightDualIso p.2 (f p.1)).hom ≫ (ρ_ (parityDual (p.2 + 1) (f p.1))).inv
    have hMidTensor :
        (((evalDualIso f M).hom ⊗ₘ (evalDualIso f L).hom) ≫
          (evalAppendIso f (dual M) (dual L)).inv ≫
          eqToHom (congrArg (eval f) (dual_append L M).symm)) ⊗ₘ u =
        (((evalDualIso f M).hom ⊗ₘ (evalDualIso f L).hom) ⊗ₘ u) ≫
          ((evalAppendIso f (dual M) (dual L)).inv ▷ eval f [(p.1, p.2 + 1)]) ≫
          (eqToHom (congrArg (eval f) (dual_append L M).symm) ▷ eval f [(p.1, p.2 + 1)]) := by
      simp [tensorHom_def', comp_whiskerRight]
    rw [show (parityDualRightDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv = u from rfl,
      reassoc_of% hMidTensor, evalDualIso_append_assoc_tail f p L M,
      ← associator_inv_naturality_assoc (evalDualIso f M).hom (evalDualIso f L).hom u,
      Iso.inv_hom_id_assoc]
    simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
    congr 1
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]

private theorem rightAdjointMate_rightUnitor_hom_comp_evalDualIso_singleton
    (f : α → C) (p : α × ZMod 2) :
    ((ρ_ (parityDual p.2 (f p.1))).hom)ᘁ ≫ (evalDualIso f [p]).hom =
      (parityDualRightDualIso p.2 (f p.1)).hom ≫
        (ρ_ (parityDual (p.2 + 1) (f p.1))).inv ≫
        eqToHom (congrArg (eval f) (by simp : [(p.1, p.2 + 1)] = dual [p])) := by
  let X := parityDual p.2 (f p.1)
  rw [evalDualIso_cons, evalDualIso_nil]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, eqToIso.hom]
  have hNil : ∀ {R : ParityWord α} (_ : R = []) (h0 : 𝟙_ C = eval f R)
      (hApp : [(p.1, p.2 + 1)] = R ++ [(p.1, p.2 + 1)]),
      (eqToHom h0 ▷ eval f [(p.1, p.2 + 1)]) ≫
        (evalAppendIso f R [(p.1, p.2 + 1)]).inv =
      (λ_ (parityDual (p.2 + 1) (f p.1) ⊗ 𝟙_ C)).hom ≫
        eqToHom (congrArg (eval f) hApp) := by
    rintro _ rfl h0 hApp
    have h0' : eqToHom h0 = 𝟙 (𝟙_ C) := eqToHom_refl _ _
    have hApp' : eqToHom (congrArg (eval f) hApp) = 𝟙 (eval f [(p.1, p.2 + 1)]) :=
      eqToHom_refl _ _
    rw [h0', hApp', evalAppendIso_nil, Iso.symm_inv, id_whiskerRight, Category.id_comp,
      Category.comp_id]
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [comp_whiskerRight_assoc, ← whisker_exchange_assoc,
    reassoc_of% (hNil dual_nil _ (by simp))]
  simp only [eqToHom_trans]
  rw [rightDualUnitIso_hom,
    reassoc_of% (@rightDualTensorIso_rightUnitality C _ _ X _
      (RightRigidCategory.rightDual (𝟙_ C)) _).symm,
    ← leftUnitor_inv_naturality_assoc, Iso.inv_hom_id_assoc, Category.assoc]

private theorem rightDualTensorIso_inv_mate_comp_pivotalIsoApp_inv (A B : C) :
    ((rightDualTensorIso A B).inv)ᘁ ≫ (rightDualTensorIso Bᘁ Aᘁ).hom ≫
        ((pivotalIsoApp A).inv ⊗ₘ (pivotalIsoApp B).inv) =
      (pivotalIsoApp (A ⊗ B)).inv := by
  have hφ : (pivotalIsoApp (A ⊗ B)).hom =
      ((pivotalIsoApp A).hom ⊗ₘ (pivotalIsoApp B).hom) ≫
        (rightDualTensorIso Bᘁ Aᘁ).inv ≫ ((rightDualTensorIso A B).hom)ᘁ := by
    rw [pivotalIsoApp_tensor_hom, doubleRightDualFunctor_μ]
    rfl
  rw [← cancel_epi (pivotalIsoApp (A ⊗ B)).hom, Iso.hom_inv_id, hφ, Category.assoc,
    Category.assoc, ← comp_rightAdjointMate_assoc, Iso.inv_hom_id, rightAdjointMate_id,
    Category.id_comp, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id,
    Iso.hom_inv_id, id_tensorHom_id]

private theorem evalDualIso_dual_nil (f : α → C) :
    ((evalDualIso f ([] : ParityWord α)).inv)ᘁ ≫ (evalDualIso f (dual [])).hom ≫
        eqToHom (congrArg (eval f) (dual_dual [])) =
      (pivotalIsoApp (eval f [])).inv := by
  have hSub : ∀ {S : ParityWord α} (_ : S = []) (h1 : 𝟙_ C = eval f S) (hD : S = []),
      (eqToIso h1).hom ≫ eqToHom (congrArg (eval f) hD) = 𝟙 (𝟙_ C) := by
    rintro _ rfl h1 hD
    simp
  have hNilCase : ∀ {R : ParityWord α} (_ : R = []) (h0 : 𝟙_ C = eval f R)
      (hD : dual R = []),
      ((rightDualUnitIso C ≪≫ eqToIso h0).inv)ᘁ ≫
        (evalDualIso f R).hom ≫ eqToHom (congrArg (eval f) hD) =
      (pivotalIsoApp (𝟙_ C)).inv := by
    rintro _ rfl h0 hD
    have h0' : (eqToIso h0).inv = 𝟙 (𝟙_ C) := by simp
    rw [Iso.trans_inv, h0',
      @comp_rightAdjointMate_assoc C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
        (RightRigidCategory.rightDual (𝟙_ C)) _,
      @rightAdjointMate_id C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C)),
      Category.id_comp, evalDualIso_nil, Iso.trans_hom, Category.assoc,
      hSub dual_nil _ hD, Category.comp_id, pivotalIsoApp_unit_inv, doubleRightDualFunctor_η,
      ← rightDualUnitIso_inv, ← rightDualUnitIso_hom]
    exact (@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) _
      (rightDualUnitIso C).inv =≫ _)
  rw [evalDualIso_nil]
  exact hNilCase dual_nil _ (dual_dual [])

/-- Applying `evalDualIso` twice recovers `(pivotalIsoApp (eval f L)).inv` up to `dual_dual`. -/
@[reassoc]
theorem evalDualIso_dual_hom (f : α → C) (L : ParityWord α) :
    ((evalDualIso f L).inv)ᘁ ≫ (evalDualIso f (dual L)).hom ≫
        eqToHom (congrArg (eval f) (dual_dual L)) =
      (pivotalIsoApp (eval f L)).inv := by
  have hEqDual : ∀ {W₁ W₂ : ParityWord α} (hw : W₁ = W₂),
      ((eqToHom (congrArg (eval f) hw))ᘁ) ≫ (evalDualIso f W₁).hom =
        (evalDualIso f W₂).hom ≫
          eqToHom (congrArg (eval f) (congrArg dual hw.symm)) := by
    intro W₁ W₂ hw; subst hw; simp
  induction L with
  | nil => exact evalDualIso_dual_nil f
  | cons p L ih =>
    rcases p with ⟨a, ε⟩
    have hTailGen : ∀ {δ₁ δ₂ : ZMod 2} (hδ : δ₁ = δ₂) {U R : ParityWord α}
        (hU : [(a, δ₂)] = U) (hR : R = L) (hCons : U ++ R = (a, δ₁) :: L),
        ((eqToHom (congrArg (parityDual · (f a)) hδ) ≫ (ρ_ (parityDual δ₂ (f a))).inv ≫
            eqToHom (congrArg (eval f) hU)) ⊗ₘ eqToHom (congrArg (eval f) hR.symm)) ≫
          (evalAppendIso f U R).inv ≫ eqToHom (congrArg (eval f) hCons) =
        𝟙 (parityDual δ₁ (f a) ⊗ eval f L) := by
      rintro δ₁ _ rfl _ _ rfl rfl hCons
      simp [evalAppendIso_def, tensorListAppendIso_singleton_hom]
    rw [evalDualIso_cons]
    simp only [Iso.trans_inv, eqToIso.inv, Iso.symm_inv, tensorIso_inv, comp_rightAdjointMate,
      Category.assoc]
    rw [reassoc_of% (hEqDual (dual_cons (a, ε) L)), evalDualIso_append_hom]
    simp only [Category.assoc, eqToHom_trans]
    rw [← comp_rightAdjointMate_assoc (f := (evalAppendIso f (dual L) [(a, ε + 1)]).inv)
        (g := (evalAppendIso f (dual L) [(a, ε + 1)]).hom),
      Iso.inv_hom_id, rightAdjointMate_id, Category.id_comp,
      rightDualTensorIso_hom_naturality_assoc, tensorHom_comp_tensorHom_assoc,
      comp_rightAdjointMate, Category.assoc,
      rightAdjointMate_rightUnitor_hom_comp_evalDualIso_singleton f (a, ε + 1)]
    have ih' : ((evalDualIso f L).inv)ᘁ ≫ (evalDualIso f (dual L)).hom =
        (pivotalIsoApp (eval f L)).inv ≫ eqToHom (congrArg (eval f) (dual_dual L).symm) := by
      rw [← ih]; simp
    have hp' : ((parityDualRightDualIso ε (f a)).inv)ᘁ ≫
        (parityDualRightDualIso (ε + 1) (f a)).hom =
        (pivotalIsoApp (parityDual ε (f a))).inv ≫
          eqToHom (congrArg (parityDual · (f a))
            (by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])) := by
      rw [← parityDualRightDualIso_rightDual_hom ε (f a)]; simp
    rw [ih', reassoc_of% hp', ← tensorHom_comp_tensorHom_assoc,
      hTailGen (δ₁ := ε) (δ₂ := ε + 1 + 1)
        (by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])
        (U := dual [(a, ε + 1)]) (R := (dual L).dual)
        (by simp) (dual_dual L)
        (by rw [dual_cons, dual_nil, List.nil_append, List.singleton_append, dual_dual,
          add_assoc, CharTwo.add_self_eq_zero, add_zero]),
      Category.comp_id]
    exact rightDualTensorIso_inv_mate_comp_pivotalIsoApp_inv (parityDual ε (f a)) (eval f L)

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

private theorem evalDualIso_inv_comp_eqToHom_mate (f : α → C) {U V : ParityWord α} (h : U = V) :
    (evalDualIso f V).inv ≫ (eqToHom (congrArg (eval f) h))ᘁ =
      eqToHom (congrArg (eval f) (congrArg dual h.symm)) ≫ (evalDualIso f U).inv := by
  subst h; simp

/-- Advancing `evalDualPowIso` by one right dual via `evalDualIso` and `parityDualRightDualIso`. -/
@[reassoc]
theorem evalDualIso_inv_comp_parityDualRightDualIso_hom (f : α → C) (ε : ZMod 2)
    (L : ParityWord α) :
    (evalDualIso f (dualPow ε L)).inv ≫
        ((evalDualPowIso f ε L).inv)ᘁ ≫
        (parityDualRightDualIso ε (eval f L)).hom =
      eqToHom (congrArg (eval f) (by rw [add_comm, dualPow_add, dualPow_one])) ≫
        (evalDualPowIso f (ε + 1) L).hom := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
  · have h0 : L = dualPow 0 L := (dualPow_zero L).symm
    have hGoal : (evalDualIso f (dualPow 0 L)).inv ≫
          (eqToHom (congrArg (eval f) h0))ᘁ ≫ 𝟙 (eval f L)ᘁ =
        eqToHom (congrArg (eval f) (by simp : (dualPow 0 L).dual = dualPow 1 L)) ≫
          eqToHom (congrArg (eval f) (dualPow_one L)) ≫ (evalDualIso f L).inv := by
      rw [Category.comp_id, evalDualIso_inv_comp_eqToHom_mate f h0, eqToHom_trans_assoc]
    exact hGoal
  · have h1 : L.dual = dualPow 1 L := (dualPow_one L).symm
    have hGoal : (evalDualIso f (dualPow 1 L)).inv ≫
          ((evalDualIso f L).hom ≫ eqToHom (congrArg (eval f) h1))ᘁ ≫
          (pivotalIsoApp (eval f L)).inv =
        eqToHom (congrArg (eval f) (by simp : (dualPow 1 L).dual = dualPow 0 L)) ≫
          eqToHom (congrArg (eval f) (dualPow_zero L)) := by
      rw [comp_rightAdjointMate_assoc, reassoc_of% (evalDualIso_inv_comp_eqToHom_mate f h1),
        ← evalDualIso_dual_hom f L, ← comp_rightAdjointMate_assoc, Iso.inv_hom_id,
        rightAdjointMate_id, Category.id_comp, Iso.inv_hom_id_assoc, eqToHom_trans, eqToHom_trans]
    exact hGoal

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

private theorem evalSubstIso_append_nil (g : β → C) (F : α → ParityWord β) (M : ParityWord α) :
    (evalSubstIso g F ([] ++ M)).hom ≫
        (evalAppendIso (fun a ↦ eval g (F a)) [] M).hom =
      eqToHom (congrArg (eval g) (subst_append F [] M)) ≫
        (evalAppendIso g (subst F []) (subst F M)).hom ≫
        ((evalSubstIso g F []).hom ⊗ₘ (evalSubstIso g F M).hom) := by
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
    dsimp only [List.nil_append, eval, tensorList]
    rw [Category.id_comp, id_tensorHom, leftUnitor_inv_naturality]
  rw [evalSubstIso_nil, evalAppendIso_nil]
  dsimp only [List.nil_append, Iso.symm_hom, eqToIso.hom]
  exact (hNil (subst_nil F) (subst_append F [] M) (by simp)).symm

omit [PivotalCategory C] in
private theorem evalSubstIso_append_slide (g : β → C) (F : α → ParityWord β) (p : α × ZMod 2)
    (L M : ParityWord α) :
    eqToHom (congrArg (eval g) (subst_cons F p (L ++ M))) ≫
        eqToHom (congrArg (eval g)
          (congrArg (dualPow p.2 (F p.1) ++ ·) (subst_append F L M))) ≫
        eqToHom (congrArg (eval g)
          (List.append_assoc (dualPow p.2 (F p.1)) (subst F L) (subst F M)).symm) ≫
        (evalAppendIso g (dualPow p.2 (F p.1) ++ subst F L) (subst F M)).hom =
      eqToHom (congrArg (eval g) (subst_append F (p :: L) M)) ≫
        (evalAppendIso g (subst F (p :: L)) (subst F M)).hom ≫
        (eqToHom (congrArg (eval g) (subst_cons F p L)) ▷ eval g (subst F M)) := by
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
  rw [← hSlide (subst_cons F p L) (by rw [subst_cons, List.append_assoc])]
  simp only [eqToHom_trans_assoc]

/-- `evalSubstIso` respects concatenation of parity words via `evalAppendIso`. -/
@[reassoc]
theorem evalSubstIso_append_hom (g : β → C) (F : α → ParityWord β) (L M : ParityWord α) :
    (evalSubstIso g F (L ++ M)).hom ≫
        (evalAppendIso (fun a ↦ eval g (F a)) L M).hom =
      eqToHom (congrArg (eval g) (subst_append F L M)) ≫
        (evalAppendIso g (subst F L) (subst F M)).hom ≫
        ((evalSubstIso g F L).hom ⊗ₘ (evalSubstIso g F M).hom) := by
  induction L with
  | nil => exact evalSubstIso_append_nil g F M
  | cons p L ih =>
    have hNatApp : ∀ {W₁ W₂ : ParityWord β} (hw : W₁ = W₂),
        (evalAppendIso g (dualPow p.2 (F p.1)) W₁).hom ≫
          (eval g (dualPow p.2 (F p.1)) ◁ eqToHom (congrArg (eval g) hw)) =
        eqToHom (congrArg (eval g) (congrArg (dualPow p.2 (F p.1) ++ ·) hw)) ≫
          (evalAppendIso g (dualPow p.2 (F p.1)) W₂).hom := by
      intro W₁ W₂ hw; subst hw; simp
    dsimp only [List.cons_append]
    rw [evalSubstIso_cons, evalSubstIso_cons, evalAppendIso_cons]
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
              u ⊗ₘ (v₁ ≫ v₂ ≫ v₃) = (X₁ ◁ v₁) ≫ (X₁ ◁ v₂) ≫ (u ⊗ₘ v₃) := by
            intros; simp [tensorHom_def']
          rw [hSplitR]
          simp only [Category.assoc]
          rw [associator_inv_naturality, reassoc_of% (hNatApp (subst_append F L M)),
            ← reassoc_of% (evalAppendIso_assoc_hom g (dualPow p.2 (F p.1)) (subst F L)
              (subst F M)),
            reassoc_of% (evalSubstIso_append_slide g F p L M)]
          simp only [tensorHom_def', comp_whiskerRight]
          rw [whisker_exchange_assoc
              (eqToHom (congrArg (eval g) (subst_cons F p L))) (evalSubstIso g F M).hom,
            whisker_exchange_assoc
              (evalAppendIso g (dualPow p.2 (F p.1)) (subst F L)).hom (evalSubstIso g F M).hom]

end ParityWord

end PivotalParity

end TauCeti
