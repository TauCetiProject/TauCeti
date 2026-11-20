/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Substitution
public import TauCeti.CategoryTheory.Monoidal.TensorList.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.MixedDualFunctor

/-!
# Categorical evaluation of rigid object syntax and winding words

Given a valuation `f : α → C` into a rigid monoidal category `C`, this file evaluates both
integer-labelled winding words (`WindingWord.evalObj`) and parenthesized formal rigid object
expressions (`RigidObject.evalObj`) as objects of `C`, together with structural comparisons.

* `TauCeti.iteratedRightDual`, `TauCeti.iteratedLeftDual`, `TauCeti.iteratedDual`: iterated chosen
  duals (`RightRigidCategory.rightDual`, `LeftRigidCategory.leftDual`) indexed by `ℕ` and `ℤ`,
  with step comparisons `TauCeti.iteratedDualRightDualIso` and `TauCeti.iteratedDualLeftDualIso`;
* `TauCeti.WindingWord.evalObj`: right-associated tensor evaluation of `WindingWord α` in `C`,
  with `evalObjAppendIso`, `evalObjRightDualIso`, `evalObjLeftDualIso`, `evalObjDualPowIso`, and
  `evalObjSubstIso`;
* `TauCeti.RigidObject.evalObj` and `TauCeti.RigidObject.evalObjNormalizeIso`: direct evaluation of
  `RigidObject α` and its structural isomorphism to `X.normalize.evalObj f`.

## References

* [A. Joyal and R. Street, *Planar diagrams and tensor algebra*][joyalStreet1988], §2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Iterated chosen duals -/

/-- `k`-fold chosen right dual of `X` in a right rigid monoidal category. -/
@[expose]
def iteratedRightDual [RightRigidCategory C] (X : C) : ℕ → C
  | 0 => X
  | k + 1 => (iteratedRightDual X k)ᘁ

@[simp] theorem iteratedRightDual_zero [RightRigidCategory C] (X : C) :
    iteratedRightDual X 0 = X := by rfl
@[simp] theorem iteratedRightDual_succ [RightRigidCategory C] (X : C) (k : ℕ) :
    iteratedRightDual X (k + 1) = (iteratedRightDual X k)ᘁ := by rfl
theorem iteratedRightDual_one [RightRigidCategory C] (X : C) :
    iteratedRightDual X 1 = Xᘁ := by rfl

/-- `k`-fold chosen left dual of `X` in a left rigid monoidal category. -/
@[expose]
def iteratedLeftDual [LeftRigidCategory C] (X : C) : ℕ → C
  | 0 => X
  | k + 1 => ᘁ(iteratedLeftDual X k)

@[simp] theorem iteratedLeftDual_zero [LeftRigidCategory C] (X : C) :
    iteratedLeftDual X 0 = X := by rfl
@[simp] theorem iteratedLeftDual_succ [LeftRigidCategory C] (X : C) (k : ℕ) :
    iteratedLeftDual X (k + 1) = ᘁ(iteratedLeftDual X k) := by rfl
theorem iteratedLeftDual_one [LeftRigidCategory C] (X : C) :
    iteratedLeftDual X 1 = ᘁX := by rfl

/-- `ℤ`-indexed iterated dual of `X` in a rigid monoidal category: nonnegative integers iterate
chosen right duals and negative integers iterate chosen left duals. -/
@[expose]
def iteratedDual [RigidCategory C] (X : C) : ℤ → C
  | .ofNat k => iteratedRightDual X k
  | .negSucc k => iteratedLeftDual X (k + 1)

section
variable [RigidCategory C]

@[simp] theorem iteratedDual_natCast (X : C) (k : ℕ) :
    iteratedDual X (k : ℤ) = iteratedRightDual X k := by rfl
@[simp] theorem iteratedDual_zero (X : C) : iteratedDual X 0 = X := by rfl
@[simp] theorem iteratedDual_one (X : C) : iteratedDual X 1 = Xᘁ := by rfl
@[simp] theorem iteratedDual_two (X : C) : iteratedDual X 2 = (Xᘁ : C)ᘁ := by rfl
@[simp] theorem iteratedDual_negSucc (X : C) (k : ℕ) :
    iteratedDual X (.negSucc k) = iteratedLeftDual X (k + 1) := by rfl
@[simp] theorem iteratedDual_neg_one (X : C) : iteratedDual X (-1) = ᘁX := by rfl

/-- Structural comparison `(iteratedDual X n)ᘁ ≅ iteratedDual X (n + 1)`, canceling the outermost
left dual at negative levels via `rightDualLeftDualIso`. -/
@[expose]
noncomputable def iteratedDualRightDualIso (X : C) :
    (n : ℤ) → (iteratedDual X n)ᘁ ≅ iteratedDual X (n + 1)
  | .ofNat k => Iso.refl (iteratedRightDual X (k + 1))
  | .negSucc 0 => (rightDualLeftDualIso C).app X
  | .negSucc (k + 1) => (rightDualLeftDualIso C).app (iteratedLeftDual X (k + 1))

@[simp] theorem iteratedDualRightDualIso_natCast (X : C) (k : ℕ) :
    iteratedDualRightDualIso X (k : ℤ) = Iso.refl (iteratedRightDual X (k + 1)) := by rfl
@[simp] theorem iteratedDualRightDualIso_neg_one (X : C) :
    iteratedDualRightDualIso X (-1) = (rightDualLeftDualIso C).app X := by rfl
@[simp] theorem iteratedDualRightDualIso_negSucc_succ (X : C) (k : ℕ) :
    iteratedDualRightDualIso X (.negSucc (k + 1)) =
      (rightDualLeftDualIso C).app (iteratedLeftDual X (k + 1)) := by rfl

/-- Structural comparison `ᘁ(iteratedDual X n) ≅ iteratedDual X (n - 1)`, canceling the outermost
right dual at positive levels via `leftDualRightDualIso`. -/
@[expose]
noncomputable def iteratedDualLeftDualIso (X : C) :
    (n : ℤ) → (ᘁ(iteratedDual X n)) ≅ iteratedDual X (n - 1)
  | .ofNat 0 => Iso.refl _
  | .ofNat (k + 1) => (leftDualRightDualIso C).app (iteratedRightDual X k) ≪≫
      eqToIso (congrArg (iteratedDual X) (add_sub_cancel_right (k : ℤ) 1).symm)
  | .negSucc _ => Iso.refl _

@[simp] theorem iteratedDualLeftDualIso_zero (X : C) :
    iteratedDualLeftDualIso X 0 = Iso.refl (iteratedLeftDual X 1) := by rfl
@[simp] theorem iteratedDualLeftDualIso_one (X : C) :
    iteratedDualLeftDualIso X 1 = (leftDualRightDualIso C).app X := by ext; exact Category.comp_id _
@[simp] theorem iteratedDualLeftDualIso_negSucc (X : C) (k : ℕ) :
    iteratedDualLeftDualIso X (.negSucc k) = Iso.refl (iteratedLeftDual X (k + 2)) := by rfl
end

/-! ### Evaluation of winding words -/

namespace WindingWord

variable {α β : Type*}

/-- Right dual of a winding word as reversal followed by shifting every integer level by `+1`. -/
theorem rightDual_eq_map_reverse (L : WindingWord α) :
    L.rightDual = L.reverse.map fun p ↦ (p.1, p.2 + 1) := by induction L <;> simp_all
/-- Left dual of a winding word as reversal followed by shifting every integer level by `-1`. -/
theorem leftDual_eq_map_reverse (L : WindingWord α) :
    L.leftDual = L.reverse.map fun p ↦ (p.1, p.2 - 1) := by induction L <;> simp_all

variable [RigidCategory C]

private abbrev iDual (f : α → C) (p : α × ℤ) : C := iteratedDual (f p.1) p.2

/-- Evaluate `L : WindingWord α` as the right-associated tensor of `iteratedDual (f p.1) p.2`. -/
@[expose]
def evalObj (f : α → C) (L : WindingWord α) : C :=
  tensorList (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L

@[simp] theorem evalObj_nil (f : α → C) : evalObj f ([] : WindingWord α) = 𝟙_ C := by rfl
@[simp] theorem evalObj_cons (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    evalObj f (p :: L) = iteratedDual (f p.1) p.2 ⊗ evalObj f L := by rfl

/-- Right-unitor isomorphism `evalObj f [p] ≅ iteratedDual (f p.1) p.2` on a single port. -/
@[expose]
def evalObjSingletonIso (f : α → C) (p : α × ℤ) : evalObj f [p] ≅ iteratedDual (f p.1) p.2 :=
  tensorListSingletonIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2) p

/-- Concatenation comparison `evalObj f L ⊗ evalObj f M ≅ evalObj f (L ++ M)`. -/
@[expose]
def evalObjAppendIso (f : α → C) (L M : WindingWord α) :
    evalObj f L ⊗ evalObj f M ≅ evalObj f (L ++ M) :=
  tensorListAppendIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L M

@[simp] theorem evalObjAppendIso_nil (f : α → C) (M : WindingWord α) :
    evalObjAppendIso f [] M = λ_ (evalObj f M) := tensorListAppendIso_nil _ M
theorem evalObjAppendIso_cons_hom (f : α → C) (p : α × ℤ) (L M : WindingWord α) :
    (evalObjAppendIso f (p :: L) M).hom =
      (α_ (iteratedDual (f p.1) p.2) (evalObj f L) (evalObj f M)).hom ≫
        iteratedDual (f p.1) p.2 ◁ (evalObjAppendIso f L M).hom :=
  tensorListAppendIso_cons_hom _ p L M

/-- Right-dual comparison `(evalObj f L)ᘁ ≅ evalObj f L.rightDual` reversing tensor factors and
advancing each dual level by `+1`. -/
noncomputable def evalObjRightDualIso (f : α → C) (L : WindingWord α) :
    (evalObj f L)ᘁ ≅ evalObj f L.rightDual :=
  (rightDualFunctor C).opMopTensorListIso (iDual f) L ≪≫
    tensorListCongrIso (fun p : α × ℤ ↦ iteratedDualRightDualIso (f p.1) p.2) L.reverse ≪≫
    tensorListMapIso (iDual f) (fun p ↦ (p.1, p.2 + 1)) L.reverse ≪≫
    eqToIso (congrArg (evalObj f) (rightDual_eq_map_reverse L).symm)

theorem evalObjRightDualIso_hom (f : α → C) (L : WindingWord α) :
    (evalObjRightDualIso f L).hom =
      ((rightDualFunctor C).opMopTensorListIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L).hom ≫
        tensorListCongrHom (fun p : α × ℤ ↦ (iteratedDualRightDualIso (f p.1) p.2).hom) L.reverse ≫
        (tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
          (fun p ↦ (p.1, p.2 + 1)) L.reverse).hom ≫
        eqToHom (congrArg (evalObj f) (rightDual_eq_map_reverse L).symm) :=
  congrArg (fun g ↦ _ ≫ g ≫ _ ≫ _) (tensorListCongrIso_hom _ _)

/-- Left-dual comparison `ᘁ(evalObj f L) ≅ evalObj f L.leftDual` reversing tensor factors and
shifting each dual level by `-1`. -/
noncomputable def evalObjLeftDualIso (f : α → C) (L : WindingWord α) :
    (ᘁ(evalObj f L)) ≅ evalObj f L.leftDual :=
  (leftDualFunctor C).opMopTensorListIso (iDual f) L ≪≫
    tensorListCongrIso (fun p : α × ℤ ↦ iteratedDualLeftDualIso (f p.1) p.2) L.reverse ≪≫
    tensorListMapIso (iDual f) (fun p ↦ (p.1, p.2 - 1)) L.reverse ≪≫
    eqToIso (congrArg (evalObj f) (leftDual_eq_map_reverse L).symm)

theorem evalObjLeftDualIso_hom (f : α → C) (L : WindingWord α) :
    (evalObjLeftDualIso f L).hom =
      ((leftDualFunctor C).opMopTensorListIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L).hom ≫
        tensorListCongrHom (fun p : α × ℤ ↦ (iteratedDualLeftDualIso (f p.1) p.2).hom) L.reverse ≫
        (tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
          (fun p ↦ (p.1, p.2 - 1)) L.reverse).hom ≫
        eqToHom (congrArg (evalObj f) (leftDual_eq_map_reverse L).symm) :=
  congrArg (fun g ↦ _ ≫ g ≫ _ ≫ _) (tensorListCongrIso_hom _ _)

private noncomputable def evalObjRightPowIso (f : α → C) :
    (k : ℕ) → (L : WindingWord α) → iteratedRightDual (evalObj f L) k ≅ evalObj f (L.dualPow k)
  | 0, L => eqToIso (congrArg (evalObj f) (dualPow_zero L).symm)
  | k + 1, L => ((rightDualFunctor C).mapIso (evalObjRightPowIso f k L).symm).unmop.unop ≪≫
      evalObjRightDualIso f (L.dualPow k) ≪≫
      eqToIso (congrArg (evalObj f) (by rw [Int.natCast_succ, dualPow_add_one]))
private noncomputable def evalObjLeftPowIso (f : α → C) :
    (k : ℕ) → (L : WindingWord α) →
      iteratedLeftDual (evalObj f L) (k + 1) ≅ evalObj f (L.dualPow (.negSucc k))
  | 0, L => evalObjLeftDualIso f L ≪≫ eqToIso (congrArg (evalObj f) (dualPow_neg_one L).symm)
  | k + 1, L => ((leftDualFunctor C).mapIso (evalObjLeftPowIso f k L).symm).unmop.unop ≪≫
      evalObjLeftDualIso f (L.dualPow (.negSucc k)) ≪≫
      eqToIso (congrArg (evalObj f) (dualPow_sub_one (.negSucc k) L).symm)

/-- Iterated-dual comparison `iteratedDual (evalObj f L) n ≅ evalObj f (L.dualPow n)`. -/
noncomputable def evalObjDualPowIso (f : α → C) :
    (n : ℤ) → (L : WindingWord α) → iteratedDual (evalObj f L) n ≅ evalObj f (L.dualPow n)
  | .ofNat k, L => evalObjRightPowIso f k L
  | .negSucc k, L => evalObjLeftPowIso f k L

@[simp] theorem evalObjDualPowIso_zero (f : α → C) (L : WindingWord α) :
    evalObjDualPowIso f 0 L = eqToIso (congrArg (evalObj f) (dualPow_zero L).symm) := by rfl

/-- Substitution comparison `evalObj (fun a ↦ evalObj f (σ a)) L ≅ evalObj f (L.subst σ)`. -/
noncomputable def evalObjSubstIso (f : β → C) (σ : α → WindingWord β) (L : WindingWord α) :
    evalObj (fun a ↦ evalObj f (σ a)) L ≅ evalObj f (L.subst σ) :=
  tensorListCongrIso (fun p : α × ℤ ↦ evalObjDualPowIso f p.2 (σ p.1)) L ≪≫
    tensorListFlatMapIso (iDual f) (fun p : α × ℤ ↦ (σ p.1).dualPow p.2) L ≪≫
    eqToIso (congrArg (evalObj f) (subst_def σ L).symm)

end WindingWord

/-! ### Direct evaluation of formal rigid objects -/

namespace RigidObject

variable [RigidCategory C] {α : Type*}

/-- Evaluate `RigidObject α` directly in `C` using chosen tensor products, unit, and duals. -/
@[expose]
def evalObj (f : α → C) : RigidObject α → C
  | .of a => f a
  | .unit => 𝟙_ C
  | .tensor X Y => evalObj f X ⊗ evalObj f Y
  | .rightDual X => (evalObj f X)ᘁ
  | .leftDual X => ᘁ(evalObj f X)

@[simp] theorem evalObj_of (f : α → C) (a : α) : evalObj f (.of a) = f a := by rfl
@[simp] theorem evalObj_unit (f : α → C) : evalObj f (.unit : RigidObject α) = 𝟙_ C := by rfl
@[simp] theorem evalObj_tensor (f : α → C) (X Y : RigidObject α) :
    evalObj f (X.tensor Y) = evalObj f X ⊗ evalObj f Y := by rfl
@[simp] theorem evalObj_rightDual (f : α → C) (X : RigidObject α) :
    evalObj f X.rightDual = (evalObj f X)ᘁ := by rfl
@[simp] theorem evalObj_leftDual (f : α → C) (X : RigidObject α) :
    evalObj f X.leftDual = ᘁ(evalObj f X) := by rfl

/-- Canonical comparison isomorphism between `X.evalObj f` and `X.normalize.evalObj f`. -/
noncomputable def evalObjNormalizeIso (f : α → C) :
    (X : RigidObject α) → X.evalObj f ≅ X.normalize.evalObj f
  | .of a => (ρ_ (f a)).symm ≪≫ eqToIso (congrArg (WindingWord.evalObj f) (normalize_of a).symm)
  | .unit => eqToIso (congrArg (WindingWord.evalObj f) normalize_unit.symm)
  | .tensor X Y => (evalObjNormalizeIso f X ⊗ᵢ evalObjNormalizeIso f Y) ≪≫
      WindingWord.evalObjAppendIso f X.normalize Y.normalize ≪≫
      eqToIso (congrArg (WindingWord.evalObj f) (normalize_tensor X Y).symm)
  | .rightDual X => ((rightDualFunctor C).mapIso (evalObjNormalizeIso f X).symm).unmop.unop ≪≫
      WindingWord.evalObjRightDualIso f X.normalize ≪≫
      eqToIso (congrArg (WindingWord.evalObj f) (normalize_rightDual X).symm)
  | .leftDual X => ((leftDualFunctor C).mapIso (evalObjNormalizeIso f X).symm).unmop.unop ≪≫
      WindingWord.evalObjLeftDualIso f X.normalize ≪≫
      eqToIso (congrArg (WindingWord.evalObj f) (normalize_leftDual X).symm)

@[simp] theorem evalObjNormalizeIso_unit (f : α → C) :
    evalObjNormalizeIso f (.unit : RigidObject α) =
      eqToIso (congrArg (WindingWord.evalObj f) normalize_unit.symm) := by rfl

end RigidObject

end TauCeti
