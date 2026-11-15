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

Given a generator valuation `f : α → C` into a rigid monoidal category `C`, this file evaluates
both integer-labelled winding words (`WindingWord.evalObj`) and parenthesized formal rigid object
expressions (`RigidObject.evalObj`) as objects of `C`, and constructs explicit structural
comparison isomorphisms between them.

## Design choices

* **Chosen rigid duals everywhere.** In Mathlib, typeclass search for `HasRightDual (ᘁX)`,
  `HasRightDual (𝟙_ C)`, or `HasRightDual (X ⊗ Y)` resolves to auxiliary instances (`X`, `𝟙_ C`,
  `Yᘁ ⊗ Xᘁ`) rather than `RightRigidCategory.rightDual`. Following
  `TauCeti.CategoryTheory.Monoidal.Rigid.MixedDualFunctor`, `TauCeti.iteratedRightDual` and
  `TauCeti.iteratedLeftDual` invoke `(RightRigidCategory.rightDual _).rightDual` and
  `(LeftRigidCategory.leftDual _).leftDual` directly so that
  `((rightDualFunctor C).obj Y).unmop.unop` and `((leftDualFunctor C).obj Y).unmop.unop` agree
  definitionally with one-step duality on every composite object `Y : C`.
* **Structural boundary comparisons.** `WindingWord.evalObjAppendIso`,
  `WindingWord.evalObjRightDualIso`, and `RigidObject.evalObjNormalizeIso` are assembled from
  monoidal unitors/associators, `(rightDualFunctor C).opMopTensorListIso`,
  `(leftDualFunctor C).opMopTensorListIso`, and the mixed-dual cancellations
  `TauCeti.rightDualLeftDualIso` and `TauCeti.leftDualRightDualIso`; only syntactic word/index
  identities in `List (α × ℤ)` or `ℤ` appear inside `congrArg`, never categorical object equalities.

## Main declarations

* `TauCeti.iteratedRightDual`, `TauCeti.iteratedLeftDual`, `TauCeti.iteratedDual`: iterated chosen
  duals indexed by `ℕ` and `ℤ`, with step comparisons `TauCeti.iteratedDualRightDualIso` and
  `TauCeti.iteratedDualLeftDualIso`;
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

section IteratedDual

/-- `k`-fold chosen right dual of `X` in a right rigid monoidal category. -/
@[expose]
def iteratedRightDual [RightRigidCategory C] (X : C) : ℕ → C
  | 0 => X
  | k + 1 => (RightRigidCategory.rightDual (iteratedRightDual X k)).rightDual

@[simp]
theorem iteratedRightDual_zero [RightRigidCategory C] (X : C) :
    iteratedRightDual X 0 = X := by rfl

@[simp]
theorem iteratedRightDual_succ [RightRigidCategory C] (X : C) (k : ℕ) :
    iteratedRightDual X (k + 1) =
      (RightRigidCategory.rightDual (iteratedRightDual X k)).rightDual := by rfl

/-- At exponent `1`, `iteratedRightDual` is the chosen right dual. -/
theorem iteratedRightDual_one [RightRigidCategory C] (X : C) :
    iteratedRightDual X 1 = (RightRigidCategory.rightDual X).rightDual := by rfl

/-- `k`-fold chosen left dual of `X` in a left rigid monoidal category. -/
@[expose]
def iteratedLeftDual [LeftRigidCategory C] (X : C) : ℕ → C
  | 0 => X
  | k + 1 => (LeftRigidCategory.leftDual (iteratedLeftDual X k)).leftDual

@[simp]
theorem iteratedLeftDual_zero [LeftRigidCategory C] (X : C) :
    iteratedLeftDual X 0 = X := by rfl

@[simp]
theorem iteratedLeftDual_succ [LeftRigidCategory C] (X : C) (k : ℕ) :
    iteratedLeftDual X (k + 1) =
      (LeftRigidCategory.leftDual (iteratedLeftDual X k)).leftDual := by rfl

/-- At exponent `1`, `iteratedLeftDual` is the chosen left dual. -/
theorem iteratedLeftDual_one [LeftRigidCategory C] (X : C) :
    iteratedLeftDual X 1 = (LeftRigidCategory.leftDual X).leftDual := by rfl

/-- `ℤ`-indexed iterated dual of `X` in a rigid monoidal category: nonnegative integers iterate
chosen right duals and negative integers iterate chosen left duals. -/
@[expose]
def iteratedDual [RigidCategory C] (X : C) : ℤ → C
  | .ofNat k => iteratedRightDual X k
  | .negSucc k => iteratedLeftDual X (k + 1)

@[simp]
theorem iteratedDual_natCast [RigidCategory C] (X : C) (k : ℕ) :
    iteratedDual X (k : ℤ) = iteratedRightDual X k := by rfl

@[simp]
theorem iteratedDual_zero [RigidCategory C] (X : C) :
    iteratedDual X 0 = X := by rfl

@[simp]
theorem iteratedDual_one [RigidCategory C] (X : C) :
    iteratedDual X 1 = (RightRigidCategory.rightDual X).rightDual := by rfl

@[simp]
theorem iteratedDual_two [RigidCategory C] (X : C) :
    iteratedDual X 2 =
      (RightRigidCategory.rightDual (RightRigidCategory.rightDual X).rightDual).rightDual := by
  rfl

@[simp]
theorem iteratedDual_negSucc [RigidCategory C] (X : C) (k : ℕ) :
    iteratedDual X (.negSucc k) = iteratedLeftDual X (k + 1) := by rfl

@[simp]
theorem iteratedDual_neg_one [RigidCategory C] (X : C) :
    iteratedDual X (-1) = (LeftRigidCategory.leftDual X).leftDual := by rfl

/-- Structural comparison `(iteratedDual X n)ᘁ ≅ iteratedDual X (n + 1)` built without `eqToHom`:
nonnegative levels extend `iteratedRightDual` definitionally, while negative levels cancel the
outermost left dual via `rightDualLeftDualIso`. -/
@[expose]
noncomputable def iteratedDualRightDualIso [RigidCategory C] (X : C) :
    (n : ℤ) →
      (RightRigidCategory.rightDual (iteratedDual X n)).rightDual ≅ iteratedDual X (n + 1)
  | .ofNat k => Iso.refl (iteratedRightDual X (k + 1))
  | .negSucc 0 => (rightDualLeftDualIso C).app X
  | .negSucc (k + 1) => (rightDualLeftDualIso C).app (iteratedLeftDual X (k + 1))

@[simp]
theorem iteratedDualRightDualIso_natCast [RigidCategory C] (X : C) (k : ℕ) :
    iteratedDualRightDualIso X (k : ℤ) = Iso.refl (iteratedRightDual X (k + 1)) := by rfl

@[simp]
theorem iteratedDualRightDualIso_neg_one [RigidCategory C] (X : C) :
    iteratedDualRightDualIso X (-1) = (rightDualLeftDualIso C).app X := by rfl

@[simp]
theorem iteratedDualRightDualIso_negSucc_succ [RigidCategory C] (X : C) (k : ℕ) :
    iteratedDualRightDualIso X (.negSucc (k + 1)) =
      (rightDualLeftDualIso C).app (iteratedLeftDual X (k + 1)) := by rfl

/-- Structural comparison `ᘁ(iteratedDual X n) ≅ iteratedDual X (n - 1)`: nonpositive levels extend
`iteratedLeftDual` definitionally, while positive levels cancel the outermost right dual via
`leftDualRightDualIso`. -/
@[expose]
noncomputable def iteratedDualLeftDualIso [RigidCategory C] (X : C) :
    (n : ℤ) →
      (LeftRigidCategory.leftDual (iteratedDual X n)).leftDual ≅ iteratedDual X (n - 1)
  | .ofNat 0 => Iso.refl _
  | .ofNat (k + 1) =>
      (leftDualRightDualIso C).app (iteratedRightDual X k) ≪≫
        eqToIso (congrArg (iteratedDual X) (add_sub_cancel_right (k : ℤ) 1).symm)
  | .negSucc _ => Iso.refl _

@[simp]
theorem iteratedDualLeftDualIso_zero [RigidCategory C] (X : C) :
    iteratedDualLeftDualIso X 0 = Iso.refl (iteratedLeftDual X 1) := by rfl

@[simp]
theorem iteratedDualLeftDualIso_one [RigidCategory C] (X : C) :
    iteratedDualLeftDualIso X 1 = (leftDualRightDualIso C).app X := by
  ext
  exact Category.comp_id _

@[simp]
theorem iteratedDualLeftDualIso_negSucc [RigidCategory C] (X : C) (k : ℕ) :
    iteratedDualLeftDualIso X (.negSucc k) = Iso.refl (iteratedLeftDual X (k + 2)) := by rfl

end IteratedDual

/-! ### Evaluation of winding words -/

namespace WindingWord

/-- Right dual of a winding word as reversal followed by shifting every integer level by `+1`. -/
theorem rightDual_eq_map_reverse {α : Type*} (L : WindingWord α) :
    L.rightDual = L.reverse.map fun p ↦ (p.1, p.2 + 1) := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

/-- Left dual of a winding word as reversal followed by shifting every integer level by `-1`. -/
theorem leftDual_eq_map_reverse {α : Type*} (L : WindingWord α) :
    L.leftDual = L.reverse.map fun p ↦ (p.1, p.2 - 1) := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

variable [RigidCategory C]

/-- Evaluate `L : WindingWord α` in a rigid monoidal category `C` as the right-associated tensor
product of the iterated duals `iteratedDual (f p.1) p.2`. -/
@[expose]
def evalObj {α : Type*} (f : α → C) (L : WindingWord α) : C :=
  tensorList (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L

@[simp]
theorem evalObj_nil {α : Type*} (f : α → C) :
    evalObj f ([] : WindingWord α) = 𝟙_ C := by rfl

@[simp]
theorem evalObj_cons {α : Type*} (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    evalObj f (p :: L) = iteratedDual (f p.1) p.2 ⊗ evalObj f L := by rfl

/-- Right-unitor isomorphism `evalObj f [p] ≅ iteratedDual (f p.1) p.2` on a single port. -/
def evalObjSingletonIso {α : Type*} (f : α → C) (p : α × ℤ) :
    evalObj f [p] ≅ iteratedDual (f p.1) p.2 :=
  tensorListSingletonIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2) p

/-- Concatenation comparison `evalObj f L ⊗ evalObj f M ≅ evalObj f (L ++ M)` built without
`eqToHom`. -/
def evalObjAppendIso {α : Type*} (f : α → C) (L M : WindingWord α) :
    evalObj f L ⊗ evalObj f M ≅ evalObj f (L ++ M) :=
  tensorListAppendIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L M

@[simp]
theorem evalObjAppendIso_nil {α : Type*} (f : α → C) (M : WindingWord α) :
    evalObjAppendIso f [] M = λ_ (evalObj f M) :=
  tensorListAppendIso_nil _ M

/-- Recursive step of `evalObjAppendIso` on `p :: L`. -/
theorem evalObjAppendIso_cons_hom {α : Type*} (f : α → C) (p : α × ℤ) (L M : WindingWord α) :
    (evalObjAppendIso f (p :: L) M).hom =
      (α_ (iteratedDual (f p.1) p.2) (evalObj f L) (evalObj f M)).hom ≫
        iteratedDual (f p.1) p.2 ◁ (evalObjAppendIso f L M).hom :=
  tensorListAppendIso_cons_hom _ p L M

/-- Right-dual comparison `(evalObj f L)ᘁ ≅ evalObj f L.rightDual` reversing the tensor factors via
`(rightDualFunctor C).opMopTensorListIso` and advancing each dual level by `+1`. -/
noncomputable def evalObjRightDualIso {α : Type*} (f : α → C) (L : WindingWord α) :
    (RightRigidCategory.rightDual (evalObj f L)).rightDual ≅ evalObj f L.rightDual :=
  (rightDualFunctor C).opMopTensorListIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L ≪≫
    tensorListCongrIso (fun p : α × ℤ ↦ iteratedDualRightDualIso (f p.1) p.2) L.reverse ≪≫
    tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
      (fun p : α × ℤ ↦ (p.1, p.2 + 1)) L.reverse ≪≫
    eqToIso (congrArg (evalObj f) (rightDual_eq_map_reverse L).symm)

/-- Explicit forward morphism of `evalObjRightDualIso`. -/
theorem evalObjRightDualIso_hom {α : Type*} (f : α → C) (L : WindingWord α) :
    (evalObjRightDualIso f L).hom =
      ((rightDualFunctor C).opMopTensorListIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L).hom ≫
        tensorListCongrHom (fun p : α × ℤ ↦ (iteratedDualRightDualIso (f p.1) p.2).hom) L.reverse ≫
        (tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
          (fun p : α × ℤ ↦ (p.1, p.2 + 1)) L.reverse).hom ≫
        eqToHom (congrArg (evalObj f) (rightDual_eq_map_reverse L).symm) := by
  exact congrArg (fun g ↦ _ ≫ g ≫ _ ≫ _) (tensorListCongrIso_hom _ _)

/-- Left-dual comparison `ᘁ(evalObj f L) ≅ evalObj f L.leftDual` reversing the tensor factors via
`(leftDualFunctor C).opMopTensorListIso` and shifting each dual level by `-1`. -/
noncomputable def evalObjLeftDualIso {α : Type*} (f : α → C) (L : WindingWord α) :
    (LeftRigidCategory.leftDual (evalObj f L)).leftDual ≅ evalObj f L.leftDual :=
  (leftDualFunctor C).opMopTensorListIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L ≪≫
    tensorListCongrIso (fun p : α × ℤ ↦ iteratedDualLeftDualIso (f p.1) p.2) L.reverse ≪≫
    tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
      (fun p : α × ℤ ↦ (p.1, p.2 - 1)) L.reverse ≪≫
    eqToIso (congrArg (evalObj f) (leftDual_eq_map_reverse L).symm)

/-- Explicit forward morphism of `evalObjLeftDualIso`. -/
theorem evalObjLeftDualIso_hom {α : Type*} (f : α → C) (L : WindingWord α) :
    (evalObjLeftDualIso f L).hom =
      ((leftDualFunctor C).opMopTensorListIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L).hom ≫
        tensorListCongrHom (fun p : α × ℤ ↦ (iteratedDualLeftDualIso (f p.1) p.2).hom) L.reverse ≫
        (tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
          (fun p : α × ℤ ↦ (p.1, p.2 - 1)) L.reverse).hom ≫
        eqToHom (congrArg (evalObj f) (leftDual_eq_map_reverse L).symm) := by
  exact congrArg (fun g ↦ _ ≫ g ≫ _ ≫ _) (tensorListCongrIso_hom _ _)

private noncomputable def evalObjRightPowIso {α : Type*} (f : α → C) :
    (k : ℕ) → (L : WindingWord α) →
      iteratedRightDual (evalObj f L) k ≅ evalObj f (L.dualPow (k : ℤ))
  | 0, L => eqToIso (congrArg (evalObj f) (dualPow_zero L).symm)
  | k + 1, L =>
      ((rightDualFunctor C).mapIso (evalObjRightPowIso f k L).symm).unmop.unop ≪≫
        evalObjRightDualIso f (L.dualPow (k : ℤ)) ≪≫
        eqToIso (congrArg (evalObj f) (by rw [Int.natCast_succ, dualPow_add_one]))

private noncomputable def evalObjLeftPowIso {α : Type*} (f : α → C) :
    (k : ℕ) → (L : WindingWord α) →
      iteratedLeftDual (evalObj f L) (k + 1) ≅ evalObj f (L.dualPow (.negSucc k))
  | 0, L =>
      evalObjLeftDualIso f L ≪≫ eqToIso (congrArg (evalObj f) (dualPow_neg_one L).symm)
  | k + 1, L =>
      ((leftDualFunctor C).mapIso (evalObjLeftPowIso f k L).symm).unmop.unop ≪≫
        evalObjLeftDualIso f (L.dualPow (.negSucc k)) ≪≫
        eqToIso (congrArg (evalObj f) (by
          have h : Int.negSucc (k + 1) = Int.negSucc k - 1 := rfl
          rw [h, dualPow_sub_one]))

/-- Iterated-dual comparison `iteratedDual (evalObj f L) n ≅ evalObj f (L.dualPow n)` for arbitrary
integer dual powers `n : ℤ`. -/
noncomputable def evalObjDualPowIso {α : Type*} (f : α → C) :
    (n : ℤ) → (L : WindingWord α) → iteratedDual (evalObj f L) n ≅ evalObj f (L.dualPow n)
  | .ofNat k, L => evalObjRightPowIso f k L
  | .negSucc k, L => evalObjLeftPowIso f k L

@[simp]
theorem evalObjDualPowIso_zero {α : Type*} (f : α → C) (L : WindingWord α) :
    evalObjDualPowIso f 0 L = eqToIso (congrArg (evalObj f) (dualPow_zero L).symm) := by rfl

/-- Substitution comparison `evalObj (fun a ↦ evalObj f (σ a)) L ≅ evalObj f (L.subst σ)` splicing
each multi-port replacement word through its integer dual level. -/
noncomputable def evalObjSubstIso {α β : Type*} (f : β → C) (σ : α → WindingWord β)
    (L : WindingWord α) :
    evalObj (fun a ↦ evalObj f (σ a)) L ≅ evalObj f (L.subst σ) :=
  tensorListCongrIso (fun p : α × ℤ ↦ evalObjDualPowIso f p.2 (σ p.1)) L ≪≫
    tensorListFlatMapIso (fun q : β × ℤ ↦ iteratedDual (f q.1) q.2)
      (fun p : α × ℤ ↦ (σ p.1).dualPow p.2) L ≪≫
    eqToIso (congrArg (evalObj f) (subst_def σ L).symm)

end WindingWord

/-! ### Direct evaluation of formal rigid objects -/

namespace RigidObject

variable [RigidCategory C]

/-- Evaluate a parenthesized formal `RigidObject α` directly in `C` using the chosen tensor product,
tensor unit, right dual, and left dual. -/
@[expose]
def evalObj {α : Type*} (f : α → C) : RigidObject α → C
  | .of a => f a
  | .unit => 𝟙_ C
  | .tensor X Y => evalObj f X ⊗ evalObj f Y
  | .rightDual X => (RightRigidCategory.rightDual (evalObj f X)).rightDual
  | .leftDual X => (LeftRigidCategory.leftDual (evalObj f X)).leftDual

@[simp]
theorem evalObj_of {α : Type*} (f : α → C) (a : α) :
    evalObj f (.of a) = f a := by rfl

@[simp]
theorem evalObj_unit {α : Type*} (f : α → C) :
    evalObj f (.unit : RigidObject α) = 𝟙_ C := by rfl

@[simp]
theorem evalObj_tensor {α : Type*} (f : α → C) (X Y : RigidObject α) :
    evalObj f (X.tensor Y) = evalObj f X ⊗ evalObj f Y := by rfl

@[simp]
theorem evalObj_rightDual {α : Type*} (f : α → C) (X : RigidObject α) :
    evalObj f X.rightDual = (RightRigidCategory.rightDual (evalObj f X)).rightDual := by rfl

@[simp]
theorem evalObj_leftDual {α : Type*} (f : α → C) (X : RigidObject α) :
    evalObj f X.leftDual = (LeftRigidCategory.leftDual (evalObj f X)).leftDual := by rfl

/-- Canonical comparison isomorphism between the direct evaluation of `X : RigidObject α` and
the evaluation of its normalized winding word `X.normalize`. -/
noncomputable def evalObjNormalizeIso {α : Type*} (f : α → C) :
    (X : RigidObject α) → X.evalObj f ≅ X.normalize.evalObj f
  | .of a =>
      (ρ_ (f a)).symm ≪≫ eqToIso (congrArg (WindingWord.evalObj f) (normalize_of a).symm)
  | .unit =>
      eqToIso (congrArg (WindingWord.evalObj f) normalize_unit.symm)
  | .tensor X Y =>
      (evalObjNormalizeIso f X ⊗ᵢ evalObjNormalizeIso f Y) ≪≫
        WindingWord.evalObjAppendIso f X.normalize Y.normalize ≪≫
        eqToIso (congrArg (WindingWord.evalObj f) (normalize_tensor X Y).symm)
  | .rightDual X =>
      ((rightDualFunctor C).mapIso (evalObjNormalizeIso f X).symm).unmop.unop ≪≫
        WindingWord.evalObjRightDualIso f X.normalize ≪≫
        eqToIso (congrArg (WindingWord.evalObj f) (normalize_rightDual X).symm)
  | .leftDual X =>
      ((leftDualFunctor C).mapIso (evalObjNormalizeIso f X).symm).unmop.unop ≪≫
        WindingWord.evalObjLeftDualIso f X.normalize ≪≫
        eqToIso (congrArg (WindingWord.evalObj f) (normalize_leftDual X).symm)

@[simp]
theorem evalObjNormalizeIso_unit {α : Type*} (f : α → C) :
    evalObjNormalizeIso f (.unit : RigidObject α) =
      eqToIso (congrArg (WindingWord.evalObj f) normalize_unit.symm) := by rfl

end RigidObject

end TauCeti
