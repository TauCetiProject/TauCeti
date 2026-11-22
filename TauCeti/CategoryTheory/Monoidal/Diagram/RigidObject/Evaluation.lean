/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Substitution
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.IteratedDual
public import TauCeti.CategoryTheory.Monoidal.Rigid.LeftDualFunctor

/-!
# Evaluating rigid objects and the normalization comparison

Let `C` be a rigid monoidal category and `f : α → C` an assignment of objects to generators.
A formal rigid object `X : RigidObject α` evaluates to `RigidObject.eval f X`, reading the
formal tensor, unit and duals as those of `C`, with the duals chosen by its rigid structure.
A winding word evaluates letterwise: the letter `(a, n)` becomes `TauCeti.iteratedDual n (f a)`
(from `TauCeti.CategoryTheory.Monoidal.Rigid.IteratedDual`), the `n`-fold right dual of `f a`
when `n ≥ 0` and the `-n`-fold left dual when `n < 0`, and a word is the right-associated
tensor product of its letters, closed by the unit (`WindingWord.eval`). The canonical
expression `RigidObject.ofWord L` of a word evaluates to `WindingWord.eval f L`
(`RigidObject.eval_ofWord`).

This file constructs the comparison isomorphism
`RigidObject.normalizeIso f X : RigidObject.eval f X ≅ WindingWord.eval f X.normalize`
from a formal expression to its normalized winding word. It is assembled from
the structural isomorphisms of `C`:

* `WindingWord.evalAppendIso`: concatenation of words is the tensor product, through
  associators and the left unitor;
* `WindingWord.evalRightDualIso` and `WindingWord.evalLeftDualIso`: the dual of an evaluated word
  is the evaluated dual word. The tensor order is reversed by Mathlib's `rightDualTensorIso` and
  `leftDualTensorIso`, the dual of the unit is identified with the unit, and on letters the level
  changes by one (`TauCeti.iteratedDualRightDualIso`, `TauCeti.iteratedDualLeftDualIso`). A mixed
  double dual `(ᘁY)ᘁ` or `ᘁ(Yᘁ)` is identified with `Y` by Mathlib's comparisons `rightDualIso`
  and `leftDualIso` between two duals; two duals of the same handedness are never identified, so
  the integer levels are kept.

As a consequence, two formal objects with the same normalization have isomorphic evaluations
(`RigidObject.evalIsoOfNormalizeEq`). For instance `ᘁ(Xᘁ)` and `X` do, whereas `Xᘁᘁ` and `X` have
different normalizations (`RigidObject.normalize_rightDual_rightDual_ne`), and no comparison
between them is produced. No pivotal structure is used.

Evaluation is compatible with substitution: `RigidObject.eval_subst` for formal objects, and
`WindingWord.evalSubstIso` for words, which transports each replacing word through the
integer dual level of its occurrence using `WindingWord.evalDualPowIso`.

The integer-level convention is that of Joyal and Street, *Planar diagrams and tensor
algebra*, §2: the right dual of a letter at level `n` is at level `n + 1`.
-/

public section

open CategoryTheory MonoidalCategory

universe v u w w'

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

namespace WindingWord

variable {α : Type w} {β : Type w'}

/-- Evaluate a winding word in a rigid monoidal category: the letter `(a, n)` becomes the
iterated dual `iteratedDual n (f a)`, and the word is the right-associated tensor product of its
letters, closed by the unit. In particular the empty word evaluates to `𝟙_ C`. -/
@[expose]
def eval (f : α → C) : WindingWord α → C
  | [] => 𝟙_ C
  | p :: L => iteratedDual p.2 (f p.1) ⊗ eval f L

@[simp] theorem eval_nil (f : α → C) : eval f [] = 𝟙_ C := rfl

@[simp] theorem eval_cons (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    eval f (p :: L) = iteratedDual p.2 (f p.1) ⊗ eval f L := rfl

/-- The evaluation of a concatenation is the tensor product of the evaluations. -/
def evalAppendIso (f : α → C) : (L M : WindingWord α) → eval f (L ++ M) ≅ eval f L ⊗ eval f M
  | [], M => (λ_ (eval f M)).symm
  | p :: L, M => whiskerLeftIso (iteratedDual p.2 (f p.1)) (evalAppendIso f L M) ≪≫ (α_ _ _ _).symm

@[simp] theorem evalAppendIso_nil (f : α → C) (M : WindingWord α) :
    evalAppendIso f [] M = (λ_ (eval f M)).symm := (rfl)

@[simp] theorem evalAppendIso_cons (f : α → C) (p : α × ℤ) (L M : WindingWord α) :
    evalAppendIso f (p :: L) M =
      whiskerLeftIso (iteratedDual p.2 (f p.1)) (evalAppendIso f L M) ≪≫ (α_ _ _ _).symm := (rfl)

/-- The chosen right dual of an evaluated word is the evaluation of its right dual word: the
tensor order is reversed, the dual of the unit is the unit, and each level rises by one. -/
noncomputable def evalRightDualIso (f : α → C) :
    (L : WindingWord α) → (eval f L)ᘁ ≅ eval f (rightDual L)
  | [] => rightDualUnitIso C ≪≫ eqToIso (by simp)
  | p :: L =>
    rightDualTensorIso _ _ ≪≫
      (evalRightDualIso f L ⊗ᵢ (iteratedDualRightDualIso p.2 (f p.1) ≪≫ (ρ_ _).symm)) ≪≫
      (evalAppendIso f (rightDual L) [(p.1, p.2 + 1)]).symm ≪≫
      eqToIso (congrArg (eval f) (rightDual_cons p L).symm)

/-- The chosen left dual of an evaluated word is the evaluation of its left dual word: the
tensor order is reversed, the dual of the unit is the unit, and each level falls by one. -/
noncomputable def evalLeftDualIso (f : α → C) :
    (L : WindingWord α) → (ᘁ(eval f L) : C) ≅ eval f (leftDual L)
  | [] => leftDualUnitIso C ≪≫ eqToIso (by simp)
  | p :: L =>
    leftDualTensorIso _ _ ≪≫
      (evalLeftDualIso f L ⊗ᵢ (iteratedDualLeftDualIso p.2 (f p.1) ≪≫ (ρ_ _).symm)) ≪≫
      (evalAppendIso f (leftDual L) [(p.1, p.2 - 1)]).symm ≪≫
      eqToIso (congrArg (eval f) (leftDual_cons p L).symm)

@[simp] theorem evalRightDualIso_nil (f : α → C) :
    evalRightDualIso f [] =
      rightDualUnitIso C ≪≫ eqToIso (by simp) := (rfl)

@[simp] theorem evalRightDualIso_cons (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    evalRightDualIso f (p :: L) =
      rightDualTensorIso _ _ ≪≫
        (evalRightDualIso f L ⊗ᵢ (iteratedDualRightDualIso p.2 (f p.1) ≪≫ (ρ_ _).symm)) ≪≫
        (evalAppendIso f (rightDual L) [(p.1, p.2 + 1)]).symm ≪≫
        eqToIso (congrArg (eval f) (rightDual_cons p L).symm) := (rfl)

@[simp] theorem evalLeftDualIso_nil (f : α → C) :
    evalLeftDualIso f [] =
      leftDualUnitIso C ≪≫ eqToIso (by simp) := (rfl)

@[simp] theorem evalLeftDualIso_cons (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    evalLeftDualIso f (p :: L) =
      leftDualTensorIso _ _ ≪≫
        (evalLeftDualIso f L ⊗ᵢ (iteratedDualLeftDualIso p.2 (f p.1) ≪≫ (ρ_ _).symm)) ≪≫
        (evalAppendIso f (leftDual L) [(p.1, p.2 - 1)]).symm ≪≫
        eqToIso (congrArg (eval f) (leftDual_cons p L).symm) := (rfl)

/-- The evaluation of the `n`-th right dual word is the `n`-fold iterated right dual. -/
noncomputable def evalRightDualPowIso (f : α → C) :
    (n : ℕ) → (L : WindingWord α) → eval f (dualPow (n : ℤ) L) ≅ iteratedRightDual n (eval f L)
  | 0, L => eqToIso (by simp)
  | n + 1, L =>
    eqToIso (by simp) ≪≫
      (evalRightDualIso f (dualPow (n : ℤ) L)).symm ≪≫
      (evalRightDualPowIso f n L).symm.rightAdjointMate

/-- The evaluation of the `n`-th left dual word is the `n`-fold iterated left dual. -/
noncomputable def evalLeftDualPowIso (f : α → C) :
    (n : ℕ) → (L : WindingWord α) → eval f (dualPow (-(n : ℤ)) L) ≅ iteratedLeftDual n (eval f L)
  | 0, L => eqToIso (by simp)
  | n + 1, L =>
    eqToIso (congrArg (eval f)
        (by rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by omega, dualPow_sub_one])) ≪≫
      (evalLeftDualIso f (dualPow (-(n : ℤ)) L)).symm ≪≫
      (evalLeftDualPowIso f n L).symm.leftAdjointMate

/-- The evaluation of an integer dual power of a word is the iterated dual at that level. -/
noncomputable def evalDualPowIso (f : α → C) :
    (n : ℤ) → (L : WindingWord α) → eval f (dualPow n L) ≅ iteratedDual n (eval f L)
  | .ofNat n, L => evalRightDualPowIso f n L
  | .negSucc n, L =>
    eqToIso (congrArg (fun k ↦ eval f (dualPow k L))
        (by omega : Int.negSucc n = -((n + 1 : ℕ) : ℤ))) ≪≫
      evalLeftDualPowIso f (n + 1) L

/-- Substituting words for generators and then evaluating agrees, up to isomorphism, with
evaluating at the evaluated replacing words: the replacing word at level `n` is evaluated
through `n` duals (`evalDualPowIso`). -/
noncomputable def evalSubstIso (g : β → C) (F : α → WindingWord β) :
    (L : WindingWord α) → eval g (subst F L) ≅ eval (fun a ↦ eval g (F a)) L
  | [] => eqToIso (by simp)
  | p :: L =>
    eqToIso (congrArg (eval g) (subst_cons F p L)) ≪≫
      evalAppendIso g (dualPow p.2 (F p.1)) (subst F L) ≪≫
      (evalDualPowIso g p.2 (F p.1) ⊗ᵢ evalSubstIso g F L)

@[simp] theorem evalRightDualPowIso_zero (f : α → C) (L : WindingWord α) :
    evalRightDualPowIso f 0 L = eqToIso (by simp) := (rfl)

@[simp] theorem evalRightDualPowIso_succ (f : α → C) (n : ℕ) (L : WindingWord α) :
    evalRightDualPowIso f (n + 1) L =
      eqToIso (by simp) ≪≫ (evalRightDualIso f (dualPow (n : ℤ) L)).symm ≪≫
        (evalRightDualPowIso f n L).symm.rightAdjointMate := (rfl)

@[simp] theorem evalLeftDualPowIso_zero (f : α → C) (L : WindingWord α) :
    evalLeftDualPowIso f 0 L = eqToIso (by simp) := (rfl)

@[simp] theorem evalLeftDualPowIso_succ (f : α → C) (n : ℕ) (L : WindingWord α) :
    evalLeftDualPowIso f (n + 1) L =
      eqToIso (congrArg (eval f)
          (by rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by omega, dualPow_sub_one])) ≪≫
        (evalLeftDualIso f (dualPow (-(n : ℤ)) L)).symm ≪≫
        (evalLeftDualPowIso f n L).symm.leftAdjointMate := (rfl)

@[simp] theorem evalDualPowIso_natCast (f : α → C) (n : ℕ) (L : WindingWord α) :
    evalDualPowIso f (n : ℤ) L = evalRightDualPowIso f n L := (rfl)

@[simp] theorem evalDualPowIso_negSucc (f : α → C) (n : ℕ) (L : WindingWord α) :
    evalDualPowIso f (.negSucc n) L =
      eqToIso (congrArg (fun k ↦ eval f (dualPow k L))
          (by omega : Int.negSucc n = -((n + 1 : ℕ) : ℤ))) ≪≫
        evalLeftDualPowIso f (n + 1) L := (rfl)

@[simp] theorem evalSubstIso_nil (g : β → C) (F : α → WindingWord β) :
    evalSubstIso g F [] = eqToIso (by simp) := (rfl)

@[simp] theorem evalSubstIso_cons (g : β → C) (F : α → WindingWord β) (p : α × ℤ)
    (L : WindingWord α) :
    evalSubstIso g F (p :: L) =
      eqToIso (congrArg (eval g) (subst_cons F p L)) ≪≫
        evalAppendIso g (dualPow p.2 (F p.1)) (subst F L) ≪≫
        (evalDualPowIso g p.2 (F p.1) ⊗ᵢ evalSubstIso g F L) := (rfl)

end WindingWord

namespace RigidObject

variable {α : Type w} {β : Type w'}

/-- Evaluate a formal rigid object in a rigid monoidal category, reading the formal tensor,
unit and duals as those of `C`; the duals are the ones chosen by the rigid structure. -/
@[expose]
def eval (f : α → C) : RigidObject α → C
  | .of a => f a
  | .unit => 𝟙_ C
  | .tensor X Y => eval f X ⊗ eval f Y
  | .rightDual X => (eval f X)ᘁ
  | .leftDual X => (ᘁ(eval f X) : C)

@[simp] theorem eval_of (f : α → C) (a : α) : eval f (.of a) = f a := rfl

@[simp] theorem eval_unit (f : α → C) : eval f (.unit : RigidObject α) = 𝟙_ C := rfl

@[simp] theorem eval_tensor (f : α → C) (X Y : RigidObject α) :
    eval f (X.tensor Y) = eval f X ⊗ eval f Y := rfl

@[simp] theorem eval_rightDual (f : α → C) (X : RigidObject α) :
    eval f X.rightDual = (eval f X)ᘁ := rfl

@[simp] theorem eval_leftDual (f : α → C) (X : RigidObject α) :
    eval f X.leftDual = (ᘁ(eval f X) : C) := rfl

/-- Evaluation commutes with substitution of formal objects for generators. -/
@[simp] theorem eval_subst (g : β → C) (F : α → RigidObject β) (X : RigidObject α) :
    eval g (subst F X) = eval (fun a ↦ eval g (F a)) X := by
  induction X with
  | of a => rw [subst_of, eval_of]
  | unit => rw [subst_unit, eval_unit, eval_unit]
  | tensor X Y ihX ihY => rw [subst_tensor, eval_tensor, eval_tensor, ihX, ihY]
  | rightDual X ih => rw [subst_rightDual, eval_rightDual, eval_rightDual, ih]
  | leftDual X ih => rw [subst_leftDual, eval_leftDual, eval_leftDual, ih]

private theorem eval_rightDual_iterate (f : α → C) (n : ℕ) (X : RigidObject α) :
    eval f (rightDual^[n] X) = iteratedRightDual n (eval f X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', eval_rightDual, ih, iteratedRightDual_succ]

private theorem eval_leftDual_iterate (f : α → C) (n : ℕ) (X : RigidObject α) :
    eval f (leftDual^[n] X) = iteratedLeftDual n (eval f X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', eval_leftDual, ih, iteratedLeftDual_succ]

/-- The formal atom at level `n` evaluates to the iterated dual at level `n`. -/
@[simp] theorem eval_atLevel (f : α → C) (a : α) (n : ℤ) :
    eval f (atLevel a n) = iteratedDual n (f a) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, atLevel_natCast, eval_rightDual_iterate, eval_of,
      iteratedDual_natCast]
  | negSucc n =>
    rw [atLevel_negSucc, eval_leftDual_iterate, eval_of, iteratedDual_negSucc]

/-- The canonical expression realizing a winding word evaluates to that word. -/
@[simp] theorem eval_ofWord (f : α → C) (L : WindingWord α) :
    eval f (ofWord L) = WindingWord.eval f L := by
  induction L with
  | nil => rw [ofWord_nil, eval_unit, WindingWord.eval_nil]
  | cons p L ih => rcases p with ⟨a, n⟩; simp [ih]

/-- The comparison isomorphism from a formal rigid object to its normalized winding word. It is
built from the unitors and associators (`WindingWord.evalAppendIso`) and the dual comparisons
`WindingWord.evalRightDualIso` and `WindingWord.evalLeftDualIso`; no pivotal structure is
involved. -/
noncomputable def normalizeIso (f : α → C) :
    (X : RigidObject α) → eval f X ≅ WindingWord.eval f X.normalize
  | .of a => (ρ_ (f a)).symm ≪≫ eqToIso (by simp)
  | .unit => eqToIso (by simp)
  | .tensor X Y =>
    (normalizeIso f X ⊗ᵢ normalizeIso f Y) ≪≫
      (WindingWord.evalAppendIso f X.normalize Y.normalize).symm ≪≫
      eqToIso (congrArg (WindingWord.eval f) (normalize_tensor X Y).symm)
  | .rightDual X =>
    (normalizeIso f X).symm.rightAdjointMate ≪≫ WindingWord.evalRightDualIso f X.normalize ≪≫
      eqToIso (congrArg (WindingWord.eval f) (normalize_rightDual X).symm)
  | .leftDual X =>
    (normalizeIso f X).symm.leftAdjointMate ≪≫ WindingWord.evalLeftDualIso f X.normalize ≪≫
      eqToIso (congrArg (WindingWord.eval f) (normalize_leftDual X).symm)

@[simp] theorem normalizeIso_of (f : α → C) (a : α) :
    normalizeIso f (.of a) =
      (ρ_ (f a)).symm ≪≫ eqToIso (by simp) := (rfl)

@[simp] theorem normalizeIso_unit (f : α → C) :
    normalizeIso f (.unit : RigidObject α) =
      eqToIso (by simp) := (rfl)

@[simp] theorem normalizeIso_tensor (f : α → C) (X Y : RigidObject α) :
    normalizeIso f (X.tensor Y) =
      (normalizeIso f X ⊗ᵢ normalizeIso f Y) ≪≫
        (WindingWord.evalAppendIso f X.normalize Y.normalize).symm ≪≫
        eqToIso (congrArg (WindingWord.eval f) (normalize_tensor X Y).symm) := (rfl)

@[simp] theorem normalizeIso_rightDual (f : α → C) (X : RigidObject α) :
    normalizeIso f X.rightDual =
      (normalizeIso f X).symm.rightAdjointMate ≪≫ WindingWord.evalRightDualIso f X.normalize ≪≫
        eqToIso (congrArg (WindingWord.eval f) (normalize_rightDual X).symm) := (rfl)

@[simp] theorem normalizeIso_leftDual (f : α → C) (X : RigidObject α) :
    normalizeIso f X.leftDual =
      (normalizeIso f X).symm.leftAdjointMate ≪≫ WindingWord.evalLeftDualIso f X.normalize ≪≫
        eqToIso (congrArg (WindingWord.eval f) (normalize_leftDual X).symm) := (rfl)

/-- Formal rigid objects with the same normalization have isomorphic evaluations, through their
normalization comparisons. -/
noncomputable def evalIsoOfNormalizeEq (f : α → C) {X Y : RigidObject α}
    (h : X.normalize = Y.normalize) : eval f X ≅ eval f Y :=
  normalizeIso f X ≪≫ eqToIso (congrArg (WindingWord.eval f) h) ≪≫ (normalizeIso f Y).symm

@[simp] theorem evalIsoOfNormalizeEq_hom (f : α → C) {X Y : RigidObject α}
    (h : X.normalize = Y.normalize) :
    (evalIsoOfNormalizeEq f h).hom =
      (normalizeIso f X).hom ≫ eqToHom (congrArg (WindingWord.eval f) h) ≫
        (normalizeIso f Y).inv := (rfl)

@[simp] theorem evalIsoOfNormalizeEq_inv (f : α → C) {X Y : RigidObject α}
    (h : X.normalize = Y.normalize) :
    (evalIsoOfNormalizeEq f h).inv =
      (normalizeIso f Y).hom ≫ eqToHom (congrArg (WindingWord.eval f) h.symm) ≫
        (normalizeIso f X).inv := by
  simp [evalIsoOfNormalizeEq]

@[simp] theorem evalIsoOfNormalizeEq_refl (f : α → C) (X : RigidObject α) :
    evalIsoOfNormalizeEq f (rfl : X.normalize = X.normalize) = Iso.refl _ := by
  ext; simp [evalIsoOfNormalizeEq]

@[simp] theorem evalIsoOfNormalizeEq_symm (f : α → C) {X Y : RigidObject α}
    (h : X.normalize = Y.normalize) :
    (evalIsoOfNormalizeEq f h).symm = evalIsoOfNormalizeEq f h.symm := by
  ext; simp [evalIsoOfNormalizeEq]

@[simp] theorem evalIsoOfNormalizeEq_trans (f : α → C) {X Y Z : RigidObject α}
    (h : X.normalize = Y.normalize) (h' : Y.normalize = Z.normalize) :
    evalIsoOfNormalizeEq f h ≪≫ evalIsoOfNormalizeEq f h' =
      evalIsoOfNormalizeEq f (h.trans h') := by
  ext; simp [evalIsoOfNormalizeEq]

/-- The isomorphism between evaluations of a formal rigid object induced by isomorphisms
`e a : f a ≅ g a` of the interpretations of its generators. -/
@[expose]
noncomputable def evalIso {f g : α → C} (e : ∀ a, f a ≅ g a) :
    ∀ X : RigidObject α, eval f X ≅ eval g X
  | .of a => e a
  | .unit => Iso.refl _
  | .tensor X Y => evalIso e X ⊗ᵢ evalIso e Y
  | .rightDual X => (evalIso e X).symm.rightAdjointMate
  | .leftDual X => (evalIso e X).symm.leftAdjointMate

@[simp] theorem evalIso_of {f g : α → C} (e : ∀ a, f a ≅ g a) (a : α) :
    evalIso e (.of a) = e a := (rfl)
@[simp] theorem evalIso_unit {f g : α → C} (e : ∀ a, f a ≅ g a) :
    evalIso e (.unit : RigidObject α) = Iso.refl (𝟙_ C) := (rfl)
@[simp] theorem evalIso_tensor {f g : α → C} (e : ∀ a, f a ≅ g a) (X Y : RigidObject α) :
    evalIso e (X.tensor Y) = evalIso e X ⊗ᵢ evalIso e Y := (rfl)
@[simp] theorem evalIso_rightDual {f g : α → C} (e : ∀ a, f a ≅ g a) (X : RigidObject α) :
    evalIso e X.rightDual = (evalIso e X).symm.rightAdjointMate := (rfl)
@[simp] theorem evalIso_leftDual {f g : α → C} (e : ∀ a, f a ≅ g a) (X : RigidObject α) :
    evalIso e X.leftDual = (evalIso e X).symm.leftAdjointMate := (rfl)

@[simp] theorem evalIso_refl {f : α → C} (X : RigidObject α) :
    evalIso (fun a ↦ Iso.refl (f a)) X = Iso.refl (eval f X) := by
  induction X with
  | of _ | unit => rfl
  | tensor _ _ ihX ihY => ext; simp [ihX, ihY]
  | rightDual _ ih | leftDual _ ih => ext; simp [ih]

@[simp] theorem evalIso_trans {f g h : α → C} (e : ∀ a, f a ≅ g a) (e' : ∀ a, g a ≅ h a)
    (X : RigidObject α) :
    evalIso (fun a ↦ e a ≪≫ e' a) X = evalIso e X ≪≫ evalIso e' X := by
  induction X with
  | of _ => rfl
  | unit => exact (Iso.refl_trans _).symm
  | tensor _ _ ihX ihY => ext; simp [ihX, ihY]
  | rightDual _ ih => ext; simp [ih, comp_rightAdjointMate]
  | leftDual _ ih => ext; simp [ih, comp_leftAdjointMate]

@[simp] theorem evalIso_symm {f g : α → C} (e : ∀ a, f a ≅ g a) (X : RigidObject α) :
    evalIso (fun a ↦ (e a).symm) X = (evalIso e X).symm := by
  induction X with
  | of _ => rfl
  | unit => exact (Iso.refl_symm _).symm
  | tensor _ _ ihX ihY => ext; simp [ihX, ihY]
  | rightDual _ ih | leftDual _ ih => ext; simp [ih]

end RigidObject

end TauCeti
