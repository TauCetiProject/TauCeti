/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.ParityWord.Evaluation
public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Evaluation
public import TauCeti.CategoryTheory.Monoidal.Pivotal.LeftDual
import Mathlib.Algebra.CharP.Two

/-!
# Pivotal comparison between integer winding words and parity words

In a rigid monoidal category `C` with `[PivotalCategory C]` (`φ_X : X ≅ Xᘁᘁ`), even dual shifts
are canonically identified with `X` and odd dual shifts — including negative levels via
`TauCeti.leftDualIsoRightDual` — with `Xᘁ`. Boundary objects thus reduce from `WindingWord.eval` to
`ParityWord.eval` up to pivotal isomorphism: passing from level `0` to `2` evaluates to `φ_X`
rather than `𝟙 X`.

## Main declarations

* `TauCeti.pivotalAtomIso`: the isomorphism `iteratedDual n X ≅ parityDual (n : ZMod 2) X` across
  all `n : ℤ`, with step coherence (`TauCeti.iteratedDualRightDualIso_hom_comp_pivotalAtomIso_hom`
  and `TauCeti.iteratedDualLeftDualIso_hom_comp_pivotalAtomIso_hom`);
* `TauCeti.WindingWord.pivotalComparisonIso` and `TauCeti.RigidObject.normalizeParityIso`:
  boundary comparisons coherent with the empty word, concatenation, right duality, and left duality;
* `TauCeti.WindingWord.transportCoupon`: coupon transport to parity boundaries, preserving
  identities, composition, concatenation tensoring, and right and left mates.

## References

* P. Freyd and D. Yetter, *Coherence theorems via knot theory*, J. Pure Appl. Algebra 78 (1992),
  49–76, Theorem 4.4.
* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, §2.
* P. Selinger, *A survey of graphical languages for monoidal categories*, §4.2.
* P. Etingof, S. Gelaki, D. Nikshych, and V. Ostrik, *Tensor Categories*, §4.7.
-/

public section

open CategoryTheory MonoidalCategory ExactPairing
open scoped CharTwo

namespace TauCeti

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Formal parity realizations in a rigid category -/

section RigidParityRealization

variable [RigidCategory C]

namespace RigidObject

variable {α : Type w}

/-- The formal parity atom `atParity a ε` evaluates strictly to `parityDual ε (f a)`. -/
@[simp] theorem eval_atParity (f : α → C) (a : α) (ε : ZMod 2) :
    eval f (atParity a ε) = parityDual ε (f a) := by
  rw [atParity_def, eval_atLevel]
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
  · simp
  · rw [show (ZMod.cast (1 : ZMod 2) : ℤ) = ((1 : ℕ) : ℤ) by decide]
    rfl

/-- The canonical expression `ofParityWord L` realizing a parity word evaluates strictly to
`ParityWord.eval f L`. -/
@[simp] theorem eval_ofParityWord (f : α → C) (L : ParityWord α) :
    eval f (ofParityWord L) = ParityWord.eval f L := by
  induction L with
  | nil => simp
  | cons p L ih => rcases p with ⟨a, ε⟩; simp [ih]

end RigidObject

end RigidParityRealization

/-! ### Atomic pivotal comparison across all integer dual levels -/

variable [RigidCategory C] [PivotalCategory C]

private theorem zmod2_of_succ {k : ℕ} {ε : ZMod 2} (h : ((k + 1 : ℕ) : ZMod 2) = ε) :
    (k : ZMod 2) = ε + 1 := by
  rw [← h, Nat.cast_add, Nat.cast_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem zmod2_of_negSucc {k : ℕ} {ε : ZMod 2}
    (h : (Int.negSucc (k + 1) : ZMod 2) = ε) :
    (Int.negSucc k : ZMod 2) = ε + 1 := by
  have heq : (Int.negSucc (k + 1) : ZMod 2) = (Int.negSucc k : ZMod 2) + 1 := by
    rw [show Int.negSucc (k + 1) = Int.negSucc k - 1 from rfl, Int.cast_sub, Int.cast_one,
      CharTwo.sub_eq_add]
  rw [← h, heq, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Functorial action of the chosen right dual on isomorphisms. -/
private def chosenRightDualIso {A B : C} (e : A ≅ B) :
    (RightRigidCategory.rightDual A).rightDual ≅
      (RightRigidCategory.rightDual B).rightDual where
  hom := @rightAdjointMate C _ _ B A (RightRigidCategory.rightDual B)
    (RightRigidCategory.rightDual A) e.inv
  inv := @rightAdjointMate C _ _ A B (RightRigidCategory.rightDual A)
    (RightRigidCategory.rightDual B) e.hom
  hom_inv_id := by
    rw [← @comp_rightAdjointMate C _ _ A B A (RightRigidCategory.rightDual A)
      (RightRigidCategory.rightDual B) (RightRigidCategory.rightDual A), e.hom_inv_id]
    exact @rightAdjointMate_id C _ _ A (RightRigidCategory.rightDual A)
  inv_hom_id := by
    rw [← @comp_rightAdjointMate C _ _ B A B (RightRigidCategory.rightDual B)
      (RightRigidCategory.rightDual A) (RightRigidCategory.rightDual B), e.inv_hom_id]
    exact @rightAdjointMate_id C _ _ B (RightRigidCategory.rightDual B)

/-- Functorial action of the chosen left dual on isomorphisms (avoiding `hasLeftDualRightDual`). -/
private def chosenLeftDualIso {A B : C} (e : A ≅ B) :
    (LeftRigidCategory.leftDual A).leftDual ≅
      (LeftRigidCategory.leftDual B).leftDual where
  hom := @leftAdjointMate C _ _ B A (LeftRigidCategory.leftDual B)
    (LeftRigidCategory.leftDual A) e.inv
  inv := @leftAdjointMate C _ _ A B (LeftRigidCategory.leftDual A)
    (LeftRigidCategory.leftDual B) e.hom
  hom_inv_id := by
    rw [← @comp_leftAdjointMate C _ _ A B A (LeftRigidCategory.leftDual A)
      (LeftRigidCategory.leftDual B) (LeftRigidCategory.leftDual A), e.hom_inv_id]
    exact @leftAdjointMate_id C _ _ A (LeftRigidCategory.leftDual A)
  inv_hom_id := by
    rw [← @comp_leftAdjointMate C _ _ B A B (LeftRigidCategory.leftDual B)
      (LeftRigidCategory.leftDual A) (LeftRigidCategory.leftDual B), e.inv_hom_id]
    exact @leftAdjointMate_id C _ _ B (LeftRigidCategory.leftDual B)

private noncomputable def pivotalRightPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((k : ZMod 2) = ε) →
      (iteratedRightDual k X ≅ parityDual ε X)
  | 0, ⟨0, _⟩, _ => Iso.refl X
  | 0, ⟨1, _⟩, h => False.elim ((by decide : ((0 : ℕ) : ZMod 2).val ≠ 1) (congrArg Fin.val h))
  | k + 1, ⟨0, _⟩, h =>
      chosenRightDualIso
        (pivotalRightPowAuxIso X k 1 (zmod2_of_succ (Fin.ext (congrArg Fin.val h)))) ≪≫
        (pivotalIsoApp X).symm
  | k + 1, ⟨1, _⟩, h =>
      chosenRightDualIso
        (pivotalRightPowAuxIso X k 0 (zmod2_of_succ (Fin.ext (congrArg Fin.val h))))

private noncomputable def pivotalLeftPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((Int.negSucc k : ZMod 2) = ε) →
      (iteratedLeftDual (k + 1) X ≅ parityDual ε X)
  | 0, ⟨0, _⟩, h =>
      False.elim ((by decide : (Int.negSucc 0 : ZMod 2).val ≠ 0) (congrArg Fin.val h))
  | 0, ⟨1, _⟩, _ => leftDualIsoRightDual X
  | k + 1, ⟨0, _⟩, h =>
      chosenLeftDualIso
        (pivotalLeftPowAuxIso X k 1 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))) ≪≫
        (leftDualRightDualIso C).app X
  | k + 1, ⟨1, _⟩, h =>
      chosenLeftDualIso
        (pivotalLeftPowAuxIso X k 0 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))) ≪≫
        leftDualIsoRightDual X

private noncomputable def pivotalAtomIsoAux :
    (n : ℤ) → (X : C) → (ε : ZMod 2) → ((n : ZMod 2) = ε) →
      (iteratedDual n X ≅ parityDual ε X)
  | .ofNat k, X, ε, h => pivotalRightPowAuxIso X k ε (by simpa using h)
  | .negSucc k, X, ε, h => pivotalLeftPowAuxIso X k ε h

/-- Pivotal isomorphism `iteratedDual n X ≅ parityDual (n : ZMod 2) X` reducing any integer
dual-winding level `n : ℤ` to its `ZMod 2` parity representative `X` or `Xᘁ`. -/
noncomputable def pivotalAtomIso (n : ℤ) (X : C) :
    iteratedDual n X ≅ parityDual (n : ZMod 2) X :=
  pivotalAtomIsoAux n X (n : ZMod 2) rfl

@[simp] theorem pivotalAtomIso_zero (X : C) : pivotalAtomIso 0 X = Iso.refl X := (rfl)

@[simp] theorem pivotalAtomIso_one (X : C) : pivotalAtomIso 1 X = Iso.refl Xᘁ := by
  ext
  exact rightAdjointMate_id (X := X)

@[simp] theorem pivotalAtomIso_neg_one (X : C) :
    pivotalAtomIso (-1) X = leftDualIsoRightDual X := (rfl)

/-- At winding level `2`, `pivotalAtomIso 2 X : Xᘁᘁ ≅ X` is `(pivotalIsoApp X).symm` — not the
identity — so identifying level `0` with level `2` evaluates to `(pivotalIsoApp X).hom`. -/
@[simp] theorem pivotalAtomIso_two (X : C) : pivotalAtomIso 2 X = (pivotalIsoApp X).symm := by
  ext
  exact ((congrArg rightAdjointMate (congrArg Iso.inv (pivotalAtomIso_one X))) =≫ _).trans
    ((rightAdjointMate_id (X := Xᘁ) =≫ _).trans (Category.id_comp _))

/-- By the Freyd–Yetter identity (`pivotalIsoApp_rightDual_inv`), the level-`3` comparison
`Xᘁᘁᘁ ⟶ Xᘁ` equals the inverse pivotal component at `Xᘁ`. -/
theorem pivotalAtomIso_three_hom (X : C) : (pivotalAtomIso 3 X).hom = (pivotalIsoApp Xᘁ).inv := by
  have h3 : (pivotalAtomIso 3 X).hom = ((pivotalAtomIso 2 X).inv)ᘁ := rfl
  rw [h3, pivotalAtomIso_two, Iso.symm_inv]
  exact (pivotalIsoApp_rightDual_inv X).symm

/-! ### Step coherence of `pivotalAtomIso` with right and left duality -/

private theorem pivotalAtomIsoAux_rightDual (n : ℤ) (X : C) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
    (h' : ((n + 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualRightDualIso n X).hom ≫ (pivotalAtomIsoAux (n + 1) X (ε + 1) h').hom =
      @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _) (pivotalAtomIsoAux n X ε h).inv ≫
        (parityDualRightDualIso ε X).hom := by
  cases n with
  | ofNat k =>
    refine ((congrArg Iso.hom (iteratedDualRightDualIso_natCast k X) =≫ _).trans
      (Category.id_comp _)).trans ?_
    rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
    · exact ((_ ≫= congrArg Iso.hom (parityDualRightDualIso_zero X)).trans
        (Category.comp_id _)).symm
    · exact (_ ≫= congrArg Iso.hom (parityDualRightDualIso_one X)).symm
  | negSucc k =>
    cases k with
    | zero =>
      rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
      · exact absurd (congrArg Fin.val h) (by decide)
      · rw [iteratedDualRightDualIso_negSucc_zero, ← rightDualLeftDualIso_hom_app,
          parityDualRightDualIso_one, Iso.symm_hom]
        exact (Category.comp_id _).trans
          (rightAdjointMate_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv X).symm
    | succ k =>
      rw [iteratedDualRightDualIso_negSucc_succ, ← rightDualLeftDualIso_hom_app]
      rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
      · rw [parityDualRightDualIso_zero, Iso.refl_hom]
        let q := (pivotalLeftPowAuxIso X k 1 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))).hom
        have hcomp : @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
            (RightRigidCategory.rightDual _) (pivotalAtomIsoAux (.negSucc (k + 1)) X 0 h).inv =
            (rightDualLeftDualFunctor C).map q ≫
              ((leftDualRightDualIso C).inv.app X)ᘁ :=
          @comp_rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual _)
            (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _)
            ((leftDualRightDualIso C).inv.app X)
            (@leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
              (LeftRigidCategory.leftDual _) q)
        exact ((Category.comp_id _).trans (hcomp.trans
          ((_ ≫= rightAdjointMate_leftDualRightDualIso_inv_app X).trans
            ((rightDualLeftDualIso C).hom.naturality q)))).symm
      · rw [parityDualRightDualIso_one, Iso.symm_hom]
        let q := (pivotalLeftPowAuxIso X k 0 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))).hom
        have hcomp : @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
            (RightRigidCategory.rightDual _) (pivotalAtomIsoAux (.negSucc (k + 1)) X 1 h).inv =
            (rightDualLeftDualFunctor C).map q ≫
              @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
                (RightRigidCategory.rightDual _) (leftDualIsoRightDual X).inv :=
          @comp_rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual _)
            (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _)
            (leftDualIsoRightDual X).inv
            (@leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
              (LeftRigidCategory.leftDual _) q)
        exact (((hcomp =≫ _).trans ((Category.assoc _ _ _).trans
          ((_ ≫= rightAdjointMate_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv X).trans
            ((rightDualLeftDualIso C).hom.naturality q))))).symm

private theorem eqToHom_comp_pivotalAtomIsoAux_ofNat (X : C) (m : ℤ) (k : ℕ) (δ : ZMod 2)
    (hm : m = Int.ofNat k) (h' : (m : ZMod 2) = δ) :
    eqToHom (congrArg (iteratedDual · X) hm.symm) ≫ (pivotalAtomIsoAux m X δ h').hom =
      (pivotalRightPowAuxIso X k δ (by simpa [hm] using h')).hom := by
  subst hm
  exact Category.id_comp _

private theorem pivotalAtomIsoAux_leftDual (n : ℤ) (X : C) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
    (h' : ((n - 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualLeftDualIso n X).hom ≫ (pivotalAtomIsoAux (n - 1) X (ε + 1) h').hom =
      (leftDualIsoRightDual (iteratedDual n X)).hom ≫
        @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
          (RightRigidCategory.rightDual _) (pivotalAtomIsoAux n X ε h).inv ≫
        (parityDualRightDualIso ε X).hom := by
  have hmate : ∀ {A B : C} (g : B ⟶ A),
      (leftDualIsoRightDual A).hom ≫ gᘁ =
        @leftAdjointMate C _ _ B A (LeftRigidCategory.leftDual B)
          (LeftRigidCategory.leftDual A) g ≫ (leftDualIsoRightDual B).hom :=
    fun g ↦ (leftAdjointMate_comp_leftDualIsoRightDual_hom g).symm
  cases n with
  | negSucc k =>
    refine ((congrArg Iso.hom (iteratedDualLeftDualIso_negSucc k X) =≫ _).trans
      (Category.id_comp _)).trans ?_
    rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
    · exact ((_ ≫= ((_ ≫= congrArg Iso.hom (parityDualRightDualIso_zero X)).trans
        (Category.comp_id _))).trans (hmate (pivotalAtomIsoAux _ X 0 h).inv)).symm
    · have hr1 : (parityDualRightDualIso 1 X).hom = (pivotalIsoApp X).inv :=
        congrArg Iso.hom (parityDualRightDualIso_one X)
      exact ((_ ≫= (leftDualIsoRightDual_rightDual_hom_comp_pivotalIsoApp_inv X).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (((hmate (pivotalAtomIsoAux _ X 1 h).inv).symm =≫ _).trans
            ((Category.assoc _ _ _).trans (_ ≫= (_ ≫= hr1.symm))))) )
  | ofNat k =>
    cases k with
    | zero =>
      refine ((congrArg Iso.hom (iteratedDualLeftDualIso_zero X) =≫ _).trans
        (Category.id_comp _)).trans ?_
      rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
      · exact ((_ ≫= ((rightAdjointMate_id (X := X) =≫ _).trans
          ((Category.id_comp _).trans (congrArg Iso.hom (parityDualRightDualIso_zero X))))).trans
            (Category.comp_id _)).symm
      · exact absurd (congrArg Fin.val h) (by decide)
    | succ k =>
      have hlhs : (iteratedDualLeftDualIso (.ofNat (k + 1)) X).hom =
          (leftDualRightDualIso C).hom.app (iteratedRightDual k X) ≫
            eqToHom (congrArg (iteratedDual · X) (add_sub_cancel_right (k : ℤ) 1).symm) :=
        (congrArg Iso.hom (iteratedDualLeftDualIso_natCast_add_one k X)).trans
          ((leftDualRightDualIso_hom_app (iteratedRightDual k X)).symm =≫ _)
      refine ((hlhs =≫ _).trans ((Category.assoc _ _ _).trans
        (_ ≫= eqToHom_comp_pivotalAtomIsoAux_ofNat X _ k (ε + 1)
          (add_sub_cancel_right (k : ℤ) 1) h'))).trans ?_
      rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
      · let p := (pivotalRightPowAuxIso X k 1 (zmod2_of_succ (Fin.ext (congrArg Fin.val h)))).hom
        let g := (pivotalAtomIsoAux (.ofNat (k + 1)) X 0 h).inv
        have h2 : @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
            (LeftRigidCategory.leftDual _) g =
            (leftDualRightDualFunctor C).map p ≫
              @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
                (LeftRigidCategory.leftDual _) (pivotalIsoApp X).hom :=
          @comp_leftAdjointMate C _ _ _ _ _ (LeftRigidCategory.leftDual _)
            (LeftRigidCategory.leftDual _) (LeftRigidCategory.leftDual _)
            (pivotalIsoApp X).hom (pᘁ)
        have h3 : @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
            (LeftRigidCategory.leftDual _) (pivotalIsoApp X).hom ≫
            (leftDualIsoRightDual X).hom = (leftDualRightDualIso C).hom.app Xᘁ :=
          (hmate (pivotalIsoApp X).hom).symm.trans
            ((_ ≫= (pivotalIsoApp_rightDual_inv X).symm).trans
              (leftDualIsoRightDual_rightDual_hom_comp_pivotalIsoApp_inv Xᘁ))
        exact (((_ ≫= ((_ ≫= congrArg Iso.hom (parityDualRightDualIso_zero X)).trans
          (Category.comp_id _))).trans (hmate g)).trans ((h2 =≫ _).trans
          ((Category.assoc _ _ _).trans
            ((_ ≫= h3).trans ((leftDualRightDualIso C).hom.naturality p))))).symm
      · let p := (pivotalRightPowAuxIso X k 0 (zmod2_of_succ (Fin.ext (congrArg Fin.val h)))).hom
        let g := (pivotalAtomIsoAux (.ofNat (k + 1)) X 1 h).inv
        have hr1 : (parityDualRightDualIso 1 X).hom = (pivotalIsoApp X).inv :=
          congrArg Iso.hom (parityDualRightDualIso_one X)
        exact ((_ ≫= (_ ≫= hr1)).trans ((Category.assoc _ _ _).symm.trans ((hmate g =≫ _).trans
          ((Category.assoc _ _ _).trans
            ((_ ≫= leftDualIsoRightDual_rightDual_hom_comp_pivotalIsoApp_inv X).trans
              ((leftDualRightDualIso C).hom.naturality p)))))).symm

private theorem pivotalAtomIso_hom_eq_aux {X : C} {m : ℤ} {w : ZMod 2} (hw : (m : ZMod 2) = w) :
    (pivotalAtomIso m X).hom =
      (pivotalAtomIsoAux m X w hw).hom ≫ eqToHom (congrArg (parityDual · X) hw.symm) := by
  subst hw
  exact (Category.comp_id _).symm

/-- **Right-dual step coherence of `pivotalAtomIso`**: advancing the integer dual level from `n`
to `n + 1` via `iteratedDualRightDualIso` and reducing modulo two agrees with taking the right
adjoint mate of `(pivotalAtomIso n X).inv` followed by `parityDualRightDualIso`. -/
@[reassoc]
theorem iteratedDualRightDualIso_hom_comp_pivotalAtomIso_hom (n : ℤ) (X : C) :
    (iteratedDualRightDualIso n X).hom ≫ (pivotalAtomIso (n + 1) X).hom =
      ((pivotalAtomIso n X).inv)ᘁ ≫ (parityDualRightDualIso (n : ZMod 2) X).hom ≫
        eqToHom (congrArg (parityDual · X) (by simp)) := by
  rw [pivotalAtomIso_hom_eq_aux (by simp : ((n + 1 : ℤ) : ZMod 2) = (n : ZMod 2) + 1),
    reassoc_of% (pivotalAtomIsoAux_rightDual n X (n : ZMod 2) rfl _)]
  rfl

/-- **Left-dual step coherence of `pivotalAtomIso`**: lowering the integer dual level from `n` to
`n - 1` via `iteratedDualLeftDualIso` and reducing modulo two agrees with identifying left and
right duals via `leftDualIsoRightDual` followed by `parityDualRightDualIso`. -/
@[reassoc]
theorem iteratedDualLeftDualIso_hom_comp_pivotalAtomIso_hom (n : ℤ) (X : C) :
    (iteratedDualLeftDualIso n X).hom ≫ (pivotalAtomIso (n - 1) X).hom =
      (leftDualIsoRightDual (iteratedDual n X)).hom ≫ ((pivotalAtomIso n X).inv)ᘁ ≫
        (parityDualRightDualIso (n : ZMod 2) X).hom ≫
        eqToHom (congrArg (parityDual · X) (by simp)) := by
  rw [pivotalAtomIso_hom_eq_aux (by simp : ((n - 1 : ℤ) : ZMod 2) = (n : ZMod 2) + 1),
    reassoc_of% (pivotalAtomIsoAux_leftDual n X (n : ZMod 2) rfl _)]
  rfl

/-! ### Word-level pivotal comparison and coherence -/

namespace WindingWord

variable {α : Type w}

/-- Pivotal comparison isomorphism `WindingWord.eval f L ≅ ParityWord.eval f (toParity L)`,
applying `pivotalAtomIso` port-by-port along the right-associated word evaluation. -/
noncomputable def pivotalComparisonIso (f : α → C) :
    (L : WindingWord α) → eval f L ≅ ParityWord.eval f (toParity L)
  | [] => Iso.refl (𝟙_ C)
  | p :: L => pivotalAtomIso p.2 (f p.1) ⊗ᵢ pivotalComparisonIso f L

@[simp] theorem pivotalComparisonIso_nil (f : α → C) :
    pivotalComparisonIso f [] = Iso.refl (𝟙_ C) := (rfl)

@[simp] theorem pivotalComparisonIso_cons (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    pivotalComparisonIso f (p :: L) =
      pivotalAtomIso p.2 (f p.1) ⊗ᵢ pivotalComparisonIso f L := (rfl)

/-- **Concatenation coherence of `pivotalComparisonIso`**: evaluating a concatenated winding word
and reducing modulo two commutes with `evalAppendIso` and `ParityWord.evalAppendIso`. -/
@[reassoc]
theorem pivotalComparisonIso_append_hom (f : α → C) :
    (L M : WindingWord α) →
      (pivotalComparisonIso f (L ++ M)).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (toParity_append L M)) ≫
          (ParityWord.evalAppendIso f (toParity L) (toParity M)).hom =
        (evalAppendIso f L M).hom ≫
          ((pivotalComparisonIso f L).hom ⊗ₘ (pivotalComparisonIso f M).hom)
  | [], M => by
    have hEq : eqToHom (congrArg (ParityWord.eval f) (toParity_append ([] : WindingWord α) M)) =
        𝟙 (ParityWord.eval f (toParity M)) := eqToHom_refl _ _
    have hP : (ParityWord.evalAppendIso f (toParity []) (toParity M)).hom =
        (λ_ (ParityWord.eval f (toParity M))).inv :=
      congrArg Iso.hom (ParityWord.evalAppendIso_nil f (toParity M))
    have hW : (evalAppendIso f [] M).hom = (λ_ (eval f M)).inv :=
      congrArg Iso.hom (evalAppendIso_nil f M)
    have hN : (pivotalComparisonIso f []).hom = 𝟙 (𝟙_ C) := rfl
    exact (_ ≫= ((hEq =≫ _).trans ((Category.id_comp _).trans hP))).trans
      ((leftUnitor_inv_naturality (pivotalComparisonIso f M).hom).trans
        ((hW.symm =≫ _).trans
          (_ ≫= (id_tensorHom (𝟙_ C) (pivotalComparisonIso f M).hom).symm.trans
            (congrArg (· ⊗ₘ _) hN.symm))))
  | p :: L, M => by
    have ih := pivotalComparisonIso_append_hom f L M
    have hEq : eqToHom (congrArg (ParityWord.eval f) (toParity_append (p :: L) M)) =
        parityDual (p.2 : ZMod 2) (f p.1) ◁
          eqToHom (congrArg (ParityWord.eval f) (toParity_append L M)) :=
      (MonoidalCategory.whiskerLeft_eqToHom (parityDual (p.2 : ZMod 2) (f p.1))
        (congrArg (ParityWord.eval f) (toParity_append L M))).symm
    have hP : (ParityWord.evalAppendIso f (toParity (p :: L)) (toParity M)).hom =
        (parityDual (p.2 : ZMod 2) (f p.1) ◁
          (ParityWord.evalAppendIso f (toParity L) (toParity M)).hom) ≫ (α_ _ _ _).inv :=
      congrArg Iso.hom (ParityWord.evalAppendIso_cons f (p.1, (p.2 : ZMod 2))
        (toParity L) (toParity M))
    have hW : (evalAppendIso f (p :: L) M).hom =
        (iteratedDual p.2 (f p.1) ◁ (evalAppendIso f L M).hom) ≫ (α_ _ _ _).inv :=
      congrArg Iso.hom (evalAppendIso_cons f p L M)
    have hStep : ∀ {A₁ A₂ B₁ B₂ B₃ C₁ C₂ C₁' C₂' : C} (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
        (e : B₂ ⟶ B₃) (p₁ : B₃ ⟶ C₁' ⊗ C₂') (q₁ : B₁ ⟶ C₁ ⊗ C₂) (c₁ : C₁ ⟶ C₁') (c₂ : C₂ ⟶ C₂')
        (_ : b ≫ e ≫ p₁ = q₁ ≫ (c₁ ⊗ₘ c₂)),
        (a ⊗ₘ b) ≫ (A₂ ◁ e) ≫ (A₂ ◁ p₁) ≫ (α_ A₂ C₁' C₂').inv =
          ((A₁ ◁ q₁) ≫ (α_ A₁ C₁ C₂).inv) ≫ ((a ⊗ₘ c₁) ⊗ₘ c₂) := by
      intro A₁ A₂ B₁ B₂ B₃ C₁ C₂ C₁' C₂' a b e p₁ q₁ c₁ c₂ hih
      rw [tensorHom_def'_assoc, ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc b e p₁,
        hih, MonoidalCategory.whiskerLeft_comp_assoc, ← tensorHom_def'_assoc,
        associator_inv_naturality, Category.assoc]
    exact (_ ≫= ((hEq =≫ _).trans (_ ≫= hP))).trans
      ((hStep (pivotalAtomIso p.2 (f p.1)).hom (pivotalComparisonIso f (L ++ M)).hom _ _ _ _ _
        ih).trans (hW.symm =≫ _))

/-- Inverse-append form of `pivotalComparisonIso_append_hom`. -/
@[reassoc]
theorem evalAppendIso_inv_comp_pivotalComparisonIso_hom (f : α → C) (L M : WindingWord α) :
    (evalAppendIso f L M).inv ≫ (pivotalComparisonIso f (L ++ M)).hom =
      ((pivotalComparisonIso f L).hom ⊗ₘ (pivotalComparisonIso f M).hom) ≫
        (ParityWord.evalAppendIso f (toParity L) (toParity M)).inv ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_append L M).symm) := by
  rw [Iso.inv_comp_eq, ← pivotalComparisonIso_append_hom_assoc]
  simp

private theorem eqToHom_comp_pivotalComparisonIso_hom (f : α → C) {W₁ W₂ : WindingWord α}
    (hw : W₁ = W₂) :
    eqToHom (congrArg (eval f) hw) ≫ (pivotalComparisonIso f W₂).hom =
      (pivotalComparisonIso f W₁).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (congrArg toParity hw)) := by
  subst hw
  simp

omit [PivotalCategory C] in
private theorem tensor_eqToHom_comp_evalAppendIso_inv (f : α → C)
    {P₁ P₂ Q₁ Q₂ : ParityWord α} (hP : P₁ = P₂) (hQ : Q₁ = Q₂) :
    (eqToHom (congrArg (ParityWord.eval f) hP) ⊗ₘ
        eqToHom (congrArg (ParityWord.eval f) hQ)) ≫
      (ParityWord.evalAppendIso f P₂ Q₂).inv =
    (ParityWord.evalAppendIso f P₁ Q₁).inv ≫
      eqToHom (congrArg (ParityWord.eval f) (congrArg₂ (· ++ ·) hP hQ)) := by
  subst hP hQ
  simp

private theorem singleton_toParity_eq (a : α) {m : ℤ} {δ : ZMod 2} (hm : (m : ZMod 2) = δ) :
    ([(a, δ)] : ParityWord α) = toParity [(a, m)] := by
  simp [hm]

omit [PivotalCategory C] in
private theorem eqToHom_whiskerRight_unit (f : α → C) (a : α) {m : ℤ} {δ : ZMod 2}
    (hm : (m : ZMod 2) = δ) :
    eqToHom (congrArg (parityDual · (f a)) hm.symm) ≫ (ρ_ (parityDual (m : ZMod 2) (f a))).inv =
      (ρ_ (parityDual δ (f a))).inv ≫
        eqToHom (congrArg (ParityWord.eval f) (singleton_toParity_eq a hm)) := by
  subst hm
  have h0 : eqToHom (congrArg (parityDual · (f a)) (rfl : (m : ZMod 2) = (m : ZMod 2)).symm) =
      𝟙 _ := eqToHom_refl _ _
  have h1 : eqToHom (congrArg (ParityWord.eval f)
      (singleton_toParity_eq a (rfl : (m : ZMod 2) = (m : ZMod 2)))) =
      𝟙 _ := eqToHom_refl _ _
  exact ((h0 =≫ _).trans (Category.id_comp _)).trans
    ((_ ≫= h1).trans (Category.comp_id _)).symm

/-- Shared inductive step for right- and left-dual word coherence on `p :: L`. -/
private theorem pivotalComparisonIso_dualCons_tail (f : α → C) (p : α × ℤ) (L : WindingWord α)
    (W : WindingWord α) (m : ℤ) (hW : toParity W = ParityWord.dual (toParity L))
    (hm : (m : ZMod 2) = (p.2 : ZMod 2) + 1) (hwCons : toParity (W ++ [(p.1, m)]) =
      ParityWord.dual (toParity (p :: L)))
    (u : (eval f L)ᘁ ⟶ eval f W) (v : (iteratedDual p.2 (f p.1))ᘁ ⟶ iteratedDual m (f p.1))
    (hu : u ≫ (pivotalComparisonIso f W).hom =
      ((pivotalComparisonIso f L).inv)ᘁ ≫ (ParityWord.evalDualIso f (toParity L)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) hW.symm))
    (hv : v ≫ (pivotalAtomIso m (f p.1)).hom =
      ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ ≫ (parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫
        eqToHom (congrArg (parityDual · (f p.1)) hm.symm)) :
    (u ⊗ₘ (v ≫ (ρ_ _).inv)) ≫
        (evalAppendIso f W [(p.1, m)]).inv ≫
        (pivotalComparisonIso f (W ++ [(p.1, m)])).hom =
      (((pivotalComparisonIso f L).inv)ᘁ ⊗ₘ ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ) ≫
        ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ
          ((parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv)) ≫
        (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
          [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
        eqToHom (congrArg (ParityWord.eval f)
          ((ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm.trans hwCons.symm)) := by
  have hvUnit : (v ≫ (ρ_ _).inv) ≫ (pivotalComparisonIso f [(p.1, m)]).hom =
      ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ ≫
        ((parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv) ≫
        eqToHom (congrArg (ParityWord.eval f) (singleton_toParity_eq p.1 hm)) :=
    (Category.assoc v (ρ_ _).inv _).trans
      ((_ ≫= ((_ ≫= tensorHom_id (pivotalAtomIso m (f p.1)).hom (𝟙_ C)).trans
        (rightUnitor_inv_naturality (pivotalAtomIso m (f p.1)).hom).symm)).trans
        ((Category.assoc _ _ _).symm.trans ((hv =≫ _).trans
          ((Category.assoc _ _ _).trans (_ ≫= ((Category.assoc _ _ _).trans
            ((_ ≫= eqToHom_whiskerRight_unit f p.1 hm).trans
              (Category.assoc _ _ _).symm)))))))
  have hSplit : ∀ {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C} (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
      (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃) (b₃ : B₃ ⟶ B₄),
      (a₁ ≫ a₂ ≫ a₃) ⊗ₘ (b₁ ≫ b₂ ≫ b₃) = (a₁ ⊗ₘ b₁) ≫ (a₂ ⊗ₘ b₂) ≫ (a₃ ⊗ₘ b₃) := by
    intros; simp [tensorHom_comp_tensorHom]
  refine (_ ≫= evalAppendIso_inv_comp_pivotalComparisonIso_hom f W [(p.1, m)]).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((tensorHom_comp_tensorHom _ _ _ _).trans (congrArg₂ tensorHom hu hvUnit) =≫ _).trans ?_
  refine (hSplit _ _ _ _ _ _ =≫ _).trans ?_
  refine ((Category.assoc _ _ _).trans (_ ≫= (Category.assoc _ _ _))).trans ?_
  refine (_ ≫= (_ ≫= ((Category.assoc _ _ _).symm.trans ?_)))
  exact ((tensor_eqToHom_comp_evalAppendIso_inv f hW.symm
    (singleton_toParity_eq p.1 hm)) =≫ _).trans
      ((Category.assoc _ _ _).trans (_ ≫= eqToHom_trans _ _))

omit [MonoidalCategory C] [RigidCategory C] [PivotalCategory C] in
private theorem reassoc_dualCons {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ : C}
    {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄} {d : X₄ ⟶ X₅} {k : X₅ ⟶ X₁₀}
    {k' : X₄ ⟶ X₆} {e₁ : X₆ ⟶ X₁₀} {m₁ : X₂ ⟶ X₇} {m₂ : X₇ ⟶ X₈} {m₃ : X₈ ⟶ X₉}
    {e₂ : X₉ ⟶ X₆} (hdk : d ≫ k = k' ≫ e₁)
    (htail : b ≫ c ≫ k' = m₁ ≫ m₂ ≫ m₃ ≫ e₂) :
    (a ≫ b ≫ c ≫ d) ≫ k = (a ≫ m₁) ≫ m₂ ≫ m₃ ≫ (e₂ ≫ e₁) := by
  simp only [Category.assoc] at hdk htail ⊢
  rw [hdk, reassoc_of% htail]

omit [MonoidalCategory C] [RigidCategory C] [PivotalCategory C] in
private theorem finish_dualCons {X₁ X₇ X₈ X₉ X₁₀ Y₁ Y₂ : C}
    {am₁ : X₁ ⟶ X₇} {front : X₁ ⟶ Y₁} {a' : Y₁ ⟶ X₇}
    {m₂ : X₇ ⟶ X₈} {m₃ : X₈ ⟶ X₉} {e₂₁ : X₉ ⟶ X₁₀}
    {e₃ : X₉ ⟶ Y₂} {e₄ : Y₂ ⟶ X₁₀} {rhsHom : Y₁ ⟶ Y₂}
    (hfront : am₁ = front ≫ a') (hrhs : rhsHom = a' ≫ m₂ ≫ m₃ ≫ e₃)
    (heq : e₂₁ = e₃ ≫ e₄) :
    am₁ ≫ m₂ ≫ m₃ ≫ e₂₁ = front ≫ rhsHom ≫ e₄ := by
  subst hfront hrhs heq
  simp only [Category.assoc]

/-- **Right-dual coherence of `pivotalComparisonIso`**: taking the chosen right dual of an
evaluated winding word commutes with `pivotalComparisonIso` and `ParityWord.evalDualIso`. -/
@[reassoc]
theorem pivotalComparisonIso_rightDual_hom (f : α → C) :
    (L : WindingWord α) →
      (evalRightDualIso f L).hom ≫ (pivotalComparisonIso f (rightDual L)).hom =
        ((pivotalComparisonIso f L).inv)ᘁ ≫ (ParityWord.evalDualIso f (toParity L)).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (toParity_rightDual L).symm)
  | [] => by
    have hlhs : (evalRightDualIso f []).hom =
        (rightDualUnitIso C).hom ≫ eqToHom (congrArg (eval f) rightDual_nil.symm) :=
      congrArg Iso.hom (evalRightDualIso_nil f)
    have hrhs : (ParityWord.evalDualIso f (toParity [])).hom =
        (rightDualUnitIso C).hom ≫
          eqToHom (congrArg (ParityWord.eval f) ParityWord.dual_nil.symm) :=
      congrArg Iso.hom (ParityWord.evalDualIso_nil f)
    have hmate : ((pivotalComparisonIso f ([] : WindingWord α)).inv)ᘁ = 𝟙 _ :=
      @rightAdjointMate_id C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C))
    have hL : (evalRightDualIso f []).hom ≫ (pivotalComparisonIso f (rightDual [])).hom =
        (rightDualUnitIso C).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (congrArg toParity rightDual_nil.symm)) :=
      (hlhs =≫ _).trans ((Category.assoc _ _ _).trans
        (_ ≫= ((eqToHom_comp_pivotalComparisonIso_hom f rightDual_nil.symm).trans
          (Category.id_comp _))))
    have hR : ((pivotalComparisonIso f []).inv)ᘁ ≫ (ParityWord.evalDualIso f (toParity [])).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_rightDual ([] : WindingWord α)).symm) =
        (rightDualUnitIso C).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (congrArg toParity rightDual_nil.symm)) :=
      (hmate =≫ _).trans ((Category.id_comp _).trans
        ((hrhs =≫ _).trans ((Category.assoc _ _ _).trans (_ ≫= eqToHom_trans _ _))))
    exact hL.trans hR.symm
  | p :: L => by
    have ih := pivotalComparisonIso_rightDual_hom f L
    have hlhs : (evalRightDualIso f (p :: L)).hom =
        (rightDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
          ((evalRightDualIso f L).hom ⊗ₘ
            ((iteratedDualRightDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv)) ≫
          (evalAppendIso f (rightDual L) [(p.1, p.2 + 1)]).inv ≫
          eqToHom (congrArg (eval f) (rightDual_cons p L).symm) :=
      congrArg Iso.hom (evalRightDualIso_cons f p L)
    have hrhs : (ParityWord.evalDualIso f (toParity (p :: L))).hom =
        (rightDualTensorIso (parityDual (p.2 : ZMod 2) (f p.1))
          (ParityWord.eval f (toParity L))).hom ≫
          ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ
            ((parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv)) ≫
          (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
            [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
          eqToHom (congrArg (ParityWord.eval f)
            (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm) :=
      congrArg Iso.hom (ParityWord.evalDualIso_cons f (p.1, (p.2 : ZMod 2)) (toParity L))
    exact (hlhs =≫ _).trans ((reassoc_dualCons
      (eqToHom_comp_pivotalComparisonIso_hom f (rightDual_cons p L).symm)
      (pivotalComparisonIso_dualCons_tail f p L (rightDual L) (p.2 + 1) (toParity_rightDual L)
        (by simp) (by simp) _ _ ih
        (iteratedDualRightDualIso_hom_comp_pivotalAtomIso_hom p.2 (f p.1)))).trans
      (finish_dualCons
        (rightDualTensorIso_hom_naturality (pivotalAtomIso p.2 (f p.1)).inv
          (pivotalComparisonIso f L).inv).symm hrhs
        ((eqToHom_trans _ _).trans (eqToHom_trans
          (congrArg (ParityWord.eval f)
            (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm)
          (congrArg (ParityWord.eval f) (toParity_rightDual (p :: L)).symm)).symm)))

/-- **Left-dual coherence of `pivotalComparisonIso`**: taking the chosen left dual of an evaluated
winding word agrees with identifying left and right duals via `leftDualIsoRightDual` and applying
`ParityWord.evalDualIso`. -/
@[reassoc]
theorem pivotalComparisonIso_leftDual_hom (f : α → C) :
    (L : WindingWord α) →
      (evalLeftDualIso f L).hom ≫ (pivotalComparisonIso f (leftDual L)).hom =
        (leftDualIsoRightDual (eval f L)).hom ≫ ((pivotalComparisonIso f L).inv)ᘁ ≫
          (ParityWord.evalDualIso f (toParity L)).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (toParity_leftDual L).symm)
  | [] => by
    have hlhs : (evalLeftDualIso f []).hom =
        (leftDualUnitIso C).hom ≫ eqToHom (congrArg (eval f) leftDual_nil.symm) :=
      congrArg Iso.hom (evalLeftDualIso_nil f)
    have hrhs : (ParityWord.evalDualIso f (toParity [])).hom =
        (rightDualUnitIso C).hom ≫
          eqToHom (congrArg (ParityWord.eval f) ParityWord.dual_nil.symm) :=
      congrArg Iso.hom (ParityWord.evalDualIso_nil f)
    have hmate : ((pivotalComparisonIso f ([] : WindingWord α)).inv)ᘁ = 𝟙 _ :=
      @rightAdjointMate_id C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C))
    have hunit : (leftDualUnitIso C).hom =
        (leftDualIsoRightDual (𝟙_ C)).hom ≫ (rightDualUnitIso C).hom := by
      rw [← Iso.inv_comp_eq, leftDualUnitIso_hom, rightDualUnitIso_hom]
      exact leftDualIsoRightDual_unit_inv
    have hL : (evalLeftDualIso f []).hom ≫ (pivotalComparisonIso f (leftDual [])).hom =
        (leftDualUnitIso C).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (congrArg toParity leftDual_nil.symm)) :=
      (hlhs =≫ _).trans ((Category.assoc _ _ _).trans
        (_ ≫= ((eqToHom_comp_pivotalComparisonIso_hom f leftDual_nil.symm).trans
          (Category.id_comp _))))
    have hR : (leftDualIsoRightDual (eval f ([] : WindingWord α))).hom ≫
        ((pivotalComparisonIso f []).inv)ᘁ ≫
        (ParityWord.evalDualIso f (toParity [])).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_leftDual ([] : WindingWord α)).symm) =
        (leftDualUnitIso C).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (congrArg toParity leftDual_nil.symm)) :=
      (_ ≫= ((hmate =≫ _).trans ((Category.id_comp _).trans
        ((hrhs =≫ _).trans ((Category.assoc _ _ _).trans (_ ≫= eqToHom_trans _ _)))))).trans
        ((Category.assoc _ _ _).symm.trans (hunit.symm =≫ _))
    exact hL.trans hR.symm
  | p :: L => by
    have ih := pivotalComparisonIso_leftDual_hom f L
    have htensor : (leftDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
        ((leftDualIsoRightDual (eval f L)).hom ⊗ₘ
          (leftDualIsoRightDual (iteratedDual p.2 (f p.1))).hom) =
        (leftDualIsoRightDual (iteratedDual p.2 (f p.1) ⊗ eval f L)).hom ≫
          (rightDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom := by
      rw [← cancel_epi (leftDualIsoRightDual (iteratedDual p.2 (f p.1) ⊗ eval f L)).inv,
        Iso.inv_hom_id_assoc, reassoc_of% (leftDualIsoRightDual_tensor_inv _ _),
        tensorHom_comp_tensorHom]
      simp
    have hlhs : (evalLeftDualIso f (p :: L)).hom =
        (leftDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
          ((evalLeftDualIso f L).hom ⊗ₘ
            ((iteratedDualLeftDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv)) ≫
          (evalAppendIso f (leftDual L) [(p.1, p.2 - 1)]).inv ≫
          eqToHom (congrArg (eval f) (leftDual_cons p L).symm) :=
      congrArg Iso.hom (evalLeftDualIso_cons f p L)
    have hrhs : (ParityWord.evalDualIso f (toParity (p :: L))).hom =
        (rightDualTensorIso (parityDual (p.2 : ZMod 2) (f p.1))
          (ParityWord.eval f (toParity L))).hom ≫
          ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ
            ((parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv)) ≫
          (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
            [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
          eqToHom (congrArg (ParityWord.eval f)
            (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm) :=
      congrArg Iso.hom (ParityWord.evalDualIso_cons f (p.1, (p.2 : ZMod 2)) (toParity L))
    have hSplitL : ((evalLeftDualIso f L).hom ⊗ₘ
          ((iteratedDualLeftDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv)) =
        ((leftDualIsoRightDual (eval f L)).hom ⊗ₘ
          (leftDualIsoRightDual (iteratedDual p.2 (f p.1))).hom) ≫
        (((leftDualIsoRightDual (eval f L)).inv ≫ (evalLeftDualIso f L).hom) ⊗ₘ
          (((leftDualIsoRightDual (iteratedDual p.2 (f p.1))).inv ≫
            (iteratedDualLeftDualIso p.2 (f p.1)).hom) ≫ (ρ_ _).inv)) := by
      rw [tensorHom_comp_tensorHom]
      simp
    have hfront : (leftDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
        (((leftDualIsoRightDual (eval f L)).hom ⊗ₘ
          (leftDualIsoRightDual (iteratedDual p.2 (f p.1))).hom) ≫
          (((pivotalComparisonIso f L).inv)ᘁ ⊗ₘ ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ)) =
        ((leftDualIsoRightDual (eval f (p :: L))).hom ≫
          ((pivotalComparisonIso f (p :: L)).inv)ᘁ) ≫
          (rightDualTensorIso (parityDual (p.2 : ZMod 2) (f p.1))
            (ParityWord.eval f (toParity L))).hom :=
      (Category.assoc _ _ _).symm.trans
        ((htensor =≫ _).trans ((Category.assoc _ _ _).trans
          ((_ ≫= (rightDualTensorIso_hom_naturality (pivotalAtomIso p.2 (f p.1)).inv
            (pivotalComparisonIso f L).inv).symm).trans (Category.assoc _ _ _).symm)))
    have htail := (hSplitL =≫ _).trans ((Category.assoc _ _ _).trans
      (_ ≫= pivotalComparisonIso_dualCons_tail f p L (leftDual L) (p.2 - 1)
        (toParity_leftDual L) (by simp) (by simp) _ _
        (by rw [Category.assoc, ih, Iso.inv_hom_id_assoc])
        (by rw [Category.assoc, iteratedDualLeftDualIso_hom_comp_pivotalAtomIso_hom,
          Iso.inv_hom_id_assoc])))
    exact (hlhs =≫ _).trans ((reassoc_dualCons
      (eqToHom_comp_pivotalComparisonIso_hom f (leftDual_cons p L).symm)
      (htail.trans (Category.assoc _ _ _).symm)).trans
      ((finish_dualCons hfront hrhs
        ((eqToHom_trans _ _).trans (eqToHom_trans
          (congrArg (ParityWord.eval f)
            (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm)
          (congrArg (ParityWord.eval f)
            (toParity_leftDual (p :: L)).symm)).symm)).trans (Category.assoc _ _ _)))

/-! ### Coupon transport and half-turn single mates -/

omit [MonoidalCategory C] [RigidCategory C] [PivotalCategory C] in
private theorem inv_comp_inv_of_hom_comp_hom {A B D E E' : C} (e₁ : A ≅ B) (e₂ : B ≅ E)
    (u : A ⟶ D) (v : D ⟶ A) (huv : u ≫ v = 𝟙 A) (e₄ : D ≅ E') (h : E' = E)
    (heq : e₁.hom ≫ e₂.hom = u ≫ e₄.hom ≫ eqToHom h) :
    e₂.inv ≫ e₁.inv = eqToHom h.symm ≫ e₄.inv ≫ v := by
  rw [← cancel_epi (e₁.hom ≫ e₂.hom), Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, heq]
  simp [huv]

/-- Transport a coupon morphism `g : eval f src ⟶ eval f tgt` from integer-labelled winding
boundaries to its parity-reduced boundary by conjugating with `pivotalComparisonIso`. -/
noncomputable def transportCoupon (f : α → C) {src tgt : WindingWord α}
    (g : eval f src ⟶ eval f tgt) :
    ParityWord.eval f (toParity src) ⟶ ParityWord.eval f (toParity tgt) :=
  (pivotalComparisonIso f src).inv ≫ g ≫ (pivotalComparisonIso f tgt).hom

theorem transportCoupon_def (f : α → C) {src tgt : WindingWord α} (g : eval f src ⟶ eval f tgt) :
    transportCoupon f g =
      (pivotalComparisonIso f src).inv ≫ g ≫ (pivotalComparisonIso f tgt).hom := (rfl)

/-- Intertwining characterization of `transportCoupon`. -/
@[reassoc]
theorem pivotalComparisonIso_hom_comp_transportCoupon (f : α → C) {src tgt : WindingWord α}
    (g : eval f src ⟶ eval f tgt) :
    (pivotalComparisonIso f src).hom ≫ transportCoupon f g =
      g ≫ (pivotalComparisonIso f tgt).hom := by
  simp [transportCoupon]

@[simp] theorem transportCoupon_id (f : α → C) (L : WindingWord α) :
    transportCoupon f (𝟙 (eval f L)) = 𝟙 (ParityWord.eval f (toParity L)) := by
  simp [transportCoupon]

@[simp] theorem transportCoupon_comp (f : α → C) {L₁ L₂ L₃ : WindingWord α}
    (g₁ : eval f L₁ ⟶ eval f L₂) (g₂ : eval f L₂ ⟶ eval f L₃) :
    transportCoupon f (g₁ ≫ g₂) = transportCoupon f g₁ ≫ transportCoupon f g₂ := by
  simp [transportCoupon]

/-- Tensoring two coupons along concatenated boundaries commutes with `transportCoupon`. -/
theorem transportCoupon_append (f : α → C) {src₁ tgt₁ src₂ tgt₂ : WindingWord α}
    (g₁ : eval f src₁ ⟶ eval f tgt₁) (g₂ : eval f src₂ ⟶ eval f tgt₂) :
    transportCoupon f
        ((evalAppendIso f src₁ src₂).hom ≫ (g₁ ⊗ₘ g₂) ≫ (evalAppendIso f tgt₁ tgt₂).inv) =
      eqToHom (congrArg (ParityWord.eval f) (toParity_append src₁ src₂)) ≫
        (ParityWord.evalAppendIso f (toParity src₁) (toParity src₂)).hom ≫
        (transportCoupon f g₁ ⊗ₘ transportCoupon f g₂) ≫
        (ParityWord.evalAppendIso f (toParity tgt₁) (toParity tgt₂)).inv ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_append tgt₁ tgt₂).symm) := by
  have hsrc : (pivotalComparisonIso f (src₁ ++ src₂)).inv ≫ (evalAppendIso f src₁ src₂).hom =
      eqToHom (congrArg (ParityWord.eval f) (toParity_append src₁ src₂)) ≫
        (ParityWord.evalAppendIso f (toParity src₁) (toParity src₂)).hom ≫
        ((pivotalComparisonIso f src₁).inv ⊗ₘ (pivotalComparisonIso f src₂).inv) := by
    rw [Iso.inv_comp_eq, pivotalComparisonIso_append_hom_assoc, tensorHom_comp_tensorHom]
    simp
  dsimp only [transportCoupon]
  simp only [Category.assoc]
  rw [reassoc_of% hsrc, evalAppendIso_inv_comp_pivotalComparisonIso_hom,
    ← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc]

/-- **Half-turn rotation (right mate)**: rotating a coupon `g` via right duality on winding
boundaries transports to `(transportCoupon f g)ᘁ` conjugated by `ParityWord.evalDualIso`. -/
theorem transportCoupon_rightDual (f : α → C) {src tgt : WindingWord α}
    (g : eval f src ⟶ eval f tgt) :
    transportCoupon f ((evalRightDualIso f tgt).inv ≫ gᘁ ≫ (evalRightDualIso f src).hom) =
      eqToHom (congrArg (ParityWord.eval f) (toParity_rightDual tgt)) ≫
        (ParityWord.evalDualIso f (toParity tgt)).inv ≫ (transportCoupon f g)ᘁ ≫
        (ParityWord.evalDualIso f (toParity src)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_rightDual src).symm) := by
  have htgt := inv_comp_inv_of_hom_comp_hom (evalRightDualIso f tgt)
    (pivotalComparisonIso f (rightDual tgt)) (((pivotalComparisonIso f tgt).inv)ᘁ)
    (((pivotalComparisonIso f tgt).hom)ᘁ) (by simp [← comp_rightAdjointMate])
    (ParityWord.evalDualIso f (toParity tgt)) _ (pivotalComparisonIso_rightDual_hom f tgt)
  dsimp only [transportCoupon]
  simp only [Category.assoc]
  rw [reassoc_of% htgt, pivotalComparisonIso_rightDual_hom]
  simp only [comp_rightAdjointMate, Category.assoc]

/-- **Opposite half-turn rotation (left mate)**: rotating a coupon `g` via left duality on winding
boundaries also transports to `(transportCoupon f g)ᘁ` conjugated by `ParityWord.evalDualIso`. -/
theorem transportCoupon_leftDual (f : α → C) {src tgt : WindingWord α}
    (g : eval f src ⟶ eval f tgt) :
    transportCoupon f ((evalLeftDualIso f tgt).inv ≫ (ᘁg) ≫ (evalLeftDualIso f src).hom) =
      eqToHom (congrArg (ParityWord.eval f) (toParity_leftDual tgt)) ≫
        (ParityWord.evalDualIso f (toParity tgt)).inv ≫ (transportCoupon f g)ᘁ ≫
        (ParityWord.evalDualIso f (toParity src)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_leftDual src).symm) := by
  have htgt := inv_comp_inv_of_hom_comp_hom (evalLeftDualIso f tgt)
    (pivotalComparisonIso f (leftDual tgt))
    ((leftDualIsoRightDual (eval f tgt)).hom ≫ ((pivotalComparisonIso f tgt).inv)ᘁ)
    (((pivotalComparisonIso f tgt).hom)ᘁ ≫ (leftDualIsoRightDual (eval f tgt)).inv)
    (by simp [Category.assoc, ← comp_rightAdjointMate_assoc])
    (ParityWord.evalDualIso f (toParity tgt)) _
    (by simpa only [Category.assoc] using pivotalComparisonIso_leftDual_hom f tgt)
  have hmate : (leftDualIsoRightDual (eval f tgt)).inv ≫
      (ᘁg) ≫ (leftDualIsoRightDual (eval f src)).hom = gᘁ := by
    rw [leftAdjointMate_comp_leftDualIsoRightDual_hom, Iso.inv_hom_id_assoc]
  dsimp only [transportCoupon]
  simp only [Category.assoc] at htgt ⊢
  rw [reassoc_of% htgt, pivotalComparisonIso_leftDual_hom, reassoc_of% hmate]
  simp only [comp_rightAdjointMate, Category.assoc]

end WindingWord

namespace RigidObject

variable {α : Type w}

/-- Direct pivotal comparison `RigidObject.eval f X ≅ ParityWord.eval f X.normalizeParity` between
a formal rigid object and its modulo-two parity normalization. -/
noncomputable def normalizeParityIso (f : α → C) (X : RigidObject α) :
    eval f X ≅ ParityWord.eval f X.normalizeParity :=
  normalizeIso f X ≪≫ WindingWord.pivotalComparisonIso f X.normalize ≪≫
    eqToIso (congrArg (ParityWord.eval f) (normalizeParity_eq_toParity_normalize X).symm)

theorem normalizeParityIso_def (f : α → C) (X : RigidObject α) :
    normalizeParityIso f X =
      normalizeIso f X ≪≫ WindingWord.pivotalComparisonIso f X.normalize ≪≫
        eqToIso (congrArg (ParityWord.eval f)
          (normalizeParity_eq_toParity_normalize X).symm) := (rfl)

@[simp] theorem normalizeParityIso_hom (f : α → C) (X : RigidObject α) :
    (normalizeParityIso f X).hom =
      (normalizeIso f X).hom ≫ (WindingWord.pivotalComparisonIso f X.normalize).hom ≫
        eqToHom (congrArg (ParityWord.eval f)
          (normalizeParity_eq_toParity_normalize X).symm) := (rfl)

@[simp] theorem normalizeParityIso_inv (f : α → C) (X : RigidObject α) :
    (normalizeParityIso f X).inv =
      eqToHom (congrArg (ParityWord.eval f) (normalizeParity_eq_toParity_normalize X)) ≫
        (WindingWord.pivotalComparisonIso f X.normalize).inv ≫ (normalizeIso f X).inv := by
  simp [normalizeParityIso]

end RigidObject

end TauCeti
