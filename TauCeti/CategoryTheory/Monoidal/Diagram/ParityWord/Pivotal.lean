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
  boundary comparisons coherent with the empty word, concatenation, right and left duality, integer
  dual powers (`TauCeti.WindingWord.pivotalComparisonIso_dualPow_hom`), and multi-port substitution
  (`TauCeti.WindingWord.pivotalComparisonIso_subst_hom`);
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

universe v u w w'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Formal parity realizations in a rigid category -/

section RigidParityRealization

variable [RigidCategory C]

namespace RigidObject

variable {α : Type w}

/-- The formal parity atom `atParity a ε` evaluates strictly to `parityDual ε (f a)`. -/
@[simp] theorem eval_atParity (f : α → C) (a : α) (ε : ZMod 2) :
    eval f (atParity a ε) = parityDual ε (f a) := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
  · simp
  · simp; rfl

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

private noncomputable def pivotalRightPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((k : ZMod 2) = ε) →
      (iteratedRightDual k X ≅ parityDual ε X)
  | 0, ⟨0, _⟩, _ => Iso.refl X
  | 0, ⟨1, _⟩, h => False.elim ((by decide : ((0 : ℕ) : ZMod 2).val ≠ 1) (congrArg Fin.val h))
  | k + 1, ⟨0, _⟩, h =>
      @Iso.rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _)
        (pivotalRightPowAuxIso X k 1 (by
          have hk : ((k + 1 : ℕ) : ZMod 2) = 0 := Fin.ext (congrArg Fin.val h)
          rwa [Nat.cast_add, Nat.cast_one, CharTwo.add_eq_iff_eq_add, zero_add] at hk)).symm ≪≫
        (pivotalIsoApp X).symm
  | k + 1, ⟨1, _⟩, h =>
      @Iso.rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _)
        (pivotalRightPowAuxIso X k 0 (by
          have hk : ((k + 1 : ℕ) : ZMod 2) = 1 := Fin.ext (congrArg Fin.val h)
          rwa [Nat.cast_add, Nat.cast_one, CharTwo.add_eq_iff_eq_add,
            CharTwo.add_self_eq_zero] at hk)).symm

private noncomputable def pivotalLeftPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((Int.negSucc k : ZMod 2) = ε) →
      (iteratedLeftDual (k + 1) X ≅ parityDual ε X)
  | 0, ⟨0, _⟩, h =>
      False.elim ((by decide : (Int.negSucc 0 : ZMod 2).val ≠ 0) (congrArg Fin.val h))
  | 0, ⟨1, _⟩, _ => leftDualIsoRightDual X
  | k + 1, ⟨0, _⟩, h =>
      @Iso.leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
        (LeftRigidCategory.leftDual _)
        (pivotalLeftPowAuxIso X k 1 (by
          have hk : ((Int.negSucc k - 1 : ℤ) : ZMod 2) = 0 := Fin.ext (congrArg Fin.val h)
          rwa [Int.cast_sub, Int.cast_one, CharTwo.sub_eq_add, CharTwo.add_eq_iff_eq_add,
            zero_add] at hk)).symm ≪≫
        (leftDualRightDualIso C).app X
  | k + 1, ⟨1, _⟩, h =>
      @Iso.leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
        (LeftRigidCategory.leftDual _)
        (pivotalLeftPowAuxIso X k 0 (by
          have hk : ((Int.negSucc k - 1 : ℤ) : ZMod 2) = 1 := Fin.ext (congrArg Fin.val h)
          rwa [Int.cast_sub, Int.cast_one, CharTwo.sub_eq_add, CharTwo.add_eq_iff_eq_add,
            CharTwo.add_self_eq_zero] at hk)).symm ≪≫
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

@[simp] theorem pivotalAtomIso_neg_one (X : C) :
    pivotalAtomIso (-1) X = leftDualIsoRightDual X := (rfl)

/-! ### Step coherence of `pivotalAtomIso` with right and left duality -/

omit [PivotalCategory C] in
private theorem rightAdjointMate_leftAdjointMate_eq_map {A B : C} (f : A ⟶ B) :
    @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual (ᘁB))
        (RightRigidCategory.rightDual (ᘁA))
        (@leftAdjointMate C _ _ A B (LeftRigidCategory.leftDual A)
          (LeftRigidCategory.leftDual B) f) =
      (rightDualLeftDualFunctor C).map f := by
  rw [@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual (ᘁB))
      (RightRigidCategory.rightDual (ᘁA)),
    rightDualLeftDualFunctor_map]

omit [PivotalCategory C] in
private theorem leftAdjointMate_rightAdjointMate_eq_map {A B : C} (f : A ⟶ B) :
    @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual Bᘁ)
        (LeftRigidCategory.leftDual Aᘁ) (fᘁ) =
      (leftDualRightDualFunctor C).map f := by
  rw [@leftAdjointMate_eq_leftMate C _ _ _ _ (LeftRigidCategory.leftDual Bᘁ)
      (LeftRigidCategory.leftDual Aᘁ),
    leftDualRightDualFunctor_map]

private theorem iteratedDualRightDualIso_hom_comp_pivotalAtomIsoAux_hom
    (n : ℤ) (X : C) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
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
    · refine (@Iso.rightAdjointMate_hom C _ _ _ _ (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _) _).trans ?_
      exact ((_ ≫= congrArg Iso.hom (parityDualRightDualIso_zero X)).trans
        (Category.comp_id _)).symm
    · refine (@Iso.rightAdjointMate_hom C _ _ _ _ (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _) _ =≫ _).trans ?_
      exact (_ ≫= congrArg Iso.hom (parityDualRightDualIso_one X)).symm
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
      · let e : iteratedLeftDual (k + 1) X ≅ Xᘁ := pivotalLeftPowAuxIso X k 1 (by
          have hk : ((Int.negSucc k - 1 : ℤ) : ZMod 2) = 0 := Fin.ext (congrArg Fin.val h)
          rwa [Int.cast_sub, Int.cast_one, CharTwo.sub_eq_add, CharTwo.add_eq_iff_eq_add,
            zero_add] at hk)
        have hinv : (pivotalAtomIsoAux (.negSucc (k + 1)) X 0 h).inv =
            (leftDualRightDualIso C).inv.app X ≫
              @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
                (LeftRigidCategory.leftDual _) e.hom :=
          _ ≫= @Iso.leftAdjointMate_inv C _ _ _ _ (LeftRigidCategory.leftDual _)
            (LeftRigidCategory.leftDual _) e.symm
        have hcomp : @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual X)
            (RightRigidCategory.rightDual _) (pivotalAtomIsoAux (.negSucc (k + 1)) X 0 h).inv =
            (rightDualLeftDualFunctor C).map e.hom ≫ ((leftDualRightDualIso C).inv.app X)ᘁ := by
          rw [hinv]
          refine (@comp_rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual X)
            (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _)
            ((leftDualRightDualIso C).inv.app X) _).trans ?_
          exact rightAdjointMate_leftAdjointMate_eq_map e.hom =≫ _
        have hstep := (_ ≫= rightAdjointMate_leftDualRightDualIso_inv_app X).trans
          ((rightDualLeftDualIso C).hom.naturality e.hom)
        exact (hcomp.trans hstep).symm.trans
          ((_ ≫= congrArg Iso.hom (parityDualRightDualIso_zero X)).trans
            (Category.comp_id _)).symm
      · rw [parityDualRightDualIso_one, Iso.symm_hom]
        let e : iteratedLeftDual (k + 1) X ≅ X := pivotalLeftPowAuxIso X k 0 (by
          have hk : ((Int.negSucc k - 1 : ℤ) : ZMod 2) = 1 := Fin.ext (congrArg Fin.val h)
          rwa [Int.cast_sub, Int.cast_one, CharTwo.sub_eq_add, CharTwo.add_eq_iff_eq_add,
            CharTwo.add_self_eq_zero] at hk)
        have hinv : (pivotalAtomIsoAux (.negSucc (k + 1)) X 1 h).inv =
            (leftDualIsoRightDual X).inv ≫
              @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual _)
                (LeftRigidCategory.leftDual _) e.hom :=
          _ ≫= @Iso.leftAdjointMate_inv C _ _ _ _ (LeftRigidCategory.leftDual _)
            (LeftRigidCategory.leftDual _) e.symm
        have hcomp : @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual Xᘁ)
            (RightRigidCategory.rightDual _) (pivotalAtomIsoAux (.negSucc (k + 1)) X 1 h).inv =
            (rightDualLeftDualFunctor C).map e.hom ≫
              @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual Xᘁ)
                (RightRigidCategory.rightDual _) (leftDualIsoRightDual X).inv := by
          rw [hinv]
          refine (@comp_rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual Xᘁ)
            (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _)
            (leftDualIsoRightDual X).inv _).trans ?_
          exact rightAdjointMate_leftAdjointMate_eq_map e.hom =≫ _
        have hstep := (_ ≫=
            rightAdjointMate_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv X).trans
          ((rightDualLeftDualIso C).hom.naturality e.hom)
        exact ((hcomp =≫ _).trans ((Category.assoc _ _ _).trans hstep)).symm

private theorem eqToHom_comp_pivotalAtomIsoAux_ofNat (X : C) (m : ℤ) (k : ℕ) (δ : ZMod 2)
    (hm : m = Int.ofNat k) (h' : (m : ZMod 2) = δ) :
    eqToHom (congrArg (iteratedDual · X) hm.symm) ≫ (pivotalAtomIsoAux m X δ h').hom =
      (pivotalRightPowAuxIso X k δ (by simpa [hm] using h')).hom := by
  subst hm
  exact Category.id_comp _

private theorem iteratedDualLeftDualIso_hom_comp_pivotalAtomIsoAux_pos
    (k : ℕ) (X : C) (ε : ZMod 2) (h : ((Int.ofNat (k + 1) : ℤ) : ZMod 2) = ε)
    (h' : (((Int.ofNat (k + 1) : ℤ) - 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualLeftDualIso (.ofNat (k + 1)) X).hom ≫
        (pivotalAtomIsoAux (Int.ofNat (k + 1) - 1) X (ε + 1) h').hom =
      (leftDualIsoRightDual (iteratedDual (.ofNat (k + 1)) X)).hom ≫
        @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
          (RightRigidCategory.rightDual _) (pivotalAtomIsoAux (.ofNat (k + 1)) X ε h).inv ≫
        (parityDualRightDualIso ε X).hom := by
  have hlhs : (iteratedDualLeftDualIso (.ofNat (k + 1)) X).hom =
      (leftDualRightDualIso C).hom.app (iteratedRightDual k X) ≫
        eqToHom (congrArg (iteratedDual · X) (add_sub_cancel_right (k : ℤ) 1).symm) :=
    (congrArg Iso.hom (iteratedDualLeftDualIso_natCast_add_one k X)).trans
      ((leftDualRightDualIso_hom_app (iteratedRightDual k X)).symm =≫ _)
  refine (hlhs =≫ _).trans ((Category.assoc _ _ _).trans ?_)
  refine (_ ≫= eqToHom_comp_pivotalAtomIsoAux_ofNat X _ k (ε + 1)
    (add_sub_cancel_right (k : ℤ) 1) h').trans ?_
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
  · let e : iteratedRightDual k X ≅ Xᘁ := pivotalRightPowAuxIso X k 1 (by
      have hk : ((k + 1 : ℕ) : ZMod 2) = 0 := Fin.ext (congrArg Fin.val h)
      rwa [Nat.cast_add, Nat.cast_one, CharTwo.add_eq_iff_eq_add, zero_add] at hk)
    let g : X ⟶ iteratedDual (.ofNat (k + 1)) X := (pivotalAtomIsoAux (.ofNat (k + 1)) X 0 h).inv
    have hg : g = (pivotalIsoApp X).hom ≫ e.homᘁ :=
      _ ≫= @Iso.rightAdjointMate_inv C _ _ _ _ (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _) e.symm
    have hcomp : @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual X)
        (LeftRigidCategory.leftDual _) g =
        (leftDualRightDualFunctor C).map e.hom ≫
          @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual X)
            (LeftRigidCategory.leftDual _) (pivotalIsoApp X).hom := by
      rw [hg]
      refine (@comp_leftAdjointMate C _ _ _ _ _ (LeftRigidCategory.leftDual X)
        (LeftRigidCategory.leftDual _) (LeftRigidCategory.leftDual _)
        (pivotalIsoApp X).hom (e.homᘁ)).trans ?_
      exact leftAdjointMate_rightAdjointMate_eq_map e.hom =≫ _
    have hφ : @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual X)
        (LeftRigidCategory.leftDual _) (pivotalIsoApp X).hom ≫
        (leftDualIsoRightDual X).hom = (leftDualRightDualIso C).hom.app Xᘁ := by
      rw [leftAdjointMate_comp_leftDualIsoRightDual_hom, ← pivotalIsoApp_rightDual_inv,
        leftDualIsoRightDual_rightDual_hom_comp_pivotalIsoApp_inv]
    have hstep : (leftDualIsoRightDual (iteratedDual (.ofNat (k + 1)) X)).hom ≫ gᘁ =
        (leftDualRightDualIso C).hom.app (iteratedRightDual k X) ≫ e.hom := by
      rw [← leftAdjointMate_comp_leftDualIsoRightDual_hom g, hcomp]
      exact (Category.assoc _ _ _).trans ((_ ≫= hφ).trans
        ((leftDualRightDualIso C).hom.naturality e.hom))
    exact (hstep.symm.trans
      (_ ≫= ((_ ≫= congrArg Iso.hom (parityDualRightDualIso_zero X)).trans
        (Category.comp_id _)).symm))
  · let e : iteratedRightDual k X ≅ X := pivotalRightPowAuxIso X k 0 (by
      have hk : ((k + 1 : ℕ) : ZMod 2) = 1 := Fin.ext (congrArg Fin.val h)
      rwa [Nat.cast_add, Nat.cast_one, CharTwo.add_eq_iff_eq_add,
        CharTwo.add_self_eq_zero] at hk)
    let g : Xᘁ ⟶ iteratedDual (.ofNat (k + 1)) X := (pivotalAtomIsoAux (.ofNat (k + 1)) X 1 h).inv
    have hg : g = e.homᘁ :=
      @Iso.rightAdjointMate_inv C _ _ _ _ (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _) e.symm
    have hcomp : @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual Xᘁ)
        (LeftRigidCategory.leftDual _) g = (leftDualRightDualFunctor C).map e.hom := by
      rw [hg]
      exact leftAdjointMate_rightAdjointMate_eq_map e.hom
    have hstep : (leftDualIsoRightDual (iteratedDual (.ofNat (k + 1)) X)).hom ≫ gᘁ ≫
        (pivotalIsoApp X).inv =
        (leftDualRightDualIso C).hom.app (iteratedRightDual k X) ≫ e.hom := by
      rw [← leftAdjointMate_comp_leftDualIsoRightDual_hom_assoc g, hcomp,
        leftDualIsoRightDual_rightDual_hom_comp_pivotalIsoApp_inv]
      exact (leftDualRightDualIso C).hom.naturality e.hom
    exact hstep.symm.trans (_ ≫= (_ ≫= (congrArg Iso.hom (parityDualRightDualIso_one X)).symm))

private theorem iteratedDualLeftDualIso_hom_comp_pivotalAtomIsoAux_hom
    (n : ℤ) (X : C) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
    (h' : ((n - 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualLeftDualIso n X).hom ≫ (pivotalAtomIsoAux (n - 1) X (ε + 1) h').hom =
      (leftDualIsoRightDual (iteratedDual n X)).hom ≫
        @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual _)
          (RightRigidCategory.rightDual _) (pivotalAtomIsoAux n X ε h).inv ≫
        (parityDualRightDualIso ε X).hom := by
  cases n with
  | negSucc k =>
    refine ((congrArg Iso.hom (iteratedDualLeftDualIso_negSucc k X) =≫ _).trans
      (Category.id_comp _)).trans ?_
    rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
    · let g : X ⟶ iteratedDual (.negSucc k) X := (pivotalAtomIsoAux (.negSucc k) X 0 h).inv
      refine (@Iso.leftAdjointMate_hom C _ _ _ _ (LeftRigidCategory.leftDual X)
        (LeftRigidCategory.leftDual _) _ =≫ _).trans ?_
      refine (leftAdjointMate_comp_leftDualIsoRightDual_hom g).trans ?_
      exact (_ ≫= ((_ ≫= congrArg Iso.hom (parityDualRightDualIso_zero X)).trans
        (Category.comp_id _)).symm)
    · let g : Xᘁ ⟶ iteratedDual (.negSucc k) X := (pivotalAtomIsoAux (.negSucc k) X 1 h).inv
      have hstep : @leftAdjointMate C _ _ _ _ (LeftRigidCategory.leftDual Xᘁ)
            (LeftRigidCategory.leftDual _) g ≫ ((leftDualRightDualIso C).app X).hom =
          (leftDualIsoRightDual (iteratedDual (.negSucc k) X)).hom ≫ gᘁ ≫
            (pivotalIsoApp X).inv := by
        rw [Iso.app_hom, ← leftDualIsoRightDual_rightDual_hom_comp_pivotalIsoApp_inv,
          leftAdjointMate_comp_leftDualIsoRightDual_hom_assoc]
      refine (@Iso.leftAdjointMate_hom C _ _ _ _ (LeftRigidCategory.leftDual Xᘁ)
        (LeftRigidCategory.leftDual _) _ =≫ _).trans ?_
      exact hstep.trans (_ ≫= (_ ≫= (congrArg Iso.hom (parityDualRightDualIso_one X)).symm))
  | ofNat k =>
    cases k with
    | zero =>
      refine ((congrArg Iso.hom (iteratedDualLeftDualIso_zero X) =≫ _).trans
        (Category.id_comp _)).trans ?_
      rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl
      · have hGoal : (leftDualIsoRightDual X).hom =
            (leftDualIsoRightDual X).hom ≫ (𝟙 X)ᘁ ≫ 𝟙 Xᘁ := by simp
        exact hGoal.trans (_ ≫= (_ ≫= (congrArg Iso.hom (parityDualRightDualIso_zero X)).symm))
      · exact absurd (congrArg Fin.val h) (by decide)
    | succ k => exact iteratedDualLeftDualIso_hom_comp_pivotalAtomIsoAux_pos k X ε h h'

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
    reassoc_of% (iteratedDualRightDualIso_hom_comp_pivotalAtomIsoAux_hom n X (n : ZMod 2) rfl _)]
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
    reassoc_of% (iteratedDualLeftDualIso_hom_comp_pivotalAtomIsoAux_hom n X (n : ZMod 2) rfl _)]
  rfl

private theorem pivotalAtomIso_natCast_succ_hom (k : ℕ) (ε : ZMod 2) (hε : ((k : ℤ) : ZMod 2) = ε)
    (X : C) :
    (pivotalAtomIso ((k : ℤ) + 1) X).hom =
      ((pivotalAtomIso (k : ℤ) X).inv)ᘁ ≫
        eqToHom (congrArg (fun δ ↦ (parityDual δ X)ᘁ) hε) ≫
        (parityDualRightDualIso ε X).hom ≫
        eqToHom (congrArg (parityDual · X) (by simp [← hε])) := by
  subst hε
  rw [eqToHom_refl, Category.id_comp]
  refine (Category.id_comp _).symm.trans ?_
  refine ((congrArg Iso.hom (iteratedDualRightDualIso_natCast k X) =≫ _).symm).trans ?_
  exact iteratedDualRightDualIso_hom_comp_pivotalAtomIso_hom (k : ℤ) X

@[simp] theorem pivotalAtomIso_one (X : C) : pivotalAtomIso 1 X = Iso.refl Xᘁ := by
  ext
  have h : (pivotalAtomIso 1 X).hom = ((pivotalAtomIso 0 X).inv)ᘁ ≫ 𝟙 Xᘁ :=
    (pivotalAtomIso_natCast_succ_hom 0 0 rfl X).trans
      (_ ≫= ((eqToHom_refl _ _ =≫ _).trans ((Category.id_comp _).trans
        ((_ ≫= eqToHom_refl _ _).trans
          ((congrArg Iso.hom (parityDualRightDualIso_zero X) =≫ _).trans
            (Category.comp_id _))))))
  exact h.trans ((Category.comp_id _).trans (rightAdjointMate_id (X := X)))

/-- At winding level `2`, `pivotalAtomIso 2 X : Xᘁᘁ ≅ X` is `(pivotalIsoApp X).symm` — not the
identity — so identifying level `0` with level `2` evaluates to `(pivotalIsoApp X).hom`. -/
@[simp] theorem pivotalAtomIso_two (X : C) : pivotalAtomIso 2 X = (pivotalIsoApp X).symm := by
  ext
  have h : (pivotalAtomIso 2 X).hom = ((pivotalAtomIso 1 X).inv)ᘁ ≫ (pivotalIsoApp X).inv :=
    (pivotalAtomIso_natCast_succ_hom 1 1 rfl X).trans
      (_ ≫= ((eqToHom_refl _ _ =≫ _).trans ((Category.id_comp _).trans
        ((_ ≫= eqToHom_refl _ _).trans
          ((congrArg Iso.hom (parityDualRightDualIso_one X) =≫ _).trans
            (Category.comp_id _))))))
  have hid : ((pivotalAtomIso 1 X).inv)ᘁ = 𝟙 Xᘁᘁ := by
    rw [pivotalAtomIso_one, Iso.refl_inv]
    exact rightAdjointMate_id (X := Xᘁ)
  exact h.trans ((hid =≫ _).trans (Category.id_comp _))

/-- By the Freyd–Yetter identity (`pivotalIsoApp_rightDual_inv`), the level-`3` comparison
`Xᘁᘁᘁ ⟶ Xᘁ` equals the inverse pivotal component at `Xᘁ`. -/
theorem pivotalAtomIso_three_hom (X : C) : (pivotalAtomIso 3 X).hom = (pivotalIsoApp Xᘁ).inv := by
  have h : (pivotalAtomIso 3 X).hom = ((pivotalAtomIso 2 X).inv)ᘁ ≫ 𝟙 Xᘁ :=
    (pivotalAtomIso_natCast_succ_hom 2 0 rfl X).trans
      (_ ≫= ((eqToHom_refl _ _ =≫ _).trans ((Category.id_comp _).trans
        ((_ ≫= eqToHom_refl _ _).trans
          ((congrArg Iso.hom (parityDualRightDualIso_zero X) =≫ _).trans
            (Category.comp_id _))))))
  have hφ : ((pivotalAtomIso 2 X).inv)ᘁ = (pivotalIsoApp Xᘁ).inv := by
    rw [pivotalAtomIso_two, Iso.symm_inv, pivotalIsoApp_rightDual_inv]
    rfl
  exact h.trans ((Category.comp_id _).trans hφ)

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
theorem pivotalComparisonIso_append_hom (f : α → C) (L M : WindingWord α) :
    (pivotalComparisonIso f (L ++ M)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_append L M)) ≫
        (ParityWord.evalAppendIso f (toParity L) (toParity M)).hom =
      (evalAppendIso f L M).hom ≫
        ((pivotalComparisonIso f L).hom ⊗ₘ (pivotalComparisonIso f M).hom) := by
  induction L with
  | nil =>
    have hL : (ParityWord.evalAppendIso f (toParity []) (toParity M)).hom =
        (λ_ (ParityWord.eval f (toParity M))).inv :=
      congrArg Iso.hom (ParityWord.evalAppendIso_nil f (toParity M))
    have hGoal : (pivotalComparisonIso f M).hom ≫ 𝟙 _ ≫
          (λ_ (ParityWord.eval f (toParity M))).inv =
        (λ_ (eval f M)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ (pivotalComparisonIso f M).hom) := by
      rw [Category.id_comp, id_tensorHom, leftUnitor_inv_naturality]
    exact (_ ≫= ((eqToHom_refl _ _ =≫ _).trans (_ ≫= hL))).trans
      (hGoal.trans ((congrArg Iso.hom (evalAppendIso_nil f M)).symm =≫ _))
  | cons p L ih =>
    have hEq : eqToHom (congrArg (ParityWord.eval f) (toParity_append (p :: L) M)) =
        parityDual (p.2 : ZMod 2) (f p.1) ◁
          eqToHom (congrArg (ParityWord.eval f) (toParity_append L M)) :=
      (MonoidalCategory.whiskerLeft_eqToHom (parityDual (p.2 : ZMod 2) (f p.1))
        (congrArg (ParityWord.eval f) (toParity_append L M))).symm
    have hPA : (ParityWord.evalAppendIso f (toParity (p :: L)) (toParity M)).hom =
        (parityDual (p.2 : ZMod 2) (f p.1) ◁
          (ParityWord.evalAppendIso f (toParity L) (toParity M)).hom) ≫
          (α_ (parityDual (p.2 : ZMod 2) (f p.1))
            (ParityWord.eval f (toParity L)) (ParityWord.eval f (toParity M))).inv :=
      congrArg Iso.hom (ParityWord.evalAppendIso_cons f (p.1, (p.2 : ZMod 2))
        (toParity L) (toParity M))
    have hWA : (evalAppendIso f (p :: L) M).hom =
        (iteratedDual p.2 (f p.1) ◁ (evalAppendIso f L M).hom) ≫
          (α_ (iteratedDual p.2 (f p.1)) (eval f L) (eval f M)).inv :=
      congrArg Iso.hom (evalAppendIso_cons f p L M)
    have hGoal : ((pivotalAtomIso p.2 (f p.1)).hom ⊗ₘ (pivotalComparisonIso f (L ++ M)).hom) ≫
          (parityDual (p.2 : ZMod 2) (f p.1) ◁
            eqToHom (congrArg (ParityWord.eval f) (toParity_append L M))) ≫
          ((parityDual (p.2 : ZMod 2) (f p.1) ◁
              (ParityWord.evalAppendIso f (toParity L) (toParity M)).hom) ≫
            (α_ (parityDual (p.2 : ZMod 2) (f p.1))
              (ParityWord.eval f (toParity L)) (ParityWord.eval f (toParity M))).inv) =
        ((iteratedDual p.2 (f p.1) ◁ (evalAppendIso f L M).hom) ≫
          (α_ (iteratedDual p.2 (f p.1)) (eval f L) (eval f M)).inv) ≫
          (((pivotalAtomIso p.2 (f p.1)).hom ⊗ₘ (pivotalComparisonIso f L).hom) ⊗ₘ
            (pivotalComparisonIso f M).hom) := by
      simp only [Category.assoc]
      rw [tensorHom_def'_assoc, ← whisker_exchange_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, ← whisker_exchange_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc,
        Category.assoc (pivotalComparisonIso f (L ++ M)).hom, ih,
        MonoidalCategory.whiskerLeft_comp_assoc, ← tensorHom_def'_assoc,
        associator_inv_naturality]
    exact (_ ≫= ((hEq =≫ _).trans (_ ≫= hPA))).trans (hGoal.trans (hWA.symm =≫ _))

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
  rw [eqToHom_refl, Category.id_comp]
  exact ((_ ≫= eqToHom_refl _ _).trans (Category.comp_id _)).symm

/-- Shared inductive step for right- and left-dual word coherence on `p :: L`. -/
private theorem pivotalComparisonIso_dualCons_tail (f : α → C) (p : α × ℤ) (L : WindingWord α)
    (W : WindingWord α) (m : ℤ) (hW : toParity W = ParityWord.dual (toParity L))
    (hm : (m : ZMod 2) = (p.2 : ZMod 2) + 1) (hwCons : toParity (W ++ [(p.1, m)]) =
      ParityWord.dual ((p.1, (p.2 : ZMod 2)) :: toParity L))
    (u : (eval f L)ᘁ ⟶ eval f W) (v : (iteratedDual p.2 (f p.1))ᘁ ⟶ iteratedDual m (f p.1))
    (hu : u ≫ (pivotalComparisonIso f W).hom =
      ((pivotalComparisonIso f L).inv)ᘁ ≫ (ParityWord.evalDualIso f (toParity L)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) hW.symm))
    (hv : v ≫ (pivotalAtomIso m (f p.1)).hom =
      ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ ≫ (parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫
        eqToHom (congrArg (parityDual · (f p.1)) hm.symm)) :
    (u ⊗ₘ (v ≫ (ρ_ _).inv : (iteratedDual p.2 (f p.1))ᘁ ⟶ eval f [(p.1, m)])) ≫
        (evalAppendIso f W [(p.1, m)]).inv ≫
        (pivotalComparisonIso f (W ++ [(p.1, m)])).hom =
      (((pivotalComparisonIso f L).inv)ᘁ ⊗ₘ ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ) ≫
        ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ
          ((parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv :
            (parityDual (p.2 : ZMod 2) (f p.1))ᘁ ⟶
              ParityWord.eval f [(p.1, (p.2 : ZMod 2) + 1)])) ≫
        (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
          [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
        eqToHom (congrArg (ParityWord.eval f)
          ((ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm.trans hwCons.symm)) := by
  have hvUnit : (v ≫ (ρ_ _).inv : (iteratedDual p.2 (f p.1))ᘁ ⟶ eval f [(p.1, m)]) ≫
        (pivotalComparisonIso f [(p.1, m)]).hom =
      ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ ≫
        ((parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv :
          (parityDual (p.2 : ZMod 2) (f p.1))ᘁ ⟶
            ParityWord.eval f [(p.1, (p.2 : ZMod 2) + 1)]) ≫
        eqToHom (congrArg (ParityWord.eval f) (singleton_toParity_eq p.1 hm)) := by
    have hStep : (v ≫ (ρ_ (iteratedDual m (f p.1))).inv) ≫
          (pivotalAtomIso m (f p.1) ⊗ᵢ Iso.refl (𝟙_ C)).hom =
        ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ ≫
          ((parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫
            (ρ_ (parityDual ((p.2 : ZMod 2) + 1) (f p.1))).inv) ≫
          eqToHom (congrArg (ParityWord.eval f) (singleton_toParity_eq p.1 hm)) := by
      rw [tensorIso_hom, Iso.refl_hom, tensorHom_id, Category.assoc,
        ← rightUnitor_inv_naturality, reassoc_of% hv, eqToHom_whiskerRight_unit f p.1 hm]
      simp only [Category.assoc]
      rfl
    exact hStep
  have hSplit : ∀ {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C} (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
      (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃) (b₃ : B₃ ⟶ B₄),
      (a₁ ≫ a₂ ≫ a₃) ⊗ₘ (b₁ ≫ b₂ ≫ b₃) = (a₁ ⊗ₘ b₁) ≫ (a₂ ⊗ₘ b₂) ≫ (a₃ ⊗ₘ b₃) := by
    intros; simp [tensorHom_comp_tensorHom]
  have hMain : ∀ (u' : (iteratedDual p.2 (f p.1))ᘁ ⟶ eval f [(p.1, m)])
      (w' : (parityDual (p.2 : ZMod 2) (f p.1))ᘁ ⟶
        ParityWord.eval f [(p.1, (p.2 : ZMod 2) + 1)]),
      u' ≫ (pivotalComparisonIso f [(p.1, m)]).hom =
        ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ ≫ w' ≫
          eqToHom (congrArg (ParityWord.eval f) (singleton_toParity_eq p.1 hm)) →
      (u ⊗ₘ u') ≫ (evalAppendIso f W [(p.1, m)]).inv ≫
          (pivotalComparisonIso f (W ++ [(p.1, m)])).hom =
        (((pivotalComparisonIso f L).inv)ᘁ ⊗ₘ ((pivotalAtomIso p.2 (f p.1)).inv)ᘁ) ≫
          ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ w') ≫
          (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
            [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
          eqToHom (congrArg (ParityWord.eval f)
            ((ParityWord.dual_cons (p.1, (p.2 : ZMod 2))
              (toParity L)).symm.trans hwCons.symm)) := by
    intro u' w' hvU
    rw [evalAppendIso_inv_comp_pivotalComparisonIso_hom, tensorHom_comp_tensorHom_assoc,
      hu, hvU, hSplit, Category.assoc, Category.assoc,
      reassoc_of% (tensor_eqToHom_comp_evalAppendIso_inv f hW.symm (singleton_toParity_eq p.1 hm)),
      eqToHom_trans]
  exact hMain _ _ hvUnit

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
    have hR : ((pivotalComparisonIso f ([] : WindingWord α)).inv)ᘁ ≫
        (ParityWord.evalDualIso f (toParity [])).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_rightDual ([] : WindingWord α)).symm) =
        (rightDualUnitIso C).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (congrArg toParity rightDual_nil.symm)) :=
      (hmate =≫ _).trans ((Category.id_comp _).trans
        ((hrhs =≫ _).trans ((Category.assoc _ _ _).trans (_ ≫= eqToHom_trans _ _))))
    exact hL.trans hR.symm
  | p :: L => by
    have ih := pivotalComparisonIso_rightDual_hom f L
    let r : (iteratedDual p.2 (f p.1))ᘁ ⟶ eval f [(p.1, p.2 + 1)] :=
      (iteratedDualRightDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv
    let pr : (parityDual (p.2 : ZMod 2) (f p.1))ᘁ ⟶
        ParityWord.eval f [(p.1, (p.2 : ZMod 2) + 1)] :=
      (parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv
    have hlhs : (evalRightDualIso f (p :: L)).hom =
        (rightDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
          ((evalRightDualIso f L).hom ⊗ₘ r) ≫
          (evalAppendIso f (rightDual L) [(p.1, p.2 + 1)]).inv ≫
          eqToHom (congrArg (eval f) (rightDual_cons p L).symm) :=
      congrArg Iso.hom (evalRightDualIso_cons f p L)
    have hrhs : (ParityWord.evalDualIso f (toParity (p :: L))).hom =
        (rightDualTensorIso (parityDual (p.2 : ZMod 2) (f p.1))
            (ParityWord.eval f (toParity L))).hom ≫
          ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ pr) ≫
          (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
            [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
          eqToHom (congrArg (ParityWord.eval f)
            (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm) :=
      congrArg Iso.hom (ParityWord.evalDualIso_cons f (p.1, (p.2 : ZMod 2)) (toParity L))
    have htail := pivotalComparisonIso_dualCons_tail f p L (rightDual L) (p.2 + 1)
      (toParity_rightDual L) (by simp) (by simp) _ _ ih
      (iteratedDualRightDualIso_hom_comp_pivotalAtomIso_hom p.2 (f p.1))
    have hMid : ((rightDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
          ((evalRightDualIso f L).hom ⊗ₘ r) ≫
          (evalAppendIso f (rightDual L) [(p.1, p.2 + 1)]).inv ≫
          eqToHom (congrArg (eval f) (rightDual_cons p L).symm)) ≫
          (pivotalComparisonIso f (rightDual (p :: L))).hom =
        (((pivotalAtomIso p.2 (f p.1)).inv ⊗ₘ (pivotalComparisonIso f L).inv)ᘁ) ≫
          ((rightDualTensorIso (parityDual (p.2 : ZMod 2) (f p.1))
              (ParityWord.eval f (toParity L))).hom ≫
            ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ pr) ≫
            (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
              [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
            eqToHom (congrArg (ParityWord.eval f)
              (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm)) ≫
          eqToHom (congrArg (ParityWord.eval f) (toParity_rightDual (p :: L)).symm) := by
      simp only [Category.assoc]
      rw [eqToHom_comp_pivotalComparisonIso_hom f (rightDual_cons p L).symm,
        reassoc_of% htail,
        ← rightDualTensorIso_hom_naturality_assoc (pivotalAtomIso p.2 (f p.1)).inv
          (pivotalComparisonIso f L).inv]
      simp only [eqToHom_trans]
      rfl
    exact ((hlhs =≫ _).trans hMid).trans (_ ≫= (hrhs.symm =≫ _))

private theorem pivotalComparisonIso_leftDual_nil (f : α → C) :
    (evalLeftDualIso f ([] : WindingWord α)).hom ≫ (pivotalComparisonIso f (leftDual [])).hom =
      (leftDualIsoRightDual (eval f [])).hom ≫ ((pivotalComparisonIso f []).inv)ᘁ ≫
        (ParityWord.evalDualIso f (toParity [])).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_leftDual []).symm) := by
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

private theorem leftDualTensorIso_hom_comp_leftDualIsoRightDual (X Y : C) :
    (leftDualTensorIso X Y).hom ≫
        ((leftDualIsoRightDual Y).hom ⊗ₘ (leftDualIsoRightDual X).hom) =
      (leftDualIsoRightDual (X ⊗ Y)).hom ≫ (rightDualTensorIso X Y).hom := by
  rw [← cancel_epi (leftDualIsoRightDual (X ⊗ Y)).inv, Iso.inv_hom_id_assoc,
    reassoc_of% (leftDualIsoRightDual_tensor_inv X Y), tensorHom_comp_tensorHom]
  simp

private theorem evalLeftDualIso_cons_split (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    ((evalLeftDualIso f L).hom ⊗ₘ
        ((iteratedDualLeftDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv :
          (ᘁ(iteratedDual p.2 (f p.1)) : C) ⟶ eval f [(p.1, p.2 - 1)])) =
      ((leftDualIsoRightDual (eval f L)).hom ⊗ₘ
        (leftDualIsoRightDual (iteratedDual p.2 (f p.1))).hom) ≫
      (((leftDualIsoRightDual (eval f L)).inv ≫ (evalLeftDualIso f L).hom) ⊗ₘ
        (((leftDualIsoRightDual (iteratedDual p.2 (f p.1))).inv ≫
          (iteratedDualLeftDualIso p.2 (f p.1)).hom) ≫ (ρ_ _).inv :
          (iteratedDual p.2 (f p.1))ᘁ ⟶ eval f [(p.1, p.2 - 1)])) := by
  have hStep : ((evalLeftDualIso f L).hom ⊗ₘ
        ((iteratedDualLeftDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv)) =
      ((leftDualIsoRightDual (eval f L)).hom ⊗ₘ
        (leftDualIsoRightDual (iteratedDual p.2 (f p.1))).hom) ≫
      (((leftDualIsoRightDual (eval f L)).inv ≫ (evalLeftDualIso f L).hom) ⊗ₘ
        (((leftDualIsoRightDual (iteratedDual p.2 (f p.1))).inv ≫
          (iteratedDualLeftDualIso p.2 (f p.1)).hom) ≫ (ρ_ _).inv)) := by
    rw [tensorHom_comp_tensorHom]
    simp
  exact hStep

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
  | [] => pivotalComparisonIso_leftDual_nil f
  | p :: L => by
    have ih := pivotalComparisonIso_leftDual_hom f L
    let r : (ᘁ(iteratedDual p.2 (f p.1)) : C) ⟶ eval f [(p.1, p.2 - 1)] :=
      (iteratedDualLeftDualIso p.2 (f p.1)).hom ≫ (ρ_ _).inv
    let pr : (parityDual (p.2 : ZMod 2) (f p.1))ᘁ ⟶
        ParityWord.eval f [(p.1, (p.2 : ZMod 2) + 1)] :=
      (parityDualRightDualIso (p.2 : ZMod 2) (f p.1)).hom ≫ (ρ_ _).inv
    have hlhs : (evalLeftDualIso f (p :: L)).hom =
        (leftDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
          ((evalLeftDualIso f L).hom ⊗ₘ r) ≫
          (evalAppendIso f (leftDual L) [(p.1, p.2 - 1)]).inv ≫
          eqToHom (congrArg (eval f) (leftDual_cons p L).symm) :=
      congrArg Iso.hom (evalLeftDualIso_cons f p L)
    have hrhs : (ParityWord.evalDualIso f (toParity (p :: L))).hom =
        (rightDualTensorIso (parityDual (p.2 : ZMod 2) (f p.1))
            (ParityWord.eval f (toParity L))).hom ≫
          ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ pr) ≫
          (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
            [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
          eqToHom (congrArg (ParityWord.eval f)
            (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm) :=
      congrArg Iso.hom (ParityWord.evalDualIso_cons f (p.1, (p.2 : ZMod 2)) (toParity L))
    have htail := pivotalComparisonIso_dualCons_tail f p L (leftDual L) (p.2 - 1)
      (toParity_leftDual L) (by simp) (by simp) _ _
      (by rw [Category.assoc, ih, Iso.inv_hom_id_assoc])
      (by rw [Category.assoc, iteratedDualLeftDualIso_hom_comp_pivotalAtomIso_hom,
        Iso.inv_hom_id_assoc])
    have hMid : ((leftDualTensorIso (iteratedDual p.2 (f p.1)) (eval f L)).hom ≫
          ((evalLeftDualIso f L).hom ⊗ₘ r) ≫
          (evalAppendIso f (leftDual L) [(p.1, p.2 - 1)]).inv ≫
          eqToHom (congrArg (eval f) (leftDual_cons p L).symm)) ≫
          (pivotalComparisonIso f (leftDual (p :: L))).hom =
        (leftDualIsoRightDual (iteratedDual p.2 (f p.1) ⊗ eval f L)).hom ≫
          (((pivotalAtomIso p.2 (f p.1)).inv ⊗ₘ (pivotalComparisonIso f L).inv)ᘁ) ≫
          ((rightDualTensorIso (parityDual (p.2 : ZMod 2) (f p.1))
              (ParityWord.eval f (toParity L))).hom ≫
            ((ParityWord.evalDualIso f (toParity L)).hom ⊗ₘ pr) ≫
            (ParityWord.evalAppendIso f (ParityWord.dual (toParity L))
              [(p.1, (p.2 : ZMod 2) + 1)]).inv ≫
            eqToHom (congrArg (ParityWord.eval f)
              (ParityWord.dual_cons (p.1, (p.2 : ZMod 2)) (toParity L)).symm)) ≫
          eqToHom (congrArg (ParityWord.eval f) (toParity_leftDual (p :: L)).symm) := by
      rw [evalLeftDualIso_cons_split f p L]
      simp only [Category.assoc]
      rw [eqToHom_comp_pivotalComparisonIso_hom f (leftDual_cons p L).symm,
        reassoc_of% htail,
        reassoc_of% (leftDualTensorIso_hom_comp_leftDualIsoRightDual
          (iteratedDual p.2 (f p.1)) (eval f L)),
        ← rightDualTensorIso_hom_naturality_assoc (pivotalAtomIso p.2 (f p.1)).inv
          (pivotalComparisonIso f L).inv]
      simp only [eqToHom_trans]
      rfl
    exact ((hlhs =≫ _).trans hMid).trans (_ ≫= (_ ≫= (hrhs.symm =≫ _)))

omit [PivotalCategory C] in
private theorem mate_inv_of_hom_eq {A B₁ B₂ D₁ D₂ E : C}
    (e₁ : A ≅ B₁) (e₂ : B₁ ≅ B₂) (e₃ : B₂ ≅ E)
    (d₁ : A ≅ D₁) (d₂ : D₁ ≅ D₂) (d₃ : D₂ ≅ E)
    (h : e₁.hom ≫ e₂.hom ≫ e₃.hom = d₁.hom ≫ d₂.hom ≫ d₃.hom) :
    (d₁.inv)ᘁ ≫ (d₂.inv)ᘁ ≫ (d₃.inv)ᘁ = (e₁.inv)ᘁ ≫ (e₂.inv)ᘁ ≫ (e₃.inv)ᘁ := by
  have hIso : e₁ ≪≫ e₂ ≪≫ e₃ = d₁ ≪≫ d₂ ≪≫ d₃ :=
    Iso.ext (by simpa only [Iso.trans_hom, Category.assoc] using h)
  simpa only [Iso.trans_inv, comp_rightAdjointMate, Category.assoc] using
    congrArg (fun iso : A ≅ E ↦ (iso.inv)ᘁ) hIso.symm

private theorem parityDualRightDualIso_hom_naturality_cast {ε δ : ZMod 2} (h : δ = ε + 1)
    {X Y : C} (e : X ≅ Y) :
    (parityDualRightDualIso ε X).hom ≫
        eqToHom (congrArg (parityDual · X) h.symm) ≫
        (parityDualMapIso δ e).hom =
      ((parityDualMapIso ε e).inv)ᘁ ≫
        (parityDualRightDualIso ε Y).hom ≫
        eqToHom (congrArg (parityDual · Y) h.symm) := by
  subst h
  simp [parityDualRightDualIso_hom_naturality]

private theorem evalDualIso_inv_comp_eqToHom_mate (f : α → C) {P₁ P₂ : ParityWord α}
    (hP : P₁ = P₂) :
    (ParityWord.evalDualIso f P₁).inv ≫
        (eqToHom (congrArg (ParityWord.eval f) hP.symm))ᘁ =
      eqToHom (congrArg (ParityWord.eval f) (congrArg ParityWord.dual hP)) ≫
        (ParityWord.evalDualIso f P₂).inv := by
  subst hP
  simp

private theorem evalDualIso_inv_comp_parityDualRightDualIso_hom_cast (f : α → C)
    {ε δ : ZMod 2} (h : δ = ε + 1) (P : ParityWord α) :
    (ParityWord.evalDualIso f (ParityWord.dualPow ε P)).inv ≫
        ((ParityWord.evalDualPowIso f ε P).inv)ᘁ ≫
        (parityDualRightDualIso ε (ParityWord.eval f P)).hom ≫
        eqToHom (congrArg (parityDual · (ParityWord.eval f P)) h.symm) =
      eqToHom (congrArg (ParityWord.eval f)
          (by rw [h, add_comm, ParityWord.dualPow_add, ParityWord.dualPow_one])) ≫
        (ParityWord.evalDualPowIso f δ P).hom := by
  subst h
  simpa using ParityWord.evalDualIso_inv_comp_parityDualRightDualIso_hom f ε P

omit [PivotalCategory C] in
private theorem evalDualPowIso_natCast_add_one_hom (f : α → C) (k : ℕ) (L : WindingWord α) :
    (evalDualPowIso f ((k : ℤ) + 1) L).hom =
      eqToHom (congrArg (eval f) (dualPow_add_one (k : ℤ) L)) ≫
        (evalRightDualIso f (dualPow (k : ℤ) L)).inv ≫
        ((evalDualPowIso f (k : ℤ) L).inv)ᘁ ≫
        (iteratedDualRightDualIso (k : ℤ) (eval f L)).hom := by
  have h1 : (evalDualPowIso f ((k : ℤ) + 1) L).hom =
      eqToHom (congrArg (eval f) (dualPow_add_one (k : ℤ) L)) ≫
        (evalRightDualIso f (dualPow (k : ℤ) L)).inv ≫
        ((evalRightDualPowIso f k L).symm.rightAdjointMate).hom :=
    (congrArg Iso.hom (evalDualPowIso_natCast f (k + 1) L)).trans
      (congrArg Iso.hom (evalRightDualPowIso_succ f k L))
  have h2 : ((evalRightDualPowIso f k L).symm.rightAdjointMate).hom =
      ((evalDualPowIso f (k : ℤ) L).inv)ᘁ :=
    (Iso.rightAdjointMate_hom (evalRightDualPowIso f k L).symm).trans
      (congrArg (fun e : eval f (dualPow (k : ℤ) L) ≅ iteratedRightDual k (eval f L) ↦
        rightAdjointMate e.inv) (evalDualPowIso_natCast f k L).symm)
  have h3 : (iteratedDualRightDualIso (k : ℤ) (eval f L)).hom = 𝟙 _ :=
    congrArg Iso.hom (iteratedDualRightDualIso_natCast k (eval f L))
  exact h1.trans (_ ≫= (_ ≫= (h2.trans ((Category.comp_id _).symm.trans (_ ≫= h3.symm)))))

omit [PivotalCategory C] in
private theorem evalDualPowIso_neg_natCast_sub_one_hom (f : α → C) :
    (k : ℕ) → (L : WindingWord α) →
      (evalDualPowIso f (-(k : ℤ) - 1) L).hom =
        eqToHom (congrArg (eval f) (dualPow_sub_one (-(k : ℤ)) L)) ≫
          (evalLeftDualIso f (dualPow (-(k : ℤ)) L)).inv ≫
          (ᘁ(evalDualPowIso f (-(k : ℤ)) L).inv) ≫
          (iteratedDualLeftDualIso (-(k : ℤ)) (eval f L)).hom
  | 0, L => by
    have h1 : (evalDualPowIso f (.negSucc 0) L).hom =
        eqToHom (congrArg (fun k ↦ eval f (dualPow k L))
          (by omega : Int.negSucc 0 = -((0 + 1 : ℕ) : ℤ))) ≫
          eqToHom (by simp) ≫
          (evalLeftDualIso f (dualPow 0 L)).inv ≫
          ((evalLeftDualPowIso f 0 L).symm.leftAdjointMate).hom :=
      (congrArg Iso.hom (evalDualPowIso_negSucc f 0 L)).trans
        (_ ≫= congrArg Iso.hom (evalLeftDualPowIso_succ f 0 L))
    have h0Eq : evalLeftDualPowIso f 0 L = evalDualPowIso f 0 L :=
      (evalLeftDualPowIso_zero f L).trans
        ((evalDualPowIso_natCast f 0 L).trans (evalRightDualPowIso_zero f L)).symm
    have h2 : ((evalLeftDualPowIso f 0 L).symm.leftAdjointMate).hom =
        ᘁ(evalDualPowIso f 0 L).inv :=
      (Iso.leftAdjointMate_hom (evalLeftDualPowIso f 0 L).symm).trans
        (congrArg (fun e : eval f (dualPow 0 L) ≅ eval f L ↦ leftAdjointMate e.inv) h0Eq)
    have h3 : (iteratedDualLeftDualIso 0 (eval f L)).hom = 𝟙 _ :=
      congrArg Iso.hom (iteratedDualLeftDualIso_zero (eval f L))
    exact h1.trans ((eqToHom_trans_assoc _ _ _).trans
      (_ ≫= (_ ≫= (h2.trans ((Category.comp_id _).symm.trans (_ ≫= h3.symm))))))
  | m + 1, L => by
    have h1 : (evalDualPowIso f (.negSucc (m + 1)) L).hom =
        eqToHom (congrArg (fun k ↦ eval f (dualPow k L))
          (by omega : Int.negSucc (m + 1) = -((m + 1 + 1 : ℕ) : ℤ))) ≫
          eqToHom (congrArg (eval f)
            (by rw [show -((m + 1 + 1 : ℕ) : ℤ) = Int.negSucc m - 1 by omega,
              dualPow_sub_one])) ≫
          (evalLeftDualIso f (dualPow (.negSucc m) L)).inv ≫
          ((evalLeftDualPowIso f (m + 1) L).symm.leftAdjointMate).hom :=
      (congrArg Iso.hom (evalDualPowIso_negSucc f (m + 1) L)).trans
        (_ ≫= congrArg Iso.hom (evalLeftDualPowIso_succ f (m + 1) L))
    have hInv : (evalDualPowIso f (.negSucc m) L).inv = (evalLeftDualPowIso f (m + 1) L).inv := by
      rw [evalDualPowIso_negSucc]
      simp
    have h2 : ((evalLeftDualPowIso f (m + 1) L).symm.leftAdjointMate).hom =
        ᘁ(evalDualPowIso f (.negSucc m) L).inv :=
      (Iso.leftAdjointMate_hom (evalLeftDualPowIso f (m + 1) L).symm).trans
        (congrArg (fun g : iteratedLeftDual (m + 1) (eval f L) ⟶ eval f (dualPow (.negSucc m) L) ↦
          leftAdjointMate g) hInv.symm)
    have h3 : (iteratedDualLeftDualIso (.negSucc m) (eval f L)).hom = 𝟙 _ :=
      congrArg Iso.hom (iteratedDualLeftDualIso_negSucc m (eval f L))
    exact h1.trans ((eqToHom_trans_assoc _ _ _).trans
      (_ ≫= (_ ≫= (h2.trans ((Category.comp_id _).symm.trans (_ ≫= h3.symm))))))

private theorem pivotalComparisonIso_dualPow_step (f : α → C) (L : WindingWord α)
    (m m' : ℤ) (W' : WindingWord α) (hm' : dualPow m' L = W')
    (hPar : toParity W' = ParityWord.dual (toParity (dualPow m L)))
    (hCast : (m' : ZMod 2) = (m : ZMod 2) + 1)
    (u : eval f W' ⟶ (eval f (dualPow m L))ᘁ)
    (ih : (pivotalComparisonIso f (dualPow m L)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_dualPow m L)) ≫
        (ParityWord.evalDualPowIso f (m : ZMod 2) (toParity L)).hom =
      (evalDualPowIso f m L).hom ≫
        (pivotalAtomIso m (eval f L)).hom ≫
        (parityDualMapIso (m : ZMod 2) (pivotalComparisonIso f L)).hom)
    (hStep : (evalDualPowIso f m' L).hom ≫ (pivotalAtomIso m' (eval f L)).hom =
      eqToHom (congrArg (eval f) hm') ≫ u ≫
        ((evalDualPowIso f m L).inv)ᘁ ≫
        ((pivotalAtomIso m (eval f L)).inv)ᘁ ≫
        (parityDualRightDualIso (m : ZMod 2) (eval f L)).hom ≫
        eqToHom (congrArg (parityDual · (eval f L)) hCast.symm))
    (hu : u ≫ ((pivotalComparisonIso f (dualPow m L)).inv)ᘁ =
      (pivotalComparisonIso f W').hom ≫
        eqToHom (congrArg (ParityWord.eval f) hPar) ≫
        (ParityWord.evalDualIso f (toParity (dualPow m L))).inv) :
    (pivotalComparisonIso f (dualPow m' L)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_dualPow m' L)) ≫
        (ParityWord.evalDualPowIso f (m' : ZMod 2) (toParity L)).hom =
      (evalDualPowIso f m' L).hom ≫
        (pivotalAtomIso m' (eval f L)).hom ≫
        (parityDualMapIso (m' : ZMod 2) (pivotalComparisonIso f L)).hom := by
  symm
  rw [reassoc_of% hStep,
    parityDualRightDualIso_hom_naturality_cast hCast (pivotalComparisonIso f L),
    reassoc_of% (mate_inv_of_hom_eq (pivotalComparisonIso f (dualPow m L))
      (eqToIso (congrArg (ParityWord.eval f) (toParity_dualPow m L)))
      (ParityWord.evalDualPowIso f (m : ZMod 2) (toParity L))
      (evalDualPowIso f m L) (pivotalAtomIso m (eval f L))
      (parityDualMapIso (m : ZMod 2) (pivotalComparisonIso f L)) ih),
    reassoc_of% hu]
  dsimp only [eqToIso.inv]
  rw [reassoc_of% (evalDualIso_inv_comp_eqToHom_mate f (toParity_dualPow m L)),
    evalDualIso_inv_comp_parityDualRightDualIso_hom_cast f hCast (toParity L),
    reassoc_of% (eqToHom_comp_pivotalComparisonIso_hom f hm')]
  simp only [eqToHom_trans_assoc]

/-- **Integer dual-power coherence of `pivotalComparisonIso`**: iterating duality `n : ℤ` times on a
winding word commutes with `pivotalComparisonIso`, `pivotalAtomIso n`, `parityDualMapIso`, and
`ParityWord.evalDualPowIso`. -/
@[reassoc]
theorem pivotalComparisonIso_dualPow_hom (f : α → C) (n : ℤ) (L : WindingWord α) :
    (pivotalComparisonIso f (dualPow n L)).hom ≫
        eqToHom (congrArg (ParityWord.eval f) (toParity_dualPow n L)) ≫
        (ParityWord.evalDualPowIso f (n : ZMod 2) (toParity L)).hom =
      (evalDualPowIso f n L).hom ≫
        (pivotalAtomIso n (eval f L)).hom ≫
        (parityDualMapIso (n : ZMod 2) (pivotalComparisonIso f L)).hom := by
  induction n using Int.induction_on with
  | zero =>
    have hL : (ParityWord.evalDualPowIso f ((0 : ℤ) : ZMod 2) (toParity L)).hom =
        eqToHom (congrArg (ParityWord.eval f) (ParityWord.dualPow_zero (toParity L))) :=
      congrArg Iso.hom (ParityWord.evalDualPowIso_zero f (toParity L))
    have hR1 : (evalDualPowIso f 0 L).hom = eqToHom (congrArg (eval f) (dualPow_zero L)) :=
      (congrArg Iso.hom (evalDualPowIso_natCast f 0 L)).trans
        (congrArg Iso.hom (evalRightDualPowIso_zero f L))
    have hR3 : (parityDualMapIso ((0 : ℤ) : ZMod 2) (pivotalComparisonIso f L)).hom =
        (pivotalComparisonIso f L).hom :=
      congrArg Iso.hom (parityDualMapIso_zero (pivotalComparisonIso f L))
    have hMid : (pivotalComparisonIso f (dualPow 0 L)).hom ≫
          eqToHom (congrArg (ParityWord.eval f) (toParity_dualPow 0 L)) ≫
          eqToHom (congrArg (ParityWord.eval f) (ParityWord.dualPow_zero (toParity L))) =
        eqToHom (congrArg (eval f) (dualPow_zero L)) ≫
          𝟙 (eval f L) ≫ (pivotalComparisonIso f L).hom := by
      rw [Category.id_comp, eqToHom_comp_pivotalComparisonIso_hom f (dualPow_zero L)]
      simp
    exact (_ ≫= (_ ≫= hL)).trans (hMid.trans ((hR1.symm =≫ _).trans (_ ≫= (_ ≫= hR3.symm))))
  | succ k ih =>
    refine pivotalComparisonIso_dualPow_step f L (k : ℤ) ((k : ℤ) + 1)
      (rightDual (dualPow (k : ℤ) L)) (dualPow_add_one (k : ℤ) L)
      (toParity_rightDual (dualPow (k : ℤ) L)) (by simp)
      (evalRightDualIso f (dualPow (k : ℤ) L)).inv ih ?_ ?_
    · rw [evalDualPowIso_natCast_add_one_hom]
      simp only [Category.assoc]
      rw [iteratedDualRightDualIso_hom_comp_pivotalAtomIso_hom]
    · rw [Iso.inv_comp_eq, pivotalComparisonIso_rightDual_hom_assoc]
      simp
  | pred k ih =>
    refine pivotalComparisonIso_dualPow_step f L (-(k : ℤ)) (-(k : ℤ) - 1)
      (leftDual (dualPow (-(k : ℤ)) L)) (dualPow_sub_one (-(k : ℤ)) L)
      (toParity_leftDual (dualPow (-(k : ℤ)) L)) (by simp)
      ((evalLeftDualIso f (dualPow (-(k : ℤ)) L)).inv ≫
        (leftDualIsoRightDual (eval f (dualPow (-(k : ℤ)) L))).hom) ih ?_ ?_
    · rw [evalDualPowIso_neg_natCast_sub_one_hom]
      simp only [Category.assoc]
      rw [iteratedDualLeftDualIso_hom_comp_pivotalAtomIso_hom,
        leftAdjointMate_comp_leftDualIsoRightDual_hom_assoc]
    · rw [Category.assoc, Iso.inv_comp_eq, pivotalComparisonIso_leftDual_hom_assoc]
      simp

omit [PivotalCategory C] in
private theorem eqToHom_toParity_append_comp_evalAppendIso_hom {β : Type w'} (g : β → C)
    {U V : WindingWord β} {P Q : ParityWord β} (hP : toParity U = P) (hQ : toParity V = Q)
    (hAll : toParity (U ++ V) = P ++ Q) :
    eqToHom (congrArg (ParityWord.eval g) hAll) ≫
        (ParityWord.evalAppendIso g P Q).hom =
      eqToHom (congrArg (ParityWord.eval g) (toParity_append U V)) ≫
        (ParityWord.evalAppendIso g (toParity U) (toParity V)).hom ≫
        (eqToHom (congrArg (ParityWord.eval g) hP) ⊗ₘ
          eqToHom (congrArg (ParityWord.eval g) hQ)) := by
  subst hP hQ
  simp

private theorem pivotalComparisonIso_subst_cons_mid {β : Type w'} (g : β → C)
    (F : α → WindingWord β) (p : α × ℤ) (L : WindingWord α)
    (ih : (pivotalComparisonIso g (subst F L)).hom ≫
        eqToHom (congrArg (ParityWord.eval g) (toParity_subst F L)) ≫
        (ParityWord.evalSubstIso g (fun a ↦ toParity (F a)) (toParity L)).hom =
      (evalSubstIso g F L).hom ≫
        (pivotalComparisonIso (fun a ↦ eval g (F a)) L).hom ≫
        (ParityWord.evalCongrIso (fun a ↦ pivotalComparisonIso g (F a)) (toParity L)).hom) :
    (pivotalComparisonIso g (subst F (p :: L))).hom ≫
        eqToHom (congrArg (ParityWord.eval g) (toParity_subst F (p :: L))) ≫
        (eqToHom (congrArg (ParityWord.eval g)
            (ParityWord.subst_cons (fun a ↦ toParity (F a)) (p.1, (p.2 : ZMod 2))
              (toParity L))) ≫
          (ParityWord.evalAppendIso g (ParityWord.dualPow (p.2 : ZMod 2) (toParity (F p.1)))
            (ParityWord.subst (fun a ↦ toParity (F a)) (toParity L))).hom ≫
          ((ParityWord.evalDualPowIso g (p.2 : ZMod 2) (toParity (F p.1))).hom ⊗ₘ
            (ParityWord.evalSubstIso g (fun a ↦ toParity (F a)) (toParity L)).hom)) =
      (eqToHom (congrArg (eval g) (subst_cons F p L)) ≫
        (evalAppendIso g (dualPow p.2 (F p.1)) (subst F L)).hom ≫
        ((evalDualPowIso g p.2 (F p.1)).hom ⊗ₘ (evalSubstIso g F L).hom)) ≫
        ((pivotalAtomIso p.2 (eval g (F p.1))).hom ⊗ₘ
          (pivotalComparisonIso (fun a ↦ eval g (F a)) L).hom) ≫
        ((parityDualMapIso (p.2 : ZMod 2) (pivotalComparisonIso g (F p.1))).hom ⊗ₘ
          (ParityWord.evalCongrIso (fun a ↦ pivotalComparisonIso g (F a))
            (toParity L)).hom) := by
  rw [← cancel_epi (eqToHom (congrArg (eval g) (subst_cons F p L).symm))]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (eqToHom_comp_pivotalComparisonIso_hom g (subst_cons F p L).symm)]
  simp only [eqToHom_trans_assoc]
  rw [reassoc_of% (eqToHom_toParity_append_comp_evalAppendIso_hom g
      (toParity_dualPow p.2 (F p.1)) (toParity_subst F L) (by simp)),
    reassoc_of% (pivotalComparisonIso_append_hom g (dualPow p.2 (F p.1)) (subst F L)),
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [pivotalComparisonIso_dualPow_hom g p.2 (F p.1), ih]

/-- **Multi-port substitution coherence of `pivotalComparisonIso`**: substituting winding words for
generators commutes with `pivotalComparisonIso`, `ParityWord.evalSubstIso`, and
`ParityWord.evalCongrIso`. -/
@[reassoc]
theorem pivotalComparisonIso_subst_hom {β : Type w'} (g : β → C) (F : α → WindingWord β) :
    (L : WindingWord α) →
      (pivotalComparisonIso g (subst F L)).hom ≫
          eqToHom (congrArg (ParityWord.eval g) (toParity_subst F L)) ≫
          (ParityWord.evalSubstIso g (fun a ↦ toParity (F a)) (toParity L)).hom =
        (evalSubstIso g F L).hom ≫
          (pivotalComparisonIso (fun a ↦ eval g (F a)) L).hom ≫
          (ParityWord.evalCongrIso (fun a ↦ pivotalComparisonIso g (F a)) (toParity L)).hom
  | [] => by
    have hNil : ∀ (W : WindingWord β) (hw : W = []) (P : ParityWord β) (hp : P = [])
        (hwp : toParity W = P),
        (pivotalComparisonIso g W).hom ≫
          eqToHom (congrArg (ParityWord.eval g) hwp) ≫
          eqToHom (congrArg (ParityWord.eval g) hp) =
        eqToHom (congrArg (eval g) hw) := by
      rintro _ rfl _ rfl hwp
      have hStep : 𝟙 (𝟙_ C) ≫ eqToHom (congrArg (ParityWord.eval g) hwp) ≫ 𝟙 (𝟙_ C) =
          𝟙 (𝟙_ C) := by simp
      exact hStep
    have hL : (ParityWord.evalSubstIso g (fun a ↦ toParity (F a)) (toParity [])).hom =
        eqToHom (congrArg (ParityWord.eval g)
          (ParityWord.subst_nil (fun a ↦ toParity (F a)))) :=
      congrArg Iso.hom (ParityWord.evalSubstIso_nil g (fun a ↦ toParity (F a)))
    have hR1 : (evalSubstIso g F []).hom = eqToHom (congrArg (eval g) (subst_nil F)) :=
      congrArg Iso.hom (evalSubstIso_nil g F)
    have hR3 : (ParityWord.evalCongrIso (fun a ↦ pivotalComparisonIso g (F a))
        (toParity [])).hom = 𝟙 (𝟙_ C) :=
      congrArg Iso.hom (ParityWord.evalCongrIso_nil (fun a ↦ pivotalComparisonIso g (F a)))
    exact (_ ≫= (_ ≫= hL)).trans ((hNil _ (subst_nil F) _ (ParityWord.subst_nil _)
      (toParity_subst F [])).trans ((Category.comp_id _).symm.trans
        ((hR1.symm =≫ _).trans (_ ≫= ((Category.id_comp _).symm.trans (_ ≫= hR3.symm))))))
  | p :: L => by
    let F' : α → ParityWord β := fun a ↦ toParity (F a)
    have ih := pivotalComparisonIso_subst_hom g F L
    have hL : (ParityWord.evalSubstIso g F' (toParity (p :: L))).hom =
        eqToHom (congrArg (ParityWord.eval g)
          (ParityWord.subst_cons F' (p.1, (p.2 : ZMod 2)) (toParity L))) ≫
          (ParityWord.evalAppendIso g (ParityWord.dualPow (p.2 : ZMod 2) (F' p.1))
            (ParityWord.subst F' (toParity L))).hom ≫
          ((ParityWord.evalDualPowIso g (p.2 : ZMod 2) (F' p.1)).hom ⊗ₘ
            (ParityWord.evalSubstIso g F' (toParity L)).hom) :=
      congrArg Iso.hom (ParityWord.evalSubstIso_cons g F' (p.1, (p.2 : ZMod 2)) (toParity L))
    have hR1 : (evalSubstIso g F (p :: L)).hom =
        eqToHom (congrArg (eval g) (subst_cons F p L)) ≫
          (evalAppendIso g (dualPow p.2 (F p.1)) (subst F L)).hom ≫
          ((evalDualPowIso g p.2 (F p.1)).hom ⊗ₘ (evalSubstIso g F L).hom) :=
      congrArg Iso.hom (evalSubstIso_cons g F p L)
    have hR3 : (ParityWord.evalCongrIso (fun a ↦ pivotalComparisonIso g (F a))
        (toParity (p :: L))).hom =
        (parityDualMapIso (p.2 : ZMod 2) (pivotalComparisonIso g (F p.1))).hom ⊗ₘ
          (ParityWord.evalCongrIso (fun a ↦ pivotalComparisonIso g (F a)) (toParity L)).hom :=
      congrArg Iso.hom (ParityWord.evalCongrIso_cons (fun a ↦ pivotalComparisonIso g (F a))
        (p.1, (p.2 : ZMod 2)) (toParity L))
    exact (_ ≫= (_ ≫= hL)).trans ((pivotalComparisonIso_subst_cons_mid g F p L ih).trans
      ((hR1.symm =≫ _).trans (_ ≫= (_ ≫= hR3.symm))))

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
