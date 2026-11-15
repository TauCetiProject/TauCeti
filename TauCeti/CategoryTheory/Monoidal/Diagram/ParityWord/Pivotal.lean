/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.ParityWord.Evaluation
public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Evaluation
public import TauCeti.CategoryTheory.Monoidal.Pivotal.LeftDual
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Torsor
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Basic

/-!
# Pivotal comparison between integer winding words and parity words

In a general rigid monoidal category `C`, evaluating `WindingWord α` requires keeping track of the
full integer dual-winding level `n : ℤ` on every boundary port (`WindingWord.evalObj`). Once `C` is
equipped with a `PivotalCategory C` structure `φ_X : X ≅ Xᘁᘁ`, every even dual shift is canonically
identified with `X` and every odd dual shift — including negative levels via `leftDualIsoRightDual`
— is canonically identified with `Xᘁ`. Boundary objects therefore depend up to canonical pivotal
isomorphism only on their `ZMod 2` parity reduction `ParityWord α` (`ParityWord.evalObj`, defined in
`TauCeti.CategoryTheory.Monoidal.Diagram.ParityWord.Evaluation`).

Crucially, this identification is *data*, not a definitional equality: the passage from level `0`
to level `2` evaluates to `φ_X` rather than `𝟙 X`, and twisting `P : PivotalCategory C` by a
monoidal natural automorphism `u` of `𝟭 C` scales that identification by `u_X`
(`TauCeti.smul_pivotalAtomIso_two_inv`).

## Main declarations

* `TauCeti.pivotalAtomIso`: the `eqToHom`-free isomorphism
  `iteratedDual X n ≅ parityDual X (n : ZMod 2)` for every `n : ℤ`, with explicit values at
  `0`, `1`, `2`, `3` (via Freyd–Yetter), and `-1`, right- and left-dual step coherence
  (`pivotalAtomIsoAux_rightDual`, `pivotalAtomIsoAux_leftDual`), torsor twisting
  (`smul_pivotalAtomIso_two_inv`), and pivotal functor characterization
  (`CategoryTheory.Functor.isPivotal_iff_map_pivotalAtomIso_two_inv`);
* `TauCeti.WindingWord.pivotalComparisonIso`: the `eqToHom`-free boundary isomorphism
  `WindingWord.evalObj f L ≅ ParityWord.evalObj f L.toParity`, coherent with the empty word,
  concatenation (`pivotalComparisonIso_append_hom`), right duality
  (`pivotalComparisonIso_rightDual_hom`), and left duality (`pivotalComparisonIso_leftDual_hom`);
* `TauCeti.RigidObject.evalObjNormalizeParityIso`: direct comparison from `RigidObject.evalObj` to
  `ParityWord.evalObj` along `RigidObject.normalizeParity`;
* `TauCeti.WindingWord.transportCoupon`: transport of coupon morphisms from integer winding
  boundaries to parity boundaries, preserving identities, composition, tensor products, half-turn
  single mates (both right and left), and full-turn double mates conjugated by `pivotalIsoApp`.

## References

* [P. Freyd and D. Yetter, *Braided compact closed categories with applications to low dimensional
  topology*][freydyetter1989], Theorem 4.4
* [A. Joyal and R. Street, *Planar diagrams and tensor algebra*][joyalStreet1988]
* [P. Selinger, *A survey of graphical languages for monoidal categories*][selinger2011], §4.4
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite ExactPairing

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section PivotalParity

variable [RigidCategory C] [PivotalCategory C]

/-! ### Atomic pivotal comparison across all integer dual levels -/

private theorem zmod2_succ_eq_zero_imp {k : ℕ} (h : ((k + 1 : ℕ) : ZMod 2) = 0) :
    (k : ZMod 2) = 1 := by
  have h' : (k : ZMod 2) + 1 = 0 := by simpa [Nat.cast_add] using h
  revert h'
  generalize (k : ZMod 2) = z
  revert z
  decide

private theorem zmod2_succ_eq_one_imp {k : ℕ} (h : ((k + 1 : ℕ) : ZMod 2) = 1) :
    (k : ZMod 2) = 0 := by
  have h' : (k : ZMod 2) + 1 = 1 := by simpa [Nat.cast_add] using h
  revert h'
  generalize (k : ZMod 2) = z
  revert z
  decide

private theorem zmod2_negSucc_succ_eq_zero_imp {k : ℕ}
    (h : (Int.negSucc (k + 1) : ZMod 2) = 0) : (Int.negSucc k : ZMod 2) = 1 := by
  have h' : (Int.negSucc k : ZMod 2) - 1 = 0 := by
    rw [show Int.negSucc (k + 1) = Int.negSucc k - 1 from rfl, Int.cast_sub, Int.cast_one] at h
    exact h
  revert h'
  generalize (Int.negSucc k : ZMod 2) = z
  revert z
  decide

private theorem zmod2_negSucc_succ_eq_one_imp {k : ℕ}
    (h : (Int.negSucc (k + 1) : ZMod 2) = 1) : (Int.negSucc k : ZMod 2) = 0 := by
  have h' : (Int.negSucc k : ZMod 2) - 1 = 1 := by
    rw [show Int.negSucc (k + 1) = Int.negSucc k - 1 from rfl, Int.cast_sub, Int.cast_one] at h
    exact h
  revert h'
  generalize (Int.negSucc k : ZMod 2) = z
  revert z
  decide

private noncomputable def pivotalRightPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((k : ZMod 2) = ε) → (iteratedRightDual X k ≅ parityDual X ε)
  | 0, ⟨0, _⟩, _ => Iso.refl X
  | 0, ⟨1, _⟩, h => absurd (show ((0 : ℕ) : ZMod 2).val = 1 from congrArg Fin.val h) (by decide)
  | k + 1, ⟨0, _⟩, h =>
      have hk : (k : ZMod 2) = 1 := zmod2_succ_eq_zero_imp (Fin.ext (congrArg Fin.val h))
      ((rightDualFunctor C).mapIso (pivotalRightPowAuxIso X k 1 hk).symm).unmop.unop ≪≫
        (pivotalIsoApp X).symm
  | k + 1, ⟨1, _⟩, h =>
      have hk : (k : ZMod 2) = 0 := zmod2_succ_eq_one_imp (Fin.ext (congrArg Fin.val h))
      ((rightDualFunctor C).mapIso (pivotalRightPowAuxIso X k 0 hk).symm).unmop.unop

private noncomputable def pivotalLeftPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((Int.negSucc k : ZMod 2) = ε) →
      (iteratedLeftDual X (k + 1) ≅ parityDual X ε)
  | 0, ⟨0, _⟩, h =>
      absurd (show (Int.negSucc 0 : ZMod 2).val = 0 from congrArg Fin.val h) (by decide)
  | 0, ⟨1, _⟩, _ => leftDualIsoRightDual X
  | k + 1, ⟨0, _⟩, h =>
      have hk : (Int.negSucc k : ZMod 2) = 1 :=
        zmod2_negSucc_succ_eq_zero_imp (Fin.ext (congrArg Fin.val h))
      ((leftDualFunctor C).mapIso (pivotalLeftPowAuxIso X k 1 hk).symm).unmop.unop ≪≫
        (leftDualRightDualIso C).app X
  | k + 1, ⟨1, _⟩, h =>
      have hk : (Int.negSucc k : ZMod 2) = 0 :=
        zmod2_negSucc_succ_eq_one_imp (Fin.ext (congrArg Fin.val h))
      ((leftDualFunctor C).mapIso (pivotalLeftPowAuxIso X k 0 hk).symm).unmop.unop ≪≫
        leftDualIsoRightDual X

/-- Proof-irrelevant auxiliary form of `pivotalAtomIso` with an explicit target parity `ε : ZMod 2`
witnessed by `(n : ZMod 2) = ε`, avoiding `eqToHom` when rewriting parity arithmetic. -/
noncomputable def pivotalAtomIsoAux (X : C) :
    (n : ℤ) → (ε : ZMod 2) → ((n : ZMod 2) = ε) → (iteratedDual X n ≅ parityDual X ε)
  | .ofNat k, ε, h => pivotalRightPowAuxIso X k ε (by simpa using h)
  | .negSucc k, ε, h => pivotalLeftPowAuxIso X k ε h

/-- Explicit `eqToHom`-free pivotal isomorphism `iteratedDual X n ≅ parityDual X (n : ZMod 2)`
reducing any integer dual-winding level `n : ℤ` to its `ZMod 2` parity representative `X` or `Xᘁ`.
-/
noncomputable def pivotalAtomIso (X : C) (n : ℤ) :
    iteratedDual X n ≅ parityDual X (n : ZMod 2) :=
  pivotalAtomIsoAux X n (n : ZMod 2) rfl

@[simp]
theorem pivotalAtomIso_zero (X : C) : pivotalAtomIso X 0 = Iso.refl X := by rfl

@[simp]
theorem pivotalAtomIso_one (X : C) :
    pivotalAtomIso X 1 = Iso.refl (RightRigidCategory.rightDual X).rightDual := by
  ext
  exact rightAdjointMate_id (X := X)

/-- At winding level `2`, `pivotalAtomIso X 2 : Xᘁᘁ ≅ X` is `(pivotalIsoApp X).symm` — not the
identity — so identifying level `0` with level `2` evaluates to `(pivotalIsoApp X).hom`. -/
@[simp]
theorem pivotalAtomIso_two (X : C) :
    pivotalAtomIso X 2 = (pivotalIsoApp X).symm := by
  ext
  exact ((congrArg (fun k ↦ ((rightDualFunctor C).map k).unmop.unop)
      (congrArg Iso.inv (pivotalAtomIso_one X))) =≫ _).trans
    ((rightAdjointMate_id (X := (RightRigidCategory.rightDual X).rightDual) =≫ _).trans
      (Category.id_comp _))

/-- By the Freyd–Yetter identity, the level-`3` comparison `Xᘁᘁᘁ ⟶ Xᘁ` equals the inverse pivotal
component at `Xᘁ`. -/
theorem pivotalAtomIso_three_hom (X : C) :
    (pivotalAtomIso X 3).hom =
      (pivotalIsoApp (RightRigidCategory.rightDual X).rightDual).inv := by
  change ((rightDualFunctor C).map (pivotalAtomIso X 2).inv).unmop.unop = _
  rw [pivotalAtomIso_two]
  exact (pivotalIsoApp_rightDual_inv X).symm

@[simp]
theorem pivotalAtomIso_neg_one (X : C) :
    pivotalAtomIso X (-1) = leftDualIsoRightDual X := by rfl

omit [PivotalCategory C] in
/-- Twisting `P : PivotalCategory C` by a monoidal natural automorphism `u` of `𝟭 C` scales the
level-`0`-to-level-`2` pivotal identification `(pivotalAtomIso X 2).inv : X ⟶ Xᘁᘁ` by `u_X`. -/
theorem smul_pivotalAtomIso_two_inv (u : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (P : PivotalCategory C) (X : C) :
    (@pivotalAtomIso C _ _ _ (u • P) X 2).inv =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso.hom.app X ≫
        (@pivotalAtomIso C _ _ _ P X 2).inv := by
  rw [@pivotalAtomIso_two C _ _ _ (u • P) X, @pivotalAtomIso_two C _ _ _ P X,
    Iso.symm_inv, Iso.symm_inv, PivotalCategory.smul_pivotalIsoApp, Iso.trans_hom, Iso.app_hom]
  rfl

/-! ### Step coherence of `pivotalAtomIso` with right and left duality -/

private theorem rightDualMap_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv (X : C) :
    ((rightDualFunctor C).map (leftDualIsoRightDual X).inv).unmop.unop ≫ (pivotalIsoApp X).inv =
      (rightDualLeftDualIso C).hom.app X := by
  refine (((@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual _)
    (RightRigidCategory.rightDual _) (leftDualIsoRightDual X).inv) =≫ _).trans ?_).trans
      (rightDualLeftDualIso_hom_app X).symm
  rw [Iso.comp_inv_eq, ← rightMate_leftDualIsoRightDual_inv X, rightDualIso_hom, ← comp_rightMate,
    Category.comp_id]

omit [PivotalCategory C] in
private theorem rightDualMap_leftDualRightDualIso_inv_app (X : C) :
    ((rightDualFunctor C).map ((leftDualRightDualIso C).inv.app X)).unmop.unop =
      (rightDualLeftDualIso C).hom.app (RightRigidCategory.rightDual X).rightDual := by
  refine (@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual _)
    (RightRigidCategory.rightDual _) ((leftDualRightDualIso C).inv.app X)).trans ?_
  rw [leftDualRightDualIso_inv_app, rightDualLeftDualIso_hom_app]
  exact rightMate_leftDualIso_inv _ _ _

private theorem leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv (X : C) :
    (leftDualIsoRightDual (RightRigidCategory.rightDual X).rightDual).hom ≫
        (pivotalIsoApp X).inv =
      (leftDualRightDualIso C).hom.app X := by
  refine @leftDualHom_ext C _ _ X (RightRigidCategory.rightDual X).rightDual _
    (RightRigidCategory.rightDual X).exact _ _ ?_
  rw [leftDualRightDualIso_hom_app, leftDualIso_hom, leftMate_comp_evaluation, id_whiskerRight,
    Category.id_comp, MonoidalCategory.whiskerLeft_comp_assoc,
    ← rightAdjointMate_comp_evaluation (pivotalIsoApp X).inv, ← pivotalIsoApp_rightDual X]
  exact whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation
    (RightRigidCategory.rightDual X).rightDual

omit [PivotalCategory C] in
private theorem rightDualFunctor_map_comp_unmop_unop {A B D : C} (u : A ⟶ B) (v : B ⟶ D) :
    ((rightDualFunctor C).map (u ≫ v)).unmop.unop =
      ((rightDualFunctor C).map v).unmop.unop ≫ ((rightDualFunctor C).map u).unmop.unop := by
  rw [Functor.map_comp, unmop_comp, unop_comp]

omit [PivotalCategory C] in
private theorem leftDualFunctor_map_comp_unmop_unop {A B D : C} (u : A ⟶ B) (v : B ⟶ D) :
    ((leftDualFunctor C).map (u ≫ v)).unmop.unop =
      ((leftDualFunctor C).map v).unmop.unop ≫ ((leftDualFunctor C).map u).unmop.unop := by
  rw [Functor.map_comp, unmop_comp, unop_comp]

/-- **Right-dual step coherence of `pivotalAtomIsoAux`**: taking the chosen right dual of an atom
at level `n` and reducing modulo two agrees with advancing the level to `n + 1` first. -/
theorem pivotalAtomIsoAux_rightDual (X : C) (n : ℤ) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
    (h' : ((n + 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualRightDualIso X n).hom ≫ (pivotalAtomIsoAux X (n + 1) (ε + 1) h').hom =
      ((rightDualFunctor C).map (pivotalAtomIsoAux X n ε h).inv).unmop.unop ≫
        (parityDualRightDualIso X ε).hom := by
  cases n with
  | ofNat k =>
    rcases ParityWord.eq_zero_or_one ε with rfl | rfl
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact Category.id_comp _
  | negSucc k =>
    -- Negative levels cancel the outermost left dual against the new right dual.
    cases k with
    | zero =>
      rcases ParityWord.eq_zero_or_one ε with rfl | rfl
      · exact absurd (show (Int.negSucc 0 : ZMod 2).val = 0 from congrArg Fin.val h) (by decide)
      · exact (Category.comp_id _).trans
          (rightDualMap_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv X).symm
    | succ k =>
      rcases ParityWord.eq_zero_or_one ε with rfl | rfl
      · have hk : (Int.negSucc k : ZMod 2) = 1 :=
          zmod2_negSucc_succ_eq_zero_imp (Fin.ext (congrArg Fin.val h))
        let q := (pivotalLeftPowAuxIso X k 1 hk).hom
        exact ((Category.comp_id _).trans
          ((rightDualFunctor_map_comp_unmop_unop ((leftDualRightDualIso C).inv.app X)
            ((leftDualFunctor C).map q).unmop.unop).trans
            ((_ ≫= rightDualMap_leftDualRightDualIso_inv_app X).trans
              ((rightDualLeftDualIso C).hom.naturality q)))).symm
      · have hk : (Int.negSucc k : ZMod 2) = 0 :=
          zmod2_negSucc_succ_eq_one_imp (Fin.ext (congrArg Fin.val h))
        let q := (pivotalLeftPowAuxIso X k 0 hk).hom
        exact (((rightDualFunctor_map_comp_unmop_unop (leftDualIsoRightDual X).inv
            ((leftDualFunctor C).map q).unmop.unop =≫ _).trans
          ((Category.assoc _ _ _).trans
            ((_ ≫= rightDualMap_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv X).trans
              ((rightDualLeftDualIso C).hom.naturality q))))).symm

private theorem eqToHom_comp_pivotalAtomIsoAux_ofNat (X : C) (m : ℤ) (k : ℕ) (δ : ZMod 2)
    (hm : m = Int.ofNat k) (h' : (m : ZMod 2) = δ) :
    eqToHom (congrArg (iteratedDual X) hm.symm) ≫ (pivotalAtomIsoAux X m δ h').hom =
      (pivotalRightPowAuxIso X k δ (by simpa [hm] using h')).hom := by
  subst hm
  exact Category.id_comp _

private theorem pivotalAtomIsoAux_leftDual_succ (X : C) (k : ℕ) (ε : ZMod 2)
    (h : ((Int.ofNat (k + 1) : ℤ) : ZMod 2) = ε)
    (h' : ((Int.ofNat (k + 1) - 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualLeftDualIso X (Int.ofNat (k + 1))).hom ≫
        (pivotalAtomIsoAux X (Int.ofNat (k + 1) - 1) (ε + 1) h').hom =
      (leftDualIsoRightDual (iteratedDual X (Int.ofNat (k + 1)))).hom ≫
        ((rightDualFunctor C).map (pivotalAtomIsoAux X (Int.ofNat (k + 1)) ε h).inv).unmop.unop ≫
        (parityDualRightDualIso X ε).hom := by
  have hmate : ∀ {A B : C} (g : B ⟶ A),
      (leftDualIsoRightDual A).hom ≫ ((rightDualFunctor C).map g).unmop.unop =
        ((leftDualFunctor C).map g).unmop.unop ≫ (leftDualIsoRightDual B).hom :=
    fun g ↦ (leftAdjointMate_comp_leftDualIsoRightDual_hom g).symm
  -- Cancel `ᘁ(Yᘁ) ≅ Y` on the left-hand side and compare via Freyd–Yetter on the right.
  have hsub : (Int.ofNat (k + 1) - 1 : ℤ) = Int.ofNat k := add_sub_cancel_right (k : ℤ) 1
  have hstep := eqToHom_comp_pivotalAtomIsoAux_ofNat X (Int.ofNat (k + 1) - 1) k (ε + 1) hsub h'
  have heq : (iteratedDualLeftDualIso X (Int.ofNat (k + 1))).hom ≫
        (pivotalAtomIsoAux X (Int.ofNat (k + 1) - 1) (ε + 1) h').hom =
      (leftDualRightDualIso C).hom.app (iteratedRightDual X k) ≫
        (pivotalRightPowAuxIso X k (ε + 1) (by simpa [hsub] using h')).hom :=
    (Category.assoc _ _ _).trans (_ ≫= hstep)
  refine heq.trans ?_
  rcases ParityWord.eq_zero_or_one ε with rfl | rfl
  · have hk : (k : ZMod 2) = 1 := zmod2_succ_eq_zero_imp (Fin.ext (congrArg Fin.val h))
    let p := (pivotalRightPowAuxIso X k 1 hk).hom
    let g := (pivotalAtomIsoAux X (Int.ofNat (k + 1)) 0 h).inv
    have h1 : (leftDualIsoRightDual (iteratedDual X (Int.ofNat (k + 1)))).hom ≫
          ((rightDualFunctor C).map g).unmop.unop ≫ (parityDualRightDualIso X 0).hom =
        ((leftDualFunctor C).map g).unmop.unop ≫ (leftDualIsoRightDual X).hom :=
      (_ ≫= Category.comp_id _).trans (hmate g)
    have h2 : ((leftDualFunctor C).map g).unmop.unop =
        (leftDualRightDualFunctor C).map p ≫
          ((leftDualFunctor C).map (pivotalIsoApp X).hom).unmop.unop :=
      leftDualFunctor_map_comp_unmop_unop (pivotalIsoApp X).hom
        ((rightDualFunctor C).map p).unmop.unop
    have h3 : ((leftDualFunctor C).map (pivotalIsoApp X).hom).unmop.unop ≫
          (leftDualIsoRightDual X).hom =
        (leftDualRightDualIso C).hom.app (RightRigidCategory.rightDual X).rightDual :=
      (hmate (pivotalIsoApp X).hom).symm.trans
        ((_ ≫= (pivotalIsoApp_rightDual_inv X).symm).trans
          (leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv
            (RightRigidCategory.rightDual X).rightDual))
    exact (h1.trans ((h2 =≫ _).trans
      ((Category.assoc _ _ _).trans
        ((_ ≫= h3).trans ((leftDualRightDualIso C).hom.naturality p))))).symm
  · have hk : (k : ZMod 2) = 0 := zmod2_succ_eq_one_imp (Fin.ext (congrArg Fin.val h))
    let p := (pivotalRightPowAuxIso X k 0 hk).hom
    let g := (pivotalAtomIsoAux X (Int.ofNat (k + 1)) 1 h).inv
    exact ((Category.assoc _ _ _).symm.trans
      ((hmate g =≫ _).trans
        ((Category.assoc _ _ _).trans
          ((_ ≫= leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv X).trans
            ((leftDualRightDualIso C).hom.naturality p))))).symm

/-- **Left-dual step coherence of `pivotalAtomIsoAux`**: taking the chosen left dual of an atom at
level `n` and reducing modulo two agrees with identifying left and right duals via
`leftDualIsoRightDual` followed by `parityDualRightDualIso`. -/
theorem pivotalAtomIsoAux_leftDual (X : C) (n : ℤ) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
    (h' : ((n - 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualLeftDualIso X n).hom ≫ (pivotalAtomIsoAux X (n - 1) (ε + 1) h').hom =
      (leftDualIsoRightDual (iteratedDual X n)).hom ≫
        ((rightDualFunctor C).map (pivotalAtomIsoAux X n ε h).inv).unmop.unop ≫
        (parityDualRightDualIso X ε).hom := by
  have hmate : ∀ {A B : C} (g : B ⟶ A),
      (leftDualIsoRightDual A).hom ≫ ((rightDualFunctor C).map g).unmop.unop =
        ((leftDualFunctor C).map g).unmop.unop ≫ (leftDualIsoRightDual B).hom :=
    fun g ↦ (leftAdjointMate_comp_leftDualIsoRightDual_hom g).symm
  cases n with
  | negSucc k =>
    rcases ParityWord.eq_zero_or_one ε with rfl | rfl
    · exact (Category.id_comp _).trans
        ((hmate (pivotalAtomIsoAux X (Int.negSucc k) 0 h).inv).symm.trans
          (_ ≫= (Category.comp_id _).symm))
    · exact (Category.id_comp _).trans
        ((_ ≫= (leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv X).symm).trans
          ((Category.assoc _ _ _).symm.trans
            (((hmate (pivotalAtomIsoAux X (Int.negSucc k) 1 h).inv).symm =≫ _).trans
              (Category.assoc _ _ _))))
  | ofNat k =>
    cases k with
    | zero =>
      rcases ParityWord.eq_zero_or_one ε with rfl | rfl
      · exact (Category.id_comp _).trans
          ((Category.comp_id _).symm.trans
            (_ ≫= ((rightAdjointMate_id (X := X)).symm.trans (Category.comp_id _).symm)))
      · exact absurd (show ((0 : ℕ) : ZMod 2).val = 1 from congrArg Fin.val h) (by decide)
    | succ k =>
      exact pivotalAtomIsoAux_leftDual_succ X k ε h h'

/-! ### Word-level pivotal comparison and coherence -/

namespace WindingWord

/-- Explicit `eqToHom`-free pivotal comparison isomorphism
`WindingWord.evalObj f L ≅ ParityWord.evalObj f L.toParity`, applying `pivotalAtomIso` port-by-port
and reindexing the list along `WindingWord.toParity`. -/
noncomputable def pivotalComparisonIso {α : Type*} (f : α → C) (L : WindingWord α) :
    evalObj f L ≅ ParityWord.evalObj f L.toParity :=
  tensorListCongrIso (fun p : α × ℤ ↦ pivotalAtomIso (f p.1) p.2) L ≪≫
    tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
      (fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) L

/-- On the empty boundary word, `pivotalComparisonIso` is the identity on `𝟙_ C`. -/
@[simp]
theorem pivotalComparisonIso_nil_hom {α : Type*} (f : α → C) :
    (pivotalComparisonIso f ([] : WindingWord α)).hom = 𝟙 (𝟙_ C) := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_hom]
  rw [tensorListCongrIso_hom, tensorListCongrHom_nil, tensorListMapIso_nil, Iso.refl_hom,
    Category.comp_id]

@[simp]
theorem pivotalComparisonIso_nil_inv {α : Type*} (f : α → C) :
    (pivotalComparisonIso f ([] : WindingWord α)).inv = 𝟙 (𝟙_ C) := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_inv]
  rw [tensorListCongrIso_inv, tensorListCongrHom_nil, tensorListMapIso_nil, Iso.refl_inv,
    Category.comp_id]

/-- Recursive step of `pivotalComparisonIso` on `p :: L`: it is the tensor product of
`pivotalAtomIso` at the head port with `pivotalComparisonIso` on the tail. -/
theorem pivotalComparisonIso_cons_hom {α : Type*} (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    (pivotalComparisonIso f (p :: L)).hom =
      (pivotalAtomIso (f p.1) p.2).hom ⊗ₘ (pivotalComparisonIso f L).hom := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_hom]
  rw [tensorListCongrIso_hom, tensorListCongrIso_hom, tensorListCongrHom_cons,
    tensorListMapIso_cons_hom, ← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]

/-- Recursive step of the inverse of `pivotalComparisonIso` on `p :: L`. -/
theorem pivotalComparisonIso_cons_inv {α : Type*} (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    (pivotalComparisonIso f (p :: L)).inv =
      (pivotalAtomIso (f p.1) p.2).inv ⊗ₘ (pivotalComparisonIso f L).inv := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_inv]
  rw [tensorListCongrIso_inv, tensorListCongrIso_inv, tensorListCongrHom_cons,
    tensorListMapIso_cons_inv, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]

private theorem pivotalComparisonIso_append_nil_hom {α : Type*} (f : α → C) (M : WindingWord α) :
    (evalObjAppendIso f [] M).hom ≫ (pivotalComparisonIso f ([] ++ M)).hom =
      ((pivotalComparisonIso f []).hom ⊗ₘ (pivotalComparisonIso f M).hom) ≫
        (ParityWord.evalObjAppendIso f (toParity []) M.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_append [] M).symm) := by
  have hlhs : (evalObjAppendIso f [] M).hom ≫ (pivotalComparisonIso f ([] ++ M)).hom =
      (λ_ (evalObj f M)).hom ≫ (pivotalComparisonIso f M).hom :=
    congrArg Iso.hom (evalObjAppendIso_nil f M) =≫ (pivotalComparisonIso f M).hom
  have hrhs : ((pivotalComparisonIso f []).hom ⊗ₘ (pivotalComparisonIso f M).hom) ≫
        (ParityWord.evalObjAppendIso f (toParity []) M.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_append [] M).symm) =
      (𝟙 (𝟙_ C) ⊗ₘ (pivotalComparisonIso f M).hom) ≫
        (λ_ (ParityWord.evalObj f M.toParity)).hom :=
    ((congrArg (fun u : 𝟙_ C ⟶ 𝟙_ C ↦ u ⊗ₘ (pivotalComparisonIso f M).hom)
        (pivotalComparisonIso_nil_hom f)) =≫ _).trans
      (_ ≫= ((congrArg Iso.hom (ParityWord.evalObjAppendIso_nil f M.toParity) =≫ _).trans
        ((_ ≫= eqToHom_refl _ _).trans (Category.comp_id _))))
  refine hlhs.trans (Eq.trans ?_ hrhs.symm)
  rw [id_tensorHom, leftUnitor_naturality]

/-- **Concatenation coherence of `pivotalComparisonIso`**: tensoring two evaluated winding words
and reducing modulo two commutes with concatenating first. -/
@[reassoc]
theorem pivotalComparisonIso_append_hom {α : Type*} (f : α → C) (L M : WindingWord α) :
    (evalObjAppendIso f L M).hom ≫ (pivotalComparisonIso f (L ++ M)).hom =
      ((pivotalComparisonIso f L).hom ⊗ₘ (pivotalComparisonIso f M).hom) ≫
        (ParityWord.evalObjAppendIso f L.toParity M.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_append L M).symm) := by
  induction L with
  | nil => exact pivotalComparisonIso_append_nil_hom f M
  | cons p L ih =>
    -- Expand `evalObjAppendIso` and `pivotalComparisonIso` on `p :: L` and use naturality of `α_`.
    have hlhs : (evalObjAppendIso f (p :: L) M).hom ≫
          (pivotalComparisonIso f ((p :: L) ++ M)).hom =
        ((α_ (iteratedDual (f p.1) p.2) (evalObj f L) (evalObj f M)).hom ≫
          (iteratedDual (f p.1) p.2 ◁ (evalObjAppendIso f L M).hom)) ≫
          ((pivotalAtomIso (f p.1) p.2).hom ⊗ₘ (pivotalComparisonIso f (L ++ M)).hom) :=
      (evalObjAppendIso_cons_hom f p L M =≫ _).trans
        (_ ≫= pivotalComparisonIso_cons_hom f p (L ++ M))
    have heq : eqToHom (congrArg (ParityWord.evalObj f) (toParity_append (p :: L) M).symm) =
        parityDual (f p.1) (p.2 : ZMod 2) ◁
          eqToHom (congrArg (ParityWord.evalObj f) (toParity_append L M).symm) :=
      (MonoidalCategory.whiskerLeft_eqToHom (parityDual (f p.1) (p.2 : ZMod 2))
        (congrArg (ParityWord.evalObj f) (toParity_append L M).symm)).symm
    have hrhs : ((pivotalComparisonIso f (p :: L)).hom ⊗ₘ (pivotalComparisonIso f M).hom) ≫
          (ParityWord.evalObjAppendIso f (toParity (p :: L)) M.toParity).hom ≫
          eqToHom (congrArg (ParityWord.evalObj f) (toParity_append (p :: L) M).symm) =
        (((pivotalAtomIso (f p.1) p.2).hom ⊗ₘ (pivotalComparisonIso f L).hom) ⊗ₘ
          (pivotalComparisonIso f M).hom) ≫
          ((α_ (parityDual (f p.1) (p.2 : ZMod 2)) (ParityWord.evalObj f (toParity L))
              (ParityWord.evalObj f M.toParity)).hom ≫
            (parityDual (f p.1) (p.2 : ZMod 2) ◁
              (ParityWord.evalObjAppendIso f (toParity L) M.toParity).hom)) ≫
          (parityDual (f p.1) (p.2 : ZMod 2) ◁
            eqToHom (congrArg (ParityWord.evalObj f) (toParity_append L M).symm)) :=
      ((congrArg (fun u : iteratedDual (f p.1) p.2 ⊗ evalObj f L ⟶
            parityDual (f p.1) (p.2 : ZMod 2) ⊗ ParityWord.evalObj f (toParity L) ↦
          u ⊗ₘ (pivotalComparisonIso f M).hom)
          (pivotalComparisonIso_cons_hom f p L)) =≫ _).trans
        (_ ≫= ((ParityWord.evalObjAppendIso_cons_hom f (p.1, (p.2 : ZMod 2))
          (toParity L) M.toParity =≫ _).trans (_ ≫= heq)))
    refine hlhs.trans (Eq.trans ?_ hrhs.symm)
    rw [Category.assoc, ← id_tensorHom (iteratedDual (f p.1) p.2), tensorHom_comp_tensorHom,
      Category.id_comp, ih]
    conv_lhs =>
      rw [← Category.comp_id (pivotalAtomIso (f p.1) p.2).hom, ← tensorHom_comp_tensorHom]
    rw [← associator_naturality_assoc, id_tensorHom, MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rfl

private theorem pivotalAtomIsoAux_hom_eq_comp_eqToHom (X : C) (m : ℤ) (z w : ZMod 2)
    (hz : (m : ZMod 2) = z) (hw : (m : ZMod 2) = w) (hzw : z = w) :
    (pivotalAtomIsoAux X m z hz).hom =
      (pivotalAtomIsoAux X m w hw).hom ≫ eqToHom (congrArg (parityDual X) hzw.symm) := by
  subst hzw
  exact (Category.comp_id _).symm

private theorem pivotalAtomIso_add_one_eq {X : C} (n : ℤ) :
    (iteratedDualRightDualIso X n).hom ≫ (pivotalAtomIso X (n + 1)).hom =
      ((rightDualFunctor C).map (pivotalAtomIso X n).inv).unmop.unop ≫
        (parityDualRightDualIso X (n : ZMod 2)).hom ≫
        eqToHom (congrArg (parityDual X) (by simp)) := by
  have hcast : ((n + 1 : ℤ) : ZMod 2) = (n : ZMod 2) + 1 := by simp
  have hstep := pivotalAtomIsoAux_hom_eq_comp_eqToHom X (n + 1) ((n + 1 : ℤ) : ZMod 2)
    ((n : ZMod 2) + 1) rfl hcast hcast
  exact (_ ≫= hstep).trans ((Category.assoc _ _ _).symm.trans
    (((pivotalAtomIsoAux_rightDual X n (n : ZMod 2) rfl hcast) =≫ _).trans
      (Category.assoc _ _ _)))

private theorem pivotalAtomIso_sub_one_eq {X : C} (n : ℤ) :
    (iteratedDualLeftDualIso X n).hom ≫ (pivotalAtomIso X (n - 1)).hom =
      (leftDualIsoRightDual (iteratedDual X n)).hom ≫
        ((rightDualFunctor C).map (pivotalAtomIso X n).inv).unmop.unop ≫
        (parityDualRightDualIso X (n : ZMod 2)).hom ≫
        eqToHom (congrArg (parityDual X) (by
          have hneg : (-1 : ZMod 2) = 1 := by decide
          simp [sub_eq_add_neg, hneg])) := by
  have hcast : ((n - 1 : ℤ) : ZMod 2) = (n : ZMod 2) + 1 := by
    have hneg : (-1 : ZMod 2) = 1 := by decide
    simp [sub_eq_add_neg, hneg]
  have hstep := pivotalAtomIsoAux_hom_eq_comp_eqToHom X (n - 1) ((n - 1 : ℤ) : ZMod 2)
    ((n : ZMod 2) + 1) rfl hcast hcast
  exact (_ ≫= hstep).trans ((Category.assoc _ _ _).symm.trans
    (((pivotalAtomIsoAux_leftDual X n (n : ZMod 2) rfl hcast) =≫ _).trans
      ((Category.assoc _ _ _).trans (_ ≫= Category.assoc _ _ _))))

private theorem pivotalRightDualTail {α : Type*} (f : α → C) (R : WindingWord α) :
    tensorListCongrHom (fun p : α × ℤ ↦ (iteratedDualRightDualIso (f p.1) p.2).hom) R ≫
      (tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
        (fun p : α × ℤ ↦ (p.1, p.2 + 1)) R).hom ≫
      (pivotalComparisonIso f (R.map fun p : α × ℤ ↦ (p.1, p.2 + 1))).hom =
    tensorListCongrHom (fun p : α × ℤ ↦
        ((rightDualFunctor C).map (pivotalAtomIso (f p.1) p.2).inv).unmop.unop) R ≫
      (tensorListMapIso (fun q : α × ZMod 2 ↦
          (RightRigidCategory.rightDual (parityDual (f q.1) q.2)).rightDual)
        (fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) R).hom ≫
      tensorListCongrHom (fun q : α × ZMod 2 ↦ (parityDualRightDualIso (f q.1) q.2).hom)
        R.toParity ≫
      (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
        (fun q : α × ZMod 2 ↦ (q.1, q.2 + 1)) R.toParity).hom ≫
      eqToHom (congrArg (ParityWord.evalObj f) (by
        simp [toParity, List.map_map, Function.comp_def])) := by
  induction R with
  | nil =>
    dsimp only [toParity, ParityWord.evalObj, List.map, tensorList]
    generalize_proofs
    simp [pivotalComparisonIso_nil_hom]
  | cons p R ih =>
    rw [show (pivotalComparisonIso f ((p :: R).map fun x : α × ℤ ↦ (x.1, x.2 + 1))).hom = _ from
      pivotalComparisonIso_cons_hom f (p.1, p.2 + 1) (R.map fun x : α × ℤ ↦ (x.1, x.2 + 1))]
    dsimp only [evalObj, toParity, ParityWord.evalObj, rightDualFunctor, List.map, tensorList]
      at ih ⊢
    generalize_proofs hR hpR at ih ⊢
    rw [tensorListCongrHom_cons, tensorListMapIso_cons_hom,
      tensorListCongrHom_cons, tensorListMapIso_cons_hom,
      tensorListCongrHom_cons, tensorListMapIso_cons_hom]
    rw [← id_tensorHom (iteratedDual (f p.1) (p.2 + 1)),
      ← id_tensorHom
        ((RightRigidCategory.rightDual (parityDual (f p.1) (p.2 : ZMod 2))).rightDual),
      ← id_tensorHom (parityDual (f p.1) ((p.2 : ZMod 2) + 1))]
    have heq : eqToHom hpR =
        eqToHom (congrArg (parityDual (f p.1)) (by simp)) ⊗ₘ eqToHom hR := by
      rw [tensorHom_def', MonoidalCategory.whiskerLeft_eqToHom, eqToHom_whiskerRight,
        eqToHom_trans]
    rw [heq]
    simp only [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg₂ (fun u v ↦ u ⊗ₘ v) (pivotalAtomIso_add_one_eq p.2) ih

private theorem pivotalLeftDualTail {α : Type*} (f : α → C) (R : WindingWord α) :
    tensorListCongrHom (fun p : α × ℤ ↦ (iteratedDualLeftDualIso (f p.1) p.2).hom) R ≫
      (tensorListMapIso (fun q : α × ℤ ↦ iteratedDual (f q.1) q.2)
        (fun p : α × ℤ ↦ (p.1, p.2 - 1)) R).hom ≫
      (pivotalComparisonIso f (R.map fun p : α × ℤ ↦ (p.1, p.2 - 1))).hom =
    tensorListCongrHom (fun p : α × ℤ ↦ (leftDualIsoRightDual (iteratedDual (f p.1) p.2)).hom) R ≫
      tensorListCongrHom (fun p : α × ℤ ↦
        ((rightDualFunctor C).map (pivotalAtomIso (f p.1) p.2).inv).unmop.unop) R ≫
      (tensorListMapIso (fun q : α × ZMod 2 ↦
          (RightRigidCategory.rightDual (parityDual (f q.1) q.2)).rightDual)
        (fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) R).hom ≫
      tensorListCongrHom (fun q : α × ZMod 2 ↦ (parityDualRightDualIso (f q.1) q.2).hom)
        R.toParity ≫
      (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
        (fun q : α × ZMod 2 ↦ (q.1, q.2 + 1)) R.toParity).hom ≫
      eqToHom (congrArg (ParityWord.evalObj f) (by
        have hneg : (-1 : ZMod 2) = 1 := by decide
        simp [toParity, List.map_map, Function.comp_def, sub_eq_add_neg, hneg])) := by
  induction R with
  | nil =>
    dsimp only [toParity, ParityWord.evalObj, List.map, tensorList]
    generalize_proofs
    simp [pivotalComparisonIso_nil_hom]
  | cons p R ih =>
    rw [show (pivotalComparisonIso f ((p :: R).map fun x : α × ℤ ↦ (x.1, x.2 - 1))).hom = _ from
      pivotalComparisonIso_cons_hom f (p.1, p.2 - 1) (R.map fun x : α × ℤ ↦ (x.1, x.2 - 1))]
    dsimp only [evalObj, toParity, ParityWord.evalObj, rightDualFunctor, List.map, tensorList]
      at ih ⊢
    generalize_proofs hR hpR at ih ⊢
    rw [tensorListCongrHom_cons, tensorListMapIso_cons_hom,
      tensorListCongrHom_cons, tensorListCongrHom_cons, tensorListMapIso_cons_hom,
      tensorListCongrHom_cons, tensorListMapIso_cons_hom]
    rw [← id_tensorHom (iteratedDual (f p.1) (p.2 - 1)),
      ← id_tensorHom
        ((RightRigidCategory.rightDual (parityDual (f p.1) (p.2 : ZMod 2))).rightDual),
      ← id_tensorHom (parityDual (f p.1) ((p.2 : ZMod 2) + 1))]
    have heq : eqToHom hpR =
        eqToHom (congrArg (parityDual (f p.1)) (by
          have hneg : (-1 : ZMod 2) = 1 := by decide
          simp [sub_eq_add_neg, hneg])) ⊗ₘ eqToHom hR := by
      rw [tensorHom_def', MonoidalCategory.whiskerLeft_eqToHom, eqToHom_whiskerRight,
        eqToHom_trans]
    rw [heq]
    simp only [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg₂ (fun u v ↦ u ⊗ₘ v) (pivotalAtomIso_sub_one_eq p.2) ih

private theorem eqToHom_comp_pivotalComparisonIso_hom {α : Type*} (f : α → C)
    {W₁ W₂ : WindingWord α} (hw : W₁ = W₂) :
    eqToHom (congrArg (evalObj f) hw) ≫ (pivotalComparisonIso f W₂).hom =
      (pivotalComparisonIso f W₁).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (congrArg toParity hw)) := by
  subst hw; simp

private theorem eqToHom_comp_parityDualRightDual_hom {α : Type*} (f : α → C)
    {P₁ P₂ : ParityWord α} (hp : P₁ = P₂) :
    eqToHom (congrArg (tensorList fun q : α × ZMod 2 ↦
        (RightRigidCategory.rightDual (parityDual (f q.1) q.2)).rightDual) hp) ≫
      tensorListCongrHom (fun q : α × ZMod 2 ↦ (parityDualRightDualIso (f q.1) q.2).hom) P₂ ≫
      (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
        (fun p : α × ZMod 2 ↦ (p.1, p.2 + 1)) P₂).hom =
    tensorListCongrHom (fun q : α × ZMod 2 ↦ (parityDualRightDualIso (f q.1) q.2).hom) P₁ ≫
      (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
        (fun p : α × ZMod 2 ↦ (p.1, p.2 + 1)) P₁).hom ≫
      eqToHom (congrArg (ParityWord.evalObj f)
        (congrArg (List.map fun p : α × ZMod 2 ↦ (p.1, p.2 + 1)) hp)) := by
  subst hp
  dsimp only [ParityWord.evalObj]
  simp

omit [MonoidalCategory C] [RigidCategory C] [PivotalCategory C] in
private theorem assoc4_eqToHom_eq {X₁ X₂ X₃ X₄ X₅ Z₁ Z₂ W : C}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅)
    (p₁ : X₅ = Z₁) (q₁ : Z₁ = W) (p₂ : X₅ = Z₂) (q₂ : Z₂ = W) :
    (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ eqToHom p₁) ≫ eqToHom q₁ =
      (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ eqToHom p₂) ≫ eqToHom q₂ := by
  subst p₁ q₁ p₂
  rfl

private theorem inv_rightAdjointMate_comp_evalObjDualIso_hom {α : Type*} (f : α → C)
    (L : WindingWord α) :
    ((pivotalComparisonIso f L).inv)ᘁ ≫ (ParityWord.evalObjDualIso f L.toParity).hom =
      ((rightDualFunctor C).opMopTensorListIso (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L).hom ≫
        tensorListCongrHom (fun p : α × ℤ ↦
          ((rightDualFunctor C).map (pivotalAtomIso (f p.1) p.2).inv).unmop.unop) L.reverse ≫
        (tensorListMapIso (fun q : α × ZMod 2 ↦
            (RightRigidCategory.rightDual (parityDual (f q.1) q.2)).rightDual)
          (fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) L.reverse).hom ≫
        tensorListCongrHom (fun q : α × ZMod 2 ↦ (parityDualRightDualIso (f q.1) q.2).hom)
          (toParity L.reverse) ≫
        (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
          (fun q : α × ZMod 2 ↦ (q.1, q.2 + 1)) (toParity L.reverse)).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f)
          (congrArg (List.map fun p : α × ZMod 2 ↦ (p.1, p.2 + 1))
            (List.map_reverse (f := fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) (l := L)))) := by
  have hinv : (pivotalComparisonIso f L).inv =
      (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
        (fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) L).inv ≫
      tensorListCongrHom (fun p : α × ℤ ↦ (pivotalAtomIso (f p.1) p.2).inv) L :=
    _ ≫= tensorListCongrIso_inv (fun p : α × ℤ ↦ pivotalAtomIso (f p.1) p.2) L
  have hmate : ((pivotalComparisonIso f L).inv)ᘁ =
      ((rightDualFunctor C).map
        (tensorListCongrHom (fun p : α × ℤ ↦ (pivotalAtomIso (f p.1) p.2).inv) L)).unmop.unop ≫
      ((rightDualFunctor C).map
        (tensorListMapIso (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2)
          (fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) L).inv).unmop.unop := by
    refine (congrArg (fun k ↦ ((rightDualFunctor C).map k).unmop.unop) hinv).trans ?_
    dsimp only [evalObj, ParityWord.evalObj, toParity]
    rw [Functor.map_comp, unmop_comp, unop_comp]
  have hmap := (rightDualFunctor C).opMopTensorListIso_map_hom
    (fun q : α × ZMod 2 ↦ parityDual (f q.1) q.2) (fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) L
  have hnat := (rightDualFunctor C).opMopTensorListIso_hom_naturality
    (fun p : α × ℤ ↦ (pivotalAtomIso (f p.1) p.2).inv) L
  have htr := eqToHom_comp_parityDualRightDual_hom f
    (List.map_reverse (f := fun p : α × ℤ ↦ (p.1, (p.2 : ZMod 2))) (l := L))
  rw [hmate, ParityWord.evalObjDualIso_hom]
  refine (Category.assoc _ _ _).trans ?_
  refine (_ ≫= ((Category.assoc _ _ _).symm.trans
    ((hmap =≫ _).trans
      ((Category.assoc _ _ _).trans (_ ≫=
        ((Category.assoc _ _ _).trans (_ ≫= htr))))))).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((hnat =≫ _).trans (Category.assoc _ _ _))

/-- **Right-dual coherence of `pivotalComparisonIso`**: taking the chosen right dual of an
evaluated winding word commutes with `pivotalComparisonIso` and `ParityWord.evalObjDualIso`. -/
@[reassoc]
theorem pivotalComparisonIso_rightDual_hom {α : Type*} (f : α → C) (L : WindingWord α) :
    (evalObjRightDualIso f L).hom ≫ (pivotalComparisonIso f L.rightDual).hom =
      ((pivotalComparisonIso f L).inv)ᘁ ≫
        (ParityWord.evalObjDualIso f L.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_rightDual L).symm) := by
  -- Expand both sides along list reversal and strip `opMopTensorListIso`.
  have hpush := eqToHom_comp_pivotalComparisonIso_hom f (rightDual_eq_map_reverse L).symm
  have htail := pivotalRightDualTail f L.reverse
  have hrhs := inv_rightAdjointMate_comp_evalObjDualIso_hom f L
  rw [evalObjRightDualIso_hom]
  refine (Category.assoc _ _ _).trans (Eq.trans ?_
    ((Category.assoc _ _ _).symm.trans ((hrhs =≫ _).trans (Category.assoc _ _ _))).symm)
  refine _ ≫= ?_
  refine ((Category.assoc _ _ _).trans (_ ≫= ((Category.assoc _ _ _).trans (_ ≫= hpush)))).trans ?_
  refine ((_ ≫= (Category.assoc _ _ _).symm).trans
    ((Category.assoc _ _ _).symm.trans (htail =≫ _))).trans ?_
  exact assoc4_eqToHom_eq _ _ _ _ _ _ _ _

/-- **Left-dual coherence of `pivotalComparisonIso`**: taking the chosen left dual of an evaluated
winding word agrees with identifying left and right duals via `leftDualIsoRightDual` and applying
`ParityWord.evalObjDualIso`. -/
@[reassoc]
theorem pivotalComparisonIso_leftDual_hom {α : Type*} (f : α → C) (L : WindingWord α) :
    (evalObjLeftDualIso f L).hom ≫ (pivotalComparisonIso f L.leftDual).hom =
      (leftDualIsoRightDual (evalObj f L)).hom ≫
        ((pivotalComparisonIso f L).inv)ᘁ ≫
        (ParityWord.evalObjDualIso f L.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_leftDual L).symm) := by
  -- Transport `leftDualFunctor` to `rightDualFunctor` across `opMopTensorListIso` via
  -- `dualFunctorIso`.
  rw [← cancel_epi (leftDualIsoRightDual (evalObj f L)).inv, Iso.inv_hom_id_assoc]
  have hdual := NatTrans.unmop_unop_app_comp_opMopTensorListIso_hom (dualFunctorIso C).hom
    (fun p : α × ℤ ↦ iteratedDual (f p.1) p.2) L
  simp only [dualFunctorIso_hom_app] at hdual
  have hpush := eqToHom_comp_pivotalComparisonIso_hom f (leftDual_eq_map_reverse L).symm
  have htail := pivotalLeftDualTail f L.reverse
  have hrhs := inv_rightAdjointMate_comp_evalObjDualIso_hom f L
  have hcancel :
      tensorListCongrHom (fun p : α × ℤ ↦ (leftDualIsoRightDual (iteratedDual (f p.1) p.2)).inv)
          L.reverse ≫
        tensorListCongrHom (fun p : α × ℤ ↦ (leftDualIsoRightDual (iteratedDual (f p.1) p.2)).hom)
          L.reverse = 𝟙 _ := by
    rw [← tensorListCongrHom_comp]
    simp only [Iso.inv_hom_id, tensorListCongrHom_id]
  rw [evalObjLeftDualIso_hom]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (((Category.assoc _ _ _).symm.trans
    ((hdual =≫ _).trans (Category.assoc _ _ _))) =≫ _).trans ?_
  refine (Category.assoc _ _ _).trans (Eq.trans ?_
    ((Category.assoc _ _ _).symm.trans ((hrhs =≫ _).trans (Category.assoc _ _ _))).symm)
  refine _ ≫= ?_
  refine ((Category.assoc _ _ _).trans (_ ≫=
    ((Category.assoc _ _ _).trans (_ ≫= ((Category.assoc _ _ _).trans (_ ≫= hpush)))))).trans ?_
  refine (_ ≫= ((_ ≫= (Category.assoc _ _ _).symm).trans
    ((Category.assoc _ _ _).symm.trans (htail =≫ _)))).trans ?_
  refine (_ ≫= Category.assoc _ _ _).trans ?_
  refine ((Category.assoc _ _ _).symm.trans
    ((hcancel =≫ _).trans (Category.id_comp _))).trans ?_
  exact assoc4_eqToHom_eq _ _ _ _ _ _ _ _

/-! ### Coupon transport, half-turn single mates, and full-turn double mates -/

/-- Transport a coupon morphism `g : evalObj f src ⟶ evalObj f tgt` from integer-labelled winding
boundaries to its parity-reduced boundary `ParityWord.evalObj f src.toParity ⟶
ParityWord.evalObj f tgt.toParity` by conjugating with `pivotalComparisonIso`. -/
noncomputable def transportCoupon {α : Type*} (f : α → C) {src tgt : WindingWord α}
    (g : evalObj f src ⟶ evalObj f tgt) :
    ParityWord.evalObj f src.toParity ⟶ ParityWord.evalObj f tgt.toParity :=
  (pivotalComparisonIso f src).inv ≫ g ≫ (pivotalComparisonIso f tgt).hom

@[simp]
theorem transportCoupon_id {α : Type*} (f : α → C) (L : WindingWord α) :
    transportCoupon f (𝟙 (evalObj f L)) = 𝟙 (ParityWord.evalObj f L.toParity) := by
  simp [transportCoupon]

@[simp]
theorem transportCoupon_comp {α : Type*} (f : α → C) {L₁ L₂ L₃ : WindingWord α}
    (g₁ : evalObj f L₁ ⟶ evalObj f L₂) (g₂ : evalObj f L₂ ⟶ evalObj f L₃) :
    transportCoupon f (g₁ ≫ g₂) = transportCoupon f g₁ ≫ transportCoupon f g₂ := by
  simp [transportCoupon]

/-- Tensoring two coupons along concatenated boundaries commutes with `transportCoupon`. -/
theorem transportCoupon_append {α : Type*} (f : α → C) {src₁ tgt₁ src₂ tgt₂ : WindingWord α}
    (g₁ : evalObj f src₁ ⟶ evalObj f tgt₁) (g₂ : evalObj f src₂ ⟶ evalObj f tgt₂) :
    transportCoupon f
        ((evalObjAppendIso f src₁ src₂).inv ≫ (g₁ ⊗ₘ g₂) ≫ (evalObjAppendIso f tgt₁ tgt₂).hom) =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_append src₁ src₂)) ≫
        (ParityWord.evalObjAppendIso f src₁.toParity src₂.toParity).inv ≫
        (transportCoupon f g₁ ⊗ₘ transportCoupon f g₂) ≫
        (ParityWord.evalObjAppendIso f tgt₁.toParity tgt₂.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_append tgt₁ tgt₂).symm) := by
  have hsrc : (pivotalComparisonIso f (src₁ ++ src₂)).inv ≫ (evalObjAppendIso f src₁ src₂).inv =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_append src₁ src₂)) ≫
        (ParityWord.evalObjAppendIso f src₁.toParity src₂.toParity).inv ≫
        ((pivotalComparisonIso f src₁).inv ⊗ₘ (pivotalComparisonIso f src₂).inv) := by
    rw [← cancel_epi ((evalObjAppendIso f src₁ src₂).hom ≫
      (pivotalComparisonIso f (src₁ ++ src₂)).hom)]
    rw [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, pivotalComparisonIso_append_hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.hom_inv_id_assoc]
    rw [tensorHom_comp_tensorHom, Iso.hom_inv_id, Iso.hom_inv_id, id_tensorHom,
      MonoidalCategory.whiskerLeft_id]
  dsimp only [transportCoupon]
  simp only [Category.assoc]
  rw [reassoc_of% hsrc, pivotalComparisonIso_append_hom]
  simp only [← tensorHom_comp_tensorHom_assoc]

/-- **Half-turn rotation (right mate)**: rotating a coupon `g` via right duality on winding
boundaries transports to the single right mate `(transportCoupon f g)ᘁ` conjugated by
`ParityWord.evalObjDualIso`. -/
theorem transportCoupon_rightDual {α : Type*} (f : α → C) {src tgt : WindingWord α}
    (g : evalObj f src ⟶ evalObj f tgt) :
    transportCoupon f ((evalObjRightDualIso f tgt).inv ≫ gᘁ ≫ (evalObjRightDualIso f src).hom) =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_rightDual tgt)) ≫
        (ParityWord.evalObjDualIso f tgt.toParity).inv ≫
        (transportCoupon f g)ᘁ ≫
        (ParityWord.evalObjDualIso f src.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_rightDual src).symm) := by
  have htgt : (pivotalComparisonIso f tgt.rightDual).inv ≫ (evalObjRightDualIso f tgt).inv =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_rightDual tgt)) ≫
        (ParityWord.evalObjDualIso f tgt.toParity).inv ≫
        ((pivotalComparisonIso f tgt).hom)ᘁ := by
    rw [← cancel_epi ((evalObjRightDualIso f tgt).hom ≫
      (pivotalComparisonIso f tgt.rightDual).hom)]
    rw [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, pivotalComparisonIso_rightDual_hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.hom_inv_id_assoc, ← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id]
  dsimp only [transportCoupon]
  simp only [Category.assoc]
  rw [reassoc_of% htgt, pivotalComparisonIso_rightDual_hom]
  simp only [comp_rightAdjointMate, Category.assoc]

/-- **Opposite half-turn rotation (left mate)**: rotating a coupon `g` via left duality on winding
boundaries *also* transports to the single right mate `(transportCoupon f g)ᘁ` conjugated by
`ParityWord.evalObjDualIso`. -/
theorem transportCoupon_leftDual {α : Type*} (f : α → C) {src tgt : WindingWord α}
    (g : evalObj f src ⟶ evalObj f tgt) :
    transportCoupon f ((evalObjLeftDualIso f tgt).inv ≫ (ᘁg) ≫ (evalObjLeftDualIso f src).hom) =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_leftDual tgt)) ≫
        (ParityWord.evalObjDualIso f tgt.toParity).inv ≫
        (transportCoupon f g)ᘁ ≫
        (ParityWord.evalObjDualIso f src.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_leftDual src).symm) := by
  -- Invert `pivotalComparisonIso_leftDual_hom` at `tgt` and convert `ᘁg` to `gᘁ`.
  have htgt : (pivotalComparisonIso f tgt.leftDual).inv ≫ (evalObjLeftDualIso f tgt).inv =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_leftDual tgt)) ≫
        (ParityWord.evalObjDualIso f tgt.toParity).inv ≫
        ((pivotalComparisonIso f tgt).hom)ᘁ ≫
        (leftDualIsoRightDual (evalObj f tgt)).inv := by
    rw [← cancel_epi ((evalObjLeftDualIso f tgt).hom ≫
      (pivotalComparisonIso f tgt.leftDual).hom)]
    rw [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, pivotalComparisonIso_leftDual_hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.hom_inv_id_assoc, ← comp_rightAdjointMate_assoc, Iso.hom_inv_id, rightAdjointMate_id]
  have hmate : (leftDualIsoRightDual (evalObj f tgt)).inv ≫
      (ᘁg) ≫ (leftDualIsoRightDual (evalObj f src)).hom = gᘁ := by
    rw [leftAdjointMate_comp_leftDualIsoRightDual_hom, Iso.inv_hom_id_assoc]
  dsimp only [transportCoupon]
  simp only [Category.assoc]
  rw [reassoc_of% htgt, pivotalComparisonIso_leftDual_hom, reassoc_of% hmate]
  simp only [comp_rightAdjointMate, Category.assoc]

/-- **Full-turn rotation (double mate)**: the double right mate of a parity-reduced coupon
`transportCoupon f g` is its conjugate by the pivotal isomorphism `pivotalIsoApp`. -/
theorem rightAdjointMate_rightAdjointMate_transportCoupon {α : Type*} (f : α → C)
    {src tgt : WindingWord α} (g : evalObj f src ⟶ evalObj f tgt) :
    (transportCoupon f g)ᘁᘁ =
      (pivotalIsoApp (ParityWord.evalObj f src.toParity)).inv ≫
        transportCoupon f g ≫
        (pivotalIsoApp (ParityWord.evalObj f tgt.toParity)).hom :=
  rightAdjointMate_rightAdjointMate (transportCoupon f g)

end WindingWord

namespace RigidObject

/-- Direct comparison isomorphism from `RigidObject.evalObj f X` to the parity-word evaluation
`ParityWord.evalObj f X.normalizeParity`, factoring through `evalObjNormalizeIso` and
`WindingWord.pivotalComparisonIso`. -/
noncomputable def evalObjNormalizeParityIso {α : Type*} (f : α → C) (X : RigidObject α) :
    X.evalObj f ≅ ParityWord.evalObj f X.normalizeParity :=
  evalObjNormalizeIso f X ≪≫
    WindingWord.pivotalComparisonIso f X.normalize ≪≫
    eqToIso (congrArg (ParityWord.evalObj f) (normalizeParity_eq_toParity_normalize X).symm)

end RigidObject

end PivotalParity

end TauCeti

namespace CategoryTheory.Functor

open TauCeti

variable {C : Type*} [Category* C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]
variable {D : Type*} [Category* D] [MonoidalCategory D] [RigidCategory D] [PivotalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor `F : C ⥤ D` between pivotal categories is pivotal (`F.IsPivotal`) if
and only if it preserves the level-`0`-to-level-`2` comparison `(pivotalAtomIso X 2).inv : X ⟶ Xᘁᘁ`
along `F.mapDoubleRightDualIso`. -/
theorem isPivotal_iff_map_pivotalAtomIso_two_inv :
    F.IsPivotal ↔ ∀ X : C,
      F.map (pivotalAtomIso X 2).inv ≫ (F.mapDoubleRightDualIso X).hom =
        (pivotalAtomIso (F.obj X) 2).inv := by
  simp only [pivotalAtomIso_two, Iso.symm_inv]
  exact F.isPivotal_iff_map_pivotalIsoApp_hom_comp_mapDoubleRightDualIso_hom

end CategoryTheory.Functor
