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

In a rigid monoidal category `C` with `[PivotalCategory C]` (`φ_X : X ≅ Xᘁᘁ`), even dual shifts
are canonically identified with `X` and odd dual shifts — including negative levels via
`leftDualIsoRightDual` — with `Xᘁ`. Boundary objects thus reduce from `WindingWord.evalObj` to
`ParityWord.evalObj` up to pivotal isomorphism: passing from level `0` to `2` evaluates to `φ_X`
rather than `𝟙 X`, and twisting `P` by `u : Aut (LaxMonoidalFunctor.of (𝟭 C))` scales it by `u_X`.

* `TauCeti.pivotalAtomIso`: the isomorphism `iteratedDual X n ≅ parityDual X (n : ZMod 2)` across
  all `n : ℤ`, with step coherence (`pivotalAtomIsoAux_rightDual`, `pivotalAtomIsoAux_leftDual`),
  torsor twisting (`smul_pivotalAtomIso_two_inv`), and pivotal-functor characterization
  (`CategoryTheory.Functor.isPivotal_iff_map_pivotalAtomIso_two_inv`);
* `TauCeti.WindingWord.pivotalComparisonIso` and `TauCeti.RigidObject.evalObjNormalizeParityIso`:
  boundary comparisons coherent with the empty word, concatenation, right duality, and left duality;
* `TauCeti.WindingWord.transportCoupon`: coupon transport to parity boundaries, preserving
  identities, composition, tensoring, single mates, and double mates conjugated by `pivotalIsoApp`.

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

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-! ### Atomic pivotal comparison across all integer dual levels -/

private theorem zmod2_of_succ {k : ℕ} {ε : ZMod 2} (h : ((k + 1 : ℕ) : ZMod 2) = ε) :
    (k : ZMod 2) = ε + 1 :=
  (by decide : ∀ z ε : ZMod 2, z + 1 = ε → z = ε + 1) _ _ (by simpa [Nat.cast_add] using h)
private theorem zmod2_of_negSucc {k : ℕ} {ε : ZMod 2} (h : (Int.negSucc (k + 1) : ZMod 2) = ε) :
    (Int.negSucc k : ZMod 2) = ε + 1 := by
  have heq : (Int.negSucc (k + 1) : ZMod 2) = (Int.negSucc k : ZMod 2) - 1 := by
    rw [← Int.cast_one, ← Int.cast_sub]; rfl
  exact (by decide : ∀ z ε : ZMod 2, z - 1 = ε → z = ε + 1) _ _ (heq ▸ h)

private abbrev lMap {X Y : C} (g : X ⟶ Y) := ((leftDualFunctor C).map g).unmop.unop
private abbrev rMap {X Y : C} (g : X ⟶ Y) := ((rightDualFunctor C).map g).unmop.unop
private abbrev lIso {X Y : C} (e : X ≅ Y) := ((leftDualFunctor C).mapIso e.symm).unmop.unop
private abbrev rIso {X Y : C} (e : X ≅ Y) := ((rightDualFunctor C).mapIso e.symm).unmop.unop

private noncomputable def pivotalRightPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((k : ZMod 2) = ε) → (iteratedRightDual X k ≅ parityDual X ε)
  | 0, ⟨0, _⟩, _ => Iso.refl X
  | 0, ⟨1, _⟩, h => False.elim ((by decide : ((0 : ℕ) : ZMod 2).val ≠ 1) (congrArg Fin.val h))
  | k + 1, ⟨0, _⟩, h =>
      rIso (pivotalRightPowAuxIso X k 1 (zmod2_of_succ (Fin.ext (congrArg Fin.val h)))) ≪≫
        (pivotalIsoApp X).symm
  | k + 1, ⟨1, _⟩, h =>
      rIso (pivotalRightPowAuxIso X k 0 (zmod2_of_succ (Fin.ext (congrArg Fin.val h))))
private noncomputable def pivotalLeftPowAuxIso (X : C) :
    (k : ℕ) → (ε : ZMod 2) → ((Int.negSucc k : ZMod 2) = ε) →
      (iteratedLeftDual X (k + 1) ≅ parityDual X ε)
  | 0, ⟨0, _⟩, h => False.elim ((by decide : (Int.negSucc 0 : ZMod 2).val ≠ 0) (congrArg Fin.val h))
  | 0, ⟨1, _⟩, _ => leftDualIsoRightDual X
  | k + 1, ⟨0, _⟩, h =>
      lIso (pivotalLeftPowAuxIso X k 1 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))) ≪≫
        (leftDualRightDualIso C).app X
  | k + 1, ⟨1, _⟩, h =>
      lIso (pivotalLeftPowAuxIso X k 0 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))) ≪≫
        leftDualIsoRightDual X

/-- Proof-irrelevant auxiliary form of `pivotalAtomIso` with an explicit target parity `ε : ZMod 2`
witnessed by `(n : ZMod 2) = ε`. -/
noncomputable def pivotalAtomIsoAux (X : C) :
    (n : ℤ) → (ε : ZMod 2) → ((n : ZMod 2) = ε) → (iteratedDual X n ≅ parityDual X ε)
  | .ofNat k, ε, h => pivotalRightPowAuxIso X k ε (by simpa using h)
  | .negSucc k, ε, h => pivotalLeftPowAuxIso X k ε h

/-- Pivotal isomorphism `iteratedDual X n ≅ parityDual X (n : ZMod 2)` reducing any integer
dual-winding level `n : ℤ` to its `ZMod 2` parity representative `X` or `Xᘁ`. -/
noncomputable def pivotalAtomIso (X : C) (n : ℤ) : iteratedDual X n ≅ parityDual X (n : ZMod 2) :=
  pivotalAtomIsoAux X n (n : ZMod 2) rfl

@[simp] theorem pivotalAtomIso_zero (X : C) : pivotalAtomIso X 0 = Iso.refl X := by rfl
@[simp] theorem pivotalAtomIso_one (X : C) : pivotalAtomIso X 1 = Iso.refl Xᘁ := by
  ext; exact rightAdjointMate_id (X := X)
@[simp] theorem pivotalAtomIso_neg_one (X : C) :
    pivotalAtomIso X (-1) = leftDualIsoRightDual X := by rfl

/-- At winding level `2`, `pivotalAtomIso X 2 : Xᘁᘁ ≅ X` is `(pivotalIsoApp X).symm` — not the
identity — so identifying level `0` with level `2` evaluates to `(pivotalIsoApp X).hom`. -/
@[simp] theorem pivotalAtomIso_two (X : C) : pivotalAtomIso X 2 = (pivotalIsoApp X).symm := by
  ext; exact ((congrArg rightAdjointMate (congrArg Iso.inv (pivotalAtomIso_one X))) =≫ _).trans
    ((rightAdjointMate_id (X := Xᘁ) =≫ _).trans (Category.id_comp _))

/-- By the Freyd–Yetter identity, the level-`3` comparison `Xᘁᘁᘁ ⟶ Xᘁ` equals the inverse pivotal
component at `Xᘁ`. -/
theorem pivotalAtomIso_three_hom (X : C) : (pivotalAtomIso X 3).hom = (pivotalIsoApp Xᘁ).inv := by
  change ((pivotalAtomIso X 2).inv)ᘁ = _
  rw [pivotalAtomIso_two]; exact (pivotalIsoApp_rightDual_inv X).symm

omit [PivotalCategory C] in
/-- Twisting `P : PivotalCategory C` by a monoidal natural automorphism `u` of `𝟭 C` scales the
level-`0`-to-level-`2` pivotal identification `(pivotalAtomIso X 2).inv : X ⟶ Xᘁᘁ` by `u_X`. -/
theorem smul_pivotalAtomIso_two_inv (u : Aut (LaxMonoidalFunctor.of (𝟭 C)))
    (P : PivotalCategory C) (X : C) :
    (@pivotalAtomIso C _ _ _ (u • P) X 2).inv =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso.hom.app X ≫
        (@pivotalAtomIso C _ _ _ P X 2).inv := by
  rw [@pivotalAtomIso_two C _ _ _ (u • P) X, @pivotalAtomIso_two C _ _ _ P X, Iso.symm_inv,
    Iso.symm_inv, PivotalCategory.smul_pivotalIsoApp, Iso.trans_hom, Iso.app_hom]; rfl

/-! ### Step coherence of `pivotalAtomIso` with right and left duality -/

private theorem rightDualMap_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv (X : C) :
    rMap (leftDualIsoRightDual X).inv ≫ (pivotalIsoApp X).inv =
      (rightDualLeftDualIso C).hom.app X := by
  refine (((@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual _)
    (RightRigidCategory.rightDual _) (leftDualIsoRightDual X).inv) =≫ _).trans ?_).trans
      (rightDualLeftDualIso_hom_app X).symm
  rw [Iso.comp_inv_eq, ← rightMate_leftDualIsoRightDual_inv X, rightDualIso_hom, ← comp_rightMate,
    Category.comp_id]
omit [PivotalCategory C] in
private theorem rightDualMap_leftDualRightDualIso_inv_app (X : C) :
    rMap ((leftDualRightDualIso C).inv.app X) = (rightDualLeftDualIso C).hom.app Xᘁ := by
  refine (@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual _)
    (RightRigidCategory.rightDual _) ((leftDualRightDualIso C).inv.app X)).trans ?_
  rw [leftDualRightDualIso_inv_app, rightDualLeftDualIso_hom_app]
  exact rightMate_leftDualIso_inv _ _ _
private theorem leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv (X : C) :
    (leftDualIsoRightDual Xᘁ).hom ≫ (pivotalIsoApp X).inv = (leftDualRightDualIso C).hom.app X := by
  refine @leftDualHom_ext C _ _ X Xᘁ _ (RightRigidCategory.rightDual X).exact _ _ ?_
  rw [leftDualRightDualIso_hom_app, leftDualIso_hom, leftMate_comp_evaluation, id_whiskerRight,
    Category.id_comp, MonoidalCategory.whiskerLeft_comp_assoc,
    ← rightAdjointMate_comp_evaluation (pivotalIsoApp X).inv, ← pivotalIsoApp_rightDual X]
  exact whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation Xᘁ

/-- **Right-dual step coherence of `pivotalAtomIsoAux`**: taking the chosen right dual of an atom
at level `n` and reducing modulo two agrees with advancing the level to `n + 1` first. -/
theorem pivotalAtomIsoAux_rightDual (X : C) (n : ℤ) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
    (h' : ((n + 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualRightDualIso X n).hom ≫ (pivotalAtomIsoAux X (n + 1) (ε + 1) h').hom =
      ((pivotalAtomIsoAux X n ε h).inv)ᘁ ≫ (parityDualRightDualIso X ε).hom := by
  cases n with
  | ofNat k =>
    rcases ParityWord.eq_zero_or_one ε with rfl | rfl
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact Category.id_comp _
  | negSucc k =>
    cases k with
    | zero =>
      rcases ParityWord.eq_zero_or_one ε with rfl | rfl
      · exact absurd (congrArg Fin.val h) (by decide)
      · exact (Category.comp_id _).trans
          (rightDualMap_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv X).symm
    | succ k =>
      rcases ParityWord.eq_zero_or_one ε with rfl | rfl
      · let q := (pivotalLeftPowAuxIso X k 1 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))).hom
        exact ((Category.comp_id _).trans ((congrArg (fun z ↦ z.unmop.unop)
          ((rightDualFunctor C).map_comp ((leftDualRightDualIso C).inv.app X) (lMap q))).trans
            ((_ ≫= rightDualMap_leftDualRightDualIso_inv_app X).trans
              ((rightDualLeftDualIso C).hom.naturality q)))).symm
      · let q := (pivotalLeftPowAuxIso X k 0 (zmod2_of_negSucc (Fin.ext (congrArg Fin.val h)))).hom
        exact (((congrArg (fun z ↦ z.unmop.unop)
          ((rightDualFunctor C).map_comp (leftDualIsoRightDual X).inv (lMap q)) =≫ _).trans
            ((Category.assoc _ _ _).trans
              ((_ ≫= rightDualMap_leftDualIsoRightDual_inv_comp_pivotalIsoApp_inv X).trans
                ((rightDualLeftDualIso C).hom.naturality q))))).symm

private theorem eqToHom_comp_pivotalAtomIsoAux_ofNat (X : C) (m : ℤ) (k : ℕ) (δ : ZMod 2)
    (hm : m = Int.ofNat k) (h' : (m : ZMod 2) = δ) :
    eqToHom (congrArg (iteratedDual X) hm.symm) ≫ (pivotalAtomIsoAux X m δ h').hom =
      (pivotalRightPowAuxIso X k δ (by simpa [hm] using h')).hom := by
  subst hm; exact Category.id_comp _

/-- **Left-dual step coherence of `pivotalAtomIsoAux`**: taking the chosen left dual of an atom at
level `n` and reducing modulo two agrees with identifying left and right duals via
`leftDualIsoRightDual` followed by `parityDualRightDualIso`. -/
theorem pivotalAtomIsoAux_leftDual (X : C) (n : ℤ) (ε : ZMod 2) (h : (n : ZMod 2) = ε)
    (h' : ((n - 1 : ℤ) : ZMod 2) = ε + 1) :
    (iteratedDualLeftDualIso X n).hom ≫ (pivotalAtomIsoAux X (n - 1) (ε + 1) h').hom =
      (leftDualIsoRightDual (iteratedDual X n)).hom ≫
        ((pivotalAtomIsoAux X n ε h).inv)ᘁ ≫ (parityDualRightDualIso X ε).hom := by
  have hmate : ∀ {A B : C} (g : B ⟶ A),
      (leftDualIsoRightDual A).hom ≫ gᘁ = lMap g ≫ (leftDualIsoRightDual B).hom :=
    fun g ↦ (leftAdjointMate_comp_leftDualIsoRightDual_hom g).symm
  cases n with
  | negSucc k =>
    rcases ParityWord.eq_zero_or_one ε with rfl | rfl
    · exact (Category.id_comp _).trans ((hmate (pivotalAtomIsoAux X _ 0 h).inv).symm.trans
        (_ ≫= (Category.comp_id _).symm))
    · exact (Category.id_comp _).trans
        ((_ ≫= (leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv X).symm).trans
          ((Category.assoc _ _ _).symm.trans
            (((hmate (pivotalAtomIsoAux X _ 1 h).inv).symm =≫ _).trans (Category.assoc _ _ _))))
  | ofNat k =>
    cases k with
    | zero =>
      rcases ParityWord.eq_zero_or_one ε with rfl | rfl
      · exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (_ ≫= ((rightAdjointMate_id (X := X)).symm.trans (Category.comp_id _).symm)))
      · exact absurd (congrArg Fin.val h) (by decide)
    | succ k =>
      refine ((Category.assoc _ _ _).trans (_ ≫= eqToHom_comp_pivotalAtomIsoAux_ofNat X _ k (ε + 1)
        (add_sub_cancel_right (k : ℤ) 1) h')).trans ?_
      rcases ParityWord.eq_zero_or_one ε with rfl | rfl
      · let p := (pivotalRightPowAuxIso X k 1 (zmod2_of_succ (Fin.ext (congrArg Fin.val h)))).hom
        let g := (pivotalAtomIsoAux X (Int.ofNat (k + 1)) 0 h).inv
        have h2 : lMap g = (leftDualRightDualFunctor C).map p ≫ lMap (pivotalIsoApp X).hom :=
          congrArg (fun z ↦ z.unmop.unop) ((leftDualFunctor C).map_comp (pivotalIsoApp X).hom (pᘁ))
        have h3 : lMap (pivotalIsoApp X).hom ≫ (leftDualIsoRightDual X).hom =
            (leftDualRightDualIso C).hom.app Xᘁ :=
          (hmate (pivotalIsoApp X).hom).symm.trans
            ((_ ≫= (pivotalIsoApp_rightDual_inv X).symm).trans
              (leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv Xᘁ))
        exact (((_ ≫= Category.comp_id _).trans (hmate g)).trans ((h2 =≫ _).trans
          ((Category.assoc _ _ _).trans
            ((_ ≫= h3).trans ((leftDualRightDualIso C).hom.naturality p))))).symm
      · let p := (pivotalRightPowAuxIso X k 0 (zmod2_of_succ (Fin.ext (congrArg Fin.val h)))).hom
        let g := (pivotalAtomIsoAux X (Int.ofNat (k + 1)) 1 h).inv
        exact ((Category.assoc _ _ _).symm.trans ((hmate g =≫ _).trans ((Category.assoc _ _ _).trans
          ((_ ≫= leftDualIsoRightDual_rightDual_comp_pivotalIsoApp_inv X).trans
            ((leftDualRightDualIso C).hom.naturality p))))).symm

/-! ### Word-level pivotal comparison and coherence -/

namespace WindingWord

variable {α : Type*}

private abbrev pDual (f : α → C) (q : α × ZMod 2) : C := parityDual (f q.1) q.2
private abbrev iDual (f : α → C) (p : α × ℤ) : C := iteratedDual (f p.1) p.2
private abbrev mod2 (p : α × ℤ) : α × ZMod 2 := (p.1, (p.2 : ZMod 2))
private abbrev pShift1 (q : α × ZMod 2) : α × ZMod 2 := (q.1, q.2 + 1)
private noncomputable abbrev pRDHom (f : α → C) (q : α × ZMod 2) :=
  (parityDualRightDualIso (f q.1) q.2).hom

/-- Pivotal comparison isomorphism `WindingWord.evalObj f L ≅ ParityWord.evalObj f L.toParity`,
applying `pivotalAtomIso` port-by-port and reindexing along `WindingWord.toParity`. -/
noncomputable def pivotalComparisonIso (f : α → C) (L : WindingWord α) :
    evalObj f L ≅ ParityWord.evalObj f L.toParity :=
  tensorListCongrIso (fun p : α × ℤ ↦ pivotalAtomIso (f p.1) p.2) L ≪≫
    tensorListMapIso (pDual f) mod2 L

@[simp] theorem pivotalComparisonIso_nil_hom (f : α → C) :
    (pivotalComparisonIso f ([] : WindingWord α)).hom = 𝟙 (𝟙_ C) := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_hom]; simp
@[simp] theorem pivotalComparisonIso_nil_inv (f : α → C) :
    (pivotalComparisonIso f ([] : WindingWord α)).inv = 𝟙 (𝟙_ C) := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_inv]; simp

/-- Recursive step of `pivotalComparisonIso` on `p :: L`. -/
theorem pivotalComparisonIso_cons_hom (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    (pivotalComparisonIso f (p :: L)).hom =
      (pivotalAtomIso (f p.1) p.2).hom ⊗ₘ (pivotalComparisonIso f L).hom := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_hom]; simp [← id_tensorHom, tensorHom_comp_tensorHom]
theorem pivotalComparisonIso_cons_inv (f : α → C) (p : α × ℤ) (L : WindingWord α) :
    (pivotalComparisonIso f (p :: L)).inv =
      (pivotalAtomIso (f p.1) p.2).inv ⊗ₘ (pivotalComparisonIso f L).inv := by
  dsimp only [pivotalComparisonIso, evalObj, ParityWord.evalObj, toParity, List.map, tensorList,
    Iso.trans_inv]; simp [← id_tensorHom, tensorHom_comp_tensorHom]

/-- **Concatenation coherence of `pivotalComparisonIso`**: tensoring two evaluated winding words
and reducing modulo two commutes with concatenating first. -/
@[reassoc]
theorem pivotalComparisonIso_append_hom (f : α → C) (L M : WindingWord α) :
    (evalObjAppendIso f L M).hom ≫ (pivotalComparisonIso f (L ++ M)).hom =
      ((pivotalComparisonIso f L).hom ⊗ₘ (pivotalComparisonIso f M).hom) ≫
        (ParityWord.evalObjAppendIso f L.toParity M.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_append L M).symm) := by
  let φ : ∀ p : α × ℤ, iDual f p ⟶ pDual f (mod2 p) := fun p ↦ (pivotalAtomIso (f p.1) p.2).hom
  have hc (W : WindingWord α) : (pivotalComparisonIso f W).hom =
      tensorListCongrHom φ W ≫ (tensorListMapIso (pDual f) mod2 W).hom :=
    congrArg (· ≫ _) (tensorListCongrIso_hom _ W)
  exact (congrArg (_ ≫ ·) (hc (L ++ M))).trans
    ((tensorListAppendIso_hom_naturality_assoc φ L M _).symm.trans
      ((_ ≫= tensorListMapIso_append_hom (pDual f) mod2 L M).trans
        ((Category.assoc _ _ _).symm.trans (((tensorHom_comp_tensorHom _ _ _ _) =≫ _).trans
          (congrArg (· ≫ _) (congrArg₂ tensorHom (hc L) (hc M))).symm))))

private theorem hom_eq_comp_eqToHom {X : C} {m : ℤ} {w : ZMod 2} (hw : (m : ZMod 2) = w) :
    (pivotalAtomIso X m).hom =
      (pivotalAtomIsoAux X m w hw).hom ≫ eqToHom (congrArg (parityDual X) hw.symm) := by
  subst hw; exact (Category.comp_id _).symm
private theorem pivotalAtomIso_add_one_eq {X : C} (n : ℤ) :
    (iteratedDualRightDualIso X n).hom ≫ (pivotalAtomIso X (n + 1)).hom =
      ((pivotalAtomIso X n).inv)ᘁ ≫ (parityDualRightDualIso X (n : ZMod 2)).hom ≫
        eqToHom (congrArg (parityDual X) (by simp)) := by
  rw [hom_eq_comp_eqToHom (by simp : ((n + 1 : ℤ) : ZMod 2) = (n : ZMod 2) + 1),
    reassoc_of% (pivotalAtomIsoAux_rightDual X n (n : ZMod 2) rfl _)]; rfl
private theorem zmod2_sub_one_cast (n : ℤ) : ((n - 1 : ℤ) : ZMod 2) = (n : ZMod 2) + 1 := by
  simp [sub_eq_add_neg, (by decide : (-1 : ZMod 2) = 1)]
private theorem pivotalAtomIso_sub_one_eq {X : C} (n : ℤ) :
    (iteratedDualLeftDualIso X n).hom ≫ (pivotalAtomIso X (n - 1)).hom =
      ((leftDualIsoRightDual (iteratedDual X n)).hom ≫ ((pivotalAtomIso X n).inv)ᘁ) ≫
        (parityDualRightDualIso X (n : ZMod 2)).hom ≫
        eqToHom (congrArg (parityDual X) (zmod2_sub_one_cast n).symm) := by
  rw [hom_eq_comp_eqToHom (zmod2_sub_one_cast n),
    reassoc_of% (pivotalAtomIsoAux_leftDual X n (n : ZMod 2) rfl _)]
  simp only [Category.assoc]; rfl

private theorem pivotalShiftTail (f : α → C) {D : α × ℤ → C} (s : ℤ → ℤ)
    (hs : ∀ n : ℤ, (s n : ZMod 2) = (n : ZMod 2) + 1)
    (lhsStep : ∀ p : α × ℤ, D p ⟶ iteratedDual (f p.1) (s p.2))
    (rhsStep : ∀ p : α × ℤ, D p ⟶ (parityDual (f p.1) (p.2 : ZMod 2))ᘁ)
    (hstep : ∀ p : α × ℤ, lhsStep p ≫ (pivotalAtomIso (f p.1) (s p.2)).hom =
      rhsStep p ≫ (parityDualRightDualIso (f p.1) (p.2 : ZMod 2)).hom ≫
        eqToHom (congrArg (parityDual (f p.1)) (hs p.2).symm)) (R : WindingWord α) :
    tensorListCongrHom lhsStep R ≫ (tensorListMapIso (iDual f) (fun p ↦ (p.1, s p.2)) R).hom ≫
      (pivotalComparisonIso f (R.map fun p ↦ (p.1, s p.2))).hom =
    tensorListCongrHom rhsStep R ≫ (tensorListMapIso (fun q ↦ (pDual f q)ᘁ) mod2 R).hom ≫
      tensorListCongrHom (pRDHom f) R.toParity ≫
      (tensorListMapIso (pDual f) pShift1 R.toParity).hom ≫
      eqToHom (congrArg (ParityWord.evalObj f) (by
        simp [toParity, List.map_map, Function.comp_def, hs])) := by
  induction R with
  | nil =>
    dsimp only [evalObj, toParity, ParityWord.evalObj, List.map, tensorList]
    generalize_proofs; simp [pivotalComparisonIso_nil_hom]
  | cons p R ih =>
    dsimp only [List.map]; rw [pivotalComparisonIso_cons_hom]
    dsimp only [evalObj, toParity, ParityWord.evalObj, List.map, tensorList] at ih ⊢
    generalize_proofs hR hpR at ih ⊢
    rw [tensorListCongrHom_cons, tensorListMapIso_cons_hom, tensorListCongrHom_cons,
      tensorListMapIso_cons_hom, tensorListCongrHom_cons, tensorListMapIso_cons_hom,
      ← id_tensorHom (iteratedDual (f p.1) (s p.2)), ← id_tensorHom (pDual f (mod2 p))ᘁ,
      ← id_tensorHom (parityDual (f p.1) ((p.2 : ZMod 2) + 1))]
    have heq : eqToHom hpR =
        eqToHom (congrArg (parityDual (f p.1)) (hs p.2).symm) ⊗ₘ eqToHom hR := by
      rw [tensorHom_def', MonoidalCategory.whiskerLeft_eqToHom, eqToHom_whiskerRight, eqToHom_trans]
    rw [heq]; simp only [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg₂ (fun u v ↦ u ⊗ₘ v) (hstep p) ih

private theorem eqToHom_comp_pivotalComparisonIso_hom (f : α → C) {W₁ W₂ : WindingWord α}
    (hw : W₁ = W₂) :
    eqToHom (congrArg (evalObj f) hw) ≫ (pivotalComparisonIso f W₂).hom =
      (pivotalComparisonIso f W₁).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (congrArg toParity hw)) := by subst hw; simp
private theorem eqToHom_comp_parityDualRightDual_hom (f : α → C) {P₁ P₂ : ParityWord α}
    (hp : P₁ = P₂) :
    eqToHom (congrArg (tensorList fun q ↦ (pDual f q)ᘁ) hp) ≫
      tensorListCongrHom (pRDHom f) P₂ ≫ (tensorListMapIso (pDual f) pShift1 P₂).hom =
    tensorListCongrHom (pRDHom f) P₁ ≫ (tensorListMapIso (pDual f) pShift1 P₁).hom ≫
      eqToHom (congrArg (ParityWord.evalObj f) (congrArg (List.map pShift1) hp)) := by
  subst hp; dsimp only [ParityWord.evalObj]; simp

private theorem inv_rightAdjointMate_comp_evalObjDualIso_hom (f : α → C) (L : WindingWord α) :
    ((pivotalComparisonIso f L).inv)ᘁ ≫ (ParityWord.evalObjDualIso f L.toParity).hom =
      ((rightDualFunctor C).opMopTensorListIso (iDual f) L).hom ≫
        tensorListCongrHom (fun p : α × ℤ ↦ ((pivotalAtomIso (f p.1) p.2).inv)ᘁ) L.reverse ≫
        (tensorListMapIso (fun q ↦ (pDual f q)ᘁ) mod2 L.reverse).hom ≫
        tensorListCongrHom (pRDHom f) (toParity L.reverse) ≫
        (tensorListMapIso (pDual f) pShift1 (toParity L.reverse)).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f)
          (congrArg (List.map pShift1) (List.map_reverse (f := mod2) (l := L)))) := by
  have hinv : (pivotalComparisonIso f L).inv = (tensorListMapIso (pDual f) mod2 L).inv ≫
      tensorListCongrHom (fun p : α × ℤ ↦ (pivotalAtomIso (f p.1) p.2).inv) L :=
    _ ≫= tensorListCongrIso_inv (fun p : α × ℤ ↦ pivotalAtomIso (f p.1) p.2) L
  have hmate : ((pivotalComparisonIso f L).inv)ᘁ =
      (tensorListCongrHom (fun p : α × ℤ ↦ (pivotalAtomIso (f p.1) p.2).inv) L)ᘁ ≫
      ((tensorListMapIso (pDual f) mod2 L).inv)ᘁ := by
    refine (congrArg rightAdjointMate hinv).trans ?_
    dsimp only [evalObj, ParityWord.evalObj, toParity]; exact comp_rightAdjointMate
  exact (hmate =≫ _).trans ((_ ≫= ParityWord.evalObjDualIso_hom f L.toParity).trans
    ((Category.assoc _ _ _).trans
      (((_ ≫= ((rightDualFunctor C).opMopTensorListIso_map_hom_assoc (pDual f) mod2 L _)).trans
        (_ ≫= (_ ≫= (_ ≫= eqToHom_comp_parityDualRightDual_hom f
          (List.map_reverse (f := mod2) (l := L)))))).trans
        ((rightDualFunctor C).opMopTensorListIso_hom_naturality_assoc
          (fun p : α × ℤ ↦ (pivotalAtomIso (f p.1) p.2).inv) L _))))

omit [MonoidalCategory C] [RigidCategory C] [PivotalCategory C] in
private theorem comp5_eqToHom {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : C}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅) (e : X₅ ⟶ X₆)
    (h₁ : X₆ = X₇) (h₂ : X₇ = X₉) (h₃ : X₆ = X₈) (h₄ : X₈ = X₉) :
    a ≫ ((b ≫ c ≫ d ≫ e ≫ eqToHom h₁) ≫ eqToHom h₂) =
      (a ≫ b ≫ c ≫ d ≫ e ≫ eqToHom h₃) ≫ eqToHom h₄ := by
  subst h₁ h₂ h₃; cases Subsingleton.elim h₄ rfl; simp
omit [MonoidalCategory C] [RigidCategory C] [PivotalCategory C] in
private theorem shift_reassoc {X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₄) (c : X₄ ⟶ X₅) (c' : X₃ ⟶ X₆) (e : X₆ ⟶ X₅)
    (rhs : X₁ ⟶ X₆) (hc : w ≫ c = c' ≫ e) (ht : u ≫ v ≫ c' = rhs) :
    (u ≫ v ≫ w) ≫ c = rhs ≫ e := by
  rw [Category.assoc, Category.assoc, hc, ← Category.assoc v, ← Category.assoc u, ht]

/-- **Right-dual coherence of `pivotalComparisonIso`**: taking the chosen right dual of an
evaluated winding word commutes with `pivotalComparisonIso` and `ParityWord.evalObjDualIso`. -/
@[reassoc]
theorem pivotalComparisonIso_rightDual_hom (f : α → C) (L : WindingWord α) :
    (evalObjRightDualIso f L).hom ≫ (pivotalComparisonIso f L.rightDual).hom =
      ((pivotalComparisonIso f L).inv)ᘁ ≫ (ParityWord.evalObjDualIso f L.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_rightDual L).symm) := by
  have htail := pivotalShiftTail f (· + 1) (by simp)
    (fun p ↦ (iteratedDualRightDualIso (f p.1) p.2).hom)
    (fun p ↦ ((pivotalAtomIso (f p.1) p.2).inv)ᘁ) (fun p ↦ pivotalAtomIso_add_one_eq p.2) L.reverse
  refine ((evalObjRightDualIso_hom f L =≫ _).trans ?_).trans
    ((reassoc_of% (inv_rightAdjointMate_comp_evalObjDualIso_hom f L)) _).symm
  exact (Category.assoc _ _ _).trans
    ((_ ≫= shift_reassoc _ _ _ _ _ _ _
      (eqToHom_comp_pivotalComparisonIso_hom f (rightDual_eq_map_reverse L).symm) htail).trans
      (comp5_eqToHom _ _ _ _ _ _ _ _ _))

/-- **Left-dual coherence of `pivotalComparisonIso`**: taking the chosen left dual of an evaluated
winding word agrees with identifying left and right duals via `leftDualIsoRightDual` and applying
`ParityWord.evalObjDualIso`. -/
@[reassoc]
theorem pivotalComparisonIso_leftDual_hom (f : α → C) (L : WindingWord α) :
    (evalObjLeftDualIso f L).hom ≫ (pivotalComparisonIso f L.leftDual).hom =
      (leftDualIsoRightDual (evalObj f L)).hom ≫ ((pivotalComparisonIso f L).inv)ᘁ ≫
        (ParityWord.evalObjDualIso f L.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_leftDual L).symm) := by
  rw [← cancel_epi (leftDualIsoRightDual (evalObj f L)).inv, Iso.inv_hom_id_assoc]
  have hdual := NatTrans.unmop_unop_app_comp_opMopTensorListIso_hom (dualFunctorIso C).hom
    (iDual f) L
  simp only [dualFunctorIso_hom_app] at hdual
  have htail := pivotalShiftTail f (· - 1) zmod2_sub_one_cast
    (fun p ↦ (iteratedDualLeftDualIso (f p.1) p.2).hom)
    (fun p ↦ (leftDualIsoRightDual (iDual f p)).hom ≫ ((pivotalAtomIso (f p.1) p.2).inv)ᘁ)
    (fun p ↦ pivotalAtomIso_sub_one_eq p.2) L.reverse
  have hcancel : tensorListCongrHom
      (fun a : α × ℤ ↦ (leftDualIsoRightDual (iDual f a)).inv.op.mop.unmop.unop) L.reverse ≫
      tensorListCongrHom (fun p : α × ℤ ↦ (leftDualIsoRightDual (iDual f p)).hom ≫
        ((pivotalAtomIso (f p.1) p.2).inv)ᘁ) L.reverse =
      tensorListCongrHom (fun p : α × ℤ ↦ ((pivotalAtomIso (f p.1) p.2).inv)ᘁ) L.reverse :=
    (tensorListCongrHom_comp _ _ L.reverse).symm.trans (congrArg (tensorListCongrHom · L.reverse)
      (funext fun a ↦ Iso.inv_hom_id_assoc (leftDualIsoRightDual (iDual f a)) _))
  refine ((_ ≫= (evalObjLeftDualIso_hom f L =≫ _)).trans ?_).trans
    ((reassoc_of% (inv_rightAdjointMate_comp_evalObjDualIso_hom f L)) _).symm
  exact ((_ ≫= Category.assoc _ _ _).trans (((reassoc_of% hdual) _).trans
    ((_ ≫= (_ ≫= shift_reassoc _ _ _ _ _ _ _
      (eqToHom_comp_pivotalComparisonIso_hom f (leftDual_eq_map_reverse L).symm) htail)).trans
      (_ ≫= ((Category.assoc _ _ _).symm.trans (((reassoc_of% hcancel) _) =≫ _)))))).trans
    (comp5_eqToHom _ _ _ _ _ _ _ _ _)

/-! ### Coupon transport, half-turn single mates, and full-turn double mates -/

omit [MonoidalCategory C] [RigidCategory C] [PivotalCategory C] in
private theorem inv_comp_inv_of_hom_comp_hom {A B D E E' : C} (e₁ : A ≅ B) (e₂ : B ≅ E)
    (u : A ⟶ D) (v : D ⟶ A) (huv : u ≫ v = 𝟙 A) (e₄ : D ≅ E') (h : E' = E)
    (heq : e₁.hom ≫ e₂.hom = u ≫ e₄.hom ≫ eqToHom h) :
    e₂.inv ≫ e₁.inv = eqToHom h.symm ≫ e₄.inv ≫ v := by
  rw [← cancel_epi (e₁.hom ≫ e₂.hom), Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, heq]
  simp [huv]

/-- Transport a coupon morphism `g : evalObj f src ⟶ evalObj f tgt` from integer-labelled winding
boundaries to its parity-reduced boundary by conjugating with `pivotalComparisonIso`. -/
noncomputable def transportCoupon (f : α → C) {src tgt : WindingWord α}
    (g : evalObj f src ⟶ evalObj f tgt) :
    ParityWord.evalObj f src.toParity ⟶ ParityWord.evalObj f tgt.toParity :=
  (pivotalComparisonIso f src).inv ≫ g ≫ (pivotalComparisonIso f tgt).hom

@[simp] theorem transportCoupon_id (f : α → C) (L : WindingWord α) :
    transportCoupon f (𝟙 (evalObj f L)) = 𝟙 (ParityWord.evalObj f L.toParity) := by
  simp [transportCoupon]
@[simp] theorem transportCoupon_comp (f : α → C) {L₁ L₂ L₃ : WindingWord α}
    (g₁ : evalObj f L₁ ⟶ evalObj f L₂) (g₂ : evalObj f L₂ ⟶ evalObj f L₃) :
    transportCoupon f (g₁ ≫ g₂) = transportCoupon f g₁ ≫ transportCoupon f g₂ := by
  simp [transportCoupon]

/-- Tensoring two coupons along concatenated boundaries commutes with `transportCoupon`. -/
theorem transportCoupon_append (f : α → C) {src₁ tgt₁ src₂ tgt₂ : WindingWord α}
    (g₁ : evalObj f src₁ ⟶ evalObj f tgt₁) (g₂ : evalObj f src₂ ⟶ evalObj f tgt₂) :
    transportCoupon f
        ((evalObjAppendIso f src₁ src₂).inv ≫ (g₁ ⊗ₘ g₂) ≫ (evalObjAppendIso f tgt₁ tgt₂).hom) =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_append src₁ src₂)) ≫
        (ParityWord.evalObjAppendIso f src₁.toParity src₂.toParity).inv ≫
        (transportCoupon f g₁ ⊗ₘ transportCoupon f g₂) ≫
        (ParityWord.evalObjAppendIso f tgt₁.toParity tgt₂.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_append tgt₁ tgt₂).symm) := by
  have hsrc := inv_comp_inv_of_hom_comp_hom (evalObjAppendIso f src₁ src₂)
    (pivotalComparisonIso f (src₁ ++ src₂))
    ((pivotalComparisonIso f src₁).hom ⊗ₘ (pivotalComparisonIso f src₂).hom)
    ((pivotalComparisonIso f src₁).inv ⊗ₘ (pivotalComparisonIso f src₂).inv) (by simp)
    (ParityWord.evalObjAppendIso f src₁.toParity src₂.toParity) _
    (pivotalComparisonIso_append_hom f src₁ src₂)
  dsimp only [transportCoupon]; simp only [Category.assoc]
  rw [reassoc_of% hsrc, pivotalComparisonIso_append_hom, ← tensorHom_comp_tensorHom_assoc,
    ← tensorHom_comp_tensorHom_assoc]

/-- **Half-turn rotation (right mate)**: rotating a coupon `g` via right duality on winding
boundaries transports to `(transportCoupon f g)ᘁ` conjugated by `ParityWord.evalObjDualIso`. -/
theorem transportCoupon_rightDual (f : α → C) {src tgt : WindingWord α}
    (g : evalObj f src ⟶ evalObj f tgt) :
    transportCoupon f ((evalObjRightDualIso f tgt).inv ≫ gᘁ ≫ (evalObjRightDualIso f src).hom) =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_rightDual tgt)) ≫
        (ParityWord.evalObjDualIso f tgt.toParity).inv ≫ (transportCoupon f g)ᘁ ≫
        (ParityWord.evalObjDualIso f src.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_rightDual src).symm) := by
  have htgt := inv_comp_inv_of_hom_comp_hom (evalObjRightDualIso f tgt)
    (pivotalComparisonIso f tgt.rightDual) (((pivotalComparisonIso f tgt).inv)ᘁ)
    (((pivotalComparisonIso f tgt).hom)ᘁ) (by simp [← comp_rightAdjointMate])
    (ParityWord.evalObjDualIso f tgt.toParity) _ (pivotalComparisonIso_rightDual_hom f tgt)
  dsimp only [transportCoupon]; simp only [Category.assoc]
  rw [reassoc_of% htgt, pivotalComparisonIso_rightDual_hom]
  simp only [comp_rightAdjointMate, Category.assoc]

/-- **Opposite half-turn rotation (left mate)**: rotating a coupon `g` via left duality on winding
boundaries also transports to `(transportCoupon f g)ᘁ` conjugated by `ParityWord.evalObjDualIso`. -/
theorem transportCoupon_leftDual (f : α → C) {src tgt : WindingWord α}
    (g : evalObj f src ⟶ evalObj f tgt) :
    transportCoupon f ((evalObjLeftDualIso f tgt).inv ≫ (ᘁg) ≫ (evalObjLeftDualIso f src).hom) =
      eqToHom (congrArg (ParityWord.evalObj f) (toParity_leftDual tgt)) ≫
        (ParityWord.evalObjDualIso f tgt.toParity).inv ≫ (transportCoupon f g)ᘁ ≫
        (ParityWord.evalObjDualIso f src.toParity).hom ≫
        eqToHom (congrArg (ParityWord.evalObj f) (toParity_leftDual src).symm) := by
  have htgt := inv_comp_inv_of_hom_comp_hom (evalObjLeftDualIso f tgt)
    (pivotalComparisonIso f tgt.leftDual)
    ((leftDualIsoRightDual (evalObj f tgt)).hom ≫ ((pivotalComparisonIso f tgt).inv)ᘁ)
    (((pivotalComparisonIso f tgt).hom)ᘁ ≫ (leftDualIsoRightDual (evalObj f tgt)).inv)
    (by simp [Category.assoc, ← comp_rightAdjointMate_assoc])
    (ParityWord.evalObjDualIso f tgt.toParity) _
    (by simpa only [Category.assoc] using pivotalComparisonIso_leftDual_hom f tgt)
  have hmate : (leftDualIsoRightDual (evalObj f tgt)).inv ≫
      (ᘁg) ≫ (leftDualIsoRightDual (evalObj f src)).hom = gᘁ := by
    rw [leftAdjointMate_comp_leftDualIsoRightDual_hom, Iso.inv_hom_id_assoc]
  dsimp only [transportCoupon]; simp only [Category.assoc] at htgt ⊢
  rw [reassoc_of% htgt, pivotalComparisonIso_leftDual_hom, reassoc_of% hmate]
  simp only [comp_rightAdjointMate, Category.assoc]

/-- **Full-turn rotation (double mate)**: the double right mate of `transportCoupon f g` is its
conjugate by `pivotalIsoApp`. -/
theorem rightAdjointMate_rightAdjointMate_transportCoupon (f : α → C) {src tgt : WindingWord α}
    (g : evalObj f src ⟶ evalObj f tgt) :
    (transportCoupon f g)ᘁᘁ =
      (pivotalIsoApp (ParityWord.evalObj f src.toParity)).inv ≫ transportCoupon f g ≫
        (pivotalIsoApp (ParityWord.evalObj f tgt.toParity)).hom :=
  rightAdjointMate_rightAdjointMate (transportCoupon f g)

end WindingWord

namespace RigidObject

/-- Direct comparison isomorphism `X.evalObj f ≅ ParityWord.evalObj f X.normalizeParity`. -/
noncomputable def evalObjNormalizeParityIso {α : Type*} (f : α → C) (X : RigidObject α) :
    X.evalObj f ≅ ParityWord.evalObj f X.normalizeParity :=
  evalObjNormalizeIso f X ≪≫ WindingWord.pivotalComparisonIso f X.normalize ≪≫
    eqToIso (congrArg (ParityWord.evalObj f) (normalizeParity_eq_toParity_normalize X).symm)

end RigidObject

end TauCeti

namespace CategoryTheory.Functor

open TauCeti

variable {C D : Type*} [Category* C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]
  [Category* D] [MonoidalCategory D] [RigidCategory D] [PivotalCategory D] (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor `F : C ⥤ D` between pivotal categories is pivotal (`F.IsPivotal`) if
and only if it preserves `(pivotalAtomIso X 2).inv : X ⟶ Xᘁᘁ` along `F.mapDoubleRightDualIso`. -/
theorem isPivotal_iff_map_pivotalAtomIso_two_inv :
    F.IsPivotal ↔ ∀ X : C,
      F.map (pivotalAtomIso X 2).inv ≫ (F.mapDoubleRightDualIso X).hom =
        (pivotalAtomIso (F.obj X) 2).inv := by
  simp only [pivotalAtomIso_two, Iso.symm_inv]
  exact F.isPivotal_iff_map_pivotalIsoApp_hom_comp_mapDoubleRightDualIso_hom

end CategoryTheory.Functor
