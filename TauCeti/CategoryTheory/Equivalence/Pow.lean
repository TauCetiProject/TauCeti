/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Data.Int.Init

/-!
# Additivity of the integer powers of an autoequivalence

Mathlib defines the integer powers `e ^ j` of an autoequivalence `e : C ≌ C` by recursion and
records `e ^ 0`, `e ^ 1` and `e ^ (-1)`, but leaves the comparison of `e ^ (a + b)` with the
composite `e ^ a ⋙ e ^ b` as an explicit TODO.  This file supplies that comparison as an
isomorphism of the underlying functors, together with the successor and predecessor isomorphisms
from which it is built.

Only the underlying functors are compared.  `e ^ (a + b)` and `(e ^ a).trans (e ^ b)` are not
equal as equivalences — the recursion inserts unitors — so the isomorphism below, and not an
equation, is what downstream constructions use.

## Main definitions

* `CategoryTheory.Equivalence.powSuccIso`: `e ^ (j + 1) ≅ e ⋙ e ^ j`, by case analysis on `j`.
* `CategoryTheory.Equivalence.powPredIso`: `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.
* `CategoryTheory.Equivalence.powAddIso`: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`.
* `CategoryTheory.Equivalence.powSuccRightIso`: `e ^ (j + 1) ≅ e ^ j ⋙ e`, the opposite-handed
  successor isomorphism, which the additivity isomorphism supplies but the recursion does not.
* `CategoryTheory.Equivalence.powCommIso`: a functor `F` with `e ⋙ F ≅ F ⋙ e'` also intertwines
  all integer powers, `e ^ j ⋙ F ≅ F ⋙ e' ^ j`; at negative powers it uses Mathlib's horizontal
  inverse `CategoryTheory.CatCommSq.hInv` of the square given by `e ⋙ F ≅ F ⋙ e'`.  This is how a
  functor between graded categories which commutes with the grading shifts is compared on every
  internal degree.  Its components are computed, from one power to the next, by
  `CategoryTheory.Equivalence.powCommIso_succ_hom_app`.

## Main statements

The defining cases of these isomorphisms are recorded as equations, so that they can be used
without unfolding: `CategoryTheory.Equivalence.powSuccIso_zero` and its siblings for the
successor isomorphism, `CategoryTheory.Equivalence.powAddIso_zero_left`,
`CategoryTheory.Equivalence.powAddIso_add_one_left` and
`CategoryTheory.Equivalence.powAddIso_sub_one_left` for the additivity isomorphism, and
`CategoryTheory.Equivalence.powPredIso_eq_inverseCompIso` and
`CategoryTheory.Equivalence.powSuccRightIso_eq_powAddIso` for the derived ones.
-/

public section

namespace CategoryTheory.Equivalence

universe v u v' u'

variable {C : Type u} [Category.{v} C]

/-- **The successor isomorphism `e ^ (j + 1) ≅ e ⋙ e ^ j`.**  Mathlib's power is built by
prepending a copy of `e`, so at a positive exponent the isomorphism is the identity.  Each of the
remaining cases inserts exactly what the recursion leaves out there: a right unitor at `j = 0`,
where `e ^ 0` is the identity functor; the unit isomorphism at `j = -1`, where `e ⋙ e ^ (-1)` is
`e ⋙ e.inverse`; and at every `j ≤ -2` a composite of a left unitor, the unit isomorphism and an
associator, which grows a negative power by inserting `e ⋙ e.inverse` in front of it. -/
def powSuccIso (e : C ≌ C) : ∀ j : ℤ,
    (e ^ (j + 1)).functor ≅ e.functor ⋙ (e ^ j).functor
  | (0 : ℕ) => (Functor.rightUnitor e.functor).symm
  | ((_ + 1 : ℕ) : ℤ) => Iso.refl _
  | Int.negSucc 0 => e.unitIso
  | Int.negSucc (m + 1) =>
      (Functor.leftUnitor (e.symm.powNat (m + 1)).functor).symm ≪≫
        Functor.isoWhiskerRight e.unitIso _ ≪≫
          Functor.associator e.functor e.inverse (e.symm.powNat (m + 1)).functor

/-- At the exponent `0`, `CategoryTheory.Equivalence.powSuccIso` is the inverse right unitor
`e ≅ e ⋙ 𝟭`. -/
theorem powSuccIso_zero (e : C ≌ C) :
    e.powSuccIso 0 = (Functor.rightUnitor e.functor).symm :=
  powSuccIso.eq_1 e

/-- At a positive exponent, `CategoryTheory.Equivalence.powSuccIso` is the identity. -/
theorem powSuccIso_natCast_add_one (e : C ≌ C) (n : ℕ) :
    e.powSuccIso (n + 1) = Iso.refl _ :=
  powSuccIso.eq_2 e n

/-- At the exponent `-1`, `CategoryTheory.Equivalence.powSuccIso` is the unit isomorphism
`𝟭 ≅ e ⋙ e⁻¹` of `e`. -/
theorem powSuccIso_neg_one (e : C ≌ C) :
    e.powSuccIso (-1) = e.unitIso :=
  powSuccIso.eq_3 e

/-- At an exponent `j ≤ -2`, `CategoryTheory.Equivalence.powSuccIso` inserts the unit isomorphism
of `e` in front of the negative power `e ^ (j + 1)`. -/
theorem powSuccIso_negSucc_add_one (e : C ≌ C) (m : ℕ) :
    e.powSuccIso (Int.negSucc (m + 1)) =
      (Functor.leftUnitor (e ^ Int.negSucc m).functor).symm ≪≫
        Functor.isoWhiskerRight e.unitIso _ ≪≫
          Functor.associator e.functor e.inverse (e ^ Int.negSucc m).functor :=
  powSuccIso.eq_4 e m

@[simp]
theorem powSuccIso_zero_hom_app (e : C ≌ C) (X : C) :
    (e.powSuccIso 0).hom.app X = 𝟙 _ := by
  simp [powSuccIso_zero]

@[simp]
theorem powSuccIso_zero_inv_app (e : C ≌ C) (X : C) :
    (e.powSuccIso 0).inv.app X = 𝟙 _ := by
  simp [powSuccIso_zero]

@[simp]
theorem powSuccIso_natCast_add_one_hom_app (e : C ≌ C) (n : ℕ) (X : C) :
    (e.powSuccIso (n + 1)).hom.app X = 𝟙 _ := by
  rw [powSuccIso_natCast_add_one]
  -- The identity at `(e ^ (n + 2)).functor.obj X` is the identity at
  -- `(e ^ (n + 1)).functor.obj (e.functor.obj X)` by the recursion defining `e ^ j`, which
  -- `simp` does not unfold.
  rfl

@[simp]
theorem powSuccIso_natCast_add_one_inv_app (e : C ≌ C) (n : ℕ) (X : C) :
    (e.powSuccIso (n + 1)).inv.app X = 𝟙 _ := by
  rw [powSuccIso_natCast_add_one]
  -- The identity at `(e ^ (n + 2)).functor.obj X` is the identity at
  -- `(e ^ (n + 1)).functor.obj (e.functor.obj X)` by the recursion defining `e ^ j`, which
  -- `simp` does not unfold.
  rfl

@[simp]
theorem powSuccIso_neg_one_hom_app (e : C ≌ C) (X : C) :
    (e.powSuccIso (-1)).hom.app X = e.unitIso.hom.app X := by
  rw [powSuccIso_neg_one]

@[simp]
theorem powSuccIso_neg_one_inv_app (e : C ≌ C) (X : C) :
    (e.powSuccIso (-1)).inv.app X = e.unitIso.inv.app X := by
  rw [powSuccIso_neg_one]

/-- **The predecessor isomorphism `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`**: the transpose
`CategoryTheory.Iso.inverseCompIso` of the successor isomorphism at `j - 1`. -/
def powPredIso (e : C ≌ C) (j : ℤ) :
    e.inverse ⋙ (e ^ j).functor ≅ (e ^ (j - 1)).functor :=
  Iso.inverseCompIso (G := e)
    (eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (Int.sub_add_cancel j 1).symm) ≪≫
      e.powSuccIso (j - 1))

/-- `CategoryTheory.Equivalence.powPredIso` is the transpose `CategoryTheory.Iso.inverseCompIso`
of the successor isomorphism `CategoryTheory.Equivalence.powSuccIso` at `j - 1`. -/
theorem powPredIso_eq_inverseCompIso (e : C ≌ C) (j : ℤ) :
    e.powPredIso j = Iso.inverseCompIso (G := e)
      (eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (Int.sub_add_cancel j 1).symm) ≪≫
        e.powSuccIso (j - 1)) :=
  powPredIso.eq_1 e j

/-- **Additivity of the integer powers of an autoequivalence**: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`.
At `a = 0` it is, after identifying `0 + b` with `b`, the inverse left unitor; it is extended to
every `a` by `Int.inductionOn'`, raising `a` through `CategoryTheory.Equivalence.powSuccIso` and
lowering it through `CategoryTheory.Equivalence.powPredIso`. -/
def powAddIso (e : C ≌ C) (a b : ℤ) :
    (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor :=
  Int.inductionOn' (motive := fun a => (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor)
    a 0
    (eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (Int.zero_add b)) ≪≫
      (Functor.leftUnitor _).symm)
    (fun a _ ih =>
      eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (Int.add_right_comm a 1 b)) ≪≫
        e.powSuccIso (a + b) ≪≫ Functor.isoWhiskerLeft e.functor ih ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (e.powSuccIso a).symm _)
    (fun a _ ih =>
      have h : a - 1 + b = a + b - 1 := by omega
      eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) h) ≪≫ (e.powPredIso (a + b)).symm ≪≫
        Functor.isoWhiskerLeft e.inverse ih ≪≫ (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (e.powPredIso a) _)

/-- At `a = 0`, `CategoryTheory.Equivalence.powAddIso` is the inverse left unitor of `e ^ b`, after
identifying `0 + b` with `b`. -/
theorem powAddIso_zero_left (e : C ≌ C) (b : ℤ) :
    e.powAddIso 0 b =
      eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (Int.zero_add b)) ≪≫
        (Functor.leftUnitor _).symm :=
  Int.inductionOn'_self

/-- At a nonnegative `a`, `CategoryTheory.Equivalence.powAddIso` at `a + 1` is obtained from its
value at `a` through the successor isomorphisms `CategoryTheory.Equivalence.powSuccIso`. -/
theorem powAddIso_add_one_left (e : C ≌ C) {a : ℤ} (ha : 0 ≤ a) (b : ℤ) :
    e.powAddIso (a + 1) b =
      eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (Int.add_right_comm a 1 b)) ≪≫
        e.powSuccIso (a + b) ≪≫ Functor.isoWhiskerLeft e.functor (e.powAddIso a b) ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (e.powSuccIso a).symm _ :=
  Int.inductionOn'_add_one ha

/-- At a nonpositive `a`, `CategoryTheory.Equivalence.powAddIso` at `a - 1` is obtained from its
value at `a` through the predecessor isomorphisms `CategoryTheory.Equivalence.powPredIso`. -/
theorem powAddIso_sub_one_left (e : C ≌ C) {a : ℤ} (ha : a ≤ 0) (b : ℤ) :
    e.powAddIso (a - 1) b =
      eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (by omega : a - 1 + b = a + b - 1)) ≪≫
        (e.powPredIso (a + b)).symm ≪≫ Functor.isoWhiskerLeft e.inverse (e.powAddIso a b) ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (e.powPredIso a) _ :=
  Int.inductionOn'_sub_one ha

@[simp]
theorem powAddIso_zero_left_hom_app (e : C ≌ C) (b : ℤ) (X : C) :
    (e.powAddIso 0 b).hom.app X = eqToHom (by simp) := by
  simp [powAddIso_zero_left]

@[simp]
theorem powAddIso_zero_left_inv_app (e : C ≌ C) (b : ℤ) (X : C) :
    (e.powAddIso 0 b).inv.app X = eqToHom (by simp) := by
  simp [powAddIso_zero_left]

/-- **The opposite-handed successor isomorphism `e ^ (j + 1) ≅ e ^ j ⋙ e`.** -/
def powSuccRightIso (e : C ≌ C) (j : ℤ) :
    (e ^ (j + 1)).functor ≅ (e ^ j).functor ⋙ e.functor :=
  e.powAddIso j 1

/-- `CategoryTheory.Equivalence.powSuccRightIso` is the additivity isomorphism
`CategoryTheory.Equivalence.powAddIso` at the second exponent `1`. -/
theorem powSuccRightIso_eq_powAddIso (e : C ≌ C) (j : ℤ) :
    e.powSuccRightIso j = e.powAddIso j 1 :=
  powSuccRightIso.eq_1 e j

section Comm

variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {e : C ≌ C} {e' : D ≌ D}

/-- Precomposing the horizontal inverse `CategoryTheory.CatCommSq.hInv` of the square `σ` with the
unit of `e` and postcomposing it with `σ` and the inverse unit of `e'` gives the identity: this is
the step from the power `-1` to the power `0` of
`CategoryTheory.Equivalence.powCommIso_succ_hom_app`. -/
theorem hInv_iso_hom_app_unit
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : C) :
    F.map (e.unitIso.hom.app X) ≫
      (CatCommSq.hInv e F F e' ⟨σ⟩).iso.hom.app (e.functor.obj X) ≫
        e'.inverse.map (σ.hom.app X) ≫ e'.unitIso.inv.app (F.obj X) = 𝟙 _ := by
  have h1 := e'.unitIso.hom.naturality (F.map (e.unitIso.hom.app X))
  have h2 := σ.inv.naturality (e.unitIso.hom.app X)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2
  rw [CatCommSq.hInv_iso_hom_app, Category.assoc, reassoc_of% h1]
  simp only [← Functor.map_comp_assoc, Category.assoc, reassoc_of% h2, ← F.map_comp_assoc,
    Equivalence.functor_unit_comp]
  simp

/-- The natural-number powers of two autoequivalences intertwined by a functor are intertwined by
it, following the recursion defining `CategoryTheory.Equivalence.powNat`: each step pastes one more
copy of the square `σ` with `CategoryTheory.CatCommSq.hComp`. -/
private def powNatCommIso (e : C ≌ C) (e' : D ≌ D) (F : C ⥤ D)
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) : ∀ n : ℕ,
    (e.powNat n).functor ⋙ F ≅ F ⋙ (e'.powNat n).functor
  | 0 => (CatCommSq.hId F).iso
  | 1 => σ
  | n + 2 =>
      (CatCommSq.hComp' ⟨σ⟩ ⟨CategoryTheory.Equivalence.powNatCommIso e e' F σ (n + 1)⟩).iso

/-- **A functor intertwining two autoequivalences intertwines all their integer powers**:
`e ⋙ F ≅ F ⋙ e'` gives `e ^ j ⋙ F ≅ F ⋙ e' ^ j` for every `j : ℤ`.  Negative powers use the
horizontal inverse `CategoryTheory.CatCommSq.hInv` of the square given by `σ`. -/
def powCommIso (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    ∀ j : ℤ, (e ^ j).functor ⋙ F ≅ F ⋙ (e' ^ j).functor
  | Int.ofNat n => e.powNatCommIso e' F σ n
  | Int.negSucc n => e.symm.powNatCommIso e'.symm F (CatCommSq.hInv e F F e' ⟨σ⟩).iso (n + 1)

/-- At the zeroth power, `CategoryTheory.Equivalence.powCommIso` is the comparison of unitors
`𝟭 ⋙ F ≅ F ⋙ 𝟭`. -/
theorem powCommIso_zero
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ 0 = Functor.leftUnitor F ≪≫ (Functor.rightUnitor F).symm :=
  (powCommIso.eq_1 σ 0).trans <| (powNatCommIso.eq_1 e e' F σ).trans <|
    congrArg (fun S : CatCommSq (𝟭 C) F F (𝟭 D) => S.iso) (CatCommSq.hId.eq_1 F)

/-- At the first power, `CategoryTheory.Equivalence.powCommIso` is the given intertwiner. -/
theorem powCommIso_one (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ 1 = σ :=
  (powCommIso.eq_1 σ 1).trans (powNatCommIso.eq_2 e e' F σ)

/-- At the power `-1`, `CategoryTheory.Equivalence.powCommIso` is the intertwiner of the inverses
given by the horizontal inverse `CategoryTheory.CatCommSq.hInv` of the square `σ`. -/
theorem powCommIso_neg_one
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ (-1) = (CatCommSq.hInv e F F e' ⟨σ⟩).iso :=
  (powCommIso.eq_2 σ 0).trans (powNatCommIso.eq_2 e.symm e'.symm F _)

@[simp]
theorem powCommIso_zero_hom_app
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : C) :
    (Equivalence.powCommIso σ 0).hom.app X = 𝟙 (F.obj X) := by
  simp [Equivalence.powCommIso_zero]

@[simp]
theorem powCommIso_zero_inv_app
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : C) :
    (Equivalence.powCommIso σ 0).inv.app X = 𝟙 (F.obj X) := by
  simp [Equivalence.powCommIso_zero]

@[simp]
theorem powCommIso_one_hom
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ 1).hom = σ.hom := by
  rw [Equivalence.powCommIso_one]

@[simp]
theorem powCommIso_one_inv
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ 1).inv = σ.inv := by
  rw [Equivalence.powCommIso_one]

@[simp]
theorem powCommIso_neg_one_hom
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ (-1)).hom = (CatCommSq.hInv e F F e' ⟨σ⟩).iso.hom := by
  rw [Equivalence.powCommIso_neg_one]

@[simp]
theorem powCommIso_neg_one_inv
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ (-1)).inv = (CatCommSq.hInv e F F e' ⟨σ⟩).iso.inv := by
  rw [Equivalence.powCommIso_neg_one]

/-- **The successor step of `CategoryTheory.Equivalence.powCommIso`**: its component at the power
`j + 1` is its component at the power `j`, followed by `σ`, conjugated by the successor
isomorphisms `CategoryTheory.Equivalence.powSuccIso` of `e` and `e'`. -/
theorem powCommIso_succ_hom_app
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (j : ℤ) (X : C) :
    (Equivalence.powCommIso σ (j + 1)).hom.app X =
      F.map ((e.powSuccIso j).hom.app X) ≫
        (Equivalence.powCommIso σ j).hom.app (e.functor.obj X) ≫
          (e' ^ j).functor.map (σ.hom.app X) ≫ (e'.powSuccIso j).inv.app (F.obj X) := by
  -- In each case the power `j + 1` is a numeral or constructor only up to definitional unfolding
  -- of `Int` addition and of the recursions defining `e ^ j`, `powNat` and `powCommIso`, which
  -- `simp` does not perform; `change` and `dsimp only` expose those reduced forms.
  rcases j with (_ | n) | (_ | m)
  · change (Equivalence.powCommIso σ 1).hom.app X = _
    simp [Equivalence.powSuccIso]
  · change (e.powNatCommIso e' F σ (n + 2)).hom.app X =
      F.map (𝟙 _) ≫ (e.powNatCommIso e' F σ (n + 1)).hom.app (e.functor.obj X) ≫
        (e'.powNat (n + 1)).functor.map (σ.hom.app X) ≫ 𝟙 _
    dsimp only [Equivalence.powNat, Equivalence.powNatCommIso]
    simp
  · change (Equivalence.powCommIso σ 0).hom.app X = _
    simpa [Equivalence.powSuccIso] using (Equivalence.hInv_iso_hom_app_unit σ X).symm
  · change (Equivalence.powCommIso σ (Int.negSucc m)).hom.app X = _
    dsimp only [Equivalence.powSuccIso, Equivalence.powCommIso, HPow.hPow, Pow.pow,
      Equivalence.pow, Equivalence.powNat, Equivalence.powNatCommIso]
    have h :=
      (e.symm.powNatCommIso e'.symm F (CatCommSq.hInv e F F e' ⟨σ⟩).iso (m + 1)).hom.naturality
        (e.unitIso.hom.app X)
    have k := congrArg (e'.symm.powNat (m + 1)).functor.map
      (Equivalence.hInv_iso_hom_app_unit σ X)
    simp only [Functor.comp_map, Functor.map_comp, Functor.map_id,
      CatCommSq.hInv_iso_hom_app, Category.assoc] at h k
    simp only [Functor.comp_obj, Equivalence.trans_functor, Equivalence.symm_functor,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.id_obj,
      Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, Functor.map_comp,
      Functor.associator_inv_app, CatCommSq.hInv_iso_hom_app, Category.id_comp,
      Functor.comp_map, Iso.trans_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc,
      Functor.leftUnitor_hom_app, CatCommSq.hComp_iso_hom_app, reassoc_of% h, k]
    -- The remaining `F.map (𝟙 _)` sits at the unreduced object
    -- `(e ^ (Int.negSucc (m + 1) + 1)).functor.obj X`, so `Functor.map_id` only applies up to
    -- definitional unfolding.
    exact ((congrArg (· ≫ _) (F.map_id _)).trans (Category.id_comp _)).symm

end Comm

end CategoryTheory.Equivalence
