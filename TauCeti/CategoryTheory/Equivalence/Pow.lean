/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.Ring

/-!
# Additivity of the integer powers of an autoequivalence

Mathlib defines the integer powers `e ^ j` of an autoequivalence `e : C ≌ C` by recursion and
records `e ^ 0`, `e ^ 1` and `e ^ (-1)`, but leaves the comparison of `e ^ (a + b)` with the
composite `e ^ a ⋙ e ^ b` as an explicit TODO.  This file supplies that comparison as an
isomorphism of the underlying functors, together with the successor and predecessor forms which
consume it.

Only the underlying functors are compared.  `e ^ (a + b)` and `(e ^ a).trans (e ^ b)` are not
equal as equivalences — the recursion inserts unitors — so the isomorphism below, and not an
equation, is what downstream constructions use.

## Main definitions

* `CategoryTheory.Equivalence.powSuccIso`: `e ^ (j + 1) ≅ e ⋙ e ^ j`, by case analysis on `j`.
* `CategoryTheory.Equivalence.powPredIso`: `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.
* `CategoryTheory.Equivalence.powAddIso`: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`.
* `CategoryTheory.Equivalence.powSuccRightIso`: `e ^ (j + 1) ≅ e ^ j ⋙ e`, the opposite-handed
  successor isomorphism, which the additivity isomorphism supplies but the recursion does not.
* `CategoryTheory.Equivalence.inverseCommIso` and `CategoryTheory.Equivalence.powCommIso`: a
  functor `F` with `e ⋙ F ≅ F ⋙ e'` also intertwines the inverses and all integer powers,
  `e ^ j ⋙ F ≅ F ⋙ e' ^ j`.  This is how a functor between graded categories which commutes with
  the grading shifts is compared on every internal degree.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u v' u'

variable {C : Type u} [Category.{v} C]

/-- **The successor isomorphism `e ^ (j + 1) ≅ e ⋙ e ^ j`.**  Mathlib's power is built by
prepending a copy of `e`, so at a positive exponent the isomorphism is the identity.  Each of the
remaining cases inserts exactly what the recursion leaves out there: a right unitor at `j = 0`,
where `e ^ 0` is the identity functor; the unit isomorphism at `j = -1`, where `e ⋙ e ^ (-1)` is
`e ⋙ e.inverse`; and at every `j ≤ -2` a composite of a left unitor, the unit isomorphism and an
associator, which grows a negative power by inserting `e ⋙ e.inverse` in front of it. -/
def _root_.CategoryTheory.Equivalence.powSuccIso (e : C ≌ C) : ∀ j : ℤ,
    (e ^ (j + 1)).functor ≅ e.functor ⋙ (e ^ j).functor
  | (0 : ℕ) => (Functor.rightUnitor e.functor).symm
  | ((_ + 1 : ℕ) : ℤ) => Iso.refl _
  | Int.negSucc 0 => e.unitIso
  | Int.negSucc (m + 1) =>
      (Functor.leftUnitor (e.symm.powNat (m + 1)).functor).symm ≪≫
        Functor.isoWhiskerRight e.unitIso _ ≪≫
          Functor.associator e.functor e.inverse (e.symm.powNat (m + 1)).functor

/-- **The predecessor isomorphism `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.** -/
def _root_.CategoryTheory.Equivalence.powPredIso (e : C ≌ C) (j : ℤ) :
    e.inverse ⋙ (e ^ j).functor ≅ (e ^ (j - 1)).functor :=
  Functor.isoWhiskerLeft e.inverse
      (eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (by ring : j = j - 1 + 1)) ≪≫
        e.powSuccIso (j - 1)) ≪≫
    e.invFunIdAssoc _

/-- The inductive step of `CategoryTheory.Equivalence.powAddIso` which raises the first exponent
by one. -/
private def _root_.CategoryTheory.Equivalence.powAddIsoOfSucc (e : C ≌ C) (b a a' : ℤ)
    (h : a' = a + 1)
    (ih : (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor) :
    (e ^ (a' + b)).functor ≅ (e ^ a').functor ⋙ (e ^ b).functor :=
  eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (by rw [h]; ring : a' + b = a + b + 1)) ≪≫
    e.powSuccIso (a + b) ≪≫ Functor.isoWhiskerLeft e.functor ih ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((e.powSuccIso a).symm ≪≫
            eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (by rw [h] : a + 1 = a'))) _

/-- The inductive step of `CategoryTheory.Equivalence.powAddIso` which lowers the first exponent
by one. -/
private def _root_.CategoryTheory.Equivalence.powAddIsoOfPred (e : C ≌ C) (b a a' : ℤ)
    (h : a' = a - 1)
    (ih : (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor) :
    (e ^ (a' + b)).functor ≅ (e ^ a').functor ⋙ (e ^ b).functor :=
  (e.invFunIdAssoc _).symm ≪≫
    Functor.isoWhiskerLeft e.inverse
        ((e.powSuccIso (a' + b)).symm ≪≫
          eqToIso (congrArg (fun i : ℤ => (e ^ i).functor)
            (by rw [h]; ring : a' + b + 1 = a + b)) ≪≫ ih) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (e.powPredIso a ≪≫
            eqToIso (congrArg (fun i : ℤ => (e ^ i).functor) (by rw [h] : a - 1 = a'))) _

/-- Additivity of the integer powers at a nonnegative first exponent. -/
private def _root_.CategoryTheory.Equivalence.powAddNatIso (e : C ≌ C) (b : ℤ) : ∀ n : ℕ,
    (e ^ ((n : ℤ) + b)).functor ≅ (e ^ (n : ℤ)).functor ⋙ (e ^ b).functor
  | 0 =>
      eqToIso (congrArg (fun i : ℤ => (e ^ i).functor)
          (by push_cast; ring : ((0 : ℕ) : ℤ) + b = b)) ≪≫
        (Functor.leftUnitor _).symm
  | n + 1 =>
      e.powAddIsoOfSucc b (n : ℤ) (((n + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (CategoryTheory.Equivalence.powAddNatIso e b n)

/-- Additivity of the integer powers at a nonpositive first exponent. -/
private def _root_.CategoryTheory.Equivalence.powSubNatIso (e : C ≌ C) (b : ℤ) : ∀ n : ℕ,
    (e ^ (-(n : ℤ) + b)).functor ≅ (e ^ (-(n : ℤ))).functor ⋙ (e ^ b).functor
  | 0 =>
      eqToIso (congrArg (fun i : ℤ => (e ^ i).functor)
          (by push_cast; ring : -((0 : ℕ) : ℤ) + b = b)) ≪≫
        (Functor.leftUnitor _).symm
  | n + 1 =>
      e.powAddIsoOfPred b (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (CategoryTheory.Equivalence.powSubNatIso e b n)

/-- **Additivity of the integer powers of an autoequivalence**: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`. -/
def _root_.CategoryTheory.Equivalence.powAddIso (e : C ≌ C) : ∀ a b : ℤ,
    (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor
  | Int.ofNat n, b => e.powAddNatIso b n
  | Int.negSucc n, b => e.powSubNatIso b (n + 1)

/-- **The opposite-handed successor isomorphism `e ^ (j + 1) ≅ e ^ j ⋙ e`.** -/
def _root_.CategoryTheory.Equivalence.powSuccRightIso (e : C ≌ C) (j : ℤ) :
    (e ^ (j + 1)).functor ≅ (e ^ j).functor ⋙ e.functor :=
  e.powAddIso j 1

section Comm

variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {e : C ≌ C} {e' : D ≌ D}

/-- A functor intertwining two autoequivalences, `e ⋙ F ≅ F ⋙ e'`, also intertwines their
inverses: `e⁻¹ ⋙ F ≅ F ⋙ e'⁻¹`. -/
def _root_.CategoryTheory.Equivalence.inverseCommIso (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    e.inverse ⋙ F ≅ F ⋙ e'.inverse :=
  Iso.isoCompInverse (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse σ.symm ≪≫
    Iso.inverseCompIso (Iso.refl _))

/-- The natural-number powers of two autoequivalences intertwined by a functor are intertwined by
it, following the recursion defining `CategoryTheory.Equivalence.powNat`. -/
private def _root_.CategoryTheory.Equivalence.powNatCommIso (e : C ≌ C) (e' : D ≌ D) (F : C ⥤ D)
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) : ∀ n : ℕ,
    (e.powNat n).functor ⋙ F ≅ F ⋙ (e'.powNat n).functor
  | 0 => Functor.leftUnitor F ≪≫ (Functor.rightUnitor F).symm
  | 1 => σ
  | n + 2 => Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e.functor
        (CategoryTheory.Equivalence.powNatCommIso e e' F σ (n + 1)) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σ _ ≪≫ Functor.associator _ _ _

/-- **A functor intertwining two autoequivalences intertwines all their integer powers**:
`e ⋙ F ≅ F ⋙ e'` gives `e ^ j ⋙ F ≅ F ⋙ e' ^ j` for every `j : ℤ`.  Negative powers use
`CategoryTheory.Equivalence.inverseCommIso`. -/
def _root_.CategoryTheory.Equivalence.powCommIso (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    ∀ j : ℤ, (e ^ j).functor ⋙ F ≅ F ⋙ (e' ^ j).functor
  | Int.ofNat n => e.powNatCommIso e' F σ n
  | Int.negSucc n => e.symm.powNatCommIso e'.symm F (Equivalence.inverseCommIso σ) (n + 1)

/-- At the zeroth power, `CategoryTheory.Equivalence.powCommIso` is the comparison of unitors
`𝟭 ⋙ F ≅ F ⋙ 𝟭`. -/
theorem _root_.CategoryTheory.Equivalence.powCommIso_zero
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ 0 = Functor.leftUnitor F ≪≫ (Functor.rightUnitor F).symm := by
  unfold Equivalence.powCommIso; rfl

/-- At the first power, `CategoryTheory.Equivalence.powCommIso` is the given intertwiner. -/
theorem _root_.CategoryTheory.Equivalence.powCommIso_one (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ 1 = σ := by
  unfold Equivalence.powCommIso; rfl

/-- At the power `-1`, `CategoryTheory.Equivalence.powCommIso` is the intertwiner of the inverses
given by `CategoryTheory.Equivalence.inverseCommIso`. -/
theorem _root_.CategoryTheory.Equivalence.powCommIso_neg_one
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ (-1) = Equivalence.inverseCommIso σ := by
  unfold Equivalence.powCommIso; rfl

@[simp]
theorem _root_.CategoryTheory.Equivalence.powCommIso_zero_hom_app
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : C) :
    (Equivalence.powCommIso σ 0).hom.app X = 𝟙 (F.obj X) := by
  simp [Equivalence.powCommIso_zero]

@[simp]
theorem _root_.CategoryTheory.Equivalence.powCommIso_zero_inv_app
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : C) :
    (Equivalence.powCommIso σ 0).inv.app X = 𝟙 (F.obj X) := by
  simp [Equivalence.powCommIso_zero]

@[simp]
theorem _root_.CategoryTheory.Equivalence.powCommIso_one_hom
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ 1).hom = σ.hom := by
  rw [Equivalence.powCommIso_one]

@[simp]
theorem _root_.CategoryTheory.Equivalence.powCommIso_one_inv
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ 1).inv = σ.inv := by
  rw [Equivalence.powCommIso_one]

@[simp]
theorem _root_.CategoryTheory.Equivalence.powCommIso_neg_one_hom
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ (-1)).hom = (Equivalence.inverseCommIso σ).hom := by
  rw [Equivalence.powCommIso_neg_one]

@[simp]
theorem _root_.CategoryTheory.Equivalence.powCommIso_neg_one_inv
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ (-1)).inv = (Equivalence.inverseCommIso σ).inv := by
  rw [Equivalence.powCommIso_neg_one]

end Comm

end TauCeti
