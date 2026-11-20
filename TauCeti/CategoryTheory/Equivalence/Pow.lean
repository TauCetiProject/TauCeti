/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Equivalence
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
* `CategoryTheory.Equivalence.inverseCommIso` and `CategoryTheory.Equivalence.powCommIso`: a
  functor `F` with `e ⋙ F ≅ F ⋙ e'` also intertwines the inverses and all integer powers,
  `e ^ j ⋙ F ≅ F ⋙ e' ^ j`.  This is how a functor between graded categories which commutes with
  the grading shifts is compared on every internal degree.  Their components are computed by
  `CategoryTheory.Equivalence.inverseCommIso_hom_app` and, from one power to the next, by
  `CategoryTheory.Equivalence.powCommIso_succ_hom_app`.
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

/-- **The predecessor isomorphism `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.** -/
def powPredIso (e : C ≌ C) (j : ℤ) :
    e.inverse ⋙ (e ^ j).functor ≅ (e ^ (j - 1)).functor :=
  Functor.isoWhiskerLeft e.inverse (eqToIso (by rw [Int.sub_add_cancel]) ≪≫ e.powSuccIso (j - 1)) ≪≫
    e.invFunIdAssoc _

/-- **Additivity of the integer powers of an autoequivalence**: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`.
At `a = 0` it is the left unitor; it is extended to every `a` by `Int.inductionOn'`, raising `a`
through `CategoryTheory.Equivalence.powSuccIso` and lowering it through
`CategoryTheory.Equivalence.powPredIso`. -/
def powAddIso (e : C ≌ C) (a b : ℤ) :
    (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor :=
  Int.inductionOn' (motive := fun a => (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor)
    a 0 (eqToIso (by rw [Int.zero_add]) ≪≫ (Functor.leftUnitor _).symm)
    (fun a _ ih => eqToIso (by rw [Int.add_right_comm]) ≪≫ e.powSuccIso (a + b) ≪≫
      Functor.isoWhiskerLeft e.functor ih ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (e.powSuccIso a).symm _)
    (fun a _ ih => (e.invFunIdAssoc _).symm ≪≫
      Functor.isoWhiskerLeft e.inverse
        ((e.powSuccIso (a - 1 + b)).symm ≪≫
          eqToIso (by rw [show a - 1 + b + 1 = a + b by omega]) ≪≫ ih) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (e.powPredIso a) _)

/-- **The opposite-handed successor isomorphism `e ^ (j + 1) ≅ e ^ j ⋙ e`.** -/
def powSuccRightIso (e : C ≌ C) (j : ℤ) :
    (e ^ (j + 1)).functor ≅ (e ^ j).functor ⋙ e.functor :=
  e.powAddIso j 1

section Comm

variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {e : C ≌ C} {e' : D ≌ D}

/-- A functor intertwining two autoequivalences, `e ⋙ F ≅ F ⋙ e'`, also intertwines their
inverses: `e⁻¹ ⋙ F ≅ F ⋙ e'⁻¹`.  This is the horizontal inverse `CategoryTheory.CatCommSq.hInv`
of the 2-commutative square given by `σ`. -/
def inverseCommIso (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    e.inverse ⋙ F ≅ F ⋙ e'.inverse :=
  (CatCommSq.hInv e F F e' ⟨σ⟩).iso

@[simp]
theorem inverseCommIso_hom_app
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (Y : C) :
    (Equivalence.inverseCommIso σ).hom.app Y =
      e'.unitIso.hom.app (F.obj (e.inverse.obj Y)) ≫
        e'.inverse.map (σ.inv.app (e.inverse.obj Y)) ≫
          e'.inverse.map (F.map (e.counitIso.hom.app Y)) := by
  simp [Equivalence.inverseCommIso]

@[simp]
theorem inverseCommIso_inv_app
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (Y : C) :
    (Equivalence.inverseCommIso σ).inv.app Y =
      e'.inverse.map (F.map (e.counitIso.inv.app Y)) ≫
        e'.inverse.map (σ.hom.app (e.inverse.obj Y)) ≫
          e'.unitIso.inv.app (F.obj (e.inverse.obj Y)) := by
  simp [Equivalence.inverseCommIso]

/-- Precomposing `CategoryTheory.Equivalence.inverseCommIso σ` with the unit of `e` and
postcomposing with `σ` and the inverse unit of `e'` gives the identity: this is the step from the
power `-1` to the power `0` of `CategoryTheory.Equivalence.powCommIso_succ_hom_app`. -/
theorem inverseCommIso_hom_app_unit
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : C) :
    F.map (e.unitIso.hom.app X) ≫ (Equivalence.inverseCommIso σ).hom.app (e.functor.obj X) ≫
      e'.inverse.map (σ.hom.app X) ≫ e'.unitIso.inv.app (F.obj X) = 𝟙 _ := by
  have h1 := e'.unitIso.hom.naturality (F.map (e.unitIso.hom.app X))
  have h2 := σ.inv.naturality (e.unitIso.hom.app X)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2
  rw [Equivalence.inverseCommIso_hom_app, Category.assoc, reassoc_of% h1]
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
`e ⋙ F ≅ F ⋙ e'` gives `e ^ j ⋙ F ≅ F ⋙ e' ^ j` for every `j : ℤ`.  Negative powers use
`CategoryTheory.Equivalence.inverseCommIso`. -/
def powCommIso (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    ∀ j : ℤ, (e ^ j).functor ⋙ F ≅ F ⋙ (e' ^ j).functor
  | Int.ofNat n => e.powNatCommIso e' F σ n
  | Int.negSucc n => e.symm.powNatCommIso e'.symm F (Equivalence.inverseCommIso σ) (n + 1)

/-- At the zeroth power, `CategoryTheory.Equivalence.powCommIso` is the comparison of unitors
`𝟭 ⋙ F ≅ F ⋙ 𝟭`. -/
theorem powCommIso_zero
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ 0 = Functor.leftUnitor F ≪≫ (Functor.rightUnitor F).symm := by
  rfl

/-- At the first power, `CategoryTheory.Equivalence.powCommIso` is the given intertwiner. -/
theorem powCommIso_one (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ 1 = σ := by
  rfl

/-- At the power `-1`, `CategoryTheory.Equivalence.powCommIso` is the intertwiner of the inverses
given by `CategoryTheory.Equivalence.inverseCommIso`. -/
theorem powCommIso_neg_one
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    Equivalence.powCommIso σ (-1) = Equivalence.inverseCommIso σ := by
  rfl

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
    (Equivalence.powCommIso σ (-1)).hom = (Equivalence.inverseCommIso σ).hom := by
  rw [Equivalence.powCommIso_neg_one]

@[simp]
theorem powCommIso_neg_one_inv
    (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    (Equivalence.powCommIso σ (-1)).inv = (Equivalence.inverseCommIso σ).inv := by
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
    simpa [Equivalence.powSuccIso] using (Equivalence.inverseCommIso_hom_app_unit σ X).symm
  · change (Equivalence.powCommIso σ (Int.negSucc m)).hom.app X = _
    dsimp only [Equivalence.powSuccIso, Equivalence.powCommIso, HPow.hPow, Pow.pow,
      Equivalence.pow, Equivalence.powNat, Equivalence.powNatCommIso]
    have h := (e.symm.powNatCommIso e'.symm F (Equivalence.inverseCommIso σ) (m + 1)).hom.naturality
      (e.unitIso.hom.app X)
    have k := congrArg (e'.symm.powNat (m + 1)).functor.map
      (Equivalence.inverseCommIso_hom_app_unit σ X)
    simp only [Functor.comp_map, Functor.map_comp, Functor.map_id,
      Equivalence.inverseCommIso_hom_app, Category.assoc] at h k
    simp only [Functor.comp_obj, Equivalence.trans_functor, Equivalence.symm_functor,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.id_obj,
      Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, Functor.map_comp,
      Functor.associator_inv_app, Equivalence.inverseCommIso_hom_app, Category.id_comp,
      Functor.comp_map, Iso.trans_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc,
      Functor.leftUnitor_hom_app, CatCommSq.hComp_iso_hom_app, reassoc_of% h, k]
    -- The remaining `F.map (𝟙 _)` sits at the unreduced object
    -- `(e ^ (Int.negSucc (m + 1) + 1)).functor.obj X`, so `Functor.map_id` only applies up to
    -- definitional unfolding.
    exact ((congrArg (· ≫ _) (F.map_id _)).trans (Category.id_comp _)).symm

end Comm

end CategoryTheory.Equivalence
