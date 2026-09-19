/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring

/-!
# The shift on periodic complexes

An `n`-periodic complex in a preadditive category `C` is a family of objects `Xⁱ` indexed by
`i : ZMod n` with differentials `Xⁱ ⟶ Xⁱ⁺¹` whose consecutive composites vanish. We use Mathlib's
homological complexes for the shape `ComplexShape.up (ZMod n)`, so that the category, its
preadditive and linear structures, evaluation functors, homotopies and the homotopy category
`HomotopyCategory C (ComplexShape.up (ZMod n))` are all Mathlib's.

This file equips periodic complexes and their homotopy category with a shift by `ℤ`, following
the conventions of Mathlib's shift on cochain complexes: `(X⟦k⟧)ⁱ = Xⁱ⁺ᵏ` and the differential
is multiplied by `(-1)ᵏ`. The shift by `1` is thus the cyclic shift
`(X⟦1⟧)ⁱ = Xⁱ⁺¹`, `d_{X⟦1⟧} = -d_X`, and generates the whole shift. Since the grading is cyclic,
the shift is periodic: shifting by an even multiple `k` of the period is isomorphic to the
identity, both on complexes and on the homotopy category.

None of the constructions here needs the period to be positive, so no `NeZero n` hypothesis
is imposed. For `n = 0`, `ZMod 0` is `ℤ` and the formulas are those of Mathlib's shift on
cochain complexes.

## Main definitions

* `TauCeti.PeriodicComplex.shiftFunctor`: the shift by `k : ℤ` on `ZMod n`-graded complexes.
* `TauCeti.PeriodicComplex.instHasShift`: the resulting shift by `ℤ` on periodic complexes.
* `TauCeti.PeriodicComplex.shiftFunctorIsoId`: the periodicity isomorphism `X⟦k⟧ ≅ X` for even
  `k` divisible by `n`.
* `TauCeti.PeriodicComplex.homotopyShift`: the shift of a homotopy.
* `TauCeti.PeriodicComplex.homotopyCategoryShiftFunctorIsoId`: periodicity in the homotopy
  category.

## References

* Torkil Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters
  **25** (2018), 199–236, Section 3.
* The construction mirrors Joël Riou's shift on cochain complexes in
  `Mathlib.Algebra.Homology.HomotopyCategory.Shift`.
-/

@[expose] public section

namespace TauCeti

open CategoryTheory

universe v u

namespace PeriodicComplex

open HomologicalComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] (n : ℕ)

/-- The shift by `k : ℤ` on `ZMod n`-graded complexes: it sends `K` to the complex which is
`K.X (i + k)` in degree `i`, with the differentials multiplied by `(-1)ᵏ`. -/
@[implicit_reducible, simps]
def shiftFunctor (k : ℤ) :
    HomologicalComplex C (ComplexShape.up (ZMod n)) ⥤
      HomologicalComplex C (ComplexShape.up (ZMod n)) where
  obj K :=
    { X := fun i => K.X (i + k)
      d := fun i j => k.negOnePow • K.d (i + k) (j + k)
      shape i j hij := by
        rw [K.shape _ _ (fun h => hij (by simp only [ComplexShape.up_Rel] at h ⊢; grind)),
          smul_zero] }
  map φ := { f := fun i => φ.f (i + k) }

instance (k : ℤ) : (shiftFunctor C n k).Additive where

instance (k : ℤ) {R : Type*} [Ring R] [Linear R C] : Functor.Linear R (shiftFunctor C n k) where

variable {C n} in
/-- The canonical isomorphism `((shiftFunctor C n k).obj K).X i ≅ K.X m` when `m = i + k`. -/
@[simp]
def shiftFunctorObjXIso (K : HomologicalComplex C (ComplexShape.up (ZMod n))) (k : ℤ)
    (i m : ZMod n) (hm : m = i + k) : ((shiftFunctor C n k).obj K).X i ≅ K.X m :=
  K.XIsoOfEq hm.symm

attribute [local simp] XIsoOfEq_hom_naturality

/-- The shift by `k` identifies to the identity functor when `k = 0`. -/
@[implicit_reducible, simps!]
def shiftFunctorZero' (k : ℤ) (h : k = 0) : shiftFunctor C n k ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => shiftFunctorObjXIso K k i i (by simp [h]))
    (fun _ _ _ => by simp [h])) (fun _ ↦ by ext; simp)

/-- The compatibility of the shift functors with the addition of integers. -/
@[implicit_reducible, simps!]
def shiftFunctorAdd' (k₁ k₂ k₁₂ : ℤ) (h : k₁ + k₂ = k₁₂) :
    shiftFunctor C n k₁₂ ≅ shiftFunctor C n k₁ ⋙ shiftFunctor C n k₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => shiftFunctorObjXIso K k₁₂ i (i + k₂ + k₁) (by subst h; push_cast; ring))
    (fun _ _ _ => by subst h; simp [Int.negOnePow_add, smul_smul, mul_comm k₁.negOnePow]))
    (fun _ ↦ by ext; simp)

section

attribute [local simp] XIsoOfEq

/-- Periodic complexes carry a shift by `ℤ`, whose shift by `1` is the cyclic shift. -/
instance instHasShift : HasShift (HomologicalComplex C (ComplexShape.up (ZMod n))) ℤ :=
  hasShiftMk _ _
    { F := shiftFunctor C n
      zero := shiftFunctorZero' C n _ rfl
      add := fun k₁ k₂ => shiftFunctorAdd' C n k₁ k₂ _ rfl }

end

instance (k : ℤ) :
    (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up (ZMod n))) k).Additive :=
  inferInstanceAs (shiftFunctor C n k).Additive

instance (k : ℤ) {R : Type*} [Ring R] [Linear R C] :
    Functor.Linear R
      (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up (ZMod n))) k) :=
  inferInstanceAs (Functor.Linear R (shiftFunctor C n k))

variable {C n}

@[simp]
lemma shiftFunctor_obj_X' (K : HomologicalComplex C (ComplexShape.up (ZMod n))) (k : ℤ)
    (i : ZMod n) : (K⟦k⟧).X i = K.X (i + k) := rfl

@[simp]
lemma shiftFunctor_map_f' {K L : HomologicalComplex C (ComplexShape.up (ZMod n))} (φ : K ⟶ L)
    (k : ℤ) (i : ZMod n) : (φ⟦k⟧').f i = φ.f (i + k) := rfl

@[simp]
lemma shiftFunctor_obj_d' (K : HomologicalComplex C (ComplexShape.up (ZMod n))) (k : ℤ)
    (i j : ZMod n) : (K⟦k⟧).d i j = k.negOnePow • K.d (i + k) (j + k) := rfl

lemma shiftFunctorAdd_hom_app_f (K : HomologicalComplex C (ComplexShape.up (ZMod n)))
    (k₁ k₂ : ℤ) (i : ZMod n) :
    ((CategoryTheory.shiftFunctorAdd (HomologicalComplex C (ComplexShape.up (ZMod n)))
      k₁ k₂).hom.app K).f i = (K.XIsoOfEq (by push_cast; ring)).hom := rfl

lemma shiftFunctorAdd_inv_app_f (K : HomologicalComplex C (ComplexShape.up (ZMod n)))
    (k₁ k₂ : ℤ) (i : ZMod n) :
    ((CategoryTheory.shiftFunctorAdd (HomologicalComplex C (ComplexShape.up (ZMod n)))
      k₁ k₂).inv.app K).f i = (K.XIsoOfEq (by push_cast; ring)).hom := rfl

lemma shiftFunctorAdd'_hom_app_f' (K : HomologicalComplex C (ComplexShape.up (ZMod n)))
    (k₁ k₂ k₁₂ : ℤ) (h : k₁ + k₂ = k₁₂) (i : ZMod n) :
    ((CategoryTheory.shiftFunctorAdd' (HomologicalComplex C (ComplexShape.up (ZMod n)))
      k₁ k₂ k₁₂ h).hom.app K).f i =
      (K.XIsoOfEq (by subst h; push_cast; ring)).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_hom_app_f]

lemma shiftFunctorAdd'_inv_app_f' (K : HomologicalComplex C (ComplexShape.up (ZMod n)))
    (k₁ k₂ k₁₂ : ℤ) (h : k₁ + k₂ = k₁₂) (i : ZMod n) :
    ((CategoryTheory.shiftFunctorAdd' (HomologicalComplex C (ComplexShape.up (ZMod n)))
      k₁ k₂ k₁₂ h).inv.app K).f i =
      (K.XIsoOfEq (by subst h; push_cast; ring)).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_inv_app_f]

lemma shiftFunctorZero_hom_app_f (K : HomologicalComplex C (ComplexShape.up (ZMod n)))
    (i : ZMod n) :
    ((CategoryTheory.shiftFunctorZero (HomologicalComplex C (ComplexShape.up (ZMod n))) ℤ).hom.app
      K).f i = (K.XIsoOfEq (by simp)).hom := rfl

lemma shiftFunctorZero_inv_app_f (K : HomologicalComplex C (ComplexShape.up (ZMod n)))
    (i : ZMod n) :
    ((CategoryTheory.shiftFunctorZero (HomologicalComplex C (ComplexShape.up (ZMod n))) ℤ).inv.app
      K).f i = (K.XIsoOfEq (by simp)).hom := rfl

variable (C n)

/-- Shifting by `k` and evaluating in degree `i` identifies to evaluating in degree `i'` when
`i + k = i'`. -/
@[simps!]
def shiftEval (k : ℤ) (i i' : ZMod n) (hi : i + k = i') :
    CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up (ZMod n))) k ⋙
      HomologicalComplex.eval C (ComplexShape.up (ZMod n)) i ≅
      HomologicalComplex.eval C (ComplexShape.up (ZMod n)) i' :=
  NatIso.ofComponents (fun K => K.XIsoOfEq hi) (by simp)

/-- Periodicity of the shift: shifting by an even integer `k` which is a multiple of the period
is isomorphic to the identity. The degree-`i` component is the identification
`Xⁱ⁺ᵏ = Xⁱ`; evenness of `k` is what makes it commute with the differentials. -/
@[simps!]
def shiftFunctorIsoId (k : ℤ) (hk : (k : ZMod n) = 0) (he : Even k) :
    CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up (ZMod n))) k ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.XIsoOfEq (by simp [hk]))
    (fun _ _ _ => by simp [Int.negOnePow_even k he]))
    (fun _ ↦ by ext; simp)

variable {C n}

/-- If `h : Homotopy φ₁ φ₂` and `k : ℤ`, this is the induced homotopy between `φ₁⟦k⟧'` and
`φ₂⟦k⟧'`. -/
def homotopyShift {K L : HomologicalComplex C (ComplexShape.up (ZMod n))} {φ₁ φ₂ : K ⟶ L}
    (h : Homotopy φ₁ φ₂) (k : ℤ) : Homotopy (φ₁⟦k⟧') (φ₂⟦k⟧') where
  hom i j := k.negOnePow • h.hom (i + k) (j + k)
  zero i j hij := by
    rw [h.zero _ _ (fun h => hij (by simp only [ComplexShape.up_Rel] at h ⊢; grind)), smul_zero]
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up (ZMod n)).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up (ZMod n)).Rel (i - 1) i by simp)]
    simpa [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
      dNext_eq _ (show (ComplexShape.up (ZMod n)).Rel (i + k) (i + 1 + k) by simp; ring),
      prevD_eq _ (show (ComplexShape.up (ZMod n)).Rel (i - 1 + k) (i + k) by simp; ring)]
      using h.comm (i + k)

variable (C n)

instance : (homotopic C (ComplexShape.up (ZMod n))).IsCompatibleWithShift ℤ :=
  ⟨fun k _ _ _ _ ⟨h⟩ => ⟨homotopyShift h k⟩⟩

/-- The periodic homotopy category carries the shift by `ℤ` induced from periodic complexes. -/
noncomputable instance homotopyCategoryHasShift :
    HasShift (HomotopyCategory C (ComplexShape.up (ZMod n))) ℤ :=
  inferInstanceAs
    (HasShift (CategoryTheory.Quotient (homotopic C (ComplexShape.up (ZMod n)))) ℤ)

/-- The quotient functor to the periodic homotopy category commutes with the shift. -/
noncomputable instance commShiftQuotient :
    (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).CommShift ℤ :=
  Quotient.functor_commShift (homotopic C (ComplexShape.up (ZMod n))) ℤ

lemma shift_quotient_obj (K : HomologicalComplex C (ComplexShape.up (ZMod n))) (k : ℤ) :
    ((HomotopyCategory.quotient _ _).obj K)⟦k⟧ = (HomotopyCategory.quotient _ _).obj (K⟦k⟧) :=
  Quotient.functor_obj_shift ..

instance (k : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up (ZMod n))) k).Additive := by
  have : ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n)) ⋙
      CategoryTheory.shiftFunctor _ k)).Additive :=
    Functor.additive_of_iso
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso k)
  exact Functor.additive_of_full_essSurj_comp (HomotopyCategory.quotient _ _) _

attribute [local implicit_reducible] HomotopyCategory.quotient in
instance {R : Type*} [Ring R] [Linear R C] (k : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up (ZMod n))) k).Linear R where
  map_smul := by
    rintro ⟨X⟩ ⟨Y⟩ f r
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map_surjective f
    have h₁ := NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso k) f
    have h₂ := NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso k) (r • f)
    dsimp at h₁ h₂
    rw [← Functor.map_smul, ← h₁, ← h₂]
    simp

/-- Periodicity of the shift on the periodic homotopy category: shifting by an even integer `k`
which is a multiple of the period is isomorphic to the identity. -/
noncomputable def homotopyCategoryShiftFunctorIsoId (k : ℤ) (hk : (k : ZMod n) = 0)
    (he : Even k) :
    CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up (ZMod n))) k ≅ 𝟭 _ :=
  Quotient.natIsoLift (F := CategoryTheory.shiftFunctor _ k) (G := 𝟭 _) _
    (((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso k).symm ≪≫
      Functor.isoWhiskerRight (shiftFunctorIsoId C n k hk he) _)

@[simp]
lemma homotopyCategoryShiftFunctorIsoId_hom_app_quotient_obj (k : ℤ) (hk : (k : ZMod n) = 0)
    (he : Even k) (K : HomologicalComplex C (ComplexShape.up (ZMod n))) :
    (homotopyCategoryShiftFunctorIsoId C n k hk he).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K) =
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso k).inv.app K ≫
        (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map
          ((shiftFunctorIsoId C n k hk he).hom.app K) := rfl

@[simp]
lemma homotopyCategoryShiftFunctorIsoId_inv_app_quotient_obj (k : ℤ) (hk : (k : ZMod n) = 0)
    (he : Even k) (K : HomologicalComplex C (ComplexShape.up (ZMod n))) :
    (homotopyCategoryShiftFunctorIsoId C n k hk he).inv.app
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K) =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map
          ((shiftFunctorIsoId C n k hk he).inv.app K) ≫
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso k).hom.app K := rfl

end PeriodicComplex

end TauCeti
