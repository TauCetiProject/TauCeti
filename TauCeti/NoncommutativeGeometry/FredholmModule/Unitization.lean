/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import TauCeti.NoncommutativeGeometry.FredholmModule.Basic
import TauCeti.Algebra.Algebra.Unitization

/-!
# Forced unitization of Fredholm modules with compact defect

Whenever a Fredholm module `(H, π, F)` over a non-unital `*`-algebra `A` has compact defect
`F² - 1` on `H` (in particular whenever `M` is normalized so `F² - 1 = 0`), Mathlib's
`Unitization.starLift` extends `π` to a unital `*`-algebra homomorphism on `Unitization ℂ A`,
sending `(c, a) ↦ c • 1 + π(a)`, without changing `F` (or the grading `γ` in the even case).

## Main definitions

* `TauCeti.FredholmModule.unitize`: extension of an odd Fredholm module with compact defect
  `F² - 1` over `A` to `Unitization ℂ A`.
* `TauCeti.EvenFredholmModule.unitize`: even counterpart preserving the grading `γ`.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.3.
-/

public section

noncomputable section

namespace TauCeti

variable {A : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FredholmModule

/-- **Forced unitization.** A Fredholm module over a non-unital `*`-algebra `A` whose defect
`F² - 1` is compact (in particular any normalized module) extends canonically to a unital Fredholm
module over `Unitization ℂ A` via `Unitization.starLift M.rep`, sending `(c, a) ↦ c • 1 + π(a)`. -/
def unitize (M : FredholmModule A H) (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) :
    FredholmModule (Unitization ℂ A) H where
  rep := (Unitization.starLift M.rep).toNonUnitalStarAlgHom
  operator := M.operator
  isSelfAdjoint_operator := M.isSelfAdjoint_operator
  isCompactOperator_commutator x := by
    rw [StarAlgHom.coe_toNonUnitalStarAlgHom]
    induction x with
    | inl_add_inr c a =>
      have hcomm :
          M.operator * Unitization.starLift M.rep (Unitization.inl c + Unitization.inr a) -
            Unitization.starLift M.rep (Unitization.inl c + Unitization.inr a) * M.operator =
            M.operator * M.rep a - M.rep a * M.operator := by
        rw [Unitization.starLift_inl_add_inr, Algebra.algebraMap_eq_smul_one, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, mul_one, one_mul, add_sub_add_left_eq_sub]
      rw [hcomm]
      exact M.isCompactOperator_commutator a
  isCompactOperator_mul_self_sub_one_mul x :=
    hK.comp_clm ((Unitization.starLift M.rep).toNonUnitalStarAlgHom x)

@[simp]
theorem unitize_operator (M : FredholmModule A H)
    (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) :
    (M.unitize hK).operator = M.operator :=
  (rfl)

@[simp]
theorem unitize_rep_apply (M : FredholmModule A H)
    (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) (x : Unitization ℂ A) :
    (M.unitize hK).rep x = Unitization.starLift M.rep x :=
  (rfl)

theorem unitize_rep_one (M : FredholmModule A H)
    (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) :
    (M.unitize hK).rep 1 = 1 :=
  (Unitization.starLift M.rep).map_one

theorem unitize_rep_inr (M : FredholmModule A H)
    (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) (a : A) :
    (M.unitize hK).rep (Unitization.inr a) = M.rep a :=
  Unitization.starLift_inr M.rep a

theorem unitize_rep_algebraMap (M : FredholmModule A H)
    (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) (c : ℂ) :
    (M.unitize hK).rep (algebraMap ℂ (Unitization ℂ A) c) = c • 1 := by
  rw [unitize_rep_apply, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]

/-- Forced unitization preserves normalization (`F² = 1`). -/
theorem isNormalized_unitize (M : FredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM.isCompactOperator_mul_self_sub_one).IsNormalized := by
  rw [isNormalized_iff, unitize_operator, hM.operator_mul_operator]

end FredholmModule

namespace EvenFredholmModule

/-- **Forced unitization**, even version: extends an even Fredholm module over `A` with compact
defect `F² - 1` to `Unitization ℂ A`, preserving `F` and `γ`. -/
def unitize (M : EvenFredholmModule A H) (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) :
    EvenFredholmModule (Unitization ℂ A) H where
  toFredholmModule := M.toFredholmModule.unitize hK
  grading := M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading
  grading_mul_grading := M.grading_mul_grading
  commute_grading_rep x := by
    rw [FredholmModule.unitize_rep_apply]
    induction x with
    | inl_add_inr c a =>
      rw [Unitization.starLift_inl_add_inr, Algebra.algebraMap_eq_smul_one]
      exact ((Commute.one_right M.grading).smul_right c).add_right (M.commute_grading_rep a)
  grading_mul_operator := M.grading_mul_operator

@[simp]
theorem unitize_toFredholmModule (M : EvenFredholmModule A H)
    (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) :
    (M.unitize hK).toFredholmModule = M.toFredholmModule.unitize hK :=
  (rfl)

@[simp]
theorem unitize_grading (M : EvenFredholmModule A H)
    (hK : IsCompactOperator ⇑(M.operator * M.operator - 1)) :
    (M.unitize hK).grading = M.grading :=
  (rfl)

/-- Forced unitization preserves normalization (`F² = 1`) for even Fredholm modules. -/
theorem isNormalized_unitize (M : EvenFredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM.isCompactOperator_mul_self_sub_one).IsNormalized := by
  rw [IsNormalized, unitize_toFredholmModule]
  exact M.toFredholmModule.isNormalized_unitize hM

end EvenFredholmModule

end TauCeti
