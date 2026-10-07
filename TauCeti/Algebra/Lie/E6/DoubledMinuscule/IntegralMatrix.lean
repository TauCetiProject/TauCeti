/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GroupScheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion

/-!
# Integral matrices of doubled minuscule E₆ generators

The numbered root operators on `V(ϖ₁) ⊕ V(ϖ₆)` preserve its two summands. This file records
that property in the carrier's `Fin 54` coordinates, obtained by `matrixIndexEquiv` from the
block coordinates. Each root operator squares to zero, so the corresponding root subgroup is
`1 + t X` over any commutative ring. These formulas allow block preservation to be checked on
the universal root-subgroup coordinate maps, including over nonreduced rings.

The integral matrix interface follows
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1–2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra
open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

/-- The summand label of a matrix coordinate: zero for `V(ϖ₁)`, one for `V(ϖ₆)`. -/
def matrixSummand (a : Fin 54) : ℤ :=
  if (matrixIndexEquiv.symm a).isRight then 1 else 0

/-- Coordinates of the first minuscule summand have label zero. -/
@[simp]
theorem matrixSummand_inl (a : Fin 27) : matrixSummand (matrixIndexEquiv (.inl a)) = 0 := by
  simp [matrixSummand]

/-- Coordinates of the dual minuscule summand have label one. -/
@[simp]
theorem matrixSummand_inr (a : Fin 27) : matrixSummand (matrixIndexEquiv (.inr a)) = 1 := by
  simp [matrixSummand]

/-- A simple reflection preserves the minuscule summand label. -/
@[simp]
theorem matrixSummand_reflection (i : Fin 6) (a : Fin 54) :
    matrixSummand (matrixIndexEquiv (reflection i (matrixIndexEquiv.symm a))) =
      matrixSummand a := by
  simp only [matrixSummand, Equiv.symm_apply_apply]
  cases matrixIndexEquiv.symm a <;> simp

/-- The integral matrix of a numbered simple root operator in the carrier's lattice basis. -/
noncomputable def rootIntMatrix (j : Fin 6 ⊕ Fin 6) : Matrix (Fin 54) (Fin 54) ℤ :=
  kostantRootGeneratorIntMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice j matrixBasis

/-- A represented root operator acts on a lattice basis vector by its integral matrix column. -/
theorem rep_rootGenerator_matrixBasis_eq_sum (j : Fin 6 ⊕ Fin 6) (s : Fin 54) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ j))
        ((matrixBasis s : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) =
      ∑ r, rootIntMatrix j r s •
        ((matrixBasis r : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) := by
  rw [rootIntMatrix]
  exact rep_rootGenerator_basis_eq_sum
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice j matrixBasis s

/-- Numbered root operators have nilpotency class at most two on the doubled module. -/
theorem nilpotencyClass_rep_rootGenerator_le_two (j : Fin 6 ⊕ Fin 6) :
    nilpotencyClass (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ j))) ≤ 2 :=
  Nat.sInf_le (rep_serreRootGenerator_sq j)

private theorem rep_rootGenerator_matrixBasis_eq_smul (j : Fin 6 ⊕ Fin 6) (s : Fin 54) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ j))
        ((matrixBasis s : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) =
      (if matrixWeight s (Sum.elim id id j) = (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) j : ℤ)
        then summandSign (matrixIndexEquiv.symm s) else 0) •
        ((matrixBasis (matrixIndexEquiv (reflection (Sum.elim id id j)
          (matrixIndexEquiv.symm s))) : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) := by
  rw [matrixBasis_apply, matrixBasis_apply, Equiv.symm_apply_apply, coe_latticeBasis,
    coe_latticeBasis, rep_ι_apply]
  cases j with
  | inl i =>
    rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE,
      Matrix.mulVec_single_one]
    ext a
    simp only [matrixWeight_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all
  | inr i =>
    rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF,
      Matrix.mulVec_single_one]
    ext a
    simp only [matrixWeight_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all

/-- A numbered root operator moves a coordinate to its simple reflection, with coefficient
`1` on the minuscule block and `-1` on the dual block, when its weight permits the move. -/
@[simp]
theorem rootIntMatrix_apply (j : Fin 6 ⊕ Fin 6) (a b : Fin 54) :
    rootIntMatrix j a b =
      if a = matrixIndexEquiv (reflection (Sum.elim id id j) (matrixIndexEquiv.symm b)) then
        if matrixWeight b (Sum.elim id id j) =
            (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) j : ℤ)
        then summandSign (matrixIndexEquiv.symm b) else 0
      else 0 :=
  kostantRootGeneratorIntMatrix_apply_of_eq
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice j matrixBasis
    (rep_rootGenerator_matrixBasis_eq_smul j b) a

/-- The root-operator matrices have zero entries between distinct minuscule summands. -/
theorem rootIntMatrix_eq_zero_of_summand_ne (j : Fin 6 ⊕ Fin 6) {a b : Fin 54}
    (hab : matrixSummand a ≠ matrixSummand b) : rootIntMatrix j a b = 0 := by
  have hne : a ≠ matrixIndexEquiv (reflection (Sum.elim id id j) (matrixIndexEquiv.symm b)) :=
    fun h ↦ hab (h ▸ matrixSummand_reflection _ b)
  simpa only [rootIntMatrix, hne, ↓reduceIte] using
    kostantRootGeneratorIntMatrix_apply_of_eq
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice j matrixBasis
      (rep_rootGenerator_matrixBasis_eq_smul j b) a

/-- A numbered root subgroup is `1 + t X` for its integral root-operator matrix. -/
theorem coe_rootSubgroupPoints_eq_one_add_smul (j : Fin 6 ⊕ Fin 6)
    (A : Type*) [CommRing A] (u : Multiplicative A) :
    ((rootSubgroupPoints j A u : Matrix.GeneralLinearGroup (Fin 54) A) :
      Matrix (Fin 54) (Fin 54) A) =
      1 + Multiplicative.toAdd u • (rootIntMatrix j).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply] using
    kostantRootSubgroupMatrix_eq_one_add_smul _ _ _ _ _ _ _ _ (rootIntMatrix j)
      (nilpotencyClass_rep_rootGenerator_le_two j) (rep_rootGenerator_matrixBasis_eq_sum j)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)

end TauCeti.E6DoubledMinuscule
