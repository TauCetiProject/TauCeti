/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.VectorBlock
public import TauCeti.RepresentationTheory.Spin.HalfSpin.D4Tripled

/-!
# Concrete intertwiners for type-D4 triality

The tripled type-`D₄` weight table cycles its natural block and its two half-spin blocks. This
file transports that cycle to the standard split vector representation and the exterior
half-spin modules. The alternating sign on the negative vector coordinates is included in the
vector comparison, while the exterior half-spin bases need no further sign changes.

The resulting cycle is
`V(ϖ₁) → V(ϖ₃) → V(ϖ₄) → V(ϖ₁)`. Each equivalence intertwines the positive, negative, and
Cartan Chevalley generators after applying the pinned order-three permutation to the Dynkin node.

## Main declarations

* `SpinPolarizationData.d4VectorToSpinMinusEquiv`,
  `SpinPolarizationData.d4SpinMinusToSpinPlusEquiv`, and
  `SpinPolarizationData.d4SpinPlusToVectorEquiv`: the concrete triality cycle.
* The three `d4TrialityCycle_*apply_apply_apply` theorems: the cycle is the identity from each
  starting module.
* The corresponding `_serreE`, `_serreF`, and `_serreH` theorems: compatibility with all
  Chevalley generators.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

open scoped Matrix

public section

namespace TauCeti.SpinPolarizationData

open TauCeti.DynkinType
open TauCeti.D4Tripled

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) (b : Module.Basis (Fin 4) ℚ P.W)

/-! ## The concrete triality cycle -/

/-- Triality from the standard split vector module to the odd half-spin module. -/
noncomputable def d4VectorToSpinMinusEquiv :
    (Fin 4 ⊕ Fin 4 → ℚ) ≃ₗ[ℚ] spinMinus Q P :=
  D4Tripled.vectorBlockEquiv |>.trans
    d4BlockZeroToOneEquiv |>.trans
      (P.d4SpinMinusBlockEquiv b).symm

/-- Triality from the odd half-spin module to the even half-spin module. -/
noncomputable def d4SpinMinusToSpinPlusEquiv :
    spinMinus Q P ≃ₗ[ℚ] spinPlus Q P :=
  P.d4SpinMinusBlockEquiv b |>.trans
    d4BlockOneToTwoEquiv |>.trans
      (P.d4SpinPlusBlockEquiv b).symm

/-- Triality from the even half-spin module to the standard split vector module. -/
noncomputable def d4SpinPlusToVectorEquiv :
    spinPlus Q P ≃ₗ[ℚ] (Fin 4 ⊕ Fin 4 → ℚ) :=
  P.d4SpinPlusBlockEquiv b |>.trans
    d4BlockTwoToZeroEquiv |>.trans
      D4Tripled.vectorBlockEquiv.symm

/-- Three successive concrete triality intertwiners return every vector to itself. -/
@[simp]
theorem d4TrialityCycle_apply_apply_apply (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4SpinPlusToVectorEquiv b
        (P.d4SpinMinusToSpinPlusEquiv b (P.d4VectorToSpinMinusEquiv b v)) = v := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, d4SpinMinusToSpinPlusEquiv,
    d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact d4BlockCycle_apply_apply_apply (D4Tripled.vectorBlockEquiv v)

/-- Three successive concrete triality intertwiners return every odd spinor to itself. -/
@[simp]
theorem d4TrialityCycle_spinMinus_apply_apply_apply (x : spinMinus Q P) :
    P.d4VectorToSpinMinusEquiv b
        (P.d4SpinPlusToVectorEquiv b (P.d4SpinMinusToSpinPlusEquiv b x)) = x := by
  apply (P.d4SpinMinusToSpinPlusEquiv b).injective
  apply (P.d4SpinPlusToVectorEquiv b).injective
  exact P.d4TrialityCycle_apply_apply_apply b
    (P.d4SpinPlusToVectorEquiv b (P.d4SpinMinusToSpinPlusEquiv b x))

/-- Three successive concrete triality intertwiners return every even spinor to itself. -/
@[simp]
theorem d4TrialityCycle_spinPlus_apply_apply_apply (x : spinPlus Q P) :
    P.d4SpinMinusToSpinPlusEquiv b
        (P.d4VectorToSpinMinusEquiv b (P.d4SpinPlusToVectorEquiv b x)) = x := by
  apply (P.d4SpinPlusToVectorEquiv b).injective
  exact P.d4TrialityCycle_apply_apply_apply b (P.d4SpinPlusToVectorEquiv b x)

/-- The vector-to-odd-spin equivalence intertwines positive generators after applying triality
to the Dynkin node. -/
@[simp ←]
theorem d4VectorToSpinMinusEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4VectorToSpinMinusEquiv b
        (TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      P.typeDSpinMinusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inl (trialityPermD4 i)))
        (P.d4VectorToSpinMinusEquiv b v) := by
  apply (P.d4SpinMinusBlockEquiv b).injective
  rw [P.d4SpinMinusBlockEquiv_serreE]
  simp only [d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [D4Tripled.vectorBlockEquiv_raising_mulVec,
    blockRaisingMatrix_eq_submatrixQ,
    d4BlockZeroToOneEquiv_raising_mulVec]
  rfl

/-- The odd-to-even-spin equivalence intertwines positive generators after applying triality to
the Dynkin node. -/
@[simp]
theorem d4SpinMinusToSpinPlusEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusToSpinPlusEquiv b
        (P.typeDSpinMinusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inl i)) x) =
      P.typeDSpinPlusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inl (trialityPermD4 i)))
        (P.d4SpinMinusToSpinPlusEquiv b x) := by
  apply (P.d4SpinPlusBlockEquiv b).injective
  rw [P.d4SpinPlusBlockEquiv_serreE]
  simp only [d4SpinMinusToSpinPlusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinMinusBlockEquiv_serreE]
  exact d4BlockOneToTwoEquiv_raising_mulVec i (P.d4SpinMinusBlockEquiv b x)

/-- The even-spin-to-vector equivalence intertwines positive generators after applying triality
to the Dynkin node. -/
@[simp]
theorem d4SpinPlusToVectorEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusToVectorEquiv b
        (P.typeDSpinPlusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inl i)) x) =
      TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) (trialityPermD4 i) *ᵥ
        P.d4SpinPlusToVectorEquiv b x := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinPlusBlockEquiv_serreE]
  calc
    _ = (D4Tripled.weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ
        d4BlockTwoToZeroEquiv (P.d4SpinPlusBlockEquiv b x) :=
      d4BlockTwoToZeroEquiv_raising_mulVec i (P.d4SpinPlusBlockEquiv b x)
    _ = _ := by
      rw [D4Tripled.vectorBlockEquiv_raising_mulVec]
      simp only [LinearEquiv.apply_symm_apply, blockRaisingMatrix_eq_submatrixQ]

/-- The vector-to-odd-spin equivalence intertwines negative generators after applying triality
to the Dynkin node. -/
@[simp ←]
theorem d4VectorToSpinMinusEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4VectorToSpinMinusEquiv b
        (TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      P.typeDSpinMinusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inr (trialityPermD4 i)))
        (P.d4VectorToSpinMinusEquiv b v) := by
  apply (P.d4SpinMinusBlockEquiv b).injective
  rw [P.d4SpinMinusBlockEquiv_serreF]
  simp only [d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [D4Tripled.vectorBlockEquiv_lowering_mulVec,
    blockLoweringMatrix_eq_submatrixQ,
    d4BlockZeroToOneEquiv_lowering_mulVec]
  rfl

/-- The odd-to-even-spin equivalence intertwines negative generators after applying triality. -/
@[simp]
theorem d4SpinMinusToSpinPlusEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusToSpinPlusEquiv b
        (P.typeDSpinMinusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inr i)) x) =
      P.typeDSpinPlusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inr (trialityPermD4 i)))
        (P.d4SpinMinusToSpinPlusEquiv b x) := by
  apply (P.d4SpinPlusBlockEquiv b).injective
  rw [P.d4SpinPlusBlockEquiv_serreF]
  simp only [d4SpinMinusToSpinPlusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinMinusBlockEquiv_serreF]
  exact d4BlockOneToTwoEquiv_lowering_mulVec i (P.d4SpinMinusBlockEquiv b x)

/-- The even-spin-to-vector equivalence intertwines negative generators after applying triality. -/
@[simp]
theorem d4SpinPlusToVectorEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusToVectorEquiv b
        (P.typeDSpinPlusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inr i)) x) =
      TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) (trialityPermD4 i) *ᵥ
        P.d4SpinPlusToVectorEquiv b x := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinPlusBlockEquiv_serreF]
  calc
    _ = (D4Tripled.weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ
        d4BlockTwoToZeroEquiv (P.d4SpinPlusBlockEquiv b x) :=
      d4BlockTwoToZeroEquiv_lowering_mulVec i (P.d4SpinPlusBlockEquiv b x)
    _ = _ := by
      rw [D4Tripled.vectorBlockEquiv_lowering_mulVec]
      simp only [LinearEquiv.apply_symm_apply, blockLoweringMatrix_eq_submatrixQ]

/-- The vector-to-odd-spin equivalence intertwines Cartan generators after applying triality to
the Dynkin node. -/
@[simp ←]
theorem d4VectorToSpinMinusEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4VectorToSpinMinusEquiv b
        (typeDDiagonalMatrix (fun j =>
          (typeDSimpleRoot 4 (by omega) i j : ℚ)) *ᵥ v) =
      P.typeDSpinMinusLieRep b hline
        (TypeDStd.cartanGenerator 4 (by omega) (trialityPermD4 i))
        (P.d4VectorToSpinMinusEquiv b v) := by
  apply (P.d4SpinMinusBlockEquiv b).injective
  rw [P.d4SpinMinusBlockEquiv_serreH]
  simp only [d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [D4Tripled.vectorBlockEquiv_cartanGenerator_mulVec,
    blockCartanGeneratorMatrix_eq_submatrixQ,
    d4BlockZeroToOneEquiv_cartanGenerator_mulVec]
  rfl

/-- The odd-to-even-spin equivalence intertwines Cartan generators after applying triality. -/
@[simp]
theorem d4SpinMinusToSpinPlusEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusToSpinPlusEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i) x) =
      P.typeDSpinPlusLieRep b hline
        (TypeDStd.cartanGenerator 4 (by omega) (trialityPermD4 i))
        (P.d4SpinMinusToSpinPlusEquiv b x) := by
  apply (P.d4SpinPlusBlockEquiv b).injective
  rw [P.d4SpinPlusBlockEquiv_serreH]
  simp only [d4SpinMinusToSpinPlusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinMinusBlockEquiv_serreH]
  exact d4BlockOneToTwoEquiv_cartanGenerator_mulVec i (P.d4SpinMinusBlockEquiv b x)

/-- The even-spin-to-vector equivalence intertwines Cartan generators after applying triality. -/
@[simp]
theorem d4SpinPlusToVectorEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusToVectorEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i) x) =
      typeDDiagonalMatrix (fun j =>
        (typeDSimpleRoot 4 (by omega) (trialityPermD4 i) j : ℚ)) *ᵥ
        P.d4SpinPlusToVectorEquiv b x := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinPlusBlockEquiv_serreH]
  calc
    _ = (D4Tripled.weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ
        d4BlockTwoToZeroEquiv (P.d4SpinPlusBlockEquiv b x) :=
      d4BlockTwoToZeroEquiv_cartanGenerator_mulVec i (P.d4SpinPlusBlockEquiv b x)
    _ = _ := by
      rw [D4Tripled.vectorBlockEquiv_cartanGenerator_mulVec]
      simp only [LinearEquiv.apply_symm_apply,
        blockCartanGeneratorMatrix_eq_submatrixQ]

end TauCeti.SpinPolarizationData
