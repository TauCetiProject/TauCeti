/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Action

/-!
# Pinned coordinates on the modular F4 quotient

This file fixes the coordinate identification between the long-root quotient and the short-root
ideal.  It also records the elementary reversal and exponent data for the special isogeny on the
eight signed simple roots.  The actual first- and second-order column comparison is built on this
normalization.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.F4ShortRoot

/-- The length-exchanging involution of the positive and negative numbered simple roots. -/
@[expose] def isogenyReverse : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 :=
  Sum.map Fin.revPerm Fin.revPerm

/-- The parameter exponent of a numbered simple root under the special isogeny. -/
@[expose] def isogenyExponent : Fin 4 ⊕ Fin 4 → ℕ :=
  Sum.elim ![1, 1, 2, 2] ![1, 1, 2, 2]

/-- Each special-isogeny parameter exponent is one or two. -/
theorem isogenyExponent_eq_one_or_two (k : Fin 4 ⊕ Fin 4) :
    isogenyExponent k = 1 ∨ isogenyExponent k = 2 := by
  revert k
  decide

/-- Reversal of the signed simple-root labels is involutive. -/
@[simp] theorem isogenyReverse_isogenyReverse (k : Fin 4 ⊕ Fin 4) :
    isogenyReverse (isogenyReverse k) = k := by
  revert k
  decide

/-- The exponents on two successively reversed labels multiply to two. -/
theorem isogenyExponent_mul_isogenyExponent_eq_two (k : Fin 4 ⊕ Fin 4) :
    isogenyExponent k * isogenyExponent (isogenyReverse k) = 2 := by
  revert k
  decide

end TauCeti.F4ShortRoot

namespace TauCeti.DynkinType

open TauCeti.F4ShortRoot
open _root_.LieAlgebra
open LieModule

noncomputable section

/-- The coordinate identification from the long-root quotient to the short-root ideal.  Both
sides use the same `Fin 26` labels, already normalized by the special root permutation. -/
noncomputable def f4ShortRootQuotientToIdealEquiv :
    (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) ≃ₗ[ZMod 2]
      f4ShortRootLieIdeal :=
  f4ShortRootQuotientBasis.equiv f4ShortRootLieIdealBasis (Equiv.refl (Fin 26))

@[simp] theorem f4ShortRootQuotientToIdealEquiv_basis (a : Fin 26) :
    f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientBasis a) =
      f4ShortRootLieIdealBasis a := by
  exact Module.Basis.equiv_apply f4ShortRootQuotientBasis a
    f4ShortRootLieIdealBasis (Equiv.refl (Fin 26))

/-- The canonical ambient lift of a quotient coordinate. -/
noncomputable def f4ShortRootQuotientLift (a : Fin 26) :
    f4ModularChevalleyLieAlgebra :=
  f4ModularChevalleyBasis (f4LongRootBasisCoordinate a)

@[simp] theorem f4ShortRootQuotientLift_eq_basis (a : Fin 26) :
    f4ShortRootQuotientLift a =
      f4ModularChevalleyBasis (f4LongRootBasisCoordinate a) := by
  rfl

theorem f4ShortRootSubspace_mkQ_quotientLift (a : Fin 26) :
    f4ShortRootSubspace.mkQ (f4ShortRootQuotientLift a) =
      f4ShortRootQuotientBasis a := by
  exact (f4ShortRootQuotientBasis_apply a).symm

theorem f4ShortRootQuotientToIdealEquiv_mkQ_quotientLift (a : Fin 26) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootSubspace.mkQ (f4ShortRootQuotientLift a)) =
      f4ShortRootLieIdealBasis a := by
  calc
    _ = f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientBasis a) :=
      congrArg f4ShortRootQuotientToIdealEquiv
        (f4ShortRootSubspace_mkQ_quotientLift a)
    _ = _ := f4ShortRootQuotientToIdealEquiv_basis a


/-- The first-order quotient column of a numbered signed simple root. -/
noncomputable def f4ShortRootQuotientFirstColumn
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace :=
  f4ShortRootSubspace.mkQ
    ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), f4ShortRootQuotientLift a⁆

@[simp] theorem f4ShortRootQuotientFirstColumn_eq
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootQuotientFirstColumn k a =
      f4ShortRootSubspace.mkQ
        ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
          f4ShortRootQuotientLift a⁆ := by
  rfl

/-- The second divided-power quotient column of a numbered signed simple root. -/
noncomputable def f4ShortRootQuotientDividedSquareColumn
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace :=
  f4ShortRootSubspace.mkQ
    (f4ModularDividedAdjointSquare k (f4ShortRootQuotientLift a))

@[simp] theorem f4ShortRootQuotientDividedSquareColumn_eq
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootQuotientDividedSquareColumn k a =
      f4ShortRootSubspace.mkQ
        (f4ModularDividedAdjointSquare k (f4ShortRootQuotientLift a)) := by
  rfl

/-- The first-order column on the short-root ideal, in its canonical coordinates. -/
noncomputable def f4ShortRootIdealFirstColumn
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) : f4ShortRootLieIdeal :=
  f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis a)

@[simp] theorem f4ShortRootIdealFirstColumn_apply
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootIdealFirstColumn k a =
      f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis a) := by
  rfl

theorem coe_f4ShortRootIdealFirstColumn
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    (f4ShortRootIdealFirstColumn k a : f4ModularChevalleyLieAlgebra) =
      ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
        (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆ := by
  unfold f4ShortRootIdealFirstColumn
  exact coe_f4ShortRootSignedSimpleAdjoint_apply _ _

/-- The second divided-power column on the short-root ideal, in its canonical coordinates. -/
noncomputable def f4ShortRootIdealDividedSquareColumn
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) : f4ShortRootLieIdeal :=
  f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis a)

@[simp] theorem f4ShortRootIdealDividedSquareColumn_apply
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootIdealDividedSquareColumn k a =
      f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis a) := by
  rfl

/-- The ideal's first-order canonical column is the corresponding sparse root-matrix column. -/
theorem f4ShortRootIdealFirstColumn_eq
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootIdealFirstColumn k a =
      (f4SimpleRootCoeff k a : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k a) := by
  apply f4ShortRootLieIdealBasis.repr.injective
  ext b
  have hentry :
      (f4ShortRootLieIdealBasis.repr (f4ShortRootIdealFirstColumn k a)) b =
        f4ShortRootSignedSimpleAdjointMatrix k b a := by
    exact (f4ShortRootSignedSimpleAdjointMatrix_apply k b a).symm
  calc
    _ = f4ShortRootSignedSimpleAdjointMatrix k b a := hentry
    _ = ((rootMatrix k).map (Int.cast : ℤ → ZMod 2)) b a :=
      congrArg (fun M : Matrix (Fin 26) (Fin 26) (ZMod 2) ↦ M b a)
        (f4ShortRootSignedSimpleAdjointMatrix_eq_rootMatrix_map k)
    _ = if b = f4SimpleRootTarget k a then
          (f4SimpleRootCoeff k a : ZMod 2) else 0 := by
      rw [Matrix.map_apply, rootMatrix_apply]
      split_ifs <;> rfl
    _ = (f4ShortRootLieIdealBasis.repr
        ((f4SimpleRootCoeff k a : ZMod 2) •
          f4ShortRootLieIdealBasis (f4SimpleRootTarget k a))) b := by
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single]
      by_cases h : b = f4SimpleRootTarget k a
      · subst b
        simp
      · simp [h]

/-- The ideal's second divided-power canonical column is the corresponding sparse matrix
column. -/
theorem f4ShortRootIdealDividedSquareColumn_eq
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootIdealDividedSquareColumn k a =
      (f4DividedSquareCoeff k a : ZMod 2) •
        f4ShortRootLieIdealBasis (f4DividedSquareTarget k a) := by
  exact f4ShortRootDividedAdjointSquare_basis k a

/-- A short signed-simple source has zero first-order action on every quotient coordinate. -/
theorem f4ShortRootQuotientToIdealEquiv_firstColumn_eq_zero_of_short
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1)
    (a : Fin 26) :
    f4ShortRootQuotientToIdealEquiv
        (f4ShortRootQuotientFirstColumn k a) = 0 := by
  have hzero : f4ShortRootQuotientFirstColumn k a = 0 := by
    exact f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_short
      (f4SignedSimpleRootIndex k) hk (f4ShortRootQuotientLift a)
  calc
    _ = f4ShortRootQuotientToIdealEquiv 0 :=
      congrArg f4ShortRootQuotientToIdealEquiv hzero
    _ = 0 := map_zero f4ShortRootQuotientToIdealEquiv

/-- The special root permutation reverses the numbered signed simple roots. -/
theorem f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex
    (k : Fin 4 ⊕ Fin 4) :
    f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k) =
      f4SignedSimpleRootIndex (isogenyReverse k) := by
  rcases k with i | i
  · simp [f4SignedSimpleRootIndex_inl, isogenyReverse,
      f4SpecialIsogenyIndexEquiv_apply, f4SpecialIsogenyIndex_castAdd,
      lengthPermF4_apply]
  · have hleft : f4SignedSimpleRootIndex (.inr i) =
        (Fin.castAdd 44 i : Fin 48) + 24 := by
      simp only [f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_castAdd]
      fin_cases i <;> decide +kernel
    have hright : f4SignedSimpleRootIndex (isogenyReverse (.inr i)) =
        (Fin.castAdd 44 i.rev : Fin 48) + 24 := by
      simp only [isogenyReverse, Sum.map_inr, f4SignedSimpleRootIndex_inr,
        f4OppositeRootIndex_castAdd]
      fin_cases i <;> decide +kernel
    rw [hleft, hright, f4SpecialIsogenyIndexEquiv_apply,
      f4SpecialIsogenyIndex_add_twentyFour, f4SpecialIsogenyIndex_castAdd,
      lengthPermF4_apply]

/-- The special root permutation also reverses the opposite signed-simple indices. -/
theorem f4SpecialIsogenyIndexEquiv_opposite_f4SignedSimpleRootIndex
    (k : Fin 4 ⊕ Fin 4) :
    f4SpecialIsogenyIndexEquiv (f4OppositeRootIndex (f4SignedSimpleRootIndex k)) =
      f4OppositeRootIndex (f4SignedSimpleRootIndex (isogenyReverse k)) := by
  rcases k with i | i
  · simpa only [isogenyReverse, Sum.map_inl, Sum.map_inr,
      f4SignedSimpleRootIndex_inl, f4SignedSimpleRootIndex_inr] using
      f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex (.inr i)
  · simp only [isogenyReverse, Sum.map_inr, f4SignedSimpleRootIndex_inr,
      f4OppositeRootIndex_f4OppositeRootIndex]
    simp [f4SpecialIsogenyIndexEquiv_apply, f4SpecialIsogenyIndex_castAdd,
      lengthPermF4_apply]

end

end TauCeti.DynkinType
