/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.GraphAutomorphism
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Coordinates
import TauCeti.LinearAlgebra.Basis.RangeSpan
import TauCeti.LinearAlgebra.End.OrderTwoThree

/-!
# Root vectors for the type-D graph involution

Exchanging a hyperbolic pair acts on every native root matrix, not just on the simple
roots. Roots avoiding that pair are fixed. The difference and sum roots meeting the
pair are exchanged, with the signs of the negative sum-root convention retained; the
individual Cartan vector at the pair is negated.

The fixed submodule is spanned by the two-term symmetrizations of the native matrix basis
when two is invertible. A fixed basis vector contributes twice itself, not a distinct-orbit
sum; no integral fixed basis is asserted. This gives a concrete spanning family for the fixed
Lie algebra before identifying it with a split odd orthogonal Lie algebra. The action formulas
hold over arbitrary commutative rings, including characteristic two.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate IV.
* V. Kac, *Infinite dimensional Lie algebras*, §8.2.

The root conventions and native basis are those of
`TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.AllGenerators` and
`TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Coordinates`.
-/

public section

namespace TauCeti

open TypeDStd

section Action

variable {R I : Type*} [CommRing R] [DecidableEq I] [Fintype I]

/-- Difference-root matrices avoiding the exchanged pair are fixed. -/
@[simp]
theorem typeDGraphLieEquiv_differenceRootGenerator_of_ne (c i j : I)
    (hi : i ≠ c) (hj : j ≠ c) :
    typeDGraphLieEquiv c R (differenceRootGenerator i j) = differenceRootGenerator i j := by
  apply Subtype.ext
  ext (a | a) (b | b) <;>
    simp only [typeDGraphLieEquiv_apply_apply] <;>
    by_cases ha : a = c <;> by_cases hb : b = c <;>
    simp_all [val_differenceRootGenerator, differenceRootMatrix_def, Matrix.fromBlocks,
      Matrix.single_apply, eq_comm]

/-- Positive sum-root matrices avoiding the exchanged pair are fixed. -/
@[simp]
theorem typeDGraphLieEquiv_sumRootGenerator_of_ne (c i j : I)
    (hi : i ≠ c) (hj : j ≠ c) :
    typeDGraphLieEquiv c R (sumRootGenerator i j) = sumRootGenerator i j := by
  apply Subtype.ext
  ext (a | a) (b | b) <;>
    simp only [typeDGraphLieEquiv_apply_apply] <;>
    by_cases ha : a = c <;> by_cases hb : b = c <;>
    simp_all [val_sumRootGenerator, sumRootMatrix_def, Matrix.fromBlocks,
      Matrix.single_apply, eq_comm]

/-- Negative sum-root matrices avoiding the exchanged pair are fixed. -/
@[simp]
theorem typeDGraphLieEquiv_negSumRootGenerator_of_ne (c i j : I)
    (hi : i ≠ c) (hj : j ≠ c) :
    typeDGraphLieEquiv c R (negSumRootGenerator i j) = negSumRootGenerator i j := by
  apply Subtype.ext
  ext (a | a) (b | b) <;>
    simp only [typeDGraphLieEquiv_apply_apply] <;>
    by_cases ha : a = c <;> by_cases hb : b = c <;>
    simp_all [val_negSumRootGenerator, negSumRootMatrix_def, Matrix.fromBlocks,
      Matrix.single_apply, eq_comm]

/-- A difference root ending at the exchanged pair becomes the corresponding positive sum root. -/
@[simp]
theorem typeDGraphLieEquiv_differenceRootGenerator_right (c i : I) (hi : i ≠ c) :
    typeDGraphLieEquiv c R (differenceRootGenerator i c) = sumRootGenerator i c := by
  apply Subtype.ext
  ext (a | a) (b | b) <;>
    simp only [typeDGraphLieEquiv_apply_apply] <;>
    by_cases ha : a = c <;> by_cases hb : b = c <;>
    simp_all [val_differenceRootGenerator, val_sumRootGenerator, differenceRootMatrix_def,
      sumRootMatrix_def, Matrix.fromBlocks, Matrix.single_apply, eq_comm]

/-- A difference root starting at the exchanged pair becomes a negative sum root. -/
@[simp]
theorem typeDGraphLieEquiv_differenceRootGenerator_left (c j : I) (hj : j ≠ c) :
    typeDGraphLieEquiv c R (differenceRootGenerator c j) = negSumRootGenerator c j := by
  apply Subtype.ext
  ext (a | a) (b | b) <;>
    simp only [typeDGraphLieEquiv_apply_apply] <;>
    by_cases ha : a = c <;> by_cases hb : b = c <;>
    simp_all [val_differenceRootGenerator, val_negSumRootGenerator, differenceRootMatrix_def,
      negSumRootMatrix_def, Matrix.fromBlocks, Matrix.single_apply, eq_comm]

/-- The individual hyperbolic Cartan vector at the exchanged pair is negated. -/
@[simp]
theorem typeDGraphLieEquiv_differenceRootGenerator_self (c : I) :
    typeDGraphLieEquiv c R (differenceRootGenerator c c) = -differenceRootGenerator c c := by
  apply Subtype.ext
  ext (a | a) (b | b) <;>
    simp only [typeDGraphLieEquiv_apply_apply] <;>
    by_cases ha : a = c <;> by_cases hb : b = c <;>
    simp_all [val_differenceRootGenerator, differenceRootMatrix_def, Matrix.fromBlocks,
      Matrix.single_apply, eq_comm]

/-- The positive sum root ending at the exchanged pair returns to the difference root. -/
@[simp]
theorem typeDGraphLieEquiv_sumRootGenerator_right (c i : I) (hi : i ≠ c) :
    typeDGraphLieEquiv c R (sumRootGenerator i c) = differenceRootGenerator i c := by
  rw [← typeDGraphLieEquiv_differenceRootGenerator_right c i hi,
    typeDGraphLieEquiv_typeDGraphLieEquiv]

/-- The negative sum root starting at the exchanged pair returns to the difference root. -/
@[simp]
theorem typeDGraphLieEquiv_negSumRootGenerator_left (c j : I) (hj : j ≠ c) :
    typeDGraphLieEquiv c R (negSumRootGenerator c j) = differenceRootGenerator c j := by
  rw [← typeDGraphLieEquiv_differenceRootGenerator_left c j hj,
    typeDGraphLieEquiv_typeDGraphLieEquiv]

/-- Reversing the indices of a positive sum root retains its minus sign under the involution. -/
@[simp]
theorem typeDGraphLieEquiv_sumRootGenerator_left (c j : I) (hj : j ≠ c) :
    typeDGraphLieEquiv c R (sumRootGenerator c j) = -differenceRootGenerator j c := by
  rw [sumRootGenerator_swap, map_neg, typeDGraphLieEquiv_sumRootGenerator_right c j hj]

/-- Reversing the indices of a negative sum root retains its minus sign under the involution. -/
@[simp]
theorem typeDGraphLieEquiv_negSumRootGenerator_right (c i : I) (hi : i ≠ c) :
    typeDGraphLieEquiv c R (negSumRootGenerator i c) = -differenceRootGenerator c i := by
  rw [negSumRootGenerator_swap, map_neg, typeDGraphLieEquiv_negSumRootGenerator_left c i hi]

end Action

section Spanning

variable {R I : Type*} [CommRing R] [Fintype I] [LinearOrder I] [Invertible (2 : R)]

/-- When two is invertible, the two-term symmetrizations of the native root-entry basis
span the fixed submodule. Fixed basis vectors occur with coefficient two, while the negated
Cartan vector contributes zero. This is a spanning family, not a linearly independent basis. -/
theorem typeDGraphLieEquiv_fixedSubmodule_eq_span (c : I) :
    (typeDGraphLieEquiv c R).toLinearMap.fixedSubmodule =
      Submodule.span R (Set.range (fun p : RootEntryIndex I =>
        rootEntryBasis (R := R) (ι := I)
          (isUnit_of_invertible (2 : R)).eq_zero_of_add_self_eq_zero p +
          typeDGraphLieEquiv c R (rootEntryBasis (R := R) (ι := I)
            (isUnit_of_invertible (2 : R)).eq_zero_of_add_self_eq_zero p))) := by
  let f := (typeDGraphLieEquiv c R).toLinearMap
  let b := rootEntryBasis (R := R) (ι := I)
    (isUnit_of_invertible (2 : R)).eq_zero_of_add_self_eq_zero
  have hf : f ^ 2 = 1 := by
    ext X : 1
    exact typeDGraphLieEquiv_typeDGraphLieEquiv c R X
  have hfixed : f.fixedSubmodule = LinearMap.ker (1 - f) := by
    rw [LinearMap.fixedSubmodule_eq_ker, ← LinearMap.ker_neg, neg_sub, Module.End.one_eq_id]
  have hspan : Submodule.span R (Set.range (fun p => b p + f (b p))) =
      LinearMap.range (1 + f) := by
    rw [← Submodule.span_eq (LinearMap.range _), LinearMap.coe_range,
      Module.Basis.span_range_eq_span_range_basis b]
    rfl
  exact hfixed.trans ((End.range_one_add_eq_ker_one_sub hf).symm.trans hspan.symm)

end Spanning

end TauCeti
