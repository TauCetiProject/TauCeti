/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.YSeed.Geometric
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Compatibility

/-!
# Principal tropical coefficients along mutation words

The normalized tropical Y-seed with initial coefficients the generators has extended matrix
`principalExtension`, the initial principal matrix above an identity block. Reading tropical
exponents commutes with every finite mutation word. Consequently the coefficient exponent at
any frozen index is the corresponding entry of the mutated principal extension's frozen block.

Mutable and coefficient indices need not be finite: the tropical exponents still have finite
support. The comparison retains the original chosen matrix symmetrizer and uses the geometric
tropical correspondence, rather than another matrix or vector carrier.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compositio Mathematica
  143 (2007), §3, principal coefficients.
-/

public section

namespace TauCeti

namespace ExchangeMatrix

variable {K : Type*} (B : ExchangeMatrix (Function.Embedding.refl K))

/-- The normalized tropical Y-seed with matrix `B` and the principal initial coefficients. -/
noncomputable def principalYSeed : YSeed K (Trop K) where
  coefficient := Trop.generator
  exchangeMatrix := B

/-- The principal initial coefficients are the tropical generators. -/
@[simp]
theorem principalYSeed_coefficient (k : K) :
    B.principalYSeed.coefficient k = Trop.generator k :=
  (rfl)

/-- The principal tropical seed retains its original exchange matrix and chosen symmetrizer. -/
@[simp]
theorem principalYSeed_exchangeMatrix : B.principalYSeed.exchangeMatrix = B :=
  (rfl)

variable [DecidableEq K]

/-- The initial principal tropical seed presents the principal extended exchange matrix. -/
@[simp]
theorem toExtendedMatrix_principalYSeed :
    B.principalYSeed.toExtendedMatrix = B.principalExtension := by
  ext : 1
  · ext (i | i) k <;>
      simp [principalExtension_matrix, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  · simp

/-- Every frozen column of a principal matrix pattern has finite support, even with infinitely
many mutable and coefficient indices. -/
@[simp]
theorem hasFiniteFrozenColumnSupport_principalExtension_mutationWord (w : List K) :
    (B.principalExtension.mutationWord w).HasFiniteFrozenColumnSupport := by
  have h : (B.principalYSeed.mutationWord w).toExtendedMatrix =
      B.principalExtension.mutationWord w := by simp
  rw [← h]
  exact YSeed.hasFiniteFrozenColumnSupport_toExtendedMatrix _

/-- Reading the mutated principal extension recovers the normalized tropical pattern. -/
@[simp]
theorem toTropicalYSeed_principalExtension_mutationWord (w : List K)
    (h : (B.principalExtension.mutationWord w).HasFiniteFrozenColumnSupport) :
    (B.principalExtension.mutationWord w).toTropicalYSeed h =
        B.principalYSeed.mutationWord w := by
  apply YSeed.toExtendedMatrix_injective
  simp

/-- A normalized principal coefficient has the finitely supported exponent vector obtained by
reading the corresponding frozen column along the same mutation word. -/
theorem toAdd_principalYSeed_mutationWord_coefficient (w : List K)
    (h : (B.principalExtension.mutationWord w).HasFiniteFrozenColumnSupport) (k : K) :
    ((B.principalYSeed.mutationWord w).coefficient k).toAdd =
      (B.principalExtension.mutationWord w).frozenColumn h k := by
  ext i
  rw [frozenColumn_apply, ← YSeed.toExtendedMatrix_matrix_inr,
    YSeed.toExtendedMatrix_mutationWord, toExtendedMatrix_principalYSeed]

end ExchangeMatrix

end TauCeti
