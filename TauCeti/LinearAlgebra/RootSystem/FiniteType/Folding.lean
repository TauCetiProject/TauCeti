/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Folding.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

/-!
# The folded Cartan matrix of a diagram automorphism is of finite type

Let `B : Matrix I I ℤ` be positive definite with diagonal entries `2` and nonpositive off-diagonal
entries, the Cartan matrix of a simply laced Dynkin diagram, possibly disconnected, and let
`σ : Equiv.Perm I` be a diagram automorphism, `B.reindex σ σ = B`. The folded Cartan matrix
`C = Matrix.foldedCartanMatrix B σ`, indexed by the `σ`-orbits of vertices with `H` rows and `E`
columns, is the Cartan matrix of the Lie algebra fixed by the pinned action of `σ`.

This file shows that `C` is of finite type in the sense of `TauCeti.IsFiniteType`
(`Matrix.isFiniteType_foldedCartanMatrix`), so that the classification of finite-type Cartan
matrices applies to it. The symmetrization is explicit: multiplying row `O` of `C` by the positive
folding symmetrizer `δ_O` (`Matrix.foldingSymmetrizer`) gives the positive definite Gram matrix
of the folded simple roots (`Matrix.foldedGramMatrix`), both from
`TauCeti.LinearAlgebra.Matrix.Cartan.Folding.Basic`.

## Main results

* `Matrix.isFiniteType_foldedCartanMatrix`: the folded Cartan matrix is of finite type.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.9, for the fixed points of a diagram automorphism and the folded Cartan matrix.
-/

public section

namespace Matrix

variable {I : Type*} [Fintype I] [DecidableEq I] {B : Matrix I I ℤ} {σ : Equiv.Perm I}

/-- **The folded Cartan matrix is of finite type.** For a positive definite `σ`-invariant `B` with
diagonal entries `2` and nonpositive off-diagonal entries, the folded Cartan matrix is a
generalized Cartan matrix with positive symmetrizer `δ_O = Matrix.foldingSymmetrizer B σ O`, whose
symmetrization is the positive definite folded Gram matrix. -/
theorem isFiniteType_foldedCartanMatrix (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B) :
    TauCeti.IsFiniteType (B.foldedCartanMatrix σ) := by
  refine TauCeti.isFiniteType_of (foldedCartanMatrix_apply_self hB hdiag hoff hσ)
    (fun _ _ ↦ foldedCartanMatrix_nonpos hB hdiag hoff hσ)
    (foldingSymmetrizer_pos hB hdiag hoff hσ) ?_
  convert posDef_foldedGramMatrix σ hB using 1
  ext O P
  exact foldingSymmetrizer_mul_foldedCartanMatrix hB hdiag hoff hσ O P

end Matrix
