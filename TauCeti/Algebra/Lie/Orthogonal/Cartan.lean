/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import TauCeti.Algebra.Lie.Orthogonal.Basic
import TauCeti.Algebra.Lie.Orthogonal.Killing

/-!
# The Cartan involution of the indefinite orthogonal Lie algebras

The indefinite orthogonal Lie algebra `𝔰𝔬(p, q)` is closed under transpose, which over `ℝ` is the
conjugate transpose, and it has trivial radical for `p + q ≥ 3`. So the matrix Cartan criterion
`LieSubalgebra.isCartanInvolution_restrictNegConjTranspose` makes `θ X = -Xᵀ` a Cartan involution
of `𝔰𝔬(p, q)` (Knapp, Prop. 6.28).

## Main results

* `LieAlgebra.Orthogonal.isCartanInvolution_restrictNegConjTranspose_so'`: `X ↦ -Xᵀ` is a
  Cartan involution of `𝔰𝔬(p, q)` for `p + q ≥ 3`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2, Proposition 6.28.
-/

public section

namespace LieAlgebra.Orthogonal

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- **`X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔬(p, q)`** for `p + q ≥ 3`. -/
theorem isCartanInvolution_restrictNegConjTranspose_so'
    (hpq : 3 ≤ Fintype.card p + Fintype.card q) :
    ((so' p q ℝ).restrictNegConjTranspose fun _ ↦ conjTranspose_mem_so').IsCartanInvolution :=
  have := TauCeti.hasTrivialRadical_so' ℝ hpq
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose _ _

end LieAlgebra.Orthogonal
