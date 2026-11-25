/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import TauCeti.Algebra.Lie.IndefiniteUnitary

/-!
# The Cartan involution of the special indefinite unitary Lie algebras

The real Lie algebra `𝔰𝔲(p, q)` is closed under conjugate transpose
(`TauCeti.conjTranspose_mem_specialIndefiniteUnitaryLieAlgebra`) and semisimple
(`TauCeti.isSemisimple_specialIndefiniteUnitaryLieAlgebra`). So the matrix Cartan criterion
`LieSubalgebra.isCartanInvolution_restrictNegConjTranspose` makes `θ X = -Xᴴ` a Cartan involution
of `𝔰𝔲(p, q)` (Knapp, Prop. 6.28).

## Main results

* `TauCeti.isCartanInvolution_restrictNegConjTranspose_specialIndefiniteUnitaryLieAlgebra`:
  `X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔲(p, q)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2, Proposition 6.28.
-/

public section

namespace TauCeti

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- **`X ↦ -Xᴴ` is a Cartan involution of `𝔰𝔲(p, q)`.** -/
theorem isCartanInvolution_restrictNegConjTranspose_specialIndefiniteUnitaryLieAlgebra :
    ((specialIndefiniteUnitaryLieAlgebra p q).restrictNegConjTranspose
      fun _ ↦ conjTranspose_mem_specialIndefiniteUnitaryLieAlgebra).IsCartanInvolution :=
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose _ _

end TauCeti
