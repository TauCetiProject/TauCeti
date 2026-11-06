/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Coordinates with respect to a base

Let `b` be a base of a root system `P`. The simple coroots form a basis of the coweight space, so
a vector of the weight space is determined by its pairings `⟨x, αₖ∨⟩` with them. For a
crystallographic root pairing, the pairings of a simple root `αᵢ` with the simple coroots form the
row `i` of the Cartan matrix of `b`.

## Main results

* `RootPairing.Base.ext_coroot'`: a vector is determined by its pairings with the simple coroots.
* `RootPairing.Base.coroot'_root_eq_cartanMatrix_row`: the pairings of a simple root with the simple
  coroots are the corresponding row of the Cartan matrix.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

/-- A vector of a root system is determined by its pairings with the simple coroots of a base. -/
theorem ext_coroot' [P.IsRootSystem] {x y : M}
    (h : ∀ k : b.support, P.coroot' k x = P.coroot' k y) : x = y := by
  refine P.toPerfPair.injective (b.toCoweightBasis.ext fun k ↦ ?_)
  simpa using h k

/-- The pairings of the simple root `αᵢ` with the simple coroots are the row `i` of the Cartan
matrix. -/
theorem coroot'_root_eq_cartanMatrix_row [P.IsCrystallographic] (i k : b.support) :
    P.coroot' k (P.root i) = (b.cartanMatrix.row i k : R) := by
  rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, eq_intCast, Matrix.row_apply,
    cartanMatrix, cartanMatrixIn_def]

end RootPairing.Base
