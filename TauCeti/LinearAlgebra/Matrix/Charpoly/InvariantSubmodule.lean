/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Charpoly.Quotient
import Mathlib.Algebra.Star.Pi

/-!
# Matrices keeping an isotropic subspace

Let `J` be a nonzero matrix over a field `K` with involution, and `⟨x, y⟩ = xᴴ J y` the form it
defines on `K^n`. A nonzero subspace `W` on which this form vanishes is not all of `K^n`, since
`J ≠ 0`. So a matrix `g` with `g W ⊆ W` preserves a subspace other than `⊥` and `⊤`, and its
characteristic polynomial, the product of those of `g` on `W` and on `K^n ⧸ W`
(`LinearMap.not_irreducible_charpoly_of_le_comap`), is not irreducible.

## Main results

* `Matrix.not_irreducible_charpoly_of_isotropic`: for a nonzero `J`, a matrix `g` with
  `g W ⊆ W` for a nonzero subspace `W` of `K^n` on which `⟨x, y⟩ = xᴴ J y` vanishes has a
  characteristic polynomial that is not irreducible.

## References

* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `Lib/Adelic/TraceFormula/IsotropicStabiliser.lean`
  (`New.IsIsotropicFrame.not_irreducible_charpoly`), for the statement.
-/

public section

namespace Matrix

variable {K n : Type*} [Field K] [StarRing K] [Fintype n] [DecidableEq n]

/-- **A matrix keeping a nonzero isotropic subspace has a reducible characteristic polynomial.**
Let `J` be nonzero and `W` a nonzero subspace of `K^n` on which the form `⟨x, y⟩ = xᴴ J y`
vanishes. If `g W ⊆ W`, then the characteristic polynomial of `g` is not irreducible. Neither
`J` hermitian or invertible nor `g` unitary is needed. -/
theorem not_irreducible_charpoly_of_isotropic {J g : Matrix n n K} (hJ : J ≠ 0)
    {W : Submodule K (n → K)} (hbot : W ≠ ⊥)
    (hiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ J *ᵥ y = 0) (hg : ∀ x ∈ W, g *ᵥ x ∈ W) :
    ¬ Irreducible g.charpoly := by
  rw [← charpoly_toLin']
  refine LinearMap.not_irreducible_charpoly_of_le_comap _ (W := W) hg hbot fun htop ↦ hJ ?_
  ext a b
  simpa [← Pi.single_star, single_dotProduct, mulVec_single_one] using
    hiso (Pi.single a 1) (by simp [htop]) (Pi.single b 1) (by simp [htop])

end Matrix
