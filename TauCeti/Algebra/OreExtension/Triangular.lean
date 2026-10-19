/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import TauCeti.Algebra.OreExtension.Basic

import Mathlib.Data.Matrix.Mul

/-!
# Skew derivations from triangular matrix representations

For an algebra endomorphism `σ` of `R`, a linear map `δ : R → R` satisfies the skew Leibniz rule
`δ (a b) = σ a δ b + δ a b` exactly when `r ↦ !![σ r, δ r; 0, r]` is multiplicative: the
upper-right entry of a product of two such matrices is `σ a δ b + δ a b`. Consequently the
upper-right corner of any algebra map `R → Mat₂(R)` whose diagonal entries are `σ r` and `r` is
a `σ`-derivation.

This is the standard way to extend a skew derivation that is prescribed only on generators: the
matrix-valued algebra map is produced by a universal property, and checking its shape on
generators replaces checking the Leibniz rule on all of `R`. Iterated Ore presentations, such as
the presentation of the quantized enveloping algebra of `sl₂` by adjoining `F` and then `E` to
the Laurent polynomials in `K`, construct their second skew derivation this way.

## Main definitions

* `TauCeti.SigmaDerivation.ofMatrix`: the `σ`-derivation in the upper-right corner of an algebra
  map `R →ₐ[k] Matrix (Fin 2) (Fin 2) R` with diagonal entries `σ r` and `r`.
-/

public section

namespace TauCeti.SigmaDerivation

variable {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R] {σ : R →ₐ[k] R}

/-- The upper-right corner of an algebra map `Φ : R → Mat₂(R)` whose diagonal entries are
`σ r` and `r` is a `σ`-derivation: `Φ r = !![σ r, δ r; *, r]` forces the skew Leibniz rule
`δ (a b) = σ a δ b + δ a b`. -/
def ofMatrix (Φ : R →ₐ[k] Matrix (Fin 2) (Fin 2) R) (h₀₀ : ∀ r, Φ r 0 0 = σ r)
    (h₁₁ : ∀ r, Φ r 1 1 = r) : SigmaDerivation σ where
  toLinearMap := Matrix.entryLinearMap k R 0 1 ∘ₗ Φ.toLinearMap
  leibniz' a b := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, h₀₀, h₁₁]
  map_one' := by simp

/-- The value of `ofMatrix` is the upper-right entry of the matrix. -/
@[simp]
theorem ofMatrix_apply (Φ : R →ₐ[k] Matrix (Fin 2) (Fin 2) R) (h₀₀ : ∀ r, Φ r 0 0 = σ r)
    (h₁₁ : ∀ r, Φ r 1 1 = r) (r : R) : ofMatrix Φ h₀₀ h₁₁ r = Φ r 0 1 := (rfl)

end TauCeti.SigmaDerivation
