/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# The Galois action on the ring of integers

For a number field `K`, an algebra automorphism `σ : K ≃ₐ[ℚ] K` acts on the ring of integers
`𝓞 K` (which is stable under `σ`), and that action is compatible with the inclusion `𝓞 K ↪ K`:

`algebraMap (𝓞 K) K (σ • y) = σ (algebraMap (𝓞 K) K y)`.

This is the bridge for moving an identity between `𝓞 K` and `K` along a Galois automorphism, used
whenever a computation (residues, Frobenius congruences) lives on `𝓞 K` but the conclusion is
stated on `K`.

## Main result

* `TauCeti.NumberField.algebraMap_aut_smul`: the compatibility above.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

/-- **The Galois action on `𝓞 K` is the restriction of the action on `K`.** For `σ : K ≃ₐ[ℚ] K`,
the inclusion `𝓞 K ↪ K` is `σ`-equivariant: `algebraMap (𝓞 K) K (σ • y) = σ (algebraMap (𝓞 K) K y)`.
Since `𝓞 K = integralClosure ℤ K` and its coercion to `K` is `algebraMap`, this is
`integralClosure.coe_smul`. -/
@[simp] theorem algebraMap_aut_smul {K : Type*} [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K)
    (y : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • y) = σ (algebraMap (𝓞 K) K y) :=
  integralClosure.coe_smul σ y

end TauCeti.NumberField
