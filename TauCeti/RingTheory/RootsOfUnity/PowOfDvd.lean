/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The power maps between groups of roots of unity

For `n ∣ m`, raising to the power `m / n` sends `m`-th roots of unity to `n`-th roots of unity.
These are the transition maps of the inverse system `(μₘ)ₘ`, along which, for instance, Galois
automorphisms of Kummer extensions of different degrees restrict.

## Main definitions

* `TauCeti.rootsOfUnityPowOfDvd`: for `n ∣ m`, the homomorphism `μₘ → μₙ`, `ζ ↦ ζ ^ (m / n)`.
-/

public section

namespace TauCeti

variable (M : Type*) [CommMonoid M] {n m : ℕ}

/-- For `n ∣ m`, the power map `ζ ↦ ζ ^ (m / n)` from the `m`-th to the `n`-th roots of unity. -/
def rootsOfUnityPowOfDvd (h : n ∣ m) : rootsOfUnity m M →* rootsOfUnity n M :=
  ((powMonoidHom (m / n)).comp (rootsOfUnity m M).subtype).codRestrict _ fun ζ ↦ by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, powMonoidHom_apply, mem_rootsOfUnity,
      ← pow_mul, Nat.div_mul_cancel h, (mem_rootsOfUnity _ _).mp ζ.prop]

variable {M}

/-- The power map `μₘ → μₙ` raises a root of unity to the power `m / n`. -/
@[simp]
theorem coe_rootsOfUnityPowOfDvd (h : n ∣ m) (ζ : rootsOfUnity m M) :
    (rootsOfUnityPowOfDvd M h ζ : Mˣ) = (ζ : Mˣ) ^ (m / n) :=
  (rfl)

end TauCeti
