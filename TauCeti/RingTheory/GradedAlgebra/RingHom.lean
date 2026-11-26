/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Graded ring maps from ring equivalences

## Main definitions

* `RingEquiv.toGradedRingHom` bundles a degree-preserving ring equivalence as a graded ring map.
* `RingEquiv.toGradedRingHom_apply` gives the underlying function of that map.

## References

* Mathlib's `RingEquiv.toRingHom` and `GradedRingHom` supply the underlying map and graded bundle.
-/

public section

namespace RingEquiv

variable {ι A B σ τ : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  {𝒜 : ι → σ} {ℬ : ι → τ}

/-- The graded ring homomorphism underlying a degree-preserving ring equivalence. -/
abbrev toGradedRingHom (e : A ≃+* B) (he : ∀ ⦃i a⦄, a ∈ 𝒜 i → e a ∈ ℬ i) : 𝒜 →+*ᵍ ℬ where
  __ := e.toRingHom
  map_mem := @he

/-- Evaluating the graded map gives the underlying ring equivalence. -/
@[simp]
theorem toGradedRingHom_apply (e : A ≃+* B) (he : ∀ ⦃i a⦄, a ∈ 𝒜 i → e a ∈ ℬ i) (a : A) :
    e.toGradedRingHom (𝒜 := 𝒜) (ℬ := ℬ) he a = e a := (rfl)

end RingEquiv
