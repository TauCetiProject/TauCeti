/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective

/-!
# Retracts of injective modules

A retract of an injective module in the same universe is injective, straight from the class
`Module.Injective`.

## Main results

* `Module.Injective.of_leftInverse`: a retract of an injective module of the same universe is
  injective.
-/

public section

universe u v

variable {R : Type u} [Ring R] {Q : Type v} [AddCommGroup Q] [Module R Q]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- **Injective modules are closed under retracts.** If `M` admits a split inclusion into an
injective module `Q` of the same universe, then `M` is injective. -/
theorem Module.Injective.of_leftInverse (hQ : Module.Injective R Q) (s : M →ₗ[R] Q)
    (r : Q →ₗ[R] M) (hrs : ∀ m, r (s m) = m) : Module.Injective R M :=
  ⟨fun X Y _ _ _ _ f hf g => by
    obtain ⟨h, hh⟩ := hQ.out f hf (s ∘ₗ g)
    exact ⟨r ∘ₗ h, fun x => by simp only [LinearMap.comp_apply, hh, hrs]⟩⟩
