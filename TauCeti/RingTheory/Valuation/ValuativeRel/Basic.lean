/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Basic facts about valuative relations

General lemmas about `ValuativeRel` that Mathlib does not yet provide.

## Main results

* `TauCeti.ValuativeRel.not_vle_zero_of_isUnit` : If `f` is a unit, then `¬ f ≤ᵥ 0`.
* `TauCeti.valuativeExtension_self`: every valuative commutative semiring is a valuative extension
  of itself.

## References

`TauCeti.ValuativeRel.not_vle_zero_of_isUnit` is ported from the open Mathlib pull request
[leanprover-community/mathlib4#38009](https://github.com/leanprover-community/mathlib4/pull/38009);
this copy is deleted in favour of the Mathlib declaration once that pull request reaches the
pinned Mathlib.
-/

public section

namespace TauCeti.ValuativeRel

/-- If `f` is a unit, then `¬ f ≤ᵥ 0`. -/
theorem not_vle_zero_of_isUnit {A : Type*} [Semiring A] [ValuativeRel A] {f : A}
    (hf : IsUnit f) : ¬ f ≤ᵥ (0 : A) := by
  obtain ⟨u, rfl⟩ := hf
  intro h
  simpa [Units.inv_mul, ValuativeRel.not_vle.mpr ValuativeRel.zero_vlt_one] using
    ValuativeRel.mul_vle_mul_right h ↑u⁻¹

end TauCeti.ValuativeRel

namespace TauCeti

/-- A commutative semiring equipped with a valuative relation is a valuative extension of itself. -/
instance valuativeExtension_self (K : Type*) [CommSemiring K] [ValuativeRel K] :
    ValuativeExtension K K := ⟨fun a b ↦ by simp⟩

end TauCeti
