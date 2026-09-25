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
* `TauCeti.valuation_le_one_of_sub_sq_le_one`: if an integral element differs from a square by
  an integral element, then the square root is integral.
* `TauCeti.one_add_pow_ne_zero_of_valuation_lt_one`: a positive power of an element of valuation
  less than one cannot equal `-1`.

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

open ValuativeRel

namespace TauCeti

/-- A commutative semiring equipped with a valuative relation is a valuative extension of itself. -/
instance valuativeExtension_self (K : Type*) [CommSemiring K] [ValuativeRel K] :
    ValuativeExtension K K := ⟨fun a b ↦ by simp⟩

variable {K : Type*} [Ring K] [ValuativeRel K]

/-- If an element of valuation at most one differs from a square by an element of valuation at
most one, then the square root also has valuation at most one. -/
theorem valuation_le_one_of_sub_sq_le_one {u ξ : K} (hu : valuation K u ≤ 1)
    (hξ : valuation K (u - ξ ^ 2) ≤ 1) : valuation K ξ ≤ 1 := by
  rw [← pow_le_one_iff two_ne_zero, ← map_pow]
  simpa using (valuation K).map_sub_le hu hξ

/-- A positive power of an element of valuation less than one cannot equal `-1`. -/
theorem one_add_pow_ne_zero_of_valuation_lt_one {x : K} (hx : valuation K x < 1)
    {n : ℕ} (hn : n ≠ 0) : 1 + x ^ n ≠ 0 := by
  have hxpow : valuation K (x ^ n) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hx hn
  intro h
  simpa [h] using (valuation K).map_one_add_of_lt hxpow

end TauCeti
