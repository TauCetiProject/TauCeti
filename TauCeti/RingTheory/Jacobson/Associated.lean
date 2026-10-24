/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Associated elements congruent modulo the Jacobson radical

If `z` lies in the Jacobson radical of a commutative ring and `y ≡ x` modulo `x z`, then `x` and
`y` are associated: `y = x (1 + z c)`, and `1 + z c` is a unit. A typical use is an element `x`
of the Jacobson radical and `y ≡ x` modulo `x ^ n` with `n ≥ 2`, taking `z = x ^ (n - 1)`.

## Main results

* `TauCeti.associated_of_mul_dvd_sub_of_mem_jacobson`: `x * z ∣ y - x` with `z` in the Jacobson
  radical makes `x` and `y` associated.
-/

public section

namespace TauCeti

/-- If `z` lies in the Jacobson radical and `x * z ∣ y - x`, then `x` and `y` are associated:
`y = x (z c + 1)`, and `z c + 1` is a unit. -/
theorem associated_of_mul_dvd_sub_of_mem_jacobson {R : Type*} [CommRing R] {x y z : R}
    (hz : z ∈ Ideal.jacobson (⊥ : Ideal R)) (h : x * z ∣ y - x) : Associated x y := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(Ideal.mem_jacobson_bot.mp hz c).unit, ?_⟩
  rw [IsUnit.unit_spec, mul_add_one, ← mul_assoc, ← hc, sub_add_cancel]

end TauCeti
