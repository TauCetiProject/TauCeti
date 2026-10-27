/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.Algebra.Ring.Units
import Mathlib.Tactic.NoncommRing

/-!
# The Jacobson radical of a ring, elementwise

`Ring.jacobson R` is the intersection of the maximal left ideals of `R`. This file records the
elementwise description of that ideal over a ring that is not assumed commutative: `x` lies in the
radical exactly when `1 + y * x` is a unit for every `y`, equivalently when `1 + x * y` is a unit
for every `y`. Mathlib proves the statement only over a commutative ring
(`Ideal.mem_jacobson_bot`); the content of the noncommutative version is that membership in the
radical only supplies a *left* inverse for `1 + y * x`, so the argument has to promote that left
inverse to a two-sided one.

The two descriptions differ only by the swap `TauCeti.isUnit_one_add_mul_comm`, and that is the
mechanism behind the left-right symmetry of the radical, proved in
`TauCeti/RingTheory/Jacobson/MulOpposite.lean`.

## Main results

* `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left` and
  `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_right`: the two elementwise descriptions of
  the Jacobson radical of a ring.
* `TauCeti.Ring.instNontrivialQuotientJacobson`: the quotient of a nontrivial ring by its Jacobson
  radical is nontrivial.

## References

* N. Jacobson, *Structure of Rings*, AMS Colloquium Publications 37 (1956), Chapter I.
-/

public section

namespace TauCeti

namespace Ring

variable {R : Type*} [Ring R]

/-- Membership in the Jacobson radical, unfolded: `x` lies in `Ring.jacobson R` exactly when
`1 + y * x` has a left inverse for every `y`.

This is `Ideal.mem_jacobson_iff` at the zero ideal, rearranged. Only a left inverse is available
at this stage; `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left` upgrades it to a two-sided
one and is the form to use. -/
private theorem mem_jacobson_iff_forall_exists_mul_one_add_mul_eq_one {x : R} :
    x ∈ Ring.jacobson R ↔ ∀ y : R, ∃ z : R, z * (1 + y * x) = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  refine forall_congr' fun y => exists_congr fun z => ?_
  have h : z * (1 + y * x) = z * y * x + z := by noncomm_ring
  rw [Ideal.mem_bot, sub_eq_zero, h]

/-- The Jacobson radical of a ring is `{x | ∀ y, IsUnit (1 + y * x)}`.

Mathlib's `Ideal.mem_jacobson_bot` is this statement over a commutative ring. -/
theorem mem_jacobson_iff_isUnit_one_add_mul_left {x : R} :
    x ∈ Ring.jacobson R ↔ ∀ y : R, IsUnit (1 + y * x) := by
  rw [mem_jacobson_iff_forall_exists_mul_one_add_mul_eq_one]
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · -- A left inverse `z` of `1 + y * x` is again of the form `1 + y' * x`, so it has a left
    -- inverse `w` in turn; then `w = w * (z * (1 + y * x)) = 1 + y * x`, which makes `z` a
    -- two-sided inverse of `1 + y * x`.
    obtain ⟨z, hz⟩ := h y
    have hexp : z * (1 + y * x) = z * y * x + z := by noncomm_ring
    have h1 : z * y * x + z = 1 := by rw [← hexp]; exact hz
    have hz' : 1 + -(z * y) * x = z := by
      have key : 1 + -(z * y) * x - z = 1 - (z * y * x + z) := by noncomm_ring
      rwa [h1, sub_self, sub_eq_zero] at key
    obtain ⟨w, hw⟩ := h (-(z * y))
    rw [hz'] at hw
    have hwz : w = 1 + y * x :=
      calc w = w * (z * (1 + y * x)) := by rw [hz, mul_one]
        _ = w * z * (1 + y * x) := by rw [mul_assoc]
        _ = 1 + y * x := by rw [hw, one_mul]
    exact ⟨⟨1 + y * x, z, by rw [← hwz]; exact hw, hz⟩, rfl⟩
  · obtain ⟨u, hu⟩ := h y
    exact ⟨↑u⁻¹, by rw [← hu]; exact u.inv_mul⟩

/-- The right-handed description of the Jacobson radical: it is also `{x | ∀ y, IsUnit (1 + x*y)}`.

This is where the left-right symmetry enters: the two descriptions differ only by the swap
`TauCeti.isUnit_one_add_mul_comm`. -/
theorem mem_jacobson_iff_isUnit_one_add_mul_right {x : R} :
    x ∈ Ring.jacobson R ↔ ∀ y : R, IsUnit (1 + x * y) :=
  mem_jacobson_iff_isUnit_one_add_mul_left.trans
    (forall_congr' fun _ => isUnit_one_add_mul_comm)

variable (R) in
/-- The quotient of a nontrivial ring by its Jacobson radical is nontrivial, the radical being
proper by `Ring.jacobson_lt_top`. -/
instance instNontrivialQuotientJacobson [Nontrivial R] :
    Nontrivial (R ⧸ Ring.jacobson R) :=
  Ideal.Quotient.nontrivial_iff.mpr (Ring.jacobson_lt_top R).ne

end Ring

end TauCeti
