/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The roots of a unit

In a monoid `M`, for `n ≠ 0`, every root of `x ^ n = u` with `u` a unit is a unit: this is
Mathlib's `Units.ofPow`. Thus the roots of `x ^ n = u` in `M` are the roots of `y ^ n = u` in the
unit group `Mˣ`, and the two sets have the same cardinality. This reduces a count of roots in a
monoid with zero, such as a finite field, to a count in its unit group, where group theory
applies.

## Main results

* `Units.natCard_pow_eq_val`: `Nat.card {x : M // x ^ n = u} = Nat.card {y : Mˣ // y ^ n = u}`
  for `n ≠ 0`.
-/

public section

/-- **The roots of a unit are units.** In a monoid `M`, for `n ≠ 0`, every root of `x ^ n = u`
with `u` a unit is a unit (Mathlib's `Units.ofPow`). Thus the roots of `x ^ n = u` in `M` are as
many as the roots of `y ^ n = u` in `Mˣ`. -/
theorem Units.natCard_pow_eq_val {M : Type*} [Monoid M] {n : ℕ} (hn : n ≠ 0) (u : Mˣ) :
    Nat.card {x : M // x ^ n = u} = Nat.card {y : Mˣ // y ^ n = u} :=
  Nat.card_congr <| .symm <| .ofBijective
    (fun y => ⟨(y.val : M), by rw [← val_pow_eq_pow_val, y.property]⟩)
    ⟨fun _ _ h => Subtype.ext <| Units.ext <| congrArg Subtype.val h, fun x =>
      ⟨⟨u.ofPow x hn x.property, Units.ext <| by rw [val_pow_eq_pow_val]; exact x.property⟩, rfl⟩⟩
