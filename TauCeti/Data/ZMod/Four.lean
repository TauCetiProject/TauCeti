/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# The carry from `ℤ/4` to `𝔽₂`

A residue `x` modulo four has canonical representative `x.val ∈ {0, 1, 2, 3}`, whose binary digits
are `x mod 2` and the carry `⌊x.val / 2⌋`. Reducing the carry modulo two gives the function
`ZMod.carryFour : ℤ/4 → 𝔽₂`. Its failure to be additive is measured by the product of the
residues modulo two: `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)`. This is the identity behind
the vanishing of the cup square of a class of `H¹(G, 𝔽₂)` that lifts to a character to `ℤ/4`.

## Main results

* `ZMod.carryFour`: the carry `⌊x.val / 2⌋ : ℤ/4 → 𝔽₂`.
* `ZMod.carryFour_add`: **the carry identity** `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)`.
* `ZMod.carryFour_zero`: the carry of `0` is `0`.
* `ZMod.cast_add_two_mul_cast_sub_mul`: the lift `(u, s) ↦ u + 2s` of a pair of residues modulo
  two to `ℤ/4` is additive up to the carry `u v` in the second coordinate.
* `ZMod.cast_cast_add_two_mul_cast`: that lift reduces to its first coordinate modulo `2`.
-/

public section

namespace ZMod

/-- The carry `⌊x.val / 2⌋ : ℤ/4 → 𝔽₂`: the binary digit of weight two of the canonical
representative of a residue modulo four. -/
def carryFour (x : ZMod 4) : ZMod 2 := ((x.val / 2 : ℕ) : ZMod 2)

/-- The carry of `0` is `0`. -/
@[simp]
theorem carryFour_zero : carryFour 0 = 0 := by
  decide

/-- **The carry identity in `ℤ/4`**: `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)` in `𝔽₂`. -/
@[simp]
theorem carryFour_add (u v : ZMod 4) :
    carryFour (u + v) =
      carryFour u + carryFour v +
        castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2) u *
          castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2) v := by
  revert u v
  decide

/-- **The lift `(u, s) ↦ u + 2s` of two residues modulo two to `ℤ/4` is additive up to the
carry**: `(u + v) + 2 (s + t - u v) = (u + 2 s) + (v + 2 t)` in `ℤ/4`, where the residues are
lifted through `ZMod.cast`. This is the identity that turns a character `G → 𝔽₂` with vanishing
cup square into a character `G → ℤ/4`. -/
theorem cast_add_two_mul_cast_sub_mul (u v s t : ZMod 2) :
    (cast (u + v) : ZMod 4) + 2 * cast (s + t - u * v) =
      (cast u + 2 * cast s) + (cast v + 2 * cast t) := by
  revert u v s t
  decide

/-- The lift `u + 2s` of a pair of residues modulo two reduces to `u` modulo `2`. -/
@[simp]
theorem cast_cast_add_two_mul_cast (u s : ZMod 2) :
    (cast ((cast u : ZMod 4) + 2 * cast s) : ZMod 2) = u := by
  revert u s
  decide

end ZMod
