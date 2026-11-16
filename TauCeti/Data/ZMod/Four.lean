/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Residues and units modulo four

A residue `x` modulo four has canonical representative `x.val ∈ {0, 1, 2, 3}`, whose binary digits
are `x mod 2` and the carry `⌊x.val / 2⌋`. Reducing the carry modulo two gives the function
`ZMod.carryFour : ℤ/4 → 𝔽₂`. Its failure to be additive is measured by the product of the
residues modulo two: `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)`. This is the identity behind
the vanishing of the cup square of a class of `H¹(G, 𝔽₂)` that lifts to a character to `ℤ/4`.

The unit group `(ZMod 4)ˣ` has order two, consisting of `1` and `-1`, so it is a `2`-group
canonically isomorphic to `Multiplicative (ZMod 2)`.

## Main results

* `ZMod.carryFour`: the carry `⌊x.val / 2⌋ : ℤ/4 → 𝔽₂`.
* `ZMod.carryFour_add`: **the carry identity** `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)`.
* `ZMod.carryFour_zero`: the carry of `0` is `0`.
* `ZMod.cast_add_two_mul_cast_sub_mul`: the lift `(u, s) ↦ u + 2s` of a pair of residues modulo
  two to `ℤ/4` is additive up to the carry `u v` in the second coordinate.
* `ZMod.cast_cast_add_two_mul_cast`: that lift reduces to its first coordinate modulo `2`.
* `ZMod.unitsFourMulEquiv`: the multiplicative isomorphism `(ZMod 4)ˣ ≃* Multiplicative (ZMod 2)`.
* `ZMod.unitsFour_eq_one_or_neg_one`, `ZMod.neg_one_ne_one_unitsFour`, `ZMod.isPGroup_unitsFour`:
  the elements of `(ZMod 4)ˣ` are `1 ≠ -1` and `(ZMod 4)ˣ` is a `2`-group.
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
    carryFour (u + v) = carryFour u + carryFour v + (cast u : ZMod 2) * cast v := by
  decide +revert

/-- **The lift `(u, s) ↦ u + 2s` of two residues modulo two to `ℤ/4` is additive up to the
carry**: `(u + v) + 2 (s + t - u v) = (u + 2 s) + (v + 2 t)` in `ℤ/4`, where the residues are
lifted through `ZMod.cast`. This is the identity that turns a character `G → 𝔽₂` with vanishing
cup square into a character `G → ℤ/4`. -/
theorem cast_add_two_mul_cast_sub_mul (u v s t : ZMod 2) :
    (cast (u + v) : ZMod 4) + 2 * cast (s + t - u * v) =
      (cast u + 2 * cast s) + (cast v + 2 * cast t) := by
  decide +revert

/-- The lift `u + 2s` of a pair of residues modulo two reduces to `u` modulo `2`. -/
@[simp]
theorem cast_cast_add_two_mul_cast (u s : ZMod 2) :
    (cast ((cast u : ZMod 4) + 2 * cast s) : ZMod 2) = u := by
  decide +revert

/-- Multiplicative isomorphism `(ZMod 4)ˣ ≃* Multiplicative (ZMod 2)` sending `1 ↦ 1` and
`-1 ↦ Multiplicative.ofAdd 1`. -/
def unitsFourMulEquiv : (ZMod 4)ˣ ≃* Multiplicative (ZMod 2) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd 1
  invFun g := if g = 1 then 1 else -1
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- `unitsFourMulEquiv` sends `-1 : (ZMod 4)ˣ` to the generator `Multiplicative.ofAdd 1`. -/
@[simp]
theorem unitsFourMulEquiv_neg_one :
    unitsFourMulEquiv (-1 : (ZMod 4)ˣ) = Multiplicative.ofAdd 1 := by
  decide

/-- The inverse of `unitsFourMulEquiv` sends `Multiplicative.ofAdd 1` to `-1 : (ZMod 4)ˣ`. -/
@[simp]
theorem unitsFourMulEquiv_symm_ofAdd_one :
    unitsFourMulEquiv.symm (Multiplicative.ofAdd 1) = -1 := by
  decide

/-- Every unit of `ZMod 4` is either `1` or `-1`. -/
theorem unitsFour_eq_one_or_neg_one (u : (ZMod 4)ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide

/-- The two units `-1` and `1` of `ZMod 4` are distinct. -/
theorem neg_one_ne_one_unitsFour : (-1 : (ZMod 4)ˣ) ≠ 1 := by
  decide

/-- The unit group `(ZMod 4)ˣ` has order `2`, hence is a `2`-group. -/
theorem isPGroup_unitsFour : IsPGroup 2 (ZMod 4)ˣ :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card]; decide)

end ZMod
