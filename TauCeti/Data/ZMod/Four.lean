/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

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
* `ZMod.cast_add_two_mul_cast_sub_add_eq_zero`: if `a - b + c = 0` and `p - q + r = c a` in `𝔽₂`,
  the lifts `a + 2 p`, `b + 2 q`, `c + 2 r` have alternating sum `0` in `ℤ/4`.
* `ZMod.castHom_eq_zero_of_two_smul_eq_zero`: an element of `ℤ/4` killed by `2` reduces to `0`
  modulo `2`.
* `ZMod.eq_zero_or_eq_one_or_eq_two_or_eq_three`: every residue modulo four is `0`, `1`, `2` or `3`.
* `TauCeti.forall_multiplicative_zmod_four`: a statement holds on `C₄ = Multiplicative (ZMod 4)`
  iff it holds at `ofAdd 0`, `ofAdd 1`, `ofAdd 2` and `ofAdd 3`.
* `TauCeti.univ_multiplicative_zmod_four`: the elements of `C₄` are `ofAdd 0`, `ofAdd 1`,
  `ofAdd 2` and `ofAdd 3`.
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

/-- The lift `(u, s) ↦ u + 2s` on the three faces of a `2`-simplex: if `a - b + c = 0` and
`p - q + r = c a` in `𝔽₂`, the lifts `a + 2 p`, `b + 2 q`, `c + 2 r` have alternating sum `0` in
`ℤ/4`. -/
theorem cast_add_two_mul_cast_sub_add_eq_zero {a b c p q r : ZMod 2} (h : a - b + c = 0)
    (h' : p - q + r = c * a) :
    ((cast a : ZMod 4) + 2 * cast p) - ((cast b : ZMod 4) + 2 * cast q) +
      ((cast c : ZMod 4) + 2 * cast r) = 0 := by
  obtain rfl : b = c + a := eq_of_sub_eq_zero (by rw [← neg_eq_zero, ← h]; ring)
  obtain rfl : q = r + p - c * a :=
    eq_of_sub_eq_zero (by rw [← neg_eq_zero, ← sub_eq_zero.2 h']; ring)
  rw [cast_add_two_mul_cast_sub_mul c a r p]
  ring

/-- The lift `u + 2s` of a pair of residues modulo two reduces to `u` modulo `2`. -/
@[simp]
theorem cast_cast_add_two_mul_cast (u s : ZMod 2) :
    (cast ((cast u : ZMod 4) + 2 * cast s) : ZMod 2) = u := by
  decide +revert

/-- An element of `ℤ/4` killed by `2` reduces to `0` modulo `2`. -/
theorem castHom_eq_zero_of_two_smul_eq_zero {m : ZMod 4} (h : (2 : ℤ) • m = 0) :
    castHom (by decide : 2 ∣ 4) (ZMod 2) m = 0 := by
  revert m h
  decide

/-- Every residue modulo four is `0`, `1`, `2` or `3`. -/
theorem eq_zero_or_eq_one_or_eq_two_or_eq_three (a : ZMod 4) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  decide +revert

end ZMod

namespace TauCeti

open Multiplicative

/-- A statement holds for every element of `C₄ = Multiplicative (ZMod 4)` if and only if it holds
at `ofAdd 0`, `ofAdd 1`, `ofAdd 2` and `ofAdd 3`. -/
theorem forall_multiplicative_zmod_four {P : Multiplicative (ZMod 4) → Prop} :
    (∀ g, P g) ↔ P (ofAdd 0) ∧ P (ofAdd 1) ∧ P (ofAdd 2) ∧ P (ofAdd 3) := by
  refine ⟨fun h ↦ ⟨h _, h _, h _, h _⟩, fun ⟨h₀, h₁, h₂, h₃⟩ g ↦ ?_⟩
  obtain ⟨a, rfl⟩ := ofAdd.surjective g
  rcases ZMod.eq_zero_or_eq_one_or_eq_two_or_eq_three a with rfl | rfl | rfl | rfl <;> assumption

/-- The elements of `C₄ = Multiplicative (ZMod 4)` are `ofAdd 0`, `ofAdd 1`, `ofAdd 2` and
`ofAdd 3`. -/
theorem univ_multiplicative_zmod_four :
    (Finset.univ : Finset (Multiplicative (ZMod 4))) = {ofAdd 0, ofAdd 1, ofAdd 2, ofAdd 3} := by
  decide

end TauCeti
