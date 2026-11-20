/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
import TauCeti.FieldTheory.Finite.ProdXSubC

/-!
# The residues of `ZMod p` in a ring of characteristic `p`

Ring homomorphisms commute with `ZMod.cast`. In a ring of prime characteristic `p`, the
image of every residue `i ∈ ZMod p` is fixed by the `p`-power map; in a commutative such
ring, so is its translate `x - i` whenever `x` is. The polynomial identity
`∏ i ∈ 𝔽_p, (X - i) = X ^ p - X` specializes to `∏ i : ZMod p, (x - i) = x ^ p - x` for every
element `x`.

## Main results

* `TauCeti.map_zmodCast`: `f (i : R) = (i : S)` for a ring homomorphism `f : R → S` and
  `i : ZMod n`.
* `TauCeti.zmodCast_pow_char`: `(i : R) ^ p = i` for `i : ZMod p` in characteristic `p`.
* `TauCeti.sub_zmodCast_pow_char`: if `x ^ p = x`, then `(x - i) ^ p = x - i`.
* `TauCeti.prod_sub_zmodCast`: `∏ i : ZMod p, (x - i) = x ^ p - x` in characteristic `p`.
-/

public section

open Polynomial

namespace TauCeti

/-- Ring homomorphisms commute with the cast from `ZMod n`, for every `n` including `0`. -/
@[simp]
theorem map_zmodCast {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) {n : ℕ} (i : ZMod n) : f (i.cast : R) = (i.cast : S) := by
  rw [← ZMod.intCast_cast, map_intCast, ZMod.intCast_cast]

/-- In characteristic `p`, the image of a residue `i ∈ ZMod p` is fixed by the `p`-power map. -/
@[simp]
theorem zmodCast_pow_char {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] (i : ZMod p) :
    (i.cast : R) ^ p = i.cast := by
  rw [← ZMod.cast_pow', ZMod.pow_card]

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime] [CharP R p]

/-- In characteristic `p`, elements fixed by the `p`-power map stay fixed after translation by a
residue of `ZMod p`. -/
theorem sub_zmodCast_pow_char {x : R} (hx : x ^ p = x) (i : ZMod p) :
    (x - (i.cast : R)) ^ p = x - (i.cast : R) := by
  rw [sub_pow_char, hx, zmodCast_pow_char]

variable (p) in
/-- In characteristic `p`, `x ^ p - x` is the product of the translates `x - i` over all
residues `i ∈ ZMod p`. -/
theorem prod_sub_zmodCast (x : R) : ∏ i : ZMod p, (x - (i.cast : R)) = x ^ p - x := by
  simpa [map_prod] using congrArg (eval₂RingHom (ZMod.castHom dvd_rfl R) x)
    (FiniteField.prod_X_sub_C_eq_X_pow_card_sub_X (ZMod p))

end TauCeti
