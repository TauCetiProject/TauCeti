/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Algebra.Ring.GeomSum

/-!
# Orthogonality for the powers of a generating character

Let `M` be a finite commutative monoid and `R` a domain with enough roots of unity, so that
there are as many `R`-valued multiplicative characters of `M` as there are units in `M`
(Mathlib's `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity`). A character `ω` whose order
is `#Mˣ` then generates the group of characters, and the column orthogonality relation can be
written as a sum over the powers `ω ^ m`, `0 ≤ m < #Mˣ`: it is `#Mˣ` at `x = 1` and `0` at every
other `x`. Over a finite field `F` with `ω` of order `#F - 1`, this is the form in which the
indicator of `x = y` is expanded when a sum over a torus is written through Gauss sums, as in the
finite hypergeometric sums of Beukers, Cohen and Mellit.

## Main results

* `MulChar.zpowers_eq_top_of_orderOf_eq_card_units`: a character of order `#Mˣ` generates the
  group of characters.
* `MulChar.sum_range_pow_apply_eq_ite`: `∑_{m < #Mˣ} (ω ^ m) x` is `#Mˣ` at `x = 1` and `0`
  elsewhere, for `ω` of order `#Mˣ`.
-/

public section

namespace MulChar

open Finset

variable {M R : Type*} [CommMonoid M] [Fintype Mˣ] [Finite M] [CommRing R] [IsDomain R]
  [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)] {ω : MulChar M R}

/-- A multiplicative character whose order is the order `#Mˣ` of the unit group generates the
group of all characters with values in a domain with enough roots of unity. -/
theorem zpowers_eq_top_of_orderOf_eq_card_units (hω : orderOf ω = Fintype.card Mˣ) :
    Subgroup.zpowers ω = ⊤ :=
  Subgroup.eq_top_of_card_eq _ <| by
    rw [Nat.card_zpowers, hω, card_eq_card_units_of_hasEnoughRootsOfUnity,
      Nat.card_eq_fintype_card]

/-- **Orthogonality over the powers of a generating character.** If `ω` has order `#Mˣ`, then
`∑_{m < #Mˣ} (ω ^ m) x` is `#Mˣ` when `x = 1` and `0` otherwise. -/
theorem sum_range_pow_apply_eq_ite [DecidableEq M] (hω : orderOf ω = Fintype.card Mˣ) (x : M) :
    ∑ m ∈ range (Fintype.card Mˣ), (ω ^ m) x = if x = 1 then (Fintype.card Mˣ : R) else 0 := by
  split_ifs with hx
  · simp [hx]
  by_cases hu : IsUnit x
  swap
  · simp [map_nonunit _ hu]
  obtain ⟨u, rfl⟩ := hu
  simp_rw [pow_apply_coe]
  -- Some character separates `u` from `1`, and it is a power of `ω`, so `ω u ≠ 1`.
  have hne : ω u ≠ 1 := by
    intro h
    obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity M R hx
    have hmem : χ ∈ Submonoid.powers ω := mem_powers_iff_mem_zpowers.mpr <| by
      rw [zpowers_eq_top_of_orderOf_eq_card_units hω]
      exact Subgroup.mem_top χ
    obtain ⟨k, rfl⟩ := hmem
    exact hχ (by rw [pow_apply_coe, h, one_pow])
  have hpow : ω u ^ Fintype.card Mˣ = 1 := by
    rw [← pow_apply_coe, ω.pow_card_eq_one, one_apply_coe]
  have hgeom := geom_sum_mul (ω u) (Fintype.card Mˣ)
  rw [hpow, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

end MulChar
