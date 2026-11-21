/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.IntegralDomain

/-!
# Orthogonality for the powers of a generating character

Let `M` be a commutative monoid with finitely many units and `R` a domain. If an `R`-valued
multiplicative character `ω` of `M` has order `#Mˣ`, then the column orthogonality relation can
be written as a sum over the powers `ω ^ m`, `0 ≤ m < #Mˣ`: it is `#Mˣ` at `x = 1` and `0` at
every other `x`. Indeed the image of `ω` on `Mˣ` is a finite subgroup of the units of a domain,
hence cyclic, so its order is its exponent `orderOf ω = #Mˣ` and `ω` is injective on `Mˣ`. If
`R` moreover has enough roots of unity, so that there are as many characters as units
(Mathlib's `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity`), such an `ω` generates the
group of characters. Over a finite field `F` with `ω` of order `#F - 1`, this is the form in
which the indicator of `x = y` is expanded when a sum over a torus is written through Gauss
sums, as in the finite hypergeometric sums of Beukers, Cohen and Mellit.

## Main results

* `MulChar.zpowers_eq_top_of_orderOf_eq_card_units`: a character of order `#Mˣ` generates the
  group of characters, with values in a domain with enough roots of unity.
* `MulChar.sum_range_pow_apply_eq_ite`: `∑_{m < #Mˣ} (ω ^ m) x` is `#Mˣ` at `x = 1` and `0`
  elsewhere, for `ω` of order `#Mˣ` with values in a domain.
-/

public section

namespace MulChar

open Finset

variable {M R : Type*} [CommMonoid M] [Fintype Mˣ] [CommRing R] [IsDomain R] {ω : MulChar M R}

/-- A multiplicative character whose order is the order `#Mˣ` of the unit group generates the
group of all characters with values in a domain with enough roots of unity. -/
theorem zpowers_eq_top_of_orderOf_eq_card_units [Finite M]
    [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)] (hω : orderOf ω = Fintype.card Mˣ) :
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
  -- The image of `ω` on `Mˣ` is cyclic, so its order is its exponent, which `orderOf ω` divides.
  -- Hence it has `#Mˣ` elements, `ω` is injective on `Mˣ` and `ω u ≠ 1`.
  have : Finite ω.toUnitHom.range := .of_surjective _ ω.toUnitHom.rangeRestrict_surjective
  have hdvd : orderOf ω ∣ Nat.card ω.toUnitHom.range := by
    rw [← IsCyclic.exponent_eq_card]
    refine orderOf_dvd_of_pow_eq_one (MulChar.ext fun v ↦ ?_)
    have h := congrArg (fun w : ω.toUnitHom.range ↦ ((w : Rˣ) : R))
      (Monoid.pow_exponent_eq_one (⟨ω.toUnitHom v, v, rfl⟩ : ω.toUnitHom.range))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_toUnitHom,
      OneMemClass.coe_one, Units.val_one] at h
    rw [pow_apply_coe, h, one_apply_coe]
  have hinj : Function.Injective ω.toUnitHom :=
    MonoidHom.rangeRestrict_injective_iff.mp
      (ω.toUnitHom.rangeRestrict_surjective.bijective_of_nat_card_le <| by
        rw [Nat.card_eq_fintype_card, ← hω]
        exact Nat.le_of_dvd Nat.card_pos hdvd).1
  have hne : ω u ≠ 1 := fun h ↦ hx <| Units.val_eq_one.mpr <| hinj <| Units.ext <| by
    rw [coe_toUnitHom, h, map_one, Units.val_one]
  have hpow : ω u ^ Fintype.card Mˣ = 1 := by
    rw [← pow_apply_coe, ω.pow_card_eq_one, one_apply_coe]
  have hgeom := geom_sum_mul (ω u) (Fintype.card Mˣ)
  rw [hpow, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

end MulChar
