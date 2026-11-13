/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive additive characters

Mathlib's `AddChar.IsPrimitive` asks that every multiplicative shift of an additive character by a
nonzero element be nontrivial. Consumers that just need *some* nontrivial additive character —
character sums over a finite field, the cuspidal characters of `GL₂(F)` — want the weaker
statement that a primitive character differs from the trivial one, which is primitivity read at
the shift by `1`. Over a field the converse is Mathlib's `AddChar.IsPrimitive.of_ne_one`. Through
it, a nontrivial additive character of a finite field has vanishing character sum, and this file
records the punctured form of that sum, over the units of the field.

## Main results

* `AddChar.IsPrimitive.ne_one`: a primitive additive character on a nontrivial ring is
  nontrivial.
* `AddChar.IsPrimitive.natCast_ne_zero`: the level of a primitive additive character of `ZMod n`
  with values in a domain is nonzero in that domain.
* `AddChar.sum_units_mul_eq_neg_one`: a nontrivial additive character of a finite field sums to
  `-1` over the nonzero elements, even after multiplication by a unit. This is the punctured form
  of Mathlib's `AddChar.sum_eq_zero_of_ne_one`, reindexed by `Fˣ`, which is the shape character
  computations over a finite field consume directly.
-/

public section

namespace AddChar

variable {R R' : Type*} [CommRing R] [Nontrivial R] [CommMonoid R']

/-- A primitive additive character on a nontrivial ring is nontrivial. -/
theorem IsPrimitive.ne_one {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) : ψ ≠ 1 := by
  simpa only [mulShift_one] using hψ one_ne_zero

/-- The level of a primitive additive character of `ZMod n` with values in a domain is nonzero in
that domain. This is the level hypothesis needed to show that Gauss sums against primitive
additive characters are nonzero. -/
theorem IsPrimitive.natCast_ne_zero {S : Type*} [CommRing S] [IsDomain S] {n : ℕ} [NeZero n]
    {e : AddChar (ZMod n) S} (he : e.IsPrimitive) : (n : S) ≠ 0 := by
  have hroot : IsPrimitiveRoot (e 1) n :=
    { pow_eq_one := by
        rw [← map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero_eq_one]
      dvd_of_pow_eq_one := fun l hl ↦ by
        rw [← map_nsmul_eq_pow, he.zmod_char_eq_one_iff n, nsmul_eq_mul, mul_one] at hl
        exact (ZMod.natCast_eq_zero_iff l n).1 hl }
  exact hroot.neZero'.out

/-- A nontrivial additive character of a finite field sums to `-1` over the units, even after
multiplication by a fixed unit. This is the punctured form of `AddChar.sum_eq_zero_of_ne_one`. -/
theorem sum_units_mul_eq_neg_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {S : Type*} [CommRing S] [IsDomain S] (ψ : AddChar F S) (hψ : ψ ≠ 1) (c : Fˣ) :
    ∑ d : Fˣ, ψ ((c : F) * (d : F)) = -1 := by
  -- the full sum over `F` vanishes, `ψ (c * ·)` being a nontrivial additive character
  have hsum : ∑ x : F, ψ ((c : F) * x) = 0 := by
    simpa [AddChar.mulShift_apply] using
      AddChar.sum_eq_zero_of_ne_one ((AddChar.IsPrimitive.of_ne_one hψ) c.ne_zero)
  -- split off the term at `0`, which is `ψ 0 = 1`, and reindex the nonzero terms by `Fˣ`
  rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, mul_zero, AddChar.map_zero_eq_one,
    ← Fintype.sum_equiv unitsEquivNeZero (fun d : Fˣ ↦ ψ ((c : F) * (d : F))) _
      fun d ↦ by rw [unitsEquivNeZero_apply_coe]] at hsum
  exact eq_neg_of_add_eq_zero_right hsum

end AddChar
