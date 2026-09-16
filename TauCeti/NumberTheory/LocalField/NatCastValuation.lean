/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation

/-!
# The normalized valuation of a natural number in a local field

Let `K` be a nonarchimedean local field. The image of a natural number `n` under the canonical
map `ℕ → K` lies in the ring of integers `𝒪[K]`, so its normalized valuation is a natural
number as soon as it is defined, that is as soon as `(n : K) ≠ 0`. This file introduces that
natural number,

`natCastValuation K n hn : ℕ`,

and its basic API.

It is the quantity that measures how far `n` is from being invertible in `𝒪[K]`: it vanishes
exactly when `(n : 𝒪[K])` is a unit, equivalently when the residue characteristic of `K` does
not divide `n`. In particular it vanishes identically when `K` has positive characteristic, so
it carries information only in mixed characteristic; there its value at the residue
characteristic is the absolute ramification index of `K`.

## Main definitions

* `TauCeti.natCastValuation`: the normalized valuation of the image of a natural number in a
  nonarchimedean local field, as a natural number.

## Main results

* `TauCeti.normalizedValuation_natCast`: the characteristic equation, which also records that
  the value is nonnegative.
* `TauCeti.natCastValuation_eq_zero_iff`: the vanishing criterion, in terms of invertibility in
  `𝒪[K]`.
* `TauCeti.natCastValuation_eq_zero_iff_not_dvd`: the vanishing criterion read off the residue
  characteristic.
* `TauCeti.natCastValuation_eq_zero_of_ringChar_ne_zero`: in equal characteristic the invariant
  is identically zero.
* `TauCeti.normalizedAbsoluteValue_natCast`: the normalized absolute value of `n` is
  `q ^ (-natCastValuation K n hn)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §1.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

open scoped NNRat WithZero

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- The declaration sequence follows the human-authored specification in
-- `TauCetiRoadmap/LocalFieldsRamification/Suggested.lean`.
variable (K) in
/-- The normalized valuation `v_K((n : K))` of the image of a natural number `n` in a
nonarchimedean local field `K`, as a natural number. The proof `hn` that the image is nonzero
is part of the input: in positive characteristic the image can vanish, and no junk value is
assigned there. -/
def natCastValuation (n : ℕ) (hn : (n : K) ≠ 0) : ℕ :=
  (Multiplicative.toAdd (normalizedValuation K (Units.mk0 (n : K) hn))).toNat

variable (K) in
/-- The characteristic equation of `natCastValuation`: it decodes the normalized valuation of
`(n : K)`. The right-hand side expresses the valuation as the image of a natural number, so the
equation also records that the image of `n` lies in `𝒪[K]`. -/
@[simp]
theorem normalizedValuation_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    normalizedValuation K (Units.mk0 (n : K) hn)
      = Multiplicative.ofAdd (natCastValuation K n hn : ℤ) := by
  have h : (0 : ℤ) ≤ Multiplicative.toAdd (normalizedValuation K (Units.mk0 (n : K) hn)) :=
    (mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 (n : K) hn)).mp
      (by simp)
  rw [natCastValuation, Int.toNat_of_nonneg h, ofAdd_toAdd]

variable (K) in
/-- The zero-preserving form of the characteristic equation of `natCastValuation`. -/
@[simp]
theorem normalizedValuationWithZero_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    normalizedValuationWithZero K (n : K) = WithZero.exp (natCastValuation K n hn : ℤ) := by
  have h := normalizedValuationWithZero_coe (Units.mk0 (n : K) hn)
  rwa [Units.val_mk0, normalizedValuation_natCast K n hn,
    ← WithZero.exp_eq_coe_ofAdd] at h

variable (K) in
/-- The vanishing criterion: the normalized valuation of `n` is zero exactly when `n` is
invertible in the ring of integers. -/
@[simp]
theorem natCastValuation_eq_zero_iff (n : ℕ) (hn : (n : K) ≠ 0) :
    natCastValuation K n hn = 0 ↔ IsUnit (n : 𝒪[K]) := by
  have hcast : ((n : 𝒪[K]) : K) = (n : K) := by push_cast; rfl
  rw [isUnit_iff_normalizedValuationWithZero_eq_one, hcast,
    normalizedValuationWithZero_natCast K n hn, ← WithZero.exp_zero, WithZero.exp_inj,
    Nat.cast_eq_zero]

variable (K) in
/-- If `n` is invertible in the ring of integers then its normalized valuation vanishes. -/
theorem natCastValuation_eq_zero_of_isUnit {n : ℕ} (hn : (n : K) ≠ 0)
    (hn' : IsUnit (n : 𝒪[K])) : natCastValuation K n hn = 0 :=
  (natCastValuation_eq_zero_iff K n hn).mpr hn'

variable (K) in
/-- The vanishing criterion read off the residue field: the normalized valuation of `n` is zero
exactly when the residue characteristic of `K` does not divide `n`. -/
theorem natCastValuation_eq_zero_iff_not_dvd (n : ℕ) (hn : (n : K) ≠ 0) :
    natCastValuation K n hn = 0 ↔ ¬ ringChar 𝓀[K] ∣ n := by
  rw [natCastValuation_eq_zero_iff, ← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast,
    ne_eq, ← ringChar.spec]

variable (K) in
/-- In equal characteristic the normalized valuation of a nonzero natural-number cast always
vanishes: a natural number whose image in `K` is nonzero is prime to the characteristic, hence
invertible in `𝒪[K]`. The invariant therefore carries information only in mixed characteristic,
which is why the absolute ramification index is defined only there. -/
theorem natCastValuation_eq_zero_of_ringChar_ne_zero (hK : ringChar K ≠ 0) (n : ℕ)
    (hn : (n : K) ≠ 0) : natCastValuation K n hn = 0 := by
  have hp : (ringChar K).Prime := CharP.char_prime_of_ne_zero K hK
  have hcop : IsCoprime ((ringChar K : ℕ) : 𝒪[K]) ((n : ℕ) : 𝒪[K]) := by
    simpa using (Nat.isCoprime_iff_coprime.mpr
      (hp.coprime_iff_not_dvd.mpr fun h ↦ hn ((ringChar.spec K n).mpr h))).map
        (Int.castRingHom 𝒪[K])
  have h0 : ((ringChar K : ℕ) : 𝒪[K]) = 0 :=
    Subtype.ext (by push_cast; exact ringChar.Nat.cast_ringChar (R := K))
  rw [h0] at hcop
  exact (natCastValuation_eq_zero_iff K n hn).mpr (isCoprime_zero_left.mp hcop)

variable (K) in
/-- The normalized valuation of `1` vanishes. -/
@[simp]
theorem natCastValuation_one :
    natCastValuation K 1 (by simpa only [Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)) = 0 := by
  have h1 : ((1 : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)
  exact (natCastValuation_eq_zero_iff K 1 h1).mpr (by simp)

variable (K) in
/-- The normalized valuation of a natural number is additive in it. -/
@[simp]
theorem natCastValuation_mul {m n : ℕ} (hm : (m : K) ≠ 0) (hn : (n : K) ≠ 0) :
    natCastValuation K (m * n) (by simpa only [Nat.cast_mul] using mul_ne_zero hm hn) =
      natCastValuation K m hm + natCastValuation K n hn := by
  have hmn : ((m * n : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_mul] using mul_ne_zero hm hn
  have h : normalizedValuationWithZero K ((m * n : ℕ) : K)
      = normalizedValuationWithZero K (m : K) * normalizedValuationWithZero K (n : K) := by
    push_cast
    exact map_mul _ _ _
  rw [normalizedValuationWithZero_natCast K _ hmn, normalizedValuationWithZero_natCast K m hm,
    normalizedValuationWithZero_natCast K n hn, ← WithZero.exp_add, WithZero.exp_inj] at h
  exact_mod_cast h

variable (K) in
/-- The normalized valuation of a power of a natural number. -/
@[simp]
theorem natCastValuation_pow {n : ℕ} (k : ℕ) (hn : (n : K) ≠ 0) :
    natCastValuation K (n ^ k) (by simpa only [Nat.cast_pow] using pow_ne_zero k hn) =
      k * natCastValuation K n hn := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.zero_mul]
    exact natCastValuation_one K
  | succ k ih =>
    have hk : ((n ^ k : ℕ) : K) ≠ 0 := by
      simpa only [Nat.cast_pow] using pow_ne_zero k hn
    simpa only [pow_succ, ih, Nat.succ_mul] using natCastValuation_mul K hk hn

variable (K) in
/-- The normalized absolute value of a natural number is `q ^ (-natCastValuation K n hn)`, where
`q` is the cardinality of the residue field. -/
@[simp]
theorem normalizedAbsoluteValue_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    normalizedAbsoluteValue K (n : K)
      = ((Nat.card 𝓀[K] : ℚ≥0)⁻¹) ^ natCastValuation K n hn := by
  rw [normalizedAbsoluteValue_apply_ne_zero (n : K) hn, normalizedValuation_natCast K n hn,
    toAdd_ofAdd, zpow_neg, zpow_natCast, inv_pow]

end TauCeti
