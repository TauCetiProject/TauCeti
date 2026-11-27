/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootDiscr

/-!
# A lower bound for the root discriminant at prime-sum scales

A number field containing a primitive root of order `q₁(s)` contains the dyadic
cyclotomic field of order `2 ^ (s + 1)`. Its root discriminant therefore grows at least
as fast as `2 ^ s`, which is at least `x ^ 11` at the ranks used in the prime sums.
This gives the discriminant lower bound without estimating a generator of the different
at the infinite places. For the discriminant bound at these scales, see
`New.Data.rootDisc_mem_Icc` in `grh/src/New/Derivatives/Field/ChosenPlaces.lean` of
lsernau/grh-lean, revision `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- At prime-sum scale `x`, the dyadic subfield alone forces the root discriminant
of the host to be at least `x ^ 11`. -/
theorem pow_le_rootDiscr (P : Parameters) {E : Type*} [Field E] [NumberField E]
    {s x m : ℕ} {ζ : E} (hζ : IsPrimitiveRoot ζ (P.q₁ s))
    (hm : x ≤ m ^ 2) (hs : m ^ 22 ≤ 2 ^ s) :
    (x : ℝ) ^ 11 ≤ NumberField.rootDiscr E := by
  obtain ⟨a, ha⟩ := P.two_pow_succ_dvd_q₁ s
  have hζ' : IsPrimitiveRoot (ζ ^ a) (2 ^ (s + 1)) :=
    hζ.pow (P.q₁_pos s) (ha.trans (Nat.mul_comm _ _))
  have hdisc : (2 : ℝ) ^ s ≤ NumberField.rootDiscr E := by
    have hexp : (s : ℝ) + 1 - ((2 : ℝ) - 1)⁻¹ = s := by norm_num
    simpa only [Nat.cast_ofNat, hexp, Real.rpow_natCast] using hζ'.rpow_le_rootDiscr Nat.prime_two
  have hx : x ^ 11 ≤ 2 ^ s := calc
    x ^ 11 ≤ (m ^ 2) ^ 11 := Nat.pow_le_pow_left hm _
    _ ≤ 2 ^ s := by rwa [← pow_mul]
  exact (by exact_mod_cast hx : (x : ℝ) ^ 11 ≤ 2 ^ s).trans hdisc

end TauCeti.OneSidedBound.Parameters
