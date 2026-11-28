/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Cyclotomic

/-!
# Roots of unity and the signature of the theta-lift host

The cyclotomic order of the host is a multiple of `5040`, as needed for the Weil data.
The primitive eighth root already forces the number of infinite places to be even, as
needed for trace comparison across signatures.

The parity assertion is `New.Data.f_even` in `New/Reduction/Data/Sizes.lean` of
<https://github.com/lsernau/grh-lean> at `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- The order `q₁(s)` is a multiple of `5040`. A primitive `q₁(s)`-th root therefore gives a
primitive `5040`-th root by taking the `q₁(s) / 5040`-th power. -/
theorem dvd_q₁_5040 (P : Parameters) (s : ℕ) : 5040 ∣ P.q₁ s := by
  rw [q₁_def, towerDeg_def, mul_assoc 3]
  exact (by decide : 5040 ∣ 18480 * 3).trans
    (Nat.mul_dvd_mul P.dvd_q₀ (dvd_mul_right 3 _))

/-- Every number field containing a primitive root of the host order has an even number
of infinite places, independently of the choice of the base quadratic field. -/
theorem even_card_infinitePlace (P : Parameters) {s : ℕ} {E : Type*} [Field E] [NumberField E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ (P.q₁ s)) :
    Even (Fintype.card (NumberField.InfinitePlace E)) := by
  have hdvd : 8 ∣ P.q₁ s := (by decide : 8 ∣ 5040).trans (P.dvd_q₁_5040 s)
  have h₈ := hζ.pow (P.q₁_pos s) (Nat.div_mul_cancel hdvd).symm
  rw [h₈.card_infinitePlace_eq_totient_div_two_mul_finrank (by decide)]
  have hφ : Nat.totient 8 = 4 := by
    simpa using Nat.totient_prime_pow_succ Nat.prime_two 2
  rw [hφ]
  exact even_two_mul _

end TauCeti.OneSidedBound.Parameters
