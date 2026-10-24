/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Ramification
import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.SplitPrime
import TauCeti.NumberTheory.NumberField.Quadratic.Splitting

/-!
# The quadratic character of a quadratic field decides how primes decompose

The discriminant `D` of a quadratic number field `K` is a fundamental discriminant
(`TauCeti.Multiquadratic.isFundamentalDiscr_discr`), so it carries the primitive quadratic
Dirichlet character `χ_D = fundamentalDiscriminantChar D` of conductor `|D|`. This file proves the
decomposition law of `K` in terms of `χ_D`. For every rational prime `p`:

* `χ_D(p) = 0` exactly when `p` ramifies in `K`;
* `χ_D(p) = 1` exactly when `p` splits in `K`, that is, there are two primes of `𝓞 K` above `p`;
* `χ_D(p) = -1` exactly when `p` is inert in `K`: it is unramified and there is a single prime of
  `𝓞 K` above `p`.

The prime `2` is included. Write `K = ℚ(√d)` with `d` squarefree. At an odd prime the splitting law
in genus-character form (`ncard_primesOver_eq_finrank_iff_genusCharFun_eq_one`) transports to
`χ_D`. At `2` the value is `χ₈(D)` (`fundamentalDiscriminantChar_two`), and when `2` is
unramified `D = d ≡ 1 (mod 4)`, so the splitting law at `2`
(`NumberField.ncard_primesOver_two_of_mod_four_eq_one`) applies. The ramified
primes are those dividing `D`, where `χ_D` vanishes.

These values determine the local factors in the factorization `ζ_K(s) = ζ(s) L(s, χ_D)` of the
Dedekind zeta function of `K`.

## Main results

* `TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_zero_iff`: `χ_D(p) = 0` iff `p`
  ramifies.
* `TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_one_iff`: `χ_D(p) = 1` iff `p`
  splits.
* `TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_neg_one_iff`: `χ_D(p) = -1` iff
  `p` is inert.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.B.
-/

public section

open Polynomial Ideal Module
open scoped NumberField
open NumberField (ramifiedPrimes)

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K]

/-- **`χ_D` vanishes exactly at the ramified primes.** For a quadratic field `K` with
discriminant `D`, the character `χ_D` vanishes at a prime `p` iff `p` ramifies in `K`. -/
theorem fundamentalDiscriminantChar_discr_eq_zero_iff (hK : finrank ℚ K = 2) (p : ℕ)
    [hp : Fact p.Prime] :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = 0 ↔
      p ∈ ramifiedPrimes K := by
  rw [← Int.cast_natCast, DirichletCharacter.apply_eq_zero_iff, Int.natCast_natAbs,
    IsCoprime.abs_right_iff, (Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd, not_not,
    NumberField.mem_ramifiedPrimes_iff_dvd_discr hp.out]

/-- At an unramified prime, `χ_D` is `1` with two primes above `p`, or `-1` with one. -/
private theorem fundamentalDiscriminantChar_discr_of_notMem_ramifiedPrimes
    (hK : finrank ℚ K = 2) (p : ℕ) [hp : Fact p.Prime] (hram : p ∉ ramifiedPrimes K) :
    (fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = 1 ∧
        (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2) ∨
      (fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = -1 ∧
        (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1) := by
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := NumberField.exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  have hD := discr_eq_fundamentalDiscriminant hmin hgen hsf
  have hndvd : ¬ (p : ℤ) ∣ fundamentalDiscriminant d := by
    rwa [NumberField.mem_ramifiedPrimes_iff_dvd_discr hp.out, hD] at hram
  by_cases hp2 : p = 2
  · -- At `2`: the field is unramified at `2`, so `D = d ≡ 1 (mod 4)`, and `χ_D(2) = χ₈(d)`.
    subst hp2
    have hd4 : d % 4 = 1 :=
      (two_not_dvd_fundamentalDiscriminant_iff_mod_four_eq_one d).mp (by exact_mod_cast hndvd)
    have h8 : ZMod.χ₈ (NumberField.discr K : ZMod 8) = if d % 8 = 1 then 1 else -1 := by
      rw [hD, fundamentalDiscriminant_of_mod_four_eq_one hd4, ZMod.χ₈_int_eq_if_mod_eight]
      split_ifs <;> omega
    simp only [Nat.cast_ofNat]
    rw [fundamentalDiscriminantChar_two, h8,
      NumberField.ncard_primesOver_two_of_mod_four_eq_one hmin hgen hd4]
    split_ifs <;> simp
  · -- At an odd prime: the genus-character splitting law, transported to `χ_D`.
    obtain ⟨s, hs, _, hprod⟩ := (isFundamentalDiscr_discr hK).exists_finset_primeDiscriminant
    have hsplit := ncard_primesOver_eq_finrank_iff_genusCharFun_eq_one hs (hprod.trans hD) hmin
      hgen hsf hp2
    rw [hK, ← fundamentalDiscriminantChar_apply_int (isFundamentalDiscr_discr hK) hs hprod,
      Int.cast_natCast] at hsplit
    have h0 :
        fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p ≠ 0 :=
      mt (fundamentalDiscriminantChar_discr_eq_zero_iff hK p).mp hram
    rcases (fundamentalDiscriminantChar_isQuadratic _ p).resolve_left h0 with h | h
    · exact Or.inl ⟨h, hsplit.mpr h⟩
    · refine Or.inr ⟨h, (NumberField.ncard_primesOver_eq_one_or_eq_two hK p).resolve_right
        fun h2 => ?_⟩
      rw [hsplit.mp h2] at h
      exact absurd h (by decide)

/-- **`χ_D(p) = 1` exactly when `p` splits.** For a quadratic field `K` with discriminant `D`,
the character `χ_D` takes the value `1` at a prime `p` iff there are two primes of `𝓞 K`
above `p`. -/
theorem fundamentalDiscriminantChar_discr_eq_one_iff (hK : finrank ℚ K = 2) (p : ℕ)
    [Fact p.Prime] :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = 1 ↔
      (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 := by
  by_cases hram : p ∈ ramifiedPrimes K
  · rw [(fundamentalDiscriminantChar_discr_eq_zero_iff hK p).mpr hram,
      NumberField.ncard_primesOver_eq_one_of_mem_ramifiedPrimes hK hram]
    decide
  · rcases fundamentalDiscriminantChar_discr_of_notMem_ramifiedPrimes hK p hram with
      ⟨h, hn⟩ | ⟨h, hn⟩ <;> rw [h, hn] <;> decide

/-- **`χ_D(p) = -1` exactly when `p` is inert.** For a quadratic field `K` with discriminant `D`,
the character `χ_D` takes the value `-1` at a prime `p` iff `p` is unramified in `K` and there is a
single prime of `𝓞 K` above `p`. -/
theorem fundamentalDiscriminantChar_discr_eq_neg_one_iff (hK : finrank ℚ K = 2) (p : ℕ)
    [Fact p.Prime] :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = -1 ↔
      p ∉ ramifiedPrimes K ∧ (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 := by
  by_cases hram : p ∈ ramifiedPrimes K
  · rw [(fundamentalDiscriminantChar_discr_eq_zero_iff hK p).mpr hram]
    simp [hram]
  · rcases fundamentalDiscriminantChar_discr_of_notMem_ramifiedPrimes hK p hram with
      ⟨h, hn⟩ | ⟨h, hn⟩ <;> simp [h, hn, hram]

end TauCeti.Multiquadratic
