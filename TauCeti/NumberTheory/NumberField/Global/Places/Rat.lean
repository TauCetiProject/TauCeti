/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Ostrowski
public import TauCeti.NumberTheory.NumberField.SUnits.Rat.Basic
import TauCeti.Analysis.AbsoluteValue.Equivalence

/-!
# Finite places of the rational numbers

Every finite place of `ℚ` is exactly a `p`-adic absolute value, and every prime gives such a
place. The equalities use Mathlib's `Rat.HeightOneSpectrum.primesEquiv` to identify the prime
of a place and preserve normalization, not just equivalence of absolute values. This is
needed to translate products over finite places into the products of `padicNorm` occurring in
Ridout's theorem.

Ostrowski's theorem supplies equivalence with a `p`-adic absolute value. The known value at
the rational prime generating the place's maximal ideal then fixes the prime and exponent.
The inverse dictionary uses `primesEquiv.symm` to supply the corresponding finite place.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §6.2.
* The original height-based normalization argument followed Ralf Stephan's
  `DiophantineApproximation/RationalPlaces.lean` in `rwst/Subspace-Theorems`, revision
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0). Here the existing local-value
  formulas replace that height computation.
-/

public section

open NumberField Rat.HeightOneSpectrum

namespace NumberField.FinitePlace

/-- A finite place of `ℚ` is the usual `p`-adic absolute value at its canonical prime under
`Rat.HeightOneSpectrum.primesEquiv`, not merely a positive power of that absolute value. -/
theorem val_eq_padic (v : FinitePlace ℚ) :
    letI : Fact (primesEquiv v.maximalIdeal : ℕ).Prime := ⟨(primesEquiv v.maximalIdeal).property⟩
    v.1 = Rat.AbsoluteValue.padic (primesEquiv v.maximalIdeal) := by
  let p : Nat.Primes := primesEquiv v.maximalIdeal
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  -- Mathlib defines the value of `primesEquiv` to be `natGenerator`.
  have hpval : (p : ℕ) = natGenerator v.maximalIdeal := rfl
  have hvp : v.1 (p : ℚ) = (p : ℝ)⁻¹ := by
    rw [← coe_apply, ← v.mk_maximalIdeal, hpval]
    exact finitePlace_mk_natGenerator v.maximalIdeal
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hsmall : v.1 (p : ℚ) < 1 := by
    rw [hvp]
    exact inv_lt_one_of_one_lt₀ hp1
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hnt : v.1.IsNontrivial := ⟨(p : ℚ), hp0, hsmall.ne⟩
  have hbdd (n : ℕ) : v.1 (n : ℚ) ≤ 1 :=
    IsNonarchimedean.apply_natCast_le_one (f := v.1) (by simp) v.1.map_one v.add_le
  obtain ⟨q, ⟨hq, hv⟩, -⟩ := Rat.AbsoluteValue.equiv_padic_of_bounded hnt hbdd
  have hqp : q = (p : ℕ) := by
    have hlt := hv.lt_one_iff.mp hsmall
    rw [Rat.AbsoluteValue.padic_eq_padicNorm] at hlt
    have hdiv := (padicNorm.nat_lt_one_iff (p : ℕ)).mp (by exact_mod_cast hlt)
    exact (Nat.prime_dvd_prime_iff_eq hq.out p.property).mp hdiv
  subst q
  apply hv.eq_of_apply_eq hp0 hsmall.ne
  rw [hvp, Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- A finite place of `ℚ`, evaluated at a rational number, is `padicNorm` at its canonical
prime under `Rat.HeightOneSpectrum.primesEquiv`. -/
theorem apply_eq_padicNorm (v : FinitePlace ℚ) (x : ℚ) :
    v x = (padicNorm (primesEquiv v.maximalIdeal) x : ℝ) := by
  let : Fact (primesEquiv v.maximalIdeal : ℕ).Prime :=
    ⟨(primesEquiv v.maximalIdeal).property⟩
  rw [coe_apply, v.val_eq_padic, Rat.AbsoluteValue.padic_eq_padicNorm]

end NumberField.FinitePlace

namespace Nat.Primes

/-- The finite place corresponding to a prime under `Rat.HeightOneSpectrum.primesEquiv.symm`
has exactly the usual `p`-adic absolute value. -/
theorem finitePlace_mk_val_eq_padic (p : Nat.Primes) :
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).1 = Rat.AbsoluteValue.padic p := by
  simpa only [FinitePlace.maximalIdeal_mk, Equiv.apply_symm_apply] using
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).val_eq_padic

/-- The finite place constructed from a prime evaluates to the usual `padicNorm`. -/
theorem finitePlace_mk_apply (p : Nat.Primes) (x : ℚ) :
    FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p) x = (padicNorm p x : ℝ) := by
  simpa only [FinitePlace.maximalIdeal_mk, Equiv.apply_symm_apply] using
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).apply_eq_padicNorm x

end Nat.Primes

/-- At the prime `2`, the finite place takes the values `1/2` at `2` and `2` at `1/2`.
In particular, the dictionary uses neither the reciprocal normalization nor another power. -/
example : ∃ v : FinitePlace ℚ, v (2 : ℚ) = 1 / 2 ∧ v ((2 : ℚ)⁻¹) = 2 := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let v := FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)
  have htwo : v (2 : ℚ) = 1 / 2 := by
    rw [Nat.Primes.finitePlace_mk_apply]
    have h := congrArg ((↑) : ℚ → ℝ) (padicNorm.padicNorm_p_of_prime (p := 2))
    norm_num at h ⊢
    exact h
  refine ⟨v, htwo, ?_⟩
  rw [map_inv₀, htwo]
  norm_num
