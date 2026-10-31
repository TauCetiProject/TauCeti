/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Ostrowski
public import TauCeti.NumberTheory.NumberField.FinitePlace
import TauCeti.Analysis.AbsoluteValue.Equivalence
import Mathlib.RingTheory.Ideal.Int

/-!
# Finite places of the rational numbers

Every finite place of `ℚ` is exactly a `p`-adic absolute value, and every prime gives such a
place. The equality preserves normalization, not just equivalence of absolute values. This is
needed to translate products over finite places into the products of `padicNorm` occurring in
Ridout's theorem.

Ostrowski's theorem supplies equivalence with a `p`-adic absolute value. The height of `p⁻¹`
then fixes the exponent: its infinite factor is one, and only the place equivalent to the
`p`-adic absolute value contributes to its finite height. Conversely, the prime ideal `(p)`
of `ℤ`, transported to `𝓞 ℚ`, supplies the required finite place.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §6.2.
* The forward normalization argument follows Ralf Stephan's
  `DiophantineApproximation/RationalPlaces.lean` in `rwst/Subspace-Theorems`, revision
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0). The converse instead uses the
  prime ideal of `ℤ` directly.
-/

public section

open NumberField Height

namespace NumberField.FinitePlace

/-- Ostrowski's theorem at a finite place of `ℚ`, before fixing its normalization. -/
private theorem exists_prime_isEquiv_padic (v : FinitePlace ℚ) :
    ∃ (p : ℕ) (_ : Fact p.Prime), v.1.IsEquiv (Rat.AbsoluteValue.padic p) := by
  have hbdd (n : ℕ) : v.1 (n : ℚ) ≤ 1 :=
    IsNonarchimedean.apply_natCast_le_one (f := v.1) (by simp) v.1.map_one v.add_le
  have hnt : v.1.IsNontrivial := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    refine ⟨(y : ℚ), RingOfIntegers.coe_ne_zero_iff.mpr hy0, ?_⟩
    have hlt : v (y : ℚ) < 1 := by
      rw [← v.mk_maximalIdeal, mk_apply]
      exact (norm_lt_one_iff_mem ℚ v.maximalIdeal y).mpr hy
    exact hlt.ne
  obtain ⟨p, ⟨hp, heq⟩, -⟩ := Rat.AbsoluteValue.equiv_padic_of_bounded hnt hbdd
  exact ⟨p, hp, heq⟩

/-- Every finite place of `ℚ` is a `p`-adic absolute value with its usual normalization,
not merely a positive power of one. -/
theorem exists_prime_padic_eq (v : FinitePlace ℚ) :
    ∃ (p : ℕ) (_ : Fact p.Prime), v.1 = Rat.AbsoluteValue.padic p := by
  obtain ⟨p, hp, hv⟩ := exists_prime_isEquiv_padic v
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hother (w : FinitePlace ℚ) (hwv : w ≠ v) : max (w ((p : ℚ)⁻¹)) 1 = 1 := by
    obtain ⟨q, hq, hw⟩ := exists_prime_isEquiv_padic w
    have hqp : q ≠ p := by
      rintro rfl
      exact hwv (eq_iff_isEquiv.mpr (hw.trans hv.symm))
    have hwp : w.1 (p : ℚ) = 1 := by
      apply hw.eq_one_iff.mpr
      rw [Rat.AbsoluteValue.padic_eq_padicNorm,
        (padicNorm.nat_eq_one_iff p).mpr (fun h ↦
          hqp ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp h))]
      norm_num
    simp only [coe_apply, map_inv₀, hwp, inv_one, max_self]
  have hheight : mulHeight₁ ((p : ℚ)⁻¹) = (p : ℝ) := by
    rw [mulHeight₁_inv, Rat.mulHeight₁_natCast]
  have harch : (∏ u : InfinitePlace ℚ, max (u ((p : ℚ)⁻¹)) 1 ^ u.mult) = 1 := by
    apply Finset.prod_eq_one
    intro u _
    have hpq : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    have hle : u ((p : ℚ)⁻¹) ≤ 1 := by
      rw [Rat.infinitePlace_apply, abs_of_nonneg (by positivity)]
      exact_mod_cast inv_le_one_of_one_le₀ hpq
    rw [max_eq_right hle, one_pow]
  rw [NumberField.mulHeight₁_eq, harch, one_mul, finprod_eq_single _ v hother] at hheight
  have hvp : v.1 ((p : ℚ)⁻¹) = p := by
    have hgt : 1 < v ((p : ℚ)⁻¹) := by
      by_contra h
      rw [max_eq_right (not_lt.mp h)] at hheight
      linarith
    rw [max_eq_left hgt.le] at hheight
    exact hheight
  refine ⟨p, hp, hv.eq_of_apply_eq (inv_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    (by rw [hvp]; exact hp1.ne') ?_⟩
  rw [hvp, map_inv₀, Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime]
  simp only [Rat.cast_inv, Rat.cast_natCast, inv_inv]

end NumberField.FinitePlace

namespace Rat

/-- Every `p`-adic absolute value of `ℚ` is the underlying absolute value of a finite place,
with equality rather than just equivalence. -/
theorem exists_finitePlace_val_eq_padic (p : ℕ) [Fact p.Prime] :
    ∃ v : FinitePlace ℚ, v.1 = AbsoluteValue.padic p := by
  let P : IsDedekindDomain.HeightOneSpectrum ℤ :=
    ⟨Ideal.span {(p : ℤ)}, inferInstance,
      Ideal.span_singleton_eq_bot.not.mpr (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)⟩
  let Q := P.comap Rat.ringOfIntegersEquiv.toRingHom Rat.ringOfIntegersEquiv.surjective
  have hpQ : (p : 𝓞 ℚ) ∈ Q.asIdeal := by
    exact Ideal.subset_span (by simp)
  have hsmall : FinitePlace.mk Q (p : ℚ) < 1 := by
    rw [FinitePlace.mk_apply]
    simpa only [map_natCast] using
      (FinitePlace.norm_lt_one_iff_mem ℚ Q (p : 𝓞 ℚ)).mpr hpQ
  obtain ⟨q, hq, heq⟩ := (FinitePlace.mk Q).exists_prime_padic_eq
  have hqp : q = p := by
    rw [FinitePlace.coe_apply, heq, AbsoluteValue.padic_eq_padicNorm] at hsmall
    have hdiv := (padicNorm.nat_lt_one_iff p).mp (by exact_mod_cast hsmall)
    exact (Nat.prime_dvd_prime_iff_eq hq.out Fact.out).mp hdiv
  exact ⟨FinitePlace.mk Q, hqp ▸ heq⟩

/-- At the prime `2`, the finite place takes the values `1/2` at `2` and `2` at `1/2`.
In particular, the dictionary uses neither the reciprocal normalization nor another power. -/
example : ∃ v : FinitePlace ℚ, v (2 : ℚ) = 1 / 2 ∧ v ((2 : ℚ)⁻¹) = 2 := by
  obtain ⟨v, hv⟩ := exists_finitePlace_val_eq_padic 2
  have htwo : v.1 (2 : ℚ) = 1 / 2 := by
    rw [hv, AbsoluteValue.padic_eq_padicNorm]
    have h := congrArg ((↑) : ℚ → ℝ) (padicNorm.padicNorm_p_of_prime (p := 2))
    norm_num at h ⊢
    exact h
  refine ⟨v, htwo, ?_⟩
  rw [FinitePlace.coe_apply, map_inv₀, htwo]
  norm_num

end Rat
