/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.RingTheory.Algebraic.Denominator

/-!
# Clearing denominators away from prescribed primes

An element of a number field admits a denominator coprime to a natural number `m` exactly when
it is integral at every finite place whose prime ideal contains `m`. For a rational prime `p`,
every embedding into a normed division algebra over `ℚ_[p]` sends an element integral above `p`
into the closed unit ball. This allows identities for algebraic integers to be used on elements
integral above `p` by clearing denominators without changing their `p`-adic size.

The denominator criterion is also used in `New.IsIntegralAbove.exists_mul_eq` in
`lsernau/grh-lean`, `grh/src/New/Derivatives/FormalGroup/Resolution.lean` at `72fead1`.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti

/-- An element admits a denominator coprime to `m` exactly when it is integral at all finite
places whose prime ideal contains `m`. -/
theorem exists_coprime_natCast_mul_isIntegral_iff {K : Type*} [Field K] [NumberField K]
    (x : K) (m : ℕ) :
    (∃ n : ℕ, m.Coprime n ∧ IsIntegral ℤ ((n : K) * x)) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ v.asIdeal → v.valuation K x ≤ 1 := by
  constructor
  · rintro ⟨n, hn, hx⟩ v hv
    have hcop : IsCoprime (m : 𝓞 K) (n : 𝓞 K) := hn.cast
    have hnmem : (n : 𝓞 K) ∉ v.asIdeal :=
      Ideal.IsPrime.notMem_of_isCoprime_of_mem hcop hv
    have hval : v.valuation K (n : K) = 1 := by
      simpa only [map_natCast] using (v.valuation_eq_one_iff_notMem (K := K)).mpr hnmem
    let a : 𝓞 K := ⟨(n : K) * x, hx⟩
    have ha : algebraMap (𝓞 K) K a = (n : K) * x := RingOfIntegers.coe_mk hx
    simpa only [ha, map_mul, hval, one_mul] using v.valuation_le_one (K := K) a
  · intro hx
    let n := Algebra.natDenominator x
    have hn : n ≠ 0 := Algebra.natDenominator_ne_zero_of_isAlgebraic_rat (.of_finite ℚ x)
    have hnx : IsIntegral ℤ ((n : K) * x) :=
      nsmul_eq_mul n x ▸ Algebra.isIntegral_natDenominator_smul x
    refine ⟨n, ?_, hnx⟩
    -- If a prime factor of `m` divided the denominator, it could be removed.
    by_contra hcop
    obtain ⟨p, hp, hpm, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    let a : 𝓞 K := ⟨(n : K) * x, hnx⟩
    have hmul : (p : K) * ((↑(n / p) : K) * x) = algebraMap (𝓞 K) K a := by
      rw [← mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hpn]
      exact (RingOfIntegers.coe_mk hnx).symm
    have hvle (v : HeightOneSpectrum (𝓞 K)) : v.valuation K ((↑(n / p) : K) * x) ≤ 1 := by
      by_cases hv : (p : 𝓞 K) ∈ v.asIdeal
      · have hm : (m : 𝓞 K) ∈ v.asIdeal := by
          obtain ⟨k, rfl⟩ := hpm
          rw [Nat.cast_mul]
          exact v.asIdeal.mul_mem_right (k : 𝓞 K) hv
        have hd : v.valuation K (↑(n / p) : K) ≤ 1 := by
          simpa only [map_natCast] using v.valuation_le_one (K := K) ((n / p : ℕ) : 𝓞 K)
        rw [map_mul]
        exact (mul_le_mul_of_nonneg_right hd bot_le).trans (by simpa using hx v hm)
      · have hval : v.valuation K (p : K) = 1 := by
          simpa only [map_natCast] using (v.valuation_eq_one_iff_notMem (K := K)).mpr hv
        simpa only [← hmul, map_mul, hval, one_mul] using v.valuation_le_one (K := K) a
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K _ hvle
    have hdvd : n ∣ n / p := Algebra.natDenominator_dvd_iff.mpr (by
      rw [nsmul_eq_mul, ← hb]
      exact b.isIntegral_coe)
    have hnpos := Nat.pos_of_ne_zero hn
    have hdivpos := Nat.div_pos (Nat.le_of_dvd hnpos hpn) hp.pos
    exact (Nat.div_lt_self hnpos hp.one_lt).not_ge (Nat.le_of_dvd hdivpos hdvd)

end TauCeti

/-- Every embedding into a normed division algebra over `ℚ_[p]` takes an element integral at
all places above `p` into the closed unit ball. This applies to any such embedding, including one
obtained by precomposing with an automorphism of the number field. -/
theorem RingHom.norm_le_one_of_integral_above_prime {K L : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L] (σ : K →+* L) {x : K}
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v.valuation K x ≤ 1) :
    ‖σ x‖ ≤ 1 := by
  obtain ⟨n, hn, hnx⟩ := (TauCeti.exists_coprime_natCast_mul_isIntegral_iff x p).mpr hx
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have hnorm : ‖(n : L)‖ = 1 := by
    rw [TauCeti.norm_natCast_eq_norm_padic (p := p), Padic.norm_natCast_eq_one_iff]
    exact hn
  simpa only [RingHom.toIntAlgHom_apply, map_mul, map_natCast, norm_mul, hnorm, one_mul] using
    IsUltrametricDist.norm_le_one_of_isIntegral (fun y k _ ↦ norm_pow y k)
      (hnx.map σ.toIntAlgHom)
