/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Boundary
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Primes in an arithmetic progression have Dirichlet density `1 / φ(m)`

For `m ≠ 0` and `a` a unit modulo `m`, the height-one primes `𝔭` of `𝓞 ℚ` whose absolute norm
is congruent to `a` modulo `m` have Dirichlet density `1 / φ(m)`, in the ratio-normalized sense of
Mathlib's `NumberField.Set.HasDirichletDensity`.

Over `ℚ` these primes correspond to the rational primes `p ≡ a (mod m)`, so the result says how
the rational primes distribute among the invertible residue classes modulo `m`: they are
equidistributed, each of the `φ(m)` classes receiving the same share `1 / φ(m)` of the primes,
measured by Dirichlet density. This is the Dirichlet-density form of Dirichlet's theorem on primes
in arithmetic progressions.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_primesCongruent`: the primes of `𝓞 ℚ` of norm
  congruent to a unit `a` modulo `m` have Dirichlet density `1 / φ(m)`.

## References

The analytic input is Mathlib's `Mathlib.NumberTheory.LSeries.PrimesInAP`, through the von
Mangoldt function restricted to a residue class, `ArithmeticFunction.vonMangoldt.residueClass`,
and its boundary results:

* `ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one`: its L-series converges
  absolutely for `re s > 1`;
* `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux` and
  `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux`: that L-series minus
  `φ(m)⁻¹ / (s - 1)` extends continuously to `re s ≥ 1`;
* `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`: the prime powers that
  are not primes contribute an absolutely convergent series at `s = 1`.
-/

public section

open scoped NumberField nonZeroDivisors
open IsDedekindDomain Filter Asymptotics

namespace NumberField.Chebotarev

open TauCeti ArithmeticFunction

variable (m a : ℕ)

/-- At a prime `p`, the von Mangoldt coefficient of the congruence set is Mathlib's von Mangoldt
function restricted to the residue class of `a`. -/
private theorem primeVonMangoldtCoeff_rat_prime {p : ℕ} (hp : p.Prime) :
    primeVonMangoldtCoeff ℚ
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % m = a % m} p =
      vonMangoldt.residueClass (a : ZMod m) p := by
  obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
  rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hv
  have := primeVonMangoldtCoeff_rat_natGenerator_pow
    {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % m = a % m} v one_pos
  rw [pow_one, hv] at this
  rw [this, vonMangoldt.residueClass, Set.indicator_apply]
  simp [hv, ZMod.natCast_eq_natCast_iff', vonMangoldt_apply_prime hp]

/-- The two coefficient systems agree at the primes, and differ by at most `Λ` elsewhere. -/
private theorem abs_primeVonMangoldtCoeff_rat_sub_residueClass_le (n : ℕ) :
    |primeVonMangoldtCoeff ℚ
        {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % m = a % m} n -
      vonMangoldt.residueClass (a : ZMod m) n| ≤ if n.Prime then 0 else Λ n := by
  split_ifs with hn
  · rw [primeVonMangoldtCoeff_rat_prime m a hn, sub_self, abs_zero]
  · exact abs_sub_le_of_nonneg_of_le (primeVonMangoldtCoeff_nonneg _ n)
      (primeVonMangoldtCoeff_rat_le _ n) (vonMangoldt.residueClass_nonneg _ n)
      (vonMangoldt.residueClass_le _ n)

/-- The L-series of the difference of the two coefficient systems converges absolutely at `1`. -/
private theorem LSeriesSummable_primeVonMangoldtCoeff_rat_sub_residueClass :
    LSeriesSummable (fun n ↦ ((primeVonMangoldtCoeff ℚ
        {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % m = a % m} n -
      vonMangoldt.residueClass (a : ZMod m) n : ℝ) : ℂ)) 1 := by
  have hsum := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  refine Summable.of_norm_bounded hsum fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_one, norm_div, Complex.norm_real,
    Complex.norm_natCast, Real.norm_eq_abs]
  refine div_le_div_of_nonneg_right
    ((abs_primeVonMangoldtCoeff_rat_sub_residueClass_le m a n).trans ?_) n.cast_nonneg
  split_ifs
  · exact le_rfl
  · simp [vonMangoldt.residueClass, Subsingleton.elim _ (0 : ZMod 1)]

/-- The primes of `𝓞 ℚ` of norm congruent to `a` modulo `m` satisfy
`π_S = φ(m)⁻¹ Li + o(x / log x)`. -/
private theorem primeCount_rat_sub_mul_logIntegral_isLittleO [NeZero m] (ha : IsUnit (a : ZMod m)) :
    (fun x ↦ primeCount ℚ
        {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % m = a % m} x -
      (Nat.totient m : ℝ)⁻¹ * Real.logIntegral x) =o[atTop] fun x : ℝ ↦ x / _root_.Real.log x :=
  -- compare with Mathlib's von Mangoldt series restricted to the residue class of `a`
  primeCount_sub_mul_logIntegral_isLittleO_of_LSeriesSummable_sub
    (vonMangoldt.abscissaOfAbsConv_residueClass_le_one _)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux _)
    (fun _ hs ↦ by simpa using vonMangoldt.eqOn_LFunctionResidueClassAux ha hs)
    (by simpa using LSeriesSummable_primeVonMangoldtCoeff_rat_sub_residueClass m a)

/-- **Dirichlet's theorem on primes in arithmetic progressions, with Dirichlet density.** For
`m ≠ 0` and `a` a unit modulo `m`, the primes of `𝓞 ℚ` whose absolute norm is congruent to `a`
modulo `m` have Dirichlet density `1 / φ(m)`. -/
theorem hasDirichletDensity_primesCongruent (m a : ℕ) [NeZero m]
    (ha : IsUnit (a : ZMod m)) :
    NumberField.Set.HasDirichletDensity
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % m = a % m}
      (1 / (Nat.totient m : ℝ)) := by
  refine Set.hasDirichletDensity_of_hasNaturalDensity
    (Set.hasNaturalDensity_of_isLittleO_logIntegral ?_ ?_)
  · rw [one_div]
    exact primeCount_rat_sub_mul_logIntegral_isLittleO m a ha
  · simpa [Nat.mod_one] using
      primeCount_rat_sub_mul_logIntegral_isLittleO 1 0 (isUnit_of_subsingleton _)

end NumberField.Chebotarev
