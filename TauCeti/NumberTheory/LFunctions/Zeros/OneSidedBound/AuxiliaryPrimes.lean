/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.LogWindow
import TauCeti.NumberTheory.Multiquadratic.Quadratic.SplitProgression

/-!
# Split primes for the principal level

To find a product of two primes that is the norm of an algebraic integer in the
quadratic field, one needs more split primes than the class number. We sample primes
congruent to `1` modulo `q₂(s)²` in `[b¹⁰, b¹¹]` from disjoint logarithmic windows.
The modulus is divisible by the absolute discriminant, so each prime splits and
is the norm of a prime ideal. The logarithmic window has width `W` where
`W^6 ≤ log b ≤ W^6 + 1`.

The interval and the class-number threshold are from the construction of
`New.Parameters.IsLargeScale.exists_isAdmissibleData` in `New/Reduction/Data/Existence.lean`
of lsernau/grh-lean at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Filter Module Set
open scoped NumberField

namespace TauCeti.OneSidedBound.Parameters

/-- At large `W`, every sufficiently small power `q₂(s)²` has more split primes than the
class number of `K` between `b^10` and `b^11`, if the logarithmic prime windows of width
`W` are available. The exponent `max 7 A` accommodates the upper endpoint `11 log b`.
Each prime is supplied with the assertion that it is an ideal norm. -/
theorem eventually_exists_auxiliary_split_primes (P : Parameters) (K : Type*) [Field K]
    [NumberField K] (hK : finrank ℚ K = 2) (hdisc : (NumberField.discr K).natAbs ∣ P.q₀ * P.d)
    (A : ℕ)
    (hwin : ∀ᶠ W : ℝ in atTop, ∀ j : ℕ, 2 ≤ j → ((P.q₀ * P.d : ℕ) : ℝ) ^ j ≤ W ^ max 7 A →
      ∀ U : ℝ, W ≤ U → U ≤ W ^ max 7 A →
        ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD (P.q₀ * P.d) ^ j] ∧ Real.log p ∈ Icc U (U + W)) :
    ∀ᶠ W : ℝ in atTop, ∀ (s b : ℕ), W ^ 6 ≤ Real.log b → Real.log b ≤ W ^ 6 + 1 →
      (P.q₂ s : ℝ) ^ 2 ≤ W ^ max 7 A →
      ∃ S : Finset ℕ, NumberField.classNumber K < S.card ∧
        ∀ p ∈ S, p.Prime ∧ p ≡ 1 [MOD P.q₂ s ^ 2] ∧ p ∈ Icc (b ^ 10) (b ^ 11) ∧
          ∃ I : Ideal (𝓞 K), I.IsPrime ∧ Ideal.absNorm I = p := by
  have hdiv (s : ℕ) : (NumberField.discr K).natAbs ∣ P.q₂ s ^ 2 := by
    rw [P.q₂_def, ← pow_mul]
    exact hdisc.trans (dvd_pow_self _ (by omega))
  filter_upwards [hwin, eventually_ge_atTop (max 22 (2 * (NumberField.classNumber K + 1) : ℝ))]
    with W hwin hW s b hlo hhi hmod
  have h22 := (le_max_left _ _).trans hW
  have hn := (le_max_right _ _).trans hW
  have h1 : 1 ≤ W := by linarith
  have hW6 : W ≤ W ^ 6 := by simpa using pow_le_pow_right₀ h1 (by decide : 1 ≤ 6)
  have hfit : 10 * Real.log b + 2 * (NumberField.classNumber K + 1) * W ≤ 11 * Real.log b := by
    have hW2 : W ^ 2 ≤ W ^ 6 := pow_le_pow_right₀ h1 (by decide)
    nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ W)]
  have htop : 11 * Real.log b ≤ W ^ max 7 A := calc
    _ ≤ 22 * W ^ 6 := by linarith [hW6]
    _ ≤ W ^ 7 := by simpa [pow_succ, mul_comm] using
      mul_le_mul_of_nonneg_right h22 (pow_nonneg (by linarith : 0 ≤ W) 6)
    _ ≤ W ^ max 7 A := pow_le_pow_right₀ h1 (le_max_left _ _)
  have hq : P.q₂ s ^ 2 = (P.q₀ * P.d) ^ ((s + 6) * 2) := by rw [P.q₂_def, pow_mul]
  obtain ⟨S, hS, hmem⟩ := exists_finset_primes_modEq_log_mem_Icc
    (n := NumberField.classNumber K + 1) (q := P.q₂ s ^ 2)
    (by linarith : 0 < W) (by simpa using hfit) fun U hU hUW ↦ by
      rw [hq]
      refine hwin _ (by omega) ?_ U (by linarith) (by linarith)
      rwa [← Nat.cast_pow, ← hq, Nat.cast_pow]
  have hb : 0 < (b : ℝ) := zero_lt_one.trans
    ((Real.log_pos_iff (Nat.cast_nonneg b)).mp (by linarith))
  refine ⟨S, by omega, fun p hpS ↦ ?_⟩
  obtain ⟨hp, hpmod, hpL, hpR⟩ := hmem p hpS
  have hpos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  refine ⟨hp, hpmod, ⟨?_, ?_⟩, ?_⟩
  · exact_mod_cast (Real.log_le_log_iff (pow_pos hb 10) hpos).mp (by simpa [Real.log_pow] using hpL)
  · exact_mod_cast (Real.log_le_log_iff hpos (pow_pos hb 11)).mp (by simpa [Real.log_pow] using hpR)
  obtain ⟨I, hI, -, hN⟩ := NumberField.exists_isPrime_and_absNorm_eq_of_modEq_one_discr
    hK hp (hpmod.of_dvd (hdiv s))
  exact ⟨I, hI, hN⟩

end TauCeti.OneSidedBound.Parameters
