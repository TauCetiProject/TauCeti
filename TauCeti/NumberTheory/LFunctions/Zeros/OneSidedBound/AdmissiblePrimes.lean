/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.ModularForms.ThetaLift.Level
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.NumberTheory.DirichletCharacter.LFunction.PowerLevelWindows
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.PrincipalLevel

/-!
# Choice of auxiliary and level primes at large cutoffs

The two auxiliary primes and the level prime all come from the same supply of primes in
logarithmic windows. The auxiliary pair determines the lower endpoint for the level prime;
uniformity in the endpoint allows the level prime to be selected after the pair. The two
integral norm witnesses live in the quadratic field and the CM field, respectively.

This is the prime selection in `New.Parameters.IsLargeScale.exists_isAdmissibleData` in
[`New/Reduction/Data/Existence.lean`][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Data/Existence.lean
-/

public section

open Filter NumberField NumberField.IsCMField Real Set
open scoped NumberField

namespace TauCeti.OneSidedBound.Parameters

/-- At sufficiently large `x`, the square of the search modulus `q₂ s` is a power of the
fixed base `q₀ d` and is polynomially bounded in `W = x ^ (ε / 6)`. Allow another factor
`W ^ 7` in the upper endpoint to cover the two prime searches. -/
private theorem eventually_level_prime_windows (P : Parameters) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ᶠ x : ℝ in atTop, 1 ≤ x ^ (ε / 6) ∧ x ≤ (x ^ (ε / 6)) ^ B ∧
      ∀ s : ℕ, (P.q₂ s : ℝ) ≤ x ^ (33 * (P.q₀ * P.d)) →
        ∀ U ∈ Icc (x ^ (ε / 6)) ((x ^ (ε / 6)) ^ (B + 7)),
          ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD P.q₂ s ^ 2] ∧
            log (p : ℝ) ∈ Icc U (U + x ^ (ε / 6)) := by
  have hε₆ : 0 < ε / 6 := by positivity
  let c : ℕ := 33 * (P.q₀ * P.d)
  obtain ⟨B, hB⟩ := exists_nat_ge ((max 1 (2 * (c : ℝ))) / (ε / 6))
  have hB' := (div_le_iff₀ hε₆).mp hB
  have hB₁ : 1 ≤ ε / 6 * B := (le_max_left _ _).trans (by simpa only [mul_comm] using hB')
  have hB₂ : (2 * c : ℝ) ≤ ε / 6 * B :=
    (le_max_right _ _).trans (by simpa only [mul_comm] using hB')
  have : NeZero (P.q₀ * P.d) := ⟨(Nat.mul_pos P.q₀_pos P.prime_d.pos).ne'⟩
  have hwin := (tendsto_rpow_atTop hε₆).eventually
    (LSeries.eventually_exists_prime_log_mem_Icc_pow_level (P.q₀ * P.d) (B + 7))
  refine ⟨B, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), hwin] with x hx hwin
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hW : 1 ≤ x ^ (ε / 6) := one_le_rpow hx hε₆.le
  have hpow : (x ^ (ε / 6)) ^ B = x ^ (ε / 6 * B) := by
    rw [rpow_mul hx₀, rpow_natCast]
  refine ⟨hW, ?_, fun s hs U hU ↦ ?_⟩
  · rw [hpow]
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx hB₁
  · have hlevel : P.q₂ s ^ 2 = (P.q₀ * P.d) ^ ((s + 6) * 2) := by
      rw [P.q₂_def, pow_mul]
    have hq : (↑((P.q₀ * P.d) ^ ((s + 6) * 2)) : ℝ) ≤ (x ^ (ε / 6)) ^ (B + 7) := by
      rw [← hlevel, Nat.cast_pow]
      calc
        (P.q₂ s : ℝ) ^ 2 ≤ (x ^ c) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2
        _ = x ^ (2 * (c : ℝ)) := by
          rw [← pow_mul, ← rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_comm]
        _ ≤ (x ^ (ε / 6)) ^ B := hpow ▸ rpow_le_rpow_of_exponent_le hx hB₂
        _ ≤ (x ^ (ε / 6)) ^ (B + 7) := pow_le_pow_right₀ hW (Nat.le_add_right _ _)
    obtain ⟨p, hp, hpa, hpI⟩ := hwin ((s + 6) * 2) hq hU 1
    rw [hlevel]
    exact ⟨p, hp, (ZMod.natCast_eq_natCast_iff p 1 _).mp (by simpa using hpa), hpI⟩

/-- Choose the two auxiliary primes and the level prime at the same large cutoff. The scale
`log b` is bracketed by `x ^ ε` and `x ^ ε + 1`, expressed here as powers of `W = x ^ (ε / 6)`.
The input `w` is the mean log weight, `D` is the root discriminant, and `m` is the chain length.
The threshold depends only on `P`, the auxiliary field and `ε`, not on the tower position or
on the eventual choices of weights and primes. -/
theorem eventually_exists_admissible_level_primes (P : Parameters) (K : Type*)
    [Field K] [NumberField K] [IsCMField K] [Algebra.IsQuadraticExtension ℚ K]
    (hK : (discr K).natAbs ∣ P.d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (s b m : ℕ) {w D : ℝ},
      (P.q₂ s : ℝ) ≤ x ^ (33 * (P.q₀ * P.d)) →
      let W := x ^ (ε / 6)
      let L := log (b : ℝ)
      L ∈ Icc (W ^ 6) (W ^ 6 + 1) → 2 ≤ m → (m : ℝ) ≤ 2 * x →
      w ∈ Icc 0 L → D ∈ Icc 1 (b : ℝ) →
      ∀ {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]
        {i : E}, IsPrimitiveRoot i 4 →
      ∃ p₀ p₁ N : ℕ, p₀ ≠ p₁ ∧ p₀.Prime ∧ p₁.Prime ∧ N.Prime ∧
        p₀ ≡ 1 [MOD P.q₂ s ^ 2] ∧ p₁ ≡ 1 [MOD P.q₂ s ^ 2] ∧ N ≡ 1 [MOD P.q₂ s ^ 2] ∧
        p₀ ∈ Icc (b ^ 10) (b ^ 11) ∧ p₁ ∈ Icc (b ^ 10) (b ^ 11) ∧
        (∃ z : 𝓞 K, z * ringOfIntegersComplexConj K z = (p₀ : 𝓞 K) * (p₁ : 𝓞 K)) ∧
        (let U := ThetaLift.logLevelMin m w ((p₀ : ℝ) * p₁) D L
         log (N : ℝ) ∈ Icc U (U + √L)) ∧
        ∃ z : 𝓞 E, z * ringOfIntegersComplexConj E z = N := by
  obtain ⟨B, hwin⟩ := P.eventually_level_prime_windows hε
  have htop := tendsto_rpow_atTop (show 0 < ε / 6 by positivity)
  filter_upwards [hwin, htop.eventually_ge_atTop (max 100 (log (2 * π))),
    htop.eventually (eventually_exists_auxiliary_prime_pair_norm K)] with x hx hWlarge hpair
  intro s b m w D hq W L hL hm hmx hw hD E _ _ _ _ i hi
  obtain ⟨hW, hx, hwin⟩ := hx
  have hWL : W ≤ L := (le_self_pow₀ hW (by decide : 6 ≠ 0)).trans hL.1
  have hL₀ : 0 ≤ L := zero_le_one.trans (hW.trans hWL)
  have hwidth : W ≤ √L := (le_sqrt (zero_le_one.trans hW) hL₀).mpr
    ((pow_le_pow_right₀ hW (by decide : 2 ≤ 6)).trans hL.1)
  have hB₇ : W ^ 7 ≤ W ^ (B + 7) := pow_le_pow_right₀ hW (Nat.le_add_left _ _)
  have h₇ : 48 * L ≤ W ^ 7 := by
    have h₆ : 1 ≤ W ^ 6 := one_le_pow₀ hW
    have hW₁ : 100 ≤ W := (le_max_left _ _).trans hWlarge
    rw [pow_succ]
    linarith only [h₆, hL.2,
      mul_le_mul_of_nonneg_left (by linarith : 96 ≤ W) (by positivity : 0 ≤ W ^ 6)]
  have hbase : P.q₀ * P.d ∣ P.q₂ s ^ 2 := by
    rw [P.q₂_def, ← pow_mul]
    exact dvd_pow_self _ (by omega)
  have hd : P.d ∣ P.q₂ s ^ 2 := (dvd_mul_left _ _).trans hbase
  obtain ⟨p₀, p₁, hne, hp₀, hp₁, hc₀, hc₁, hI₀, hI₁, hz⟩ :=
    hpair b (P.q₂ s ^ 2) hL.1 (by linarith) (hK.trans hd)
      (fun U hU ↦ hwin s hq U ⟨hU.1, hU.2.trans hB₇⟩)
  have hb : 0 < (b : ℝ) := zero_lt_one.trans_le (hD.1.trans hD.2)
  have he : exp L = (b : ℝ) := exp_log hb
  have hepow (n : ℕ) : exp ((n : ℝ) * L) = (b : ℝ) ^ n := by rw [exp_natCast_mul, he]
  have hM : (p₀ : ℝ) * p₁ ∈ Icc (exp (20 * L)) (exp (22 * L)) := by
    rw [show exp (20 * L) = (b : ℝ) ^ 20 by exact_mod_cast hepow 20,
      show exp (22 * L) = (b : ℝ) ^ 22 by exact_mod_cast hepow 22]
    have hlo := Nat.mul_le_mul hI₀.1 hI₁.1
    have hhi := Nat.mul_le_mul hI₀.2 hI₁.2
    rw [← pow_add] at hlo hhi
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hU := ThetaLift.logLevelMin_mem_Icc hm ((le_max_right _ _).trans (hWlarge.trans hWL)) hw hM
    (by simpa only [he] using hD)
  have hUtop : 24 * (m : ℝ) * L ≤ W ^ (B + 7) := calc
    24 * (m : ℝ) * L ≤ x * (48 * L) := by nlinarith [mul_le_mul_of_nonneg_right hmx hL₀]
    _ ≤ W ^ B * W ^ 7 := mul_le_mul hx h₇ (by positivity) (by positivity)
    _ = W ^ (B + 7) := by rw [pow_add]
  have hUbot : W ≤ (m : ℝ) * L := hWL.trans
    (le_mul_of_one_le_left hL₀ (by exact_mod_cast Nat.le_of_succ_le hm))
  have hfour : 4 ∣ P.q₂ s ^ 2 :=
    (by decide : 4 ∣ 18480).trans ((P.dvd_q₀.mul_right P.d).trans hbase)
  obtain ⟨N, hN, hcN, hIN, hzN⟩ := ThetaLift.exists_prime_log_mem_Icc_mul_complexConj_eq
    hi (by decide) dvd_rfl hfour ⟨hUbot.trans hU.1, hU.2.trans hUtop⟩ hwidth (hwin s hq)
  exact ⟨p₀, p₁, N, hne, hp₀, hp₁, hN, hc₀, hc₁, hcN, hI₀, hI₁, hz, hIN, hzN⟩

end TauCeti.OneSidedBound.Parameters
