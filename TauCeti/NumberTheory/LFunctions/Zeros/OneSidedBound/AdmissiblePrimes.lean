/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.PrincipalLevel
public import TauCeti.NumberTheory.ModularForms.ThetaLift.Level

/-!
# Simultaneous choice of the three theta-lift level primes

The two primes for the principal level are chosen first, with a norm witness in the
imaginary quadratic field. Their product determines the lower endpoint for the third prime.
A single supply of logarithmic prime windows suffices for both choices. The scale threshold
depends on the quadratic field, not on the growing CM field or the progression modulus.

The choice follows `New.Parameters.IsLargeScale.exists_isAdmissibleData` in
`grh/src/New/Reduction/Data/Existence.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Data/Existence.lean
-/

public section

open Filter NumberField NumberField.IsCMField Real Set
open scoped NumberField

namespace TauCeti.OneSidedBound

/-- At large scale `W`, suppose `W⁶ ≤ log b`, and primes `≡ 1` modulo `Q` are available in
all windows of width `W` with left endpoints in `[W, B]`. If `B ≥ 24 m log b`, then the
principal-level pair can be chosen in `[b¹⁰, b¹¹]` with an integral norm witness in `K`.
For that very pair, one can choose the level prime in the window of width `√(log b)`
starting at `ThetaLift.logLevelMin`, with an integral norm witness in `E`.
Here `w` is the mean log weight and `D` is the root discriminant in the level formula. -/
theorem eventually_exists_level_primes_with_norms (K : Type*)
    [Field K] [NumberField K] [IsCMField K] [Algebra.IsQuadraticExtension ℚ K] :
    ∀ᶠ W : ℝ in atTop, ∀ (E : Type*) [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E],
      ∀ {ζ : E} {n Q b m : ℕ} {w D B : ℝ},
        IsPrimitiveRoot ζ n → 0 < n → 4 ∣ n → 4 ∣ Q → (discr K).natAbs ∣ Q →
        2 ≤ m → W ^ 6 ≤ log b → w ∈ Icc 0 (log b) → D ∈ Icc 1 (b : ℝ) →
        24 * m * log b ≤ B →
        (∀ U ∈ Icc W B, ∃ p : ℕ,
          p.Prime ∧ p ≡ 1 [MOD Q] ∧ log (p : ℝ) ∈ Icc U (U + W)) →
        ∃ p₀ p₁ N : ℕ, p₀ ≠ p₁ ∧ p₀.Prime ∧ p₁.Prime ∧ N.Prime ∧
          p₀ ≡ 1 [MOD Q] ∧ p₁ ≡ 1 [MOD Q] ∧ N ≡ 1 [MOD Q] ∧
          p₀ ∈ Icc (b ^ 10) (b ^ 11) ∧ p₁ ∈ Icc (b ^ 10) (b ^ 11) ∧
          (let U := ThetaLift.logLevelMin m w (p₀ * p₁) D (log b)
           log (N : ℝ) ∈ Icc U (U + √(log b))) ∧
          (∃ z : 𝓞 K, z * ringOfIntegersComplexConj K z = (p₀ : 𝓞 K) * (p₁ : 𝓞 K)) ∧
          ∃ z : 𝓞 E, z * ringOfIntegersComplexConj E z = N := by
  have hπ : ∀ᶠ W : ℝ in atTop, log (2 * π) ≤ W ^ (6 : ℕ) :=
    (tendsto_pow_atTop (by decide : 6 ≠ 0)).eventually_ge_atTop _
  filter_upwards [eventually_exists_auxiliary_prime_pair_norm K, eventually_ge_atTop (1 : ℝ), hπ]
    with W hpair hW hπW E _ _ _ _ ζ n Q b m w D B hζ hn hn₄ hQ₄ hQ hm hL hw hD hB hwin
  have hW₆ : W ≤ W ^ 6 := le_self_pow₀ hW (by decide)
  have hWL := hW₆.trans hL
  have hL₀ : 0 ≤ log b := (zero_le_one.trans hW).trans hWL
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hBpair : 11 * log b ≤ B :=
    (mul_le_mul_of_nonneg_right (by linarith : (11 : ℝ) ≤ 24 * m) hL₀).trans hB
  obtain ⟨p₀, p₁, hne, hp₀, hp₁, hp₀Q, hp₁Q, hp₀b, hp₁b, zK, hzK⟩ :=
    hpair b Q B hL hBpair hQ hwin
  have hb : 0 < (b : ℝ) := by
    have hb₁ : (1 : ℝ) ≤ b := hD.1.trans hD.2
    positivity
  have hM : (p₀ * p₁ : ℝ) ∈ Icc (exp (20 * log b)) (exp (22 * log b)) := by
    have hexp (k : ℕ) : exp (k * log b) = (b : ℝ) ^ k := by
      rw [exp_natCast_mul, exp_log hb]
    rw [← Nat.cast_ofNat (R := ℝ) (n := 20), ← Nat.cast_ofNat (R := ℝ) (n := 22), hexp, hexp]
    have hlo : b ^ 20 ≤ p₀ * p₁ := by
      simpa only [← pow_add] using Nat.mul_le_mul hp₀b.1 hp₁b.1
    have hhi : p₀ * p₁ ≤ b ^ 22 := by
      simpa only [← pow_add] using Nat.mul_le_mul hp₀b.2 hp₁b.2
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hU := ThetaLift.logLevelMin_mem_Icc hm (hπW.trans hL) hw hM
    (by simpa only [exp_log hb] using hD)
  have hUm : W ≤ m * log b :=
    hWL.trans (le_mul_of_one_le_left hL₀ (by linarith))
  have hwidth : W ≤ √(log b) := Real.le_sqrt_of_sq_le
    ((pow_le_pow_right₀ hW (by decide : 2 ≤ 6)).trans hL)
  obtain ⟨N, hN, hNQ, hNI, zE, hzE⟩ := ThetaLift.exists_prime_log_mem_Icc_mul_complexConj_eq
    hζ hn hn₄ hQ₄ ⟨hUm.trans hU.1, hU.2.trans hB⟩ hwidth hwin
  exact ⟨p₀, p₁, N, hne, hp₀, hp₁, hN, hp₀Q, hp₁Q, hNQ, hp₀b, hp₁b, hNI, ⟨zK, hzK⟩, zE, hzE⟩

end TauCeti.OneSidedBound
