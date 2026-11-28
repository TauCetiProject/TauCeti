/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.CMField
import TauCeti.Analysis.SpecialFunctions.Log.Window
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.AuxiliaryPrimes
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
import TauCeti.NumberTheory.NumberField.CMField.QuadraticNorm
import TauCeti.NumberTheory.NumberField.Quadratic.Prime.PairNorm

/-!
# The principal-level prime pair for theta lifts

Choose distinct rational primes in a progression and a size interval whose product is the
norm of an algebraic integer in an imaginary quadratic field. Sampling more primes than the
class number allows a product to be principal even if individual primes above the selected
rational primes are not principal.

The norm witness and logarithmic intervals follow `New.Parameters.exists_prime_pair_norm` and
`New.Parameters.IsLargeScale.exists_isAdmissibleData` in `New/Reduction/Data/Existence.lean` of
lsernau/grh-lean at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Filter NumberField NumberField.IsCMField Set
open scoped NumberField

namespace TauCeti.OneSidedBound

/-- Given a prime in the progression `1 mod Q` in every window of width `W` inside `[L, R]`,
choose a pair of distinct such primes in `[L, R]` on the logarithmic scale with product
`z * conj z` in `𝓞 K`. The modulus is a multiple of the absolute discriminant of the
imaginary quadratic field, and the interval fits one window per ideal class plus one. -/
theorem exists_prime_pair_log_mem_Icc_mul_complexConj_eq (K : Type*)
    [Field K] [NumberField K] [IsCMField K] [Algebra.IsQuadraticExtension ℚ K]
    {Q : ℕ} (hQ : (discr K).natAbs ∣ Q) {L R W : ℝ} (hW : 0 < W)
    (hsize : L + 2 * ((classNumber K + 1 : ℕ) : ℝ) * W ≤ R)
    (hwin : ∀ U : ℝ, L ≤ U → U + W ≤ R →
      ∃ p : ℕ, (p.Prime ∧ p ≡ 1 [MOD Q]) ∧ Real.log p ∈ Icc U (U + W)) :
    ∃ p q : ℕ, p ≠ q ∧ p.Prime ∧ q.Prime ∧ p ≡ 1 [MOD Q] ∧ q ≡ 1 [MOD Q] ∧
      Real.log p ∈ Icc L R ∧ Real.log q ∈ Icc L R ∧
      ∃ z : 𝓞 K, z * ringOfIntegersComplexConj K z = (p : 𝓞 K) * (q : 𝓞 K) := by
  obtain ⟨S, hcard, hS⟩ := exists_finset_card_eq_and_log_mem_Icc hW hsize hwin
  have hK := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨p, hp, q, hq, hpq, z, hz⟩ :=
    NumberField.exists_norm_eq_mul_of_classNumber_lt_card_of_ncard_primesOver_eq_finrank hK
      (by rw [hcard]; exact Nat.lt_succ_self _) fun p hp ↦
        Multiquadratic.ncard_primesOver_eq_finrank_of_modEq_one_discr hK
          (hS p hp).1.1 ((hS p hp).1.2.of_dvd hQ)
  obtain ⟨⟨hp', hpQ⟩, hpI⟩ := hS p hp
  obtain ⟨⟨hq', hqQ⟩, hqI⟩ := hS q hq
  refine ⟨p, q, hpq, hp', hq', hpQ, hqQ, hpI, hqI, z, ?_⟩
  simp only [← z.intCast_norm_eq_mul_complexConj, hz, Int.cast_mul, Int.cast_natCast]

/-- At large scale `W`, the logarithmic search over `[W, W⁷]` supplies the principal-level
prime pair in `[b¹⁰, b¹¹]` with its integral norm witness if `W⁶ ≤ log b` and `11 log b ≤ W⁷`.
In particular the scale `W⁶ ≤ log b ≤ W⁶ + 1` fits. The threshold in `W` does not depend on `Q`. -/
theorem eventually_exists_auxiliary_prime_pair_norm (K : Type*)
    [Field K] [NumberField K] [IsCMField K] [Algebra.IsQuadraticExtension ℚ K] :
    ∀ᶠ W : ℝ in atTop, ∀ b Q : ℕ, W ^ 6 ≤ Real.log b → 11 * Real.log b ≤ W ^ 7 →
      (discr K).natAbs ∣ Q →
      (∀ U ∈ Icc W (W ^ 7), ∃ p : ℕ,
        p.Prime ∧ p ≡ 1 [MOD Q] ∧ Real.log p ∈ Icc U (U + W)) →
      ∃ p q : ℕ, p ≠ q ∧ p.Prime ∧ q.Prime ∧ p ≡ 1 [MOD Q] ∧ q ≡ 1 [MOD Q] ∧
        p ∈ Icc (b ^ 10) (b ^ 11) ∧ q ∈ Icc (b ^ 10) (b ^ 11) ∧
        ∃ z : 𝓞 K, z * ringOfIntegersComplexConj K z = (p : 𝓞 K) * (q : 𝓞 K) := by
  filter_upwards [eventually_log_window_bounds (classNumber K + 1)] with W hW b Q hlo hend hQ hwin
  obtain ⟨hW₁, hstart, hroom, _⟩ := hW (W ^ 6) le_rfl (by linarith)
  have hWp := zero_lt_one.trans_le hW₁
  obtain ⟨p, q, hpq, hp, hq, hpQ, hqQ, hpI, hqI, z, hz⟩ :=
    exists_prime_pair_log_mem_Icc_mul_complexConj_eq K hQ (L := 10 * Real.log b)
      (R := 11 * Real.log b) hWp (by linarith only [hroom, hlo])
      (fun U hU hUR ↦ by
        obtain ⟨p, hp, hpQ, hpI⟩ := hwin U ⟨by linarith only [hstart, hlo, hU],
          (le_add_of_nonneg_right hWp.le).trans (hUR.trans hend)⟩
        exact ⟨p, ⟨hp, hpQ⟩, hpI⟩)
  have hb : 0 < (b : ℝ) := by
    by_contra! hn
    have hb₀ : (b : ℝ) = 0 := le_antisymm hn (Nat.cast_nonneg b)
    rw [hb₀, Real.log_zero] at hlo
    exact (pow_pos hWp 6).not_ge hlo
  have hmem {r : ℕ} (hr : r.Prime)
      (hI : Real.log r ∈ Icc (10 * Real.log b) (11 * Real.log b)) :
      r ∈ Icc (b ^ 10) (b ^ 11) := by
    have hr₀ : 0 < (r : ℝ) := by exact_mod_cast hr.pos
    constructor
    · have h := (Real.log_le_log_iff (pow_pos hb 10) hr₀).mp
        ((Real.log_pow (b : ℝ) 10).trans_le hI.1)
      exact_mod_cast h
    · have h := (Real.log_le_log_iff hr₀ (pow_pos hb 11)).mp
        (hI.2.trans_eq (Real.log_pow (b : ℝ) 11).symm)
      exact_mod_cast h
  exact ⟨p, q, hpq, hp, hq, hpQ, hqQ, hmem hp hpI, hmem hq hqI, z, hz⟩

end TauCeti.OneSidedBound
