/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.Quadratic

/-!
# Uniform zero-free bounds for powers of a fixed modulus

All powers of a fixed modulus have prime factors in one finite set. This makes the near-one
lower bound for quadratic characters uniform across the tower. On a disk of radius `1 / X`
the resulting logarithmic derivative bound is at most both `X` and `2 * ((A + 1) * log X) ^ 25`
for moduli at most `X ^ A`. This is the local bound used when detecting primes in logarithmic
windows in the class of `1`.

The finite-family reduction and choice of logarithmic scale follow lsernau/grh-lean (commit
`72fead1`), `Lib/Analytic/Primes.lean` (`New.eventually_norm_logDeriv_entireL_le_near_one`).
Using the lower bound for fixed prime support avoids requiring the base modulus to be divisible
by `4`.
-/

public section

open Filter Real Topology TauCeti.DirichletCharacter

namespace DirichletCharacter

/-- For sufficiently large `X`, uniformly over levels `m ^ k ≤ X ^ A` and all their characters,
the pole-removed L-function is nonzero on the closed disk of radius `1 / X` about `1`.
The logarithmic derivative there has norm at most both `X` and `2 * ((A + 1) * log X) ^ 25`. -/
theorem eventually_norm_logDeriv_entireLFunction_le_near_one (m : ℕ) [NeZero m] (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (k : ℕ), (m : ℝ) ^ k ≤ X ^ A →
      ∀ (χ : DirichletCharacter ℂ (m ^ k)) (s : ℂ), ‖s - 1‖ ≤ 1 / X →
        χ.entireLFunction s ≠ 0 ∧
          ‖logDeriv χ.entireLFunction s‖ ≤ min X (2 * (((A + 1 : ℕ) : ℝ) * log X) ^ 25) := by
  let l (X : ℝ) : ℝ := (A + 1 : ℕ) * log X
  have htop : Tendsto l atTop atTop := tendsto_log_atTop.const_mul_atTop (by positivity)
  have hsmall : Tendsto (fun X ↦ 1 / l X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop htop
  have hpow : ∀ᶠ X : ℝ in atTop, 2 * l X ^ 25 ≤ X :=
    TauCeti.Real.eventually_const_mul_log_pow_le 2 _ 25
  obtain ⟨c, hc, hnear⟩ :=
    exists_pos_eventually_le_norm_regularizedLFunction_of_primeFactors_subset_of_sq_eq_one
      m.primeFactors
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  -- Make the disk radius smaller than both the neighbourhood radius and the lower bound.
  have hrad : ∀ᶠ X in atTop, 1 / l X < min r c := hsmall.eventually (gt_mem_nhds (lt_min hr hc))
  filter_upwards [htop.eventually_ge_atTop (10 ^ 10), hpow, eventually_ge_atTop (1 : ℝ), hrad]
    with X hl hp hX hrad k hk χ s hs
  have hl₁ : 1 ≤ l X := by linarith
  have hXL : (l X) ^ 25 ≤ X := by linarith [pow_nonneg (zero_le_one.trans hl₁) 25]
  have he : exp (l X) = X ^ (A + 1) := by
    dsimp [l]
    rw [exp_natCast_mul, exp_log (by positivity)]
  have hmod : (↑(m ^ k) : ℝ) ≤ exp (l X) := by
    rw [Nat.cast_pow, he]
    exact hk.trans (pow_le_pow_right₀ hX (Nat.le_succ _))
  have hreal : 1 - 1 / l X ^ 25 ≤ s.re := by
    have hdist : |s.re - 1| ≤ ‖s - 1‖ := by simpa using Complex.abs_re_le_norm (s - 1)
    have := one_div_le_one_div_of_le (by positivity : 0 < l X ^ 25) hXL
    linarith [(abs_le.mp hdist).1]
  have hnorm : ‖s‖ ≤ exp (l X) := by
    have h₁ := one_div_le_one_div_of_le zero_lt_one hX
    have h₂ := norm_le_norm_sub_add s (1 : ℂ)
    rw [norm_one] at h₂
    linarith [add_one_le_exp (l X)]
  have hprimes : (m ^ k).primeFactors ⊆ m.primeFactors := by
    cases k <;> simp [Nat.primeFactors_pow_succ]
  have hlower (hχ : χ ^ 2 = 1) (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / l X) :
      1 / l X ≤ ‖χ.regularizedLFunction z‖ := by
    have hzball : z ∈ Metric.ball (1 : ℂ) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hz.trans_lt (hrad.trans_le (min_le_left _ _))
    exact (hrad.le.trans (min_le_right _ _)).trans (hball hzball (m ^ k) hprimes χ hχ)
  obtain ⟨hne, hb⟩ := χ.entireLFunction_ne_zero_and_norm_logDeriv_le hl hmod hlower hreal hnorm
  exact ⟨hne, le_min (hb.trans hp) hb⟩

end DirichletCharacter
