/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.ThreeFourOne

/-!
# The 3-4-1 logarithmic-derivative inequality for Dirichlet L-functions

On the half-plane `Re s > 1`, expanding `-L'/L(s, χ)` via
`DirichletCharacter.logDeriv_LFunction_eq_neg_LSeries` (built on Michael Stoll's Mathlib identity
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`) into the absolutely convergent twisted von
Mangoldt series `∑ χ(n) Λ(n) / n ^ s` and applying `TauCeti.LSeries.threeFourOneCombination_nonneg`
termwise yields the classical `3-4-1` inequality

```text
0 ≤ 3 * (-logDeriv (1 : DirichletCharacter ℂ N).LFunction σ).re +
  4 * (-logDeriv χ.LFunction (σ + t * I)).re +
  (-logDeriv (χ ^ 2).LFunction (σ + 2 * t * I)).re
```

for every real `σ > 1`, real `t`, and Dirichlet character `χ` of any positive level `N`.
We also specialize the `3-4-1` inequality at level `1` to `riemannZeta`.

## Main results

* `DirichletCharacter.threeFourOne_neg_re_logDeriv_LFunction_nonneg`: the `3-4-1` logarithmic
  derivative inequality for any Dirichlet character `χ` modulo `N`.
* `TauCeti.threeFourOne_neg_re_logDeriv_riemannZeta_nonneg`: specialization to `riemannZeta`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13–§14.
-/

public section

open ArithmeticFunction Complex LSeries

open scoped LSeries.notation

namespace DirichletCharacter

private theorem re_term_twist_vonMangoldt_add_mul_I {N : ℕ} (χ : DirichletCharacter ℂ N)
    {n : ℕ} (hn : n ≠ 0) (σ y : ℝ) :
    (term (↗χ * ↗Λ) ((σ : ℂ) + y * I) n).re =
      Λ n * (n : ℝ) ^ (-σ) * (χ n * (n : ℂ) ^ (-(y * I))).re := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcp : (n : ℂ) ^ (-((σ : ℂ) + y * I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(y * I)) := by
    rw [neg_add, cpow_add _ _ hnc, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
      Complex.ofReal_cpow hn_pos.le]
  have hterm : term (↗χ * ↗Λ) ((σ : ℂ) + y * I) n =
      (((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) * (χ n * (n : ℂ) ^ (-(y * I))) := by
    simp only [term_of_ne_zero hn, Pi.mul_apply, div_eq_mul_inv, ← cpow_neg, hcp]
    push_cast
    ring
  rw [hterm, Complex.re_ofReal_mul]

private theorem threeFourOne_term_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (t : ℝ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re +
      4 * (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re +
      (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h0 : (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re =
      Λ n * (n : ℝ) ^ (-σ) * ((1 : DirichletCharacter ℂ N) n * (n : ℂ) ^ (-((0 : ℝ) * I))).re := by
    simpa only [ofReal_zero, zero_mul, add_zero] using
      re_term_twist_vonMangoldt_add_mul_I (1 : DirichletCharacter ℂ N) hn σ 0
  have h1 := re_term_twist_vonMangoldt_add_mul_I χ hn σ t
  have h2 : (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I) n).re =
      Λ n * (n : ℝ) ^ (-σ) * ((χ ^ 2) n * (n : ℂ) ^ (-((2 * t : ℝ) * I))).re := by
    simpa only [ofReal_mul, ofReal_ofNat, mul_assoc] using
      re_term_twist_vonMangoldt_add_mul_I (χ ^ 2) hn σ (2 * t)
  by_cases hunit : IsUnit (n : ZMod N)
  · set z : ℂ := χ n * (n : ℂ) ^ (-(t * I))
    have hz_norm : ‖z‖ ≤ 1 := by
      have hre : (-(t * I)).re = 0 := by simp
      rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
        hre, Real.rpow_zero, mul_one]
      exact χ.norm_le_one n
    have hz1 : ((1 : DirichletCharacter ℂ N) n * (n : ℂ) ^ (-((0 : ℝ) * I))).re = 1 := by
      simp [MulChar.one_apply hunit]
    have hz2 : (χ ^ 2) n * (n : ℂ) ^ (-((2 * t : ℝ) * I)) = z ^ 2 := by
      dsimp [z]
      rw [MulChar.pow_apply' χ two_ne_zero n, mul_pow, sq (χ n)]
      congr 1
      rw [sq, ← cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
      congr 1; push_cast; ring
    have hcomb : 3 * (Λ n * (n : ℝ) ^ (-σ) * 1) + 4 * (Λ n * (n : ℝ) ^ (-σ) * z.re) +
        Λ n * (n : ℝ) ^ (-σ) * (z ^ 2).re =
        Λ n * (n : ℝ) ^ (-σ) * TauCeti.LSeries.threeFourOneCombination z := by
      rw [TauCeti.LSeries.threeFourOneCombination_def]
      ring
    rw [h0, h1, h2, hz1, hz2, hcomb]
    exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hn_pos.le _))
      (TauCeti.LSeries.threeFourOneCombination_nonneg hz_norm)
  · simp [h0, h1, h2, MulChar.map_nonunit _ hunit]

/-- **The `3-4-1` logarithmic-derivative inequality for Dirichlet `L`-functions.** For any
Dirichlet character `χ` of nonzero level `N`, real `σ > 1`, and real `t`,
`0 ≤ 3 * (-Re L'/L(σ, 1)) + 4 * (-Re L'/L(σ + it, χ)) + (-Re L'/L(σ + 2it, χ²))`. -/
theorem threeFourOne_neg_re_logDeriv_LFunction_nonneg {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-logDeriv (1 : DirichletCharacter ℂ N).LFunction σ).re +
      4 * (-logDeriv χ.LFunction (σ + t * I)).re +
      (-logDeriv (χ ^ 2).LFunction (σ + 2 * t * I)).re := by
  have hσ₀ : 1 < (σ : ℂ).re := by simpa using hσ
  have hσ₁ : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hσ₂ : 1 < ((σ : ℂ) + 2 * t * I).re := by simpa using hσ
  rw [(1 : DirichletCharacter ℂ N).logDeriv_LFunction_eq_neg_LSeries hσ₀,
    χ.logDeriv_LFunction_eq_neg_LSeries hσ₁,
    (χ ^ 2).logDeriv_LFunction_eq_neg_LSeries hσ₂, neg_neg, neg_neg, neg_neg]
  have hs₀ := LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ N) hσ₀
  have hs₁ := LSeriesSummable_twist_vonMangoldt χ hσ₁
  have hs₂ := LSeriesSummable_twist_vonMangoldt (χ ^ 2) hσ₂
  rw [LSeries, LSeries, LSeries, Complex.re_tsum hs₀, Complex.re_tsum hs₁, Complex.re_tsum hs₂]
  have hr₀ : Summable fun n ↦ (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re :=
    Complex.reCLM.summable hs₀
  have hr₁ : Summable fun n ↦ (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re :=
    Complex.reCLM.summable hs₁
  have hr₂ : Summable fun n ↦ (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I) n).re :=
    Complex.reCLM.summable hs₂
  rw [← tsum_mul_left (a := 3), ← tsum_mul_left (a := 4),
    ← (hr₀.mul_left 3).tsum_add (hr₁.mul_left 4),
    ← ((hr₀.mul_left 3).add (hr₁.mul_left 4)).tsum_add hr₂]
  exact tsum_nonneg (threeFourOne_term_nonneg χ t)

end DirichletCharacter

namespace TauCeti

/-- **The `3-4-1` logarithmic-derivative inequality for `riemannZeta`.** For real `σ > 1` and
real `t`, `0 ≤ 3 * (-Re ζ'/ζ(σ)) + 4 * (-Re ζ'/ζ(σ + it)) + (-Re ζ'/ζ(σ + 2it))`. -/
theorem threeFourOne_neg_re_logDeriv_riemannZeta_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-logDeriv riemannZeta σ).re +
      4 * (-logDeriv riemannZeta (σ + t * I)).re +
      (-logDeriv riemannZeta (σ + 2 * t * I)).re := by
  simpa only [DirichletCharacter.LFunction_modOne_eq, one_pow] using
    (1 : DirichletCharacter ℂ 1).threeFourOne_neg_re_logDeriv_LFunction_nonneg hσ t

end TauCeti
