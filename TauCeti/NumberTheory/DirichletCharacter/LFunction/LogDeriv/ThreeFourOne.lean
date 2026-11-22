/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.ThreeFourOne

/-!
# The 3-4-1 logarithmic-derivative inequality for Dirichlet L-functions

On the half-plane `Re s > 1`, expanding `-L'/L(s, χ)` into its absolutely convergent twisted von
Mangoldt series `∑ χ(n) Λ(n) / n ^ s` and applying `TauCeti.LSeries.threeFourOneCombination_nonneg`
termwise yields the classical `3-4-1` inequality

```text
0 ≤ 3 * (-logDeriv (1 : DirichletCharacter ℂ N).LFunction σ).re +
  4 * (-logDeriv χ.LFunction (σ + t * I)).re +
  (-logDeriv (χ ^ 2).LFunction (σ + 2 * t * I)).re
```

for every real `σ > 1`, real `t`, and Dirichlet character `χ` of any positive level `N`.
We also record the elementary majorant `(logDeriv χ.LFunction σ).re ≤ -(logDeriv 1 σ).re`,
which uses `-(1 n).re ≤ (χ n).re` termwise, and specialize the `3-4-1` inequality at level `1`
to `riemannZeta`.

## Main results

* `DirichletCharacter.threeFourOne_neg_re_logDeriv_LFunction_nonneg`: the `3-4-1` logarithmic
  derivative inequality for any Dirichlet character `χ` modulo `N`.
* `DirichletCharacter.re_logDeriv_LFunction_le_neg_re_logDeriv_one`: real-part comparison
  `(logDeriv χ.LFunction σ).re ≤ -(logDeriv (1 : DirichletCharacter ℂ N).LFunction σ).re`
  for real `σ > 1`.
* `TauCeti.threeFourOne_neg_re_logDeriv_riemannZeta_nonneg`: specialization to `riemannZeta`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13–§14.
-/

public section

open ArithmeticFunction Complex LSeries

open scoped LSeries.notation

namespace DirichletCharacter

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
    (χ ^ 2).logDeriv_LFunction_eq_neg_LSeries hσ₂,
    neg_neg, neg_neg, neg_neg]
  have hs₀ : Summable (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)) :=
    LSeriesSummable_twist_vonMangoldt 1 hσ₀
  have hs₁ : Summable (term (↗χ * ↗Λ) ((σ : ℂ) + t * I)) :=
    LSeriesSummable_twist_vonMangoldt χ hσ₁
  have hs₂ : Summable (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I)) :=
    LSeriesSummable_twist_vonMangoldt (χ ^ 2) hσ₂
  rw [LSeries, LSeries, LSeries,
    Complex.re_tsum hs₀, Complex.re_tsum hs₁, Complex.re_tsum hs₂]
  have hr₀ : Summable fun n ↦ (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re :=
    Complex.reCLM.summable hs₀
  have hr₁ : Summable fun n ↦ (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re :=
    Complex.reCLM.summable hs₁
  have hr₂ : Summable fun n ↦ (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I) n).re :=
    Complex.reCLM.summable hs₂
  rw [← tsum_mul_left (a := 3), ← tsum_mul_left (a := 4),
    ← (hr₀.mul_left 3).tsum_add (hr₁.mul_left 4),
    ← ((hr₀.mul_left 3).add (hr₁.mul_left 4)).tsum_add hr₂]
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases hunit : IsUnit (n : ZMod N)
  · have h1n : (1 : DirichletCharacter ℂ N) n = 1 := MulChar.one_apply hunit
    have h2n : (χ ^ 2) n = (χ n) ^ 2 := MulChar.pow_apply' χ two_ne_zero n
    have hcp0 : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hn_pos.le]
    have hcp1 : (n : ℂ) ^ (-((σ : ℂ) + t * I)) =
        (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I)) := by
      rw [neg_add, cpow_add _ _ hnc, hcp0]
    have hcp2 : (n : ℂ) ^ (-((σ : ℂ) + 2 * t * I)) =
        (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(t * I))) ^ 2 := by
      rw [neg_add, cpow_add _ _ hnc, hcp0, sq, ← cpow_add _ _ hnc]
      congr 2
      ring
    set z : ℂ := χ n * (n : ℂ) ^ (-(t * I))
    have hz_norm : ‖z‖ ≤ 1 := by
      rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
      have hre : (-(t * I)).re = 0 := by simp
      rw [hre, Real.rpow_zero, mul_one]
      exact χ.norm_le_one n
    have hcoeff : 3 * (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re +
        4 * (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re +
        (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I) n).re =
        Λ n * (n : ℝ) ^ (-σ) * TauCeti.LSeries.threeFourOneCombination z := by
      simp only [term_of_ne_zero hn, Pi.mul_apply, div_eq_mul_inv, ← cpow_neg, h1n, h2n,
        hcp0, hcp1, hcp2]
      have hz2 : (χ n) ^ 2 * (Λ n : ℂ) * ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(t * I))) ^ 2) =
          (((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) * z ^ 2 := by
        dsimp [z]
        push_cast
        ring
      have hz1 : χ n * (Λ n : ℂ) * ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I))) =
          (((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) * z := by
        dsimp [z]
        push_cast
        ring
      have hz0 : (1 : ℂ) * (Λ n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) =
          (((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [hz0, hz1, hz2, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
        TauCeti.LSeries.threeFourOneCombination_def]
      ring
    rw [hcoeff]
    exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hn_pos.le _))
      (TauCeti.LSeries.threeFourOneCombination_nonneg hz_norm)
  · have h1n : (1 : DirichletCharacter ℂ N) n = 0 := MulChar.map_nonunit _ hunit
    have hχn : χ n = 0 := MulChar.map_nonunit _ hunit
    have h2n : (χ ^ 2) n = 0 := MulChar.map_nonunit _ hunit
    simp [term_of_ne_zero hn, h1n, hχn, h2n]

/-- On the real half-line `σ > 1`, `(logDeriv χ.LFunction σ).re` is at most
`-(logDeriv (1 : DirichletCharacter ℂ N).LFunction σ).re`, since `-Re χ(n) ≤ (1 : ℂ) n` termwise.
-/
theorem re_logDeriv_LFunction_le_neg_re_logDeriv_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    (logDeriv χ.LFunction σ).re ≤ -(logDeriv (1 : DirichletCharacter ℂ N).LFunction σ).re := by
  have hσ₀ : 1 < (σ : ℂ).re := by simpa using hσ
  rw [χ.logDeriv_LFunction_eq_neg_LSeries hσ₀,
    (1 : DirichletCharacter ℂ N).logDeriv_LFunction_eq_neg_LSeries hσ₀]
  have hs₁ : Summable (term (↗χ * ↗Λ) (σ : ℂ)) := LSeriesSummable_twist_vonMangoldt χ hσ₀
  have hs₀ : Summable (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)) :=
    LSeriesSummable_twist_vonMangoldt 1 hσ₀
  have hr₀ : Summable fun n ↦ (term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re :=
    Complex.reCLM.summable hs₀
  have hr₁ : Summable fun n ↦ (term (↗χ * ↗Λ) (σ : ℂ) n).re :=
    Complex.reCLM.summable hs₁
  rw [← sub_nonneg, LSeries, LSeries, Complex.neg_re, Complex.neg_re, neg_neg,
    Complex.re_tsum hs₁, Complex.re_tsum hs₀, sub_neg_eq_add, ← hr₀.tsum_add hr₁]
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hcp : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hn_pos.le]
  by_cases hunit : IsUnit (n : ZMod N)
  · have h1n : (1 : DirichletCharacter ℂ N) n = 1 := MulChar.one_apply hunit
    simp only [term_of_ne_zero hn, Pi.mul_apply, div_eq_mul_inv, ← cpow_neg, h1n, hcp]
    have hre₀ : ((1 : ℂ) * (Λ n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)).re = Λ n * (n : ℝ) ^ (-σ) := by
      rw [one_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hre₁ : (χ n * (Λ n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)).re =
        (χ n).re * (Λ n * (n : ℝ) ^ (-σ)) := by
      rw [mul_assoc, ← Complex.ofReal_mul, Complex.re_mul_ofReal]
    rw [hre₀, hre₁, show Λ n * (n : ℝ) ^ (-σ) + (χ n).re * (Λ n * (n : ℝ) ^ (-σ)) =
      (1 + (χ n).re) * (Λ n * (n : ℝ) ^ (-σ)) by ring]
    refine mul_nonneg ?_ (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hn_pos.le _))
    linarith [neg_le_of_abs_le ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))]
  · have h1n : (1 : DirichletCharacter ℂ N) n = 0 := MulChar.map_nonunit _ hunit
    have hχn : χ n = 0 := MulChar.map_nonunit _ hunit
    simp [term_of_ne_zero hn, h1n, hχn]

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
