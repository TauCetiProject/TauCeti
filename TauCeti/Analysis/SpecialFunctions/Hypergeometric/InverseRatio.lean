/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import TauCeti.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The normalized hypergeometric inverse-ratio germ

For a positive integer `N`, `TauCeti.inverseRatio N` is the quotient
`u * ₂F₁(a₊, a₊; 2a₊; u^N) / ₂F₁(a₋, a₋; 2a₋; u^N)`, where
`a₊ = (N + 1) / (2N)` and `a₋ = (N - 1) / (2N)`.
It is analytic near zero, fixes zero, has derivative one, and intertwines rotations by
`N`th roots of unity. At `N = 2` its third derivative is `3 / 2`.

These are local statements about the native hypergeometric series. In particular, no
nonvanishing assertion about the denominator on the whole disc, or identification with
an inverse covering map, is implicit in the totalized quotient.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.16, pp. 671–672.
-/

public noncomputable section

open Filter
open scoped Topology

namespace TauCeti

/-- The normalized hypergeometric quotient, viewed as a germ at zero. Its totalized
values elsewhere are not an analytic continuation of that germ. -/
def inverseRatio (N : ℕ) (u : ℂ) : ℂ :=
  u * ordinaryHypergeometric (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N))
      (((N : ℂ) + 1) / N) (u ^ N) /
    ordinaryHypergeometric (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
      (((N : ℂ) - 1) / N) (u ^ N)

/-- The defining quotient uses the native hypergeometric series, not continued branches. -/
theorem inverseRatio_def (N : ℕ) (u : ℂ) :
    inverseRatio N u =
      u * ordinaryHypergeometric (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / (2 * N))
          (((N : ℂ) + 1) / N) (u ^ N) /
        ordinaryHypergeometric (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / (2 * N))
          (((N : ℂ) - 1) / N) (u ^ N) := (rfl)

/-- The inverse-ratio expression fixes zero, even at the totalized parameter `N = 0`. -/
@[simp]
theorem inverseRatio_zero (N : ℕ) : inverseRatio N 0 = 0 := by
  simp [inverseRatio_def]

/-- The denominator is nonzero on some neighbourhood of zero. -/
theorem eventually_ne_zero_inverseRatio_denominator (N : ℕ) :
    ∀ᶠ u : ℂ in 𝓝 0, ordinaryHypergeometric (((N : ℂ) - 1) / (2 * N))
      (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / N) (u ^ N) ≠ 0 := by
  by_cases hN : N = 0
  · subst N
    simp [ordinaryHypergeometric_eq_tsum, ascPochhammer_eval_zero]
  have h := (analyticOnNhd_ordinaryHypergeometric ℂ (((N : ℂ) - 1) / (2 * N))
    (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / N) ((0 : ℂ) ^ N)
    (by simp [zero_pow hN])).continuousAt
  exact (h.comp (f := fun u : ℂ ↦ u ^ N) (continuousAt_id.pow N)).eventually_ne
    (by simp [zero_pow hN, ordinaryHypergeometric_zero])

/-- The totalized order-zero expression is the identity, with no covering interpretation. -/
@[simp]
theorem inverseRatio_zero_order : inverseRatio 0 = id := by
  ext u
  simp [inverseRatio_def, ordinaryHypergeometric_eq_tsum, ascPochhammer_eval_zero]

/-- The totalized expression represents an analytic germ at zero for every `N`. -/
theorem analyticAt_inverseRatio_zero (N : ℕ) :
    AnalyticAt ℂ (inverseRatio N) 0 := by
  by_cases hN : N = 0
  · subst N
    simpa only [inverseRatio_zero_order] using (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
  have h (a b c : ℂ) :
      AnalyticAt ℂ (fun z : ℂ ↦ ordinaryHypergeometric a b c (z ^ N)) 0 :=
    (analyticOnNhd_ordinaryHypergeometric ℂ a b c _
      (by simp [zero_pow hN])).comp (by fun_prop)
  exact (analyticAt_id.mul (h _ _ _)).div (h _ _ _)
    (by simp [zero_pow hN, ordinaryHypergeometric_zero])

/-- The inverse-ratio germ has the unscaled first derivative one. -/
theorem hasDerivAt_inverseRatio_zero (N : ℕ) :
    HasDerivAt (inverseRatio N) 1 0 := by
  by_cases hN : N = 0
  · subst N
    simpa only [inverseRatio_zero_order] using (hasDerivAt_id (0 : ℂ))
  have h (a b c : ℂ) :
      DifferentiableAt ℂ (fun z : ℂ ↦ ordinaryHypergeometric a b c (z ^ N)) 0 :=
    ((analyticOnNhd_ordinaryHypergeometric ℂ a b c _
      (by simp [zero_pow hN])).comp (by fun_prop)).differentiableAt
  have hA := (h (((N : ℂ) + 1) / (2 * N))
    (((N : ℂ) + 1) / (2 * N)) (((N : ℂ) + 1) / N)).hasDerivAt
  have hB := (h (((N : ℂ) - 1) / (2 * N))
    (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / N)).hasDerivAt
  have hne : ordinaryHypergeometric (((N : ℂ) - 1) / (2 * N))
      (((N : ℂ) - 1) / (2 * N)) (((N : ℂ) - 1) / N) ((0 : ℂ) ^ N) ≠ 0 := by
    simp [zero_pow hN, ordinaryHypergeometric_zero]
  refine HasDerivAt.congr_of_eventuallyEq ?_
    (Eventually.of_forall (inverseRatio_def N))
  simpa [zero_pow hN, ordinaryHypergeometric_zero] using
    ((hasDerivAt_id (0 : ℂ)).fun_mul hA).fun_div hB hne

/-- The derivative normalization of the inverse-ratio germ. -/
@[simp]
theorem deriv_inverseRatio_zero (N : ℕ) : deriv (inverseRatio N) 0 = 1 :=
  (hasDerivAt_inverseRatio_zero N).deriv

/-- Rotation equivariance is an algebraic identity of the totalized expression, so it
requires neither convergence nor a nonzero-denominator guard. -/
theorem inverseRatio_mul_root {N : ℕ} {ζ : ℂ} (hζ : ζ ^ N = 1) (u : ℂ) :
    inverseRatio N (ζ * u) = ζ * inverseRatio N u := by
  simp only [inverseRatio_def, mul_pow, hζ, one_mul]
  ring

/-- For two punctures the first nonlinear term is `u³ / 4`: in unscaled derivative
notation the third derivative is `3 / 2`, not `1 / 4`. -/
theorem iteratedDeriv_three_inverseRatio_two_zero :
    iteratedDeriv 3 (inverseRatio 2) 0 = 3 / 2 := by
  let A : ℂ → ℂ := fun u ↦ ordinaryHypergeometric (3 / 4 : ℂ) (3 / 4) (3 / 2) (u ^ 2)
  let B : ℂ → ℂ := fun u ↦ ordinaryHypergeometric (1 / 4 : ℂ) (1 / 4) (1 / 2) (u ^ 2)
  have hA : AnalyticAt ℂ A 0 :=
    (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ _ (by simp)).comp (by fun_prop)
  have hB : AnalyticAt ℂ B 0 :=
    (analyticOnNhd_ordinaryHypergeometric ℂ _ _ _ _ (by simp)).comp (by fun_prop)
  have hJ := analyticAt_inverseRatio_zero 2
  have hcoeff (a c : ℂ) (k : ℕ) :
      iteratedDeriv k (fun u : ℂ ↦ ordinaryHypergeometric a a c (u ^ 2)) 0 =
        k.factorial * (if 2 ∣ k then ordinaryHypergeometricCoefficient a a c (k / 2) else 0) := by
    have hs := ((ordinaryHypergeometricSeries ℂ a a c).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le (one_le_radius_ordinaryHypergeometricSeries ℂ a a c))).mono
      (by simp) (one_le_radius_ordinaryHypergeometricSeries ℂ a a c)
    have hp := hs.comp_pow_ofScalars le_rfl (m := 2) (by decide)
    simpa [ordinaryHypergeometric, ← iteratedDeriv_eq_iteratedFDeriv,
      FormalMultilinearSeries.ofScalars_apply_eq] using (hp.factorial_smul 1 k).symm
  have hEq : (fun u ↦ B u * inverseRatio 2 u) =ᶠ[𝓝 0] (fun u ↦ u * A u) := by
    have hne : ∀ᶠ u in 𝓝 0, B u ≠ 0 := hB.continuousAt.eventually_ne (by
      simp [B, ordinaryHypergeometric_zero])
    filter_upwards [hne] with u hu
    have hf : inverseRatio 2 u = u * A u / B u := by norm_num [inverseRatio_def, A, B]
    rw [hf]
    field_simp
  have hd := hEq.iteratedDeriv_eq (n := 3)
  rw [iteratedDeriv_fun_mul hB.contDiffAt hJ.contDiffAt,
    iteratedDeriv_fun_mul (f := fun u : ℂ ↦ u) analyticAt_id.contDiffAt hA.contDiffAt] at hd
  have hj0 := inverseRatio_zero 2
  have hj1 := deriv_inverseRatio_zero 2
  norm_num [Finset.sum_range_succ, A, B, hcoeff, iteratedDeriv_one, hj0, hj1,
    iteratedDeriv_fun_id, ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval] at hd
  linear_combination hd

end TauCeti
