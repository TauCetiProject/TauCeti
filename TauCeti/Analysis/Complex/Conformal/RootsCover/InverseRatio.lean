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
For `N ≥ 2`, this is the candidate for the local inverse at zero of the universal cover
from the disc to the plane punctured at the `N`th roots of unity, normalized to have
derivative one at zero. The identification, with the appropriate derivative scale factor,
is used in the conformal-radius calculation but is not proved here.

The quotient is analytic near zero, fixes zero, has derivative one at zero, and intertwines
rotations by `N`th roots of unity. We compute its `(N + 1)`st derivative at zero for positive
`N`; in particular, the third derivative of `inverseRatio 2` at zero is `3 / 2`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.16, pp. 671–672.
-/

public noncomputable section

open Filter
open scoped Topology

namespace TauCeti

/-- The quotient `u * ₂F₁(a₊, a₊; 2a₊; u^N) / ₂F₁(a₋, a₋; 2a₋; u^N)`, with
`a₊ = (N + 1) / (2N)` and `a₋ = (N - 1) / (2N)`. For `N ≥ 2`, it models the
normalized inverse germ for the plane punctured at the `N`th roots of unity.
For positive `N`, the native series give an analytic quotient on `‖u‖ < 1` wherever
the denominator is nonzero; the totalized formula does not prescribe continuation outside
that disc or through denominator zeros. At `N = 0` the formula is the identity. -/
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
theorem eventually_inverseRatio_denominator_ne_zero (N : ℕ) :
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

/-- The totalized expression at `N = 0` is the identity, with no covering interpretation. -/
@[simp]
theorem inverseRatio_zero_left : inverseRatio 0 = id := by
  ext u
  simp [inverseRatio_def, ordinaryHypergeometric_eq_tsum, ascPochhammer_eval_zero]

/-- The totalized expression represents an analytic germ at zero for every `N`. -/
theorem analyticAt_inverseRatio_zero (N : ℕ) :
    AnalyticAt ℂ (inverseRatio N) 0 := by
  by_cases hN : N = 0
  · subst N
    simpa only [inverseRatio_zero_left] using (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
  have h (a b c : ℂ) :
      AnalyticAt ℂ (fun z : ℂ ↦ ordinaryHypergeometric a b c (z ^ N)) 0 :=
    (analyticOnNhd_ordinaryHypergeometric ℂ a b c _
      (by simp [zero_pow hN])).comp (by fun_prop)
  exact (analyticAt_id.mul (h _ _ _)).div (h _ _ _)
    (by simp [zero_pow hN, ordinaryHypergeometric_zero])

/-- The inverse-ratio germ has first derivative one at zero. -/
theorem hasDerivAt_inverseRatio_zero (N : ℕ) :
    HasDerivAt (inverseRatio N) 1 0 := by
  by_cases hN : N = 0
  · subst N
    simpa only [inverseRatio_zero_left] using (hasDerivAt_id (0 : ℂ))
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

/-- The derivative of the inverse-ratio germ at zero is one. -/
@[simp]
theorem deriv_inverseRatio_zero (N : ℕ) : deriv (inverseRatio N) 0 = 1 :=
  (hasDerivAt_inverseRatio_zero N).deriv

/-- Rotation equivariance is an algebraic identity of the totalized expression, so it
requires neither convergence nor a nonzero-denominator guard. -/
theorem inverseRatio_mul_of_pow_eq_one {N : ℕ} {ζ : ℂ} (hζ : ζ ^ N = 1) (u : ℂ) :
    inverseRatio N (ζ * u) = ζ * inverseRatio N u := by
  simp only [inverseRatio_def, mul_pow, hζ, one_mul]
  ring

/-- The `(N + 1)`st derivative of the inverse-ratio germ at zero, for positive `N`. -/
theorem iteratedDeriv_succ_inverseRatio_zero {N : ℕ} (hN : N ≠ 0) :
    iteratedDeriv (N + 1) (inverseRatio N) 0 = ((N + 1).factorial : ℂ) / (2 * N) := by
  let a : ℂ := ((N : ℂ) + 1) / (2 * N)
  let b : ℂ := ((N : ℂ) - 1) / (2 * N)
  let G : ℂ → ℂ := fun x ↦ ordinaryHypergeometric a a (2 * a) x /
    ordinaryHypergeometric b b (2 * b) x
  have hF (t : ℂ) : HasDerivAt (ordinaryHypergeometric t t (2 * t)) (t / 2) (0 : ℂ) := by
    have hd := (analyticOnNhd_ordinaryHypergeometric ℂ t t (2 * t) 0
      (by simp)).differentiableAt.hasDerivAt
    have hc : t * t / (2 * t) = t / 2 := by
      by_cases ht : t = 0
      · simp [ht]
      · rw [mul_comm 2 t, mul_div_mul_left _ _ ht]
    simpa only [deriv_ordinaryHypergeometric_zero, hc] using hd
  have hG : AnalyticAt ℂ G 0 :=
    (analyticOnNhd_ordinaryHypergeometric ℂ a a (2 * a) 0 (by simp)).fun_div
      (analyticOnNhd_ordinaryHypergeometric ℂ b b (2 * b) 0 (by simp))
      (by simp [ordinaryHypergeometric_zero])
  have hdG : HasDerivAt G (1 / (2 * N)) 0 := by
    convert (hF a).fun_div (hF b) (by simp [ordinaryHypergeometric_zero]) using 1
    simp [ordinaryHypergeometric_zero, a, b]
    ring
  obtain ⟨p, r, hp⟩ := hG
  -- Rewrite the Taylor series in scalar form to substitute `u ^ N`.
  have hp_eq : FormalMultilinearSeries.ofScalars ℂ p.coeff = p := by
    ext n
    simp
  have hcG : p.coeff 1 = 1 / (2 * N) := hp.hasFPowerSeriesAt.hasDerivAt.unique hdG
  have hs := (hp_eq.symm ▸ hp).mono (lt_min hp.r_pos zero_lt_one) (min_le_left _ _)
  have h := hs.comp_pow_ofScalars (min_le_right _ _) (m := N) (Nat.pos_of_ne_zero hN)
  have h' : iteratedDeriv N (fun u : ℂ ↦ G (u ^ N)) 0 = N.factorial * (1 / (2 * N)) := by
    simpa [← iteratedDeriv_eq_iteratedFDeriv, FormalMultilinearSeries.ofScalars_apply_eq,
      Nat.div_self (Nat.pos_of_ne_zero hN), hcG] using
      (h.factorial_smul 1 N).symm
  have hEq : inverseRatio N = fun u ↦ u * G (u ^ N) := by
    ext u
    have hscale (t : ℂ) : 2 * (t / (2 * (N : ℂ))) = t / N := by
      rw [← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    simp only [a, b, G, hscale, inverseRatio_def, mul_div_assoc]
  rw [hEq, iteratedDeriv_fun_mul (f := fun u : ℂ ↦ u)
    analyticAt_id.contDiffAt h.analyticAt.contDiffAt,
    Finset.sum_eq_single_of_mem 1 (by simp) (fun i _ hi ↦ by simp [iteratedDeriv_fun_id_zero, hi])]
  simp [iteratedDeriv_fun_id_zero, h', Nat.factorial_succ, div_eq_mul_inv, mul_assoc]

/-- The third derivative of `inverseRatio 2` at zero is `3 / 2`, corresponding to a
cubic Taylor coefficient of `1 / 4`. -/
theorem iteratedDeriv_three_inverseRatio_two_zero :
    iteratedDeriv 3 (inverseRatio 2) 0 = 3 / 2 := by
  convert iteratedDeriv_succ_inverseRatio_zero (N := 2) (by decide) using 1
  norm_num [Nat.factorial_succ]

end TauCeti
