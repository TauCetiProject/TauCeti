/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Energy estimates for a first-order operator on the line

For a continuously differentiable family of symmetric operators `A(s)` on a real inner product
space, integration by parts gives

`∫ ‖u' + A u‖² = ∫ ‖u'‖² + ∫ ‖A u‖² - ∫ ⟪u, A' u⟫`.

We prove this identity for compactly supported `C¹` paths, without a finite-dimensionality or
completeness assumption on the target. A spectral gap for `A` and a small upper bound on the
quadratic form of `A'` give a coercive estimate. When `A` has uniformly bounded-below limits at
both ends and `A'` tends to zero, we obtain a uniform estimate for paths supported outside a
compact interval. These estimates for bounded coefficients are inputs to the Fredholm property
of `d/ds + A(s)`; they do not assert surjectivity or the Fredholm property, nor treat unbounded
transverse operators on a strip.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A (first-order Fredholm operators).
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).
-/

public section

namespace TauCeti

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {u : ℝ → E}

/-- The energy identity for `d/ds + A(s)`. The coefficient derivative contributes with a minus
sign; symmetry is needed only for the coefficients, not assumed separately for their derivative. -/
theorem integral_norm_deriv_add_sq_eq (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) =
      (∫ s, ‖deriv u s‖ ^ 2) + (∫ s, ‖A s (u s)‖ ^ 2) -
        ∫ s, ⟪u s, deriv A s (u s)⟫_ℝ := by
  -- Compact support makes every term in the integration-by-parts identity integrable.
  have hAu : HasCompactSupport (fun s ↦ A s (u s)) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with s hs
    simp only [Pi.zero_apply, hs, map_zero]
  have hpot : HasCompactSupport (fun s ↦ ⟪u s, A s (u s)⟫_ℝ) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with s hs
    simp only [Pi.zero_apply, hs, map_zero, inner_zero_left]
  have hcross : HasCompactSupport (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hAu ⊢
    filter_upwards [hAu] with s hs
    simp only [Pi.zero_apply, hs, inner_zero_right]
  have hcorr : HasCompactSupport (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with s hs
    simp only [Pi.zero_apply, hs, inner_zero_left]
  have hcD : HasCompactSupport (fun s ↦ ‖deriv u s‖ ^ 2) :=
    hc.deriv.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hcA : HasCompactSupport (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    hAu.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiD : Integrable (fun s ↦ ‖deriv u s‖ ^ 2) :=
    (hu.continuous_deriv_one.norm.pow 2).integrable_of_hasCompactSupport hcD
  have hiA : Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    ((hA.continuous.clm_apply hu.continuous).norm.pow 2).integrable_of_hasCompactSupport hcA
  have hiCross : Integrable (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous_deriv_one.inner (hA.continuous.clm_apply hu.continuous)) hcross
  have hiCorr : Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous.inner (hA.continuous_deriv_one.clm_apply hu.continuous)) hcorr
  -- Differentiate the potential `⟪u, A u⟫`, then integrate its derivative over the line.
  have hder (s : ℝ) : HasDerivAt (fun s ↦ ⟪u s, A s (u s)⟫_ℝ)
      (2 * ⟪deriv u s, A s (u s)⟫_ℝ + ⟪u s, deriv A s (u s)⟫_ℝ) s := by
    convert (hu.differentiable one_ne_zero s).hasDerivAt.inner ℝ
      ((hA.differentiable one_ne_zero s).hasDerivAt.clm_apply
        (hu.differentiable one_ne_zero s).hasDerivAt) using 1
    simp only [inner_add_right]
    rw [← (hsym s).apply_clm (u s) (deriv u s),
      real_inner_comm (A s (u s)) (deriv u s)]
    ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hder
    ((hiCross.const_mul 2).add hiCorr)
    ((hu.inner ℝ (hA.clm_apply hu)).continuous.integrable_of_hasCompactSupport hpot)
  rw [integral_add (hiCross.const_mul 2) hiCorr, integral_const_mul] at hzero
  have hexpand : (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) =
      (∫ s, ‖deriv u s‖ ^ 2) + 2 * (∫ s, ⟪deriv u s, A s (u s)⟫_ℝ) +
        ∫ s, ‖A s (u s)‖ ^ 2 := by
    simp only [norm_add_sq_real]
    have hiSum : Integrable (fun s ↦ ‖deriv u s‖ ^ 2 + 2 * ⟪deriv u s, A s (u s)⟫_ℝ) :=
      hiD.add (hiCross.const_mul 2)
    rw [integral_add hiSum hiA, integral_add hiD (hiCross.const_mul 2), integral_const_mul]
  linarith

/-- A spectral gap and a bound on the coefficient derivative give a coercive estimate for a
compactly supported path. Both bounds need hold only where the path is nonzero. The estimate is
useful when `β < α²`, but is valid without that extra hypothesis. -/
theorem integral_deriv_sq_add_mul_norm_sq_le (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {α β : ℝ} (hα : 0 ≤ α)
    (hgap : ∀ s ∈ Function.support u, α * ‖u s‖ ≤ ‖A s (u s)‖)
    (hsmall : ∀ s ∈ Function.support u, ⟪u s, deriv A s (u s)⟫_ℝ ≤ β * ‖u s‖ ^ 2) :
    (∫ s, ‖deriv u s‖ ^ 2) + (α ^ 2 - β) * (∫ s, ‖u s‖ ^ 2) ≤
      ∫ s, ‖deriv u s + A s (u s)‖ ^ 2 := by
  have hAu : HasCompactSupport (fun s ↦ A s (u s)) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with s hs
    simp only [Pi.zero_apply, hs, map_zero]
  have hcorr : HasCompactSupport (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with s hs
    simp only [Pi.zero_apply, hs, inner_zero_left]
  have hcu : HasCompactSupport (fun s ↦ ‖u s‖ ^ 2) :=
    hc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hcA : HasCompactSupport (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    hAu.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiu : Integrable (fun s ↦ ‖u s‖ ^ 2) :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hcu
  have hiA : Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    ((hA.continuous.clm_apply hu.continuous).norm.pow 2).integrable_of_hasCompactSupport hcA
  have hiCorr : Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous.inner (hA.continuous_deriv_one.clm_apply hu.continuous)) hcorr
  have h₁ : α ^ 2 * (∫ s, ‖u s‖ ^ 2) ≤ ∫ s, ‖A s (u s)‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hiu.const_mul _) hiA
    intro s
    by_cases hs : u s = 0
    · simp only [hs, map_zero, norm_zero, zero_pow two_ne_zero, mul_zero, le_refl]
    · simpa only [mul_pow] using
        pow_le_pow_left₀ (mul_nonneg hα (norm_nonneg _)) (hgap s hs) 2
  have h₂ : (∫ s, ⟪u s, deriv A s (u s)⟫_ℝ) ≤ β * ∫ s, ‖u s‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono hiCorr (hiu.const_mul _)
    intro s
    by_cases hs : u s = 0
    · simp only [hs, inner_zero_left, norm_zero, zero_pow two_ne_zero, mul_zero, le_refl]
    · exact hsmall s hs
  rw [integral_norm_deriv_add_sq_eq hA hsym hu hc]
  nlinarith

/-- **Coercivity at infinity.** If the symmetric coefficients tend in operator norm to operators
with a common positive lower bound, and their derivative tends to zero at both ends, then
`d/ds + A(s)` controls the `L²` value and derivative of every compactly supported `C¹` path
supported outside one fixed compact interval. In finite dimension, invertible limits supply the
required lower bound. -/
theorem exists_pos_forall_integral_deriv_sq_add_norm_sq_le
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0)) :
    ∃ R > 0, ∀ (u : ℝ → E), ContDiff ℝ 1 u → HasCompactSupport u →
      Function.support u ⊆ {s | R ≤ |s|} →
      (∫ s, ‖deriv u s‖ ^ 2) + (α ^ 2 / 8) * (∫ s, ‖u s‖ ^ 2) ≤
        ∫ s, ‖deriv u s + A s (u s)‖ ^ 2 := by
  have hhalf : 0 < α / 2 := by positivity
  have heighth : 0 < α ^ 2 / 8 := by positivity
  have hpos : ∀ᶠ s in atTop, ‖A s - Aplus‖ < α / 2 ∧ ‖deriv A s‖ < α ^ 2 / 8 := by
    have h₁ := htop (Metric.ball_mem_nhds Aplus hhalf)
    have h₂ := hdtop (Metric.ball_mem_nhds 0 heighth)
    filter_upwards [h₁, h₂] with s hs hd
    simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] using And.intro hs hd
  have hneg : ∀ᶠ s in atBot, ‖A s - Aminus‖ < α / 2 ∧ ‖deriv A s‖ < α ^ 2 / 8 := by
    have h₁ := hbot (Metric.ball_mem_nhds Aminus hhalf)
    have h₂ := hdbot (Metric.ball_mem_nhds 0 heighth)
    filter_upwards [h₁, h₂] with s hs hd
    simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] using And.intro hs hd
  obtain ⟨rplus, hrplus⟩ := eventually_atTop.mp hpos
  obtain ⟨rminus, hrminus⟩ := eventually_atBot.mp hneg
  let R := max 1 (max rplus (-rminus))
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- The two limiting gaps persist under an operator-norm perturbation of size `α / 2`.
  have htail : ∀ s, R ≤ |s| →
      (∀ v, α / 2 * ‖v‖ ≤ ‖A s v‖) ∧ ‖deriv A s‖ ≤ α ^ 2 / 8 := by
    intro s hs
    have hnear : ∃ B : E →L[ℝ] E,
        (∀ v, α * ‖v‖ ≤ ‖B v‖) ∧ ‖A s - B‖ ≤ α / 2 ∧ ‖deriv A s‖ ≤ α ^ 2 / 8 := by
      rcases le_or_gt 0 s with hsign | hsign
      · have hsp : rplus ≤ s := by
          have : rplus ≤ R := (le_max_left _ _).trans (le_max_right _ _)
          rw [abs_of_nonneg hsign] at hs
          exact this.trans hs
        exact ⟨Aplus, hplus, (hrplus s hsp).1.le, (hrplus s hsp).2.le⟩
      · have hsm : s ≤ rminus := by
          have : -rminus ≤ R := (le_max_right _ _).trans (le_max_right _ _)
          rw [abs_of_neg hsign] at hs
          linarith
        exact ⟨Aminus, hminus, (hrminus s hsm).1.le, (hrminus s hsm).2.le⟩
    obtain ⟨B, hB, hdiff, hd⟩ := hnear
    refine ⟨fun v ↦ ?_, hd⟩
    have htriangle : ‖B v‖ ≤ ‖A s v‖ + ‖A s - B‖ * ‖v‖ := by
      calc
        ‖B v‖ = ‖A s v - (A s - B) v‖ := by simp only [sub_apply, sub_sub_cancel]
        _ ≤ ‖A s v‖ + ‖(A s - B) v‖ := norm_sub_le _ _
        _ ≤ ‖A s v‖ + ‖A s - B‖ * ‖v‖ := add_le_add (le_refl _) ((A s - B).le_opNorm v)
    have hbound := mul_le_mul_of_nonneg_right hdiff (norm_nonneg v)
    nlinarith [hB v]
  -- Apply the energy estimate with gap `α / 2` and derivative bound `α² / 8`.
  refine ⟨R, hRpos, fun u hu hc hs ↦ ?_⟩
  have hest := integral_deriv_sq_add_mul_norm_sq_le hA hsym hu hc hhalf.le
    (fun s hu ↦ (htail s (hs hu)).1 (u s))
    (β := α ^ 2 / 8) (fun s hu ↦ ?_)
  · have hcoeff : (α / 2) ^ 2 - α ^ 2 / 8 = α ^ 2 / 8 := by ring
    rwa [hcoeff] at hest
  · calc
      ⟪u s, deriv A s (u s)⟫_ℝ ≤ ‖u s‖ * ‖deriv A s (u s)‖ := real_inner_le_norm _ _
      _ ≤ ‖u s‖ * (‖deriv A s‖ * ‖u s‖) :=
        mul_le_mul_of_nonneg_left ((deriv A s).le_opNorm (u s)) (norm_nonneg _)
      _ ≤ (α ^ 2 / 8) * ‖u s‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right (htail s (hs hu)).2 (sq_nonneg ‖u s‖)]

end TauCeti
