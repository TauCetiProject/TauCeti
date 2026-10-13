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

-- The two integrable coefficient terms shared by the identity and the estimate.
private theorem integrable_energy_terms (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) ∧
      Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) := by
  have hAu : HasCompactSupport (fun s ↦ A s (u s)) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcorr : HasCompactSupport (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcA : HasCompactSupport (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    hAu.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiA : Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    ((hA.continuous.clm_apply hu.continuous).norm.pow 2).integrable_of_hasCompactSupport hcA
  have hiCorr : Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous.inner (hA.continuous_deriv_one.clm_apply hu.continuous)) hcorr
  exact ⟨hiA, hiCorr⟩

/-- The energy identity for `d/ds + A(s)`. The coefficient derivative contributes with a minus
sign; symmetry is needed only for the coefficients, not assumed separately for their derivative. -/
theorem integral_norm_deriv_add_sq_eq (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) =
      (∫ s, ‖deriv u s‖ ^ 2) + (∫ s, ‖A s (u s)‖ ^ 2) -
        ∫ s, ⟪u s, deriv A s (u s)⟫_ℝ := by
  -- Compact support makes every term in the integration-by-parts identity integrable.
  obtain ⟨hiA, hiCorr⟩ := integrable_energy_terms hA hu hc
  have hpot : HasCompactSupport (fun s ↦ ⟪u s, A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcross : HasCompactSupport (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcD : HasCompactSupport (fun s ↦ ‖deriv u s‖ ^ 2) :=
    hc.deriv.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiD : Integrable (fun s ↦ ‖deriv u s‖ ^ 2) :=
    (hu.continuous_deriv_one.norm.pow 2).integrable_of_hasCompactSupport hcD
  have hiCross : Integrable (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous_deriv_one.inner (hA.continuous.clm_apply hu.continuous)) hcross
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
theorem integral_norm_deriv_sq_add_mul_integral_norm_sq_le (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {α β : ℝ} (hα : 0 ≤ α)
    (hgap : ∀ s ∈ Function.support u, α * ‖u s‖ ≤ ‖A s (u s)‖)
    (hsmall : ∀ s ∈ Function.support u, ⟪u s, deriv A s (u s)⟫_ℝ ≤ β * ‖u s‖ ^ 2) :
    (∫ s, ‖deriv u s‖ ^ 2) + (α ^ 2 - β) * (∫ s, ‖u s‖ ^ 2) ≤
      ∫ s, ‖deriv u s + A s (u s)‖ ^ 2 := by
  obtain ⟨hiA, hiCorr⟩ := integrable_energy_terms hA hu hc
  have hcu : HasCompactSupport (fun s ↦ ‖u s‖ ^ 2) :=
    hc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiu : Integrable (fun s ↦ ‖u s‖ ^ 2) :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hcu
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

-- The eventual bounds needed for the energy estimate at either end of the line.
private theorem eventually_energy_bounds {l : Filter ℝ} {B : E →L[ℝ] E} {α : ℝ}
    (hα : 0 < α) (hB : ∀ v, α * ‖v‖ ≤ ‖B v‖)
    (hlim : Tendsto A l (𝓝 B)) (hdlim : Tendsto (deriv A) l (𝓝 0)) :
    ∀ᶠ s in l, (∀ v, α / 2 * ‖v‖ ≤ ‖A s v‖) ∧ ‖deriv A s‖ ≤ α ^ 2 / 8 := by
  have h₁ := hlim (Metric.ball_mem_nhds B (by positivity : 0 < α / 2))
  have h₂ := hdlim (Metric.ball_mem_nhds 0 (by positivity : 0 < α ^ 2 / 8))
  filter_upwards [h₁, h₂] with s hs hd
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] at hs hd
  refine ⟨fun v ↦ ?_, hd.le⟩
  have hdiff := ((A s - B).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hs.le (norm_nonneg v))
  rw [sub_apply] at hdiff
  nlinarith [hB v, norm_sub_norm_le (B v) (A s v), norm_sub_rev (B v) (A s v)]

/-- **Coercivity at infinity.** If the symmetric coefficients tend in operator norm to operators
with a common positive lower bound, and their derivative tends to zero at both ends, then
`d/ds + A(s)` controls the `L²` value and derivative of every compactly supported `C¹` path
supported outside one fixed compact interval. In finite dimension, invertible limits supply the
required lower bound. -/
theorem exists_pos_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le
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
  have hpos := eventually_energy_bounds hα hplus htop hdtop
  have hneg := eventually_energy_bounds hα hminus hbot hdbot
  obtain ⟨rplus, hrplus⟩ := eventually_atTop.mp hpos
  obtain ⟨rminus, hrminus⟩ := eventually_atBot.mp hneg
  let R := max 1 (max rplus (-rminus))
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- The two limiting gaps persist under an operator-norm perturbation of size `α / 2`.
  have htail : ∀ s, R ≤ |s| →
      (∀ v, α / 2 * ‖v‖ ≤ ‖A s v‖) ∧ ‖deriv A s‖ ≤ α ^ 2 / 8 := by
    intro s hs
    rcases le_or_gt 0 s with hsign | hsign
    · have hsp : rplus ≤ s := by
        have : rplus ≤ R := (le_max_left _ _).trans (le_max_right _ _)
        rw [abs_of_nonneg hsign] at hs
        exact this.trans hs
      exact hrplus s hsp
    · have hsm : s ≤ rminus := by
        have : -rminus ≤ R := (le_max_right _ _).trans (le_max_right _ _)
        rw [abs_of_neg hsign] at hs
        linarith
      exact hrminus s hsm
  -- Apply the energy estimate with gap `α / 2` and derivative bound `α² / 8`.
  refine ⟨R, hRpos, fun u hu hc hs ↦ ?_⟩
  have hest := integral_norm_deriv_sq_add_mul_integral_norm_sq_le hA hsym hu hc hhalf.le
    (fun s hu ↦ (htail s (hs hu)).1 (u s))
    (β := α ^ 2 / 8) (fun s hu ↦ ?_)
  · have hcoeff : (α / 2) ^ 2 - α ^ 2 / 8 = α ^ 2 / 8 := by ring
    rwa [hcoeff] at hest
  · grw [real_inner_le_norm, (deriv A s).le_opNorm, (htail s (hs hu)).2]
    ring_nf
    rfl

end TauCeti
