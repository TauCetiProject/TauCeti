/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Landau's theorem for Laplace transforms

Let `f : ℝ → ℝ` be nonnegative at almost every `u > u₀` and let its one-sided Laplace transform
converge to `F s` on the half-plane `a < re s`. Landau's theorem says that the transform cannot
stop converging at a point where `F` is regular: if `F` agrees, on the part of the ball
`ball a r` right of `a`, with a function `F₁` holomorphic on the whole ball, then the transform of
`f` converges on the larger half-plane `a - r < re s`, and its value on `ball a r` is `F₁`. In
other words the real point of the line of convergence of the transform of an eventually
nonnegative function is a singularity of the transform.

The proof expands `F₁` in its Taylor series at a real point `b` slightly right of `a`. The Taylor
coefficients of a Laplace transform are Laplace transforms: the `n`-th derivative of `F` is the
transform of `u ↦ (-u) ^ n • f u`. At a real point `σ < b` of the disc of convergence the Taylor
series is therefore the series of the integrals of
`u ↦ ((b - σ) * u) ^ n / n ! * (exp (-b * u) * f u)`, whose terms are nonnegative right of `u₀`
and whose pointwise sum is `exp (-σ * u) * f u`; so that function is integrable.

## Main results

* `TauCeti.hasLaplace_neg_pow_smul_iteratedDeriv`: if `F` is the Laplace transform of `f` on an
  open set, then `iteratedDeriv n F` is there the Laplace transform of `u ↦ (-u) ^ n • f u`.
* `TauCeti.integrableOn_cexp_neg_mul_ofReal_of_ae_nonneg`: **Landau's theorem**, convergence of the
  transform on `a - r < re s`.
* `TauCeti.hasLaplace_ofReal_of_ae_nonneg_of_mem_ball`: **Landau's theorem**, the value `F₁ s` of
  the transform on `ball a r`.

## References

* E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. 61 (1905).
* D. V. Widder, *The Laplace Transform*, Chapter II, Theorem 5b.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Nat Topology

namespace TauCeti

/-- **Derivatives of a Laplace transform.** If `F` is the one-sided Laplace transform of `f` on an
open set `U`, then on `U` the `n`-th derivative of `F` is the Laplace transform of
`u ↦ (-u) ^ n • f u`. -/
theorem hasLaplace_neg_pow_smul_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {U : Set ℂ} (hU : IsOpen U) (hF : ∀ s ∈ U, HasLaplace f s (F s))
    (n : ℕ) {s : ℂ} (hs : s ∈ U) :
    HasLaplace (fun u : ℝ ↦ (-(u : ℂ)) ^ n • f u) s (iteratedDeriv n F s) := by
  induction n generalizing s with
  | zero => simpa only [pow_zero, one_smul, iteratedDeriv_zero] using hF s hs
  | succ n ih =>
    obtain ⟨z', hz', hder⟩ := exists_hasLaplace_neg_smul_and_hasDerivAt
      (Filter.eventually_of_mem (hU.mem_nhds hs) fun w hw ↦ ih hw)
    rw [iteratedDeriv_succ, hder.deriv]
    have hfun : (fun u : ℝ ↦ (-(u : ℂ)) ^ (n + 1) • f u) =
        fun u : ℝ ↦ -(u : ℂ) • (-(u : ℂ)) ^ n • f u :=
      funext fun u ↦ by rw [pow_succ', mul_smul]
    rw [hfun]
    exact hz'

/-- A pointwise sum of integrable real functions is integrable when the integrals of their
absolute values are summable. -/
private theorem integrable_of_hasSum_of_summable_integral_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {G : ℕ → α → ℝ} {g : α → ℝ} (hG : ∀ n, Integrable (G n) μ)
    (hsum : Summable fun n ↦ ∫ x, ‖G n x‖ ∂μ) (hg : ∀ᵐ x ∂μ, HasSum (fun n ↦ G n x) (g x)) :
    Integrable g μ := by
  have hmeas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N ↦ (integrable_finsetSum (Finset.range N) fun n _ ↦ hG n).aestronglyMeasurable)
      (hg.mono fun x hx ↦ hx.tendsto_sum_nat)
  have hle : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ∑' n, ‖G n x‖ₑ := by
    filter_upwards [hg] with x hx
    rw [← hx.tsum_eq]
    exact eNorm_tsum_le_tsum_eNorm
  refine ⟨hmeas, hasFiniteIntegral_iff_eNorm.2 ?_⟩
  calc ∫⁻ x, ‖g x‖ₑ ∂μ ≤ ∫⁻ x, ∑' n, ‖G n x‖ₑ ∂μ := lintegral_mono_ae hle
    _ = ∑' n, ∫⁻ x, ‖G n x‖ₑ ∂μ := lintegral_tsum fun n ↦ (hG n).aestronglyMeasurable.eNorm
    _ = ∑' n, ENNReal.ofReal (∫ x, ‖G n x‖ ∂μ) :=
      tsum_congr fun n ↦ (ofReal_integral_norm_eq_lintegral_eNorm (hG n)).symm
    _ = ENNReal.ofReal (∑' n, ∫ x, ‖G n x‖ ∂μ) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- If the integrals of `u ↦ (t * u) ^ n / n ! * g u` over `(0, ∞)` are summable and `g` is
nonnegative at almost every `u > u₀`, then the integrals of their absolute values are summable. -/
private theorem summable_integral_norm_pow_div_factorial_mul {g : ℝ → ℝ} {t u₀ : ℝ} (ht : 0 ≤ t)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), u₀ < u → 0 ≤ g u)
    (hint : ∀ n : ℕ, Integrable (fun u ↦ (t * u) ^ n / (n ! : ℝ) * g u) (volume.restrict (Ioi 0)))
    (hsum : Summable fun n : ℕ ↦ ∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * g u) :
    Summable fun n : ℕ ↦ ∫ u in Ioi 0, ‖(t * u) ^ n / (n ! : ℝ) * g u‖ := by
  have hg0 : Integrable g (volume.restrict (Ioi 0)) := by simpa using hint 0
  have hbound : ∀ n : ℕ, ∫ u in Ioi 0, ‖(t * u) ^ n / (n ! : ℝ) * g u‖ ≤
      (∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * g u) +
        2 * ((t * |u₀|) ^ n / (n ! : ℝ)) * ∫ u in Ioi 0, ‖g u‖ := by
    intro n
    rw [← integral_const_mul, ← integral_add (hint n) (hg0.norm.const_mul _)]
    refine integral_mono_ae (hint n).norm ((hint n).add (hg0.norm.const_mul _)) ?_
    filter_upwards [hg, ae_restrict_mem measurableSet_Ioi] with u hu (hu0 : 0 < u)
    have hc : 0 ≤ (t * u) ^ n / (n ! : ℝ) := by positivity
    have hC : 0 ≤ (t * |u₀|) ^ n / (n ! : ℝ) := by positivity
    simp only [Real.norm_eq_abs]
    rw [abs_mul ((t * u) ^ n / (n ! : ℝ)) (g u), abs_of_nonneg hc]
    rcases lt_or_ge u₀ u with h | h
    · rw [abs_of_nonneg (hu h)]
      linarith [mul_nonneg (mul_nonneg zero_le_two hC) (hu h)]
    · have hcC : (t * u) ^ n / (n ! : ℝ) ≤ (t * |u₀|) ^ n / (n ! : ℝ) := by
        gcongr
        exact h.trans (le_abs_self _)
      nlinarith [mul_le_mul_of_nonneg_right hcC (abs_nonneg (g u)),
        mul_le_mul_of_nonneg_left (neg_abs_le (g u)) hc]
  exact Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound
    (hsum.add (((Real.summable_pow_div_factorial (t * |u₀|)).mul_left 2).mul_right _))

/-- If the integrals of `u ↦ (t * u) ^ n / n ! * g u` over `(0, ∞)` are summable and `g` is
nonnegative at almost every `u > u₀`, then `u ↦ exp (t * u) * g u` is integrable on `(0, ∞)`. -/
private theorem integrable_exp_mul_of_summable_integral {g : ℝ → ℝ} {t u₀ : ℝ} (ht : 0 ≤ t)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), u₀ < u → 0 ≤ g u)
    (hint : ∀ n : ℕ, Integrable (fun u ↦ (t * u) ^ n / (n ! : ℝ) * g u) (volume.restrict (Ioi 0)))
    (hsum : Summable fun n : ℕ ↦ ∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * g u) :
    Integrable (fun u ↦ Real.exp (t * u) * g u) (volume.restrict (Ioi 0)) := by
  refine integrable_of_hasSum_of_summable_integral_norm hint
    (summable_integral_norm_pow_div_factorial_mul ht hg hint hsum) (.of_forall fun u ↦ ?_)
  have h0 : HasSum (fun n : ℕ ↦ (t * u) ^ n / (n ! : ℝ)) (Real.exp (t * u)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (t * u)
  exact h0.mul_right (g u)

section Landau

variable {f : ℝ → ℝ} {F F₁ : ℂ → ℂ} {a r u₀ : ℝ}

/-- The Taylor coefficients of a Laplace transform at a real point `b`, evaluated at `b - t`, are
the integrals of `u ↦ (t * u) ^ n / n ! * (exp (-b * u) * f u)`. -/
private theorem integrable_and_taylor_term_eq {b : ℝ}
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s (F s)) (hb : a < b) (t : ℝ)
    (n : ℕ) :
    Integrable (fun u ↦ (t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u))
        (volume.restrict (Ioi 0)) ∧
      (n ! : ℂ)⁻¹ • (-(t : ℂ)) ^ n • iteratedDeriv n F b =
        ((∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ) := by
  have hL := hasLaplace_neg_pow_smul_iteratedDeriv
    (isOpen_lt continuous_const Complex.continuous_re) hF n
    (show a < (b : ℂ).re by rwa [Complex.ofReal_re])
  have key : ∀ u : ℝ, ((n ! : ℂ)⁻¹ * (-(t : ℂ)) ^ n) *
      (Complex.exp (-(b : ℂ) * u) • ((-(u : ℂ)) ^ n • (f u : ℂ))) =
        (((t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ) := by
    intro u
    have hpow : (-(t : ℂ)) ^ n * (-(u : ℂ)) ^ n = ((t : ℂ) * u) ^ n := by
      rw [← mul_pow, neg_mul_neg]
    simp only [smul_eq_mul]
    push_cast
    rw [← hpow]
    ring
  have hc : Integrable
      (fun u : ℝ ↦ (((t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) :=
    (hL.integrable.const_mul ((n ! : ℂ)⁻¹ * (-(t : ℂ)) ^ n)).congr (.of_forall key)
  refine ⟨hc.re.congr (.of_forall fun u ↦ by
    simp only [RCLike.re_to_complex, Complex.ofReal_re]), ?_⟩
  rw [← hL.integral_eq, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← integral_const_mul,
    ← integral_complex_ofReal]
  exact integral_congr_ae (.of_forall key)

/-- Landau's theorem at a real point `σ` with `a - r < σ ≤ a`. -/
private theorem integrableOn_exp_neg_mul_of_ae_nonneg
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s (F s))
    (hF₁ : DifferentiableOn ℂ F₁ (ball (a : ℂ) r))
    (heq : ∀ s ∈ ball (a : ℂ) r, a < s.re → F₁ s = F s) {σ : ℝ} (hσ : a - r < σ) (hσa : σ ≤ a) :
    IntegrableOn (fun u ↦ Real.exp (-σ * u) * f u) (Ioi 0) := by
  obtain ⟨ε, hε⟩ : ∃ ε, ε = σ - (a - r) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = a + ε / 4 := ⟨_, rfl⟩
  have hab : a < b := by linarith
  -- The Taylor series of `F₁` at `b`, at the point `σ` of its disc of convergence.
  have hsub : ball (b : ℂ) (r - ε / 4) ⊆ ball (a : ℂ) r :=
    ball_subset_ball' (by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith)
  have hσmem : (σ : ℂ) ∈ ball (b : ℂ) (r - ε / 4) := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hsum := (Complex.hasSum_taylorSeries_on_ball (hF₁.mono hsub) hσmem).summable
  -- Its terms are the integrals of `u ↦ ((b - σ) * u) ^ n / n ! * (exp (-b * u) * f u)`.
  have hev : F₁ =ᶠ[𝓝 (b : ℂ)] F := by
    filter_upwards [isOpen_ball.mem_nhds (hsub (mem_ball_self (by linarith))),
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show a < (b : ℂ).re by rwa [Complex.ofReal_re])] with s hs hs' using heq s hs hs'
  have hσb : (σ : ℂ) - b = -((b - σ : ℝ) : ℂ) := by
    push_cast
    ring
  have hterm : ∀ n : ℕ, (n ! : ℂ)⁻¹ • (-((b - σ : ℝ) : ℂ)) ^ n • iteratedDeriv n F₁ b =
      ((∫ u in Ioi 0, ((b - σ) * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ) := by
    intro n
    rw [hev.iteratedDeriv_eq n]
    exact (integrable_and_taylor_term_eq hF hab (b - σ) n).2
  simp_rw [hσb, hterm] at hsum
  -- Those functions are nonnegative right of `u₀`, and their sum is `exp (-σ * u) * f u`.
  have hf' : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), u₀ < u → 0 ≤ Real.exp (-b * u) * f u :=
    (ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioi).1 hf)).mono
      fun u hu h ↦ mul_nonneg (Real.exp_nonneg _) (hu h)
  refine Integrable.congr (integrable_exp_mul_of_summable_integral (by linarith) hf'
    (fun n ↦ (integrable_and_taylor_term_eq hF hab (b - σ) n).1)
    (Complex.summable_ofReal.1 hsum)) (.of_forall fun u ↦ ?_)
  change Real.exp ((b - σ) * u) * (Real.exp (-b * u) * f u) = Real.exp (-σ * u) * f u
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Landau's theorem for Laplace transforms**, convergence. Let `f` be nonnegative at almost
every `u > u₀`, with Laplace transform `F` on the half-plane `a < re s`. If `F` agrees there with
a function `F₁` holomorphic on `ball a r`, then the Laplace transform of `f` converges on the
half-plane `a - r < re s`. -/
theorem integrableOn_cexp_neg_mul_ofReal_of_ae_nonneg
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s (F s))
    (hF₁ : DifferentiableOn ℂ F₁ (ball (a : ℂ) r))
    (heq : ∀ s ∈ ball (a : ℂ) r, a < s.re → F₁ s = F s) {s : ℂ} (hs : a - r < s.re) :
    IntegrableOn (fun u : ℝ ↦ Complex.exp (-s * u) • (f u : ℂ)) (Ioi 0) := by
  rcases lt_or_ge a s.re with h | h
  · exact (hF s h).integrableOn
  · have hσ := integrableOn_exp_neg_mul_of_ae_nonneg hf hF hF₁ heq hs h
    have hc : Integrable (fun u : ℝ ↦ ((Real.exp (-s.re * u) * f u : ℝ) : ℂ))
        (volume.restrict (Ioi 0)) := Integrable.ofReal hσ
    have h0 : Integrable (fun u : ℝ ↦ Complex.exp (-(s.re : ℂ) * u) • (f u : ℂ))
        (volume.restrict (Ioi 0)) := hc.congr (.of_forall fun u ↦ by simp)
    exact h0.hasLaplace.integrableOn_of_re_le (by simp)

/-- **Landau's theorem for Laplace transforms**, the value. Let `f` be nonnegative at almost
every `u > u₀`, with Laplace transform `F` on the half-plane `a < re s`. If `F` agrees there with
a function `F₁` holomorphic on `ball a r`, then `F₁` is the Laplace transform of `f` on
`ball a r`. -/
theorem hasLaplace_ofReal_of_ae_nonneg_of_mem_ball
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hF : ∀ s : ℂ, a < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s (F s))
    (hF₁ : DifferentiableOn ℂ F₁ (ball (a : ℂ) r))
    (heq : ∀ s ∈ ball (a : ℂ) r, a < s.re → F₁ s = F s) {s : ℂ} (hs : s ∈ ball (a : ℂ) r) :
    HasLaplace (fun u ↦ (f u : ℂ)) s (F₁ s) := by
  have hr : 0 < r := pos_of_mem_ball hs
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ → ℂ,
      Φ = fun z ↦ ∫ u : ℝ in Ioi 0, Complex.exp (-z * u) • (f u : ℂ) := ⟨_, rfl⟩
  have hL : ∀ z : ℂ, a - r < z.re → HasLaplace (fun u ↦ (f u : ℂ)) z (Φ z) := by
    intro z hz
    rw [hΦ]
    exact Integrable.hasLaplace (integrableOn_cexp_neg_mul_ofReal_of_ae_nonneg hf hF hF₁ heq hz)
  have hre : ∀ z ∈ ball (a : ℂ) r, a - r < z.re := by
    intro z hz
    have h1 := (Complex.abs_re_le_norm (z - a)).trans_lt (mem_ball_iff_norm.1 hz)
    rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at h1
    linarith [h1.1]
  have hΦd : DifferentiableOn ℂ Φ (ball (a : ℂ) r) :=
    (differentiableOn_of_hasLaplace_re_gt hL).mono hre
  -- `Φ` and `F₁` agree near a point of the ball right of `a`, hence on the ball.
  have hz₀ : ((a + r / 2 : ℝ) : ℂ) ∈ ball (a : ℂ) r := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hz₀re : a < ((a + r / 2 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
  have hev : Φ =ᶠ[𝓝 ((a + r / 2 : ℝ) : ℂ)] F₁ := by
    filter_upwards [isOpen_ball.mem_nhds hz₀,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀re] with z hz hz'
    rw [heq z hz hz']
    exact (hL z (hre z hz)).unique (hF z hz')
  have hEq := (hΦd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hF₁.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected hz₀ hev
  rw [← hEq hs]
  exact hL s (hre s hs)

end Landau

end TauCeti
