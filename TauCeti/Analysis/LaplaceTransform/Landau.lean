/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.LaplaceTransform.GammaKernel
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Integral.Exp.Moment

/-!
# Landau's theorem for Laplace transforms

Let `f : ℝ → ℝ` be nonnegative at almost every `u > u₀`, let `0 < r`, and let `F₁` be holomorphic
on `ball a r`. Suppose that at every point `s` of the ball with `a < re s` the one-sided Laplace
transform of `f` converges, to `F₁ s`. Landau's theorem says that then the transform of `f`
converges on the half-plane `a - r < re s`, which strictly contains `a < re s`, and that its value
on `ball a r` is `F₁`. In other words, if the abscissa of convergence `σ_c` of the transform of an
eventually nonnegative function is finite, then the transform has no holomorphic extension to any
disc about the real point `σ_c`: the real point of the line of convergence is a singularity.

The proof expands `F₁` in its Taylor series at a real point `b` slightly right of `a`. The Taylor
coefficients of a Laplace transform are Laplace transforms
(`TauCeti.hasLaplace_pow_div_factorial_smul_iteratedDeriv`). At a real point `σ` of the disc of
convergence the Taylor series is therefore the series of the integrals of
`G n u = ((b - σ) * u) ^ n / n ! * (exp (-b * u) * f u)`, whose pointwise sum is
`exp (-σ * u) * f u`. Right of `u₀` the `G n` have constant sign, so their absolute integrals there
are bounded by the absolute values of their integrals plus the contribution of `(0, u₀]`, which is
at most `2 * (|b - σ| * |u₀|) ^ n / n ! * ∫ |G 0|`, a summable sequence. The integrals of the
`|G n|` are therefore summable (`TauCeti.summable_integral_norm_pow_div_factorial_mul`) and the
pointwise sum is integrable (`TauCeti.integrable_exp_mul_of_summable_integral`).

## Main results

* `TauCeti.integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg`: **Landau's theorem**, convergence
  of the transform on `a - r < re s`.
* `TauCeti.hasLaplace_ofReal_of_ae_nonneg_of_mem_ball`: **Landau's theorem**, the value `F₁ s` of
  the transform on `ball a r`.
* `TauCeti.exists_setIntegral_Ioi_sdiff_Icc_pow_mul_exp_neg_mul_div_factorial_le`: the Gamma-kernel
  estimate for the windowed form: for every `δ > 0` there are `σ > 2` and `C` such that for every
  `U` some `k ≥ U` makes the mass of `u ^ k * exp (-((σ - 2) * u)) / k !` off `[U, (1 + δ) U]` at
  most `C / σ ^ k`.

## References

* E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. 61 (1905).
* D. V. Widder, *The Laplace Transform*, Chapter II, Theorem 5b.
* `TauCeti.LSeries.landau` in `TauCeti.NumberTheory.LSeries.Landau` is the corresponding theorem for
  Dirichlet series with nonnegative coefficients, proved by the same Taylor-series argument; there
  the Taylor coefficients are series rather than integrals.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Nat Topology

namespace TauCeti

/-! ### The Gamma-kernel window estimate used by the windowed form of Landau's theorem -/

open Real in
/-- **Mass of the Gamma kernel off a window.** For every `δ > 0` there are `σ > 2` and `C` such
that for every real `U` some natural number `k ≥ U` bounds the mass of the Gamma kernel
`u ^ k * exp (-((σ - 2) * u)) / k !` on `(0, ∞) \ [U, (1 + δ) U]` by `C σ^(-k)`. The proof
applies the Chernoff bound `TauCeti.setIntegral_Ioi_sdiff_Icc_pow_mul_exp_neg_mul_div_factorial_le`
with the same tilt `l` for both tails and suitable `l`, `σ` and `k`. The window estimate for
`U ≥ 1` and this choice of parameters are `Deduction.landau_tails` in L. Alpöge's Lean
formalization of the Riemann hypothesis for Dirichlet L-functions
(<https://github.com/leanprover-community/riemann-hypothesis>); this theorem extends the estimate
to every real `U` (for `U < 0` it takes `k = 0`). -/
theorem exists_setIntegral_Ioi_sdiff_Icc_pow_mul_exp_neg_mul_div_factorial_le {δ : ℝ}
    (hδ : 0 < δ) : ∃ σ > 2, ∃ C, ∀ U : ℝ, ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi 0 \ Icc U ((1 + δ) * U), u ^ k * exp (-((σ - 2) * u)) / k ! ≤ C / σ ^ k := by
  -- `l = 2 + 6 / δ`, `σ = l (1 + δ) (l + 2)` (atoms with defining equations); for `0 ≤ U`, apply
  -- the Chernoff bound with `k = ⌈(1 + δ / 2) σ U⌉`, `a = σ - 2`, `V = (1 + δ) U`; else `k = 0`.
  obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = 2 + 6 / δ := ⟨_, rfl⟩
  have hlδ : δ * l = 2 * δ + 6 := by rw [hl_def]; field_simp
  have hl : 2 < l := by linarith [div_pos (by norm_num : (0 : ℝ) < 6) hδ]
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = l * (1 + δ) * (l + 2) := ⟨_, rfl⟩
  have hlδl : 0 < l * δ * (l + 2) := by positivity
  have hd : 0 < σ - 2 - l := by linarith [mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 2) hl]
  have he : 0 < σ - 2 + l := by linarith
  have hy : 0 ≤ σ / (σ - 2 - l) - 1 := by rw [sub_nonneg, le_div_iff₀ hd]; linarith
  refine ⟨σ, by linarith, exp (σ / (σ - 2 - l) - 1) / (σ - 2 - l) + 1 / (σ - 2 + l),
    fun U ↦ ?_⟩
  rcases lt_or_ge U 0 with hU | hU
  · refine ⟨0, by simpa using hU.le, ?_⟩
    calc _ ≤ ((σ - 2) ^ (0 + 1))⁻¹ :=
          setIntegral_pow_mul_exp_neg_mul_div_factorial_le 0 (by linarith)
            (ae_of_all _ sdiff_subset)
      _ ≤ exp (σ / (σ - 2 - l) - 1) / (σ - 2 - l) := by
          rw [zero_add, pow_one, inv_eq_one_div]
          exact div_le_div₀ (exp_pos _).le (one_le_exp hy) hd (by linarith)
      _ ≤ _ := by rw [pow_zero, div_one, le_add_iff_nonneg_right]; positivity
  have hσ1 : 1 ≤ (1 + δ / 2) * σ := by linarith [mul_pos hδ (by linarith : (0 : ℝ) < σ)]
  set k := ⌈(1 + δ / 2) * σ * U⌉₊
  have hk1 : (1 + δ / 2) * σ * U ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < (1 + δ / 2) * σ * U + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) hU)
  refine ⟨k, (le_mul_of_one_le_left hU hσ1).trans hk1, ?_⟩
  -- The two identities that fix `l = 2 + 6 / δ`: they make the rates of the two tails match.
  have hup : (1 + δ / 2) * (l + 2) = l * (1 + δ) - 1 := by linear_combination -hlδ / 2
  have hlow : (1 + δ / 2) * (l - 2) = l + 1 := by linear_combination hlδ / 2
  have h1 : (1 + δ / 2) * σ * (σ / (σ - 2 - l) - 1) = l * (1 + δ) := by
    rw [div_sub_one hd.ne', mul_div_assoc', div_eq_iff hd.ne']
    linear_combination σ * hup - hσ
  have h2 : (1 + δ / 2) * σ * (σ / (σ - 2 + l) - 1) ≤ -l := by
    rw [div_sub_one he.ne', mul_div_assoc', div_le_iff₀ he]
    -- By `hlow` the left side is `-(l + 1) σ`, and `l ^ 2 - 2 l ≤ σ`.
    linarith [congrArg (· * σ) hlow, hσ, hlδl]
  calc _ ≤ _ := setIntegral_Ioi_sdiff_Icc_pow_mul_exp_neg_mul_div_factorial_le k (l₂ := l)
          (by linarith) (by linarith : l < σ - 2) (by linarith) U ((1 + δ) * U)
    _ ≤ exp (σ / (σ - 2 - l) - 1) / σ ^ k / (σ - 2 - l) + exp 0 / σ ^ k / (σ - 2 + l) := by
        simp only [pow_succ, ← div_eq_mul_inv, ← div_div]
        gcongr ?_ / _ + ?_ / _
        · refine exp_div_pow_le_exp_div_pow k (by linarith) hd.le ?_
          -- `k y ≤ ((1 + δ / 2) σ U + 1) y = l (1 + δ) U + y` by `h1`.
          linarith [mul_le_mul_of_nonneg_right hk2.le hy, congrArg (· * U) h1]
        · refine exp_div_pow_le_exp_div_pow k (by linarith) he.le ?_
          have hz : σ / (σ - 2 + l) - 1 ≤ 0 := by rw [sub_nonpos, div_le_one he]; linarith
          -- `k z ≤ (1 + δ / 2) σ U z ≤ -l U` by `h2`.
          linarith [mul_le_mul_of_nonpos_right hk1 hz, mul_le_mul_of_nonneg_left h2 hU]
    _ = _ := by rw [exp_zero]; ring

section Landau

variable {f : ℝ → ℝ} {F₁ : ℂ → ℂ} {a r u₀ : ℝ}

/-- If `F₁` is the Laplace transform of `f` at the points of `ball a r` right of `a`, then it is
the transform near each such point. -/
private theorem eventually_hasLaplace_of_mem_ball
    (hF : ∀ z ∈ ball (a : ℂ) r, a < z.re → HasLaplace (fun u ↦ (f u : ℂ)) z (F₁ z)) {z : ℂ}
    (hz : z ∈ ball (a : ℂ) r) (hza : a < z.re) :
    ∀ᶠ w in 𝓝 z, HasLaplace (fun u ↦ (f u : ℂ)) w (F₁ w) := by
  filter_upwards [isOpen_ball.mem_nhds hz,
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hza] with w hw hw' using hF w hw hw'

/-- Let `F₁` be the Laplace transform of `f` near a real point `b`. For real `t`, the function
`u ↦ (t * u) ^ n / n ! * (exp (-b * u) * f u)` is integrable on `(0, ∞)`, and its integral is the
`n`-th term of the Taylor expansion of `F₁` about `b`, evaluated at `b - t`. -/
private theorem integrable_and_taylor_term_eq {b : ℝ}
    (hF : ∀ᶠ w in 𝓝 (b : ℂ), HasLaplace (fun u ↦ (f u : ℂ)) w (F₁ w)) (t : ℝ) (n : ℕ) :
    Integrable (fun u ↦ (t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u))
        (volume.restrict (Ioi 0)) ∧
      (n ! : ℂ)⁻¹ • (-(t : ℂ)) ^ n • iteratedDeriv n F₁ b =
        ((∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ) := by
  have hL := (hasLaplace_pow_div_factorial_smul_iteratedDeriv hF n).const_smul ((t : ℂ) ^ n)
  have key : ∀ u : ℝ, Complex.exp (-(b : ℂ) * u) • ((t : ℂ) ^ n • ((u : ℂ) ^ n / n !) • (f u : ℂ)) =
      (((t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ) := fun u ↦ by
    simp only [smul_eq_mul]
    push_cast
    ring
  have hc := hL.integrable.congr (.of_forall key)
  refine ⟨hc.re.congr (.of_forall fun u ↦ by
    simp only [RCLike.re_to_complex, Complex.ofReal_re]), ?_⟩
  have hI : ∫ u : ℝ in Ioi 0,
      Complex.exp (-(b : ℂ) * u) • ((t : ℂ) ^ n • ((u : ℂ) ^ n / n !) • (f u : ℂ)) =
        (t : ℂ) ^ n • ((-1) ^ n / n ! : ℂ) • iteratedDeriv n F₁ b := hL.integral_eq
  rw [← integral_complex_ofReal, ← integral_congr_ae (.of_forall key), hI]
  simp only [smul_eq_mul, neg_pow (t : ℂ)]
  ring

/-- **Landau's theorem about a real point.** Let `f` be nonnegative at almost every `u > u₀` and
let `F₁` be its Laplace transform near the real point `b`. If `F₁` is holomorphic on `ball b ρ`,
then the Laplace transform of `f` converges on the half-plane `b - ρ < re s`. -/
private theorem integrableOn_cexp_neg_mul_smul_ofReal_of_eventually_hasLaplace {b ρ : ℝ}
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hF : ∀ᶠ w in 𝓝 (b : ℂ), HasLaplace (fun u ↦ (f u : ℂ)) w (F₁ w))
    (hF₁ : DifferentiableOn ℂ F₁ (ball (b : ℂ) ρ)) {s : ℂ} (hs : b - ρ < s.re) :
    IntegrableOn (fun u : ℝ ↦ Complex.exp (-s * u) • (f u : ℂ)) (Ioi 0) := by
  rcases le_or_gt b s.re with hbs | hsb
  · exact hF.self_of_nhds.integrableOn_of_re_le (by rwa [Complex.ofReal_re])
  set σ := s.re
  -- The Taylor series of `F₁` at `b`, at the point `σ` of its disc of convergence.
  have hσmem : (σ : ℂ) ∈ ball (b : ℂ) ρ := by
    rw [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  have hsum := (Complex.hasSum_taylorSeries_on_ball hF₁ hσmem).summable
  -- Its terms are the integrals of `u ↦ ((b - σ) * u) ^ n / n ! * (exp (-b * u) * f u)`.
  have hσb : (σ : ℂ) - b = -((b - σ : ℝ) : ℂ) := by
    push_cast
    ring
  simp_rw [hσb, fun n ↦ (integrable_and_taylor_term_eq hF (b - σ) n).2,
    Complex.summable_ofReal] at hsum
  -- Those functions are nonnegative right of `u₀`, and their sum is `exp (-σ * u) * f u`.
  have hf' : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), u₀ < u → 0 ≤ Real.exp (-b * u) * f u :=
    (ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioi).1 hf)).mono
      fun u hu h ↦ mul_nonneg (Real.exp_nonneg _) (hu h)
  have hint := integrable_exp_mul_of_summable_integral hf'
    (fun n ↦ (integrable_and_taylor_term_eq hF (b - σ) n).1) hsum
  have hexp : ∀ u : ℝ, Real.exp ((b - σ) * u) * (Real.exp (-b * u) * f u) =
      Real.exp (-σ * u) * f u := fun u ↦ by
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  have hc : Integrable (fun u : ℝ ↦ ((Real.exp (-σ * u) * f u : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := (hint.congr (.of_forall hexp)).ofReal
  have hσint : Integrable (fun u : ℝ ↦ Complex.exp (-(σ : ℂ) * u) • (f u : ℂ))
      (volume.restrict (Ioi 0)) :=
    hc.congr (.of_forall fun u ↦ by
      simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg])
  exact hσint.hasLaplace.integrableOn_of_re_le (by rw [Complex.ofReal_re])

/-- **Landau's theorem for Laplace transforms**, convergence. Let `f` be nonnegative at almost
every `u > u₀`, let `0 < r`, and let `F₁` be holomorphic on `ball a r`. If at every `s ∈ ball a r`
with `a < re s` the Laplace transform of `f` converges to `F₁ s`, then the Laplace transform of `f`
converges on the half-plane `a - r < re s`. -/
theorem integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u) (hr : 0 < r)
    (hF₁ : DifferentiableOn ℂ F₁ (ball (a : ℂ) r))
    (hF : ∀ z ∈ ball (a : ℂ) r, a < z.re → HasLaplace (fun u ↦ (f u : ℂ)) z (F₁ z)) {s : ℂ}
    (hs : a - r < s.re) :
    IntegrableOn (fun u : ℝ ↦ Complex.exp (-s * u) • (f u : ℂ)) (Ioi 0) := by
  -- Expand about `b = a + ε / 4` on the disc of radius `r - ε / 4`, inside `ball a r`.
  obtain ⟨ε, hε, hεs, hεr⟩ : ∃ ε, 0 < ε ∧ a - r + ε ≤ s.re ∧ ε ≤ r :=
    ⟨min (s.re - (a - r)) r, lt_min (by linarith) hr,
      by linarith [min_le_left (s.re - (a - r)) r], min_le_right _ _⟩
  have hdist : dist ((a + ε / 4 : ℝ) : ℂ) (a : ℂ) = ε / 4 := by
    rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos (by linarith)]
  have hb : ((a + ε / 4 : ℝ) : ℂ) ∈ ball (a : ℂ) r := by
    rw [mem_ball, hdist]
    linarith
  have hbre : a < ((a + ε / 4 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  exact integrableOn_cexp_neg_mul_smul_ofReal_of_eventually_hasLaplace (ρ := r - ε / 4) hf
    (eventually_hasLaplace_of_mem_ball hF hb hbre)
    (hF₁.mono (ball_subset_ball' (by rw [hdist]; linarith))) (by linarith)

/-- **Landau's theorem for Laplace transforms**, the value. Let `f` be nonnegative at almost
every `u > u₀` and let `F₁` be holomorphic on `ball a r`. If at every `s ∈ ball a r` with
`a < re s` the Laplace transform of `f` converges to `F₁ s`, then `F₁` is the Laplace transform of
`f` on the whole of `ball a r`. -/
theorem hasLaplace_ofReal_of_ae_nonneg_of_mem_ball
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hF₁ : DifferentiableOn ℂ F₁ (ball (a : ℂ) r))
    (hF : ∀ z ∈ ball (a : ℂ) r, a < z.re → HasLaplace (fun u ↦ (f u : ℂ)) z (F₁ z)) {s : ℂ}
    (hs : s ∈ ball (a : ℂ) r) :
    HasLaplace (fun u ↦ (f u : ℂ)) s (F₁ s) := by
  have hr : 0 < r := pos_of_mem_ball hs
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ → ℂ,
      Φ = fun z ↦ ∫ u : ℝ in Ioi 0, Complex.exp (-z * u) • (f u : ℂ) := ⟨_, rfl⟩
  have hL : ∀ z : ℂ, a - r < z.re → HasLaplace (fun u ↦ (f u : ℂ)) z (Φ z) := fun z hz ↦
    hΦ ▸ (integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg hf hr hF₁ hF hz).integrable.hasLaplace
  have hre : ∀ z ∈ ball (a : ℂ) r, a - r < z.re := by
    intro z hz
    have h1 := (Complex.abs_re_le_norm (z - a)).trans_lt (mem_ball_iff_norm.1 hz)
    rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at h1
    linarith [h1.1]
  have hΦd : DifferentiableOn ℂ Φ (ball (a : ℂ) r) :=
    (differentiableOn_of_hasLaplace_re_gt hL).mono hre
  -- `Φ` and `F₁` agree near a point of the ball right of `a`, hence on the ball.
  have hz₀ : ((a + r / 2 : ℝ) : ℂ) ∈ ball (a : ℂ) r := by
    rw [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos (by linarith)]
    linarith
  have hz₀re : a < ((a + r / 2 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  have hev : Φ =ᶠ[𝓝 ((a + r / 2 : ℝ) : ℂ)] F₁ := by
    filter_upwards [eventually_hasLaplace_of_mem_ball hF hz₀ hz₀re, isOpen_ball.mem_nhds hz₀]
      with z hz hzb using (hL z (hre z hzb)).unique hz
  have hEq := (hΦd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hF₁.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected hz₀ hev
  rw [← hEq hs]
  exact hL s (hre s hs)

end Landau

end TauCeti
