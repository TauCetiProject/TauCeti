/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Log
import TauCeti.Analysis.SpecialFunctions.Log.Lipschitz

/-!
# An unbounded function of vanishing mean oscillation

On a finite-dimensional real normed space `E` of dimension `n` with an additive Haar measure `μ`,
consider

`f(x) = log (max 1 (-log ‖x‖))`,

which is `log log (1 / ‖x‖)` on the ball `‖x‖ ≤ e⁻¹` and vanishes outside it. Unlike `log ‖x‖`,
which has bounded but not vanishing mean oscillation (`TauCeti.not_memVMO_log_norm`), this
function has **vanishing mean oscillation** (`TauCeti.memVMO_log_max_one_neg_log_norm`), and it is
still not essentially bounded (`TauCeti.not_memLp_top_log_max_one_neg_log_norm`). So the space of
functions of vanishing mean oscillation is not contained in `L^∞`: just as `log ‖x‖` separates
BMO from `L^∞` and from VMO, `log log (1 / ‖x‖)` separates VMO from `L^∞`.

## The argument

Write `φ(t) = log (max 1 (-t))`, so that `f = φ ∘ log ‖·‖`. The function `φ` is `1`-Lipschitz,
since `t ↦ max 1 (-t)` is `1`-Lipschitz with values in `[1, ∞)`, where the logarithm is
`1`-Lipschitz. Composing with a `K`-Lipschitz map multiplies the BMO seminorm by at most `2 K`
(`LipschitzWith.bmoSeminorm_comp_le`), so `‖f‖_{BMO} ≤ 2 ‖log ‖·‖‖_{BMO} ≤ 4 · 3ⁿ`.

For vanishing mean oscillation, split off the large values of `f`. For `k ≥ 1` and `x ≠ 0`,

`f(x) = g_k(x) + φ(log ‖x‖ / k)`,

where `g_k(x) = φ(ℓ_k x) - φ(ℓ_k x / k)` with `ℓ_k x = log (max ‖x‖ e^{-k})`: away from the ball of
radius `e^{-k}` this is the identity `φ(t) = (φ(t) - φ(t / k)) + φ(t / k)`, and inside it
`φ(t) = log (-t) = log k + log (-t / k) = g_k(x) + φ(t / k)`. The function `g_k` is uniformly
continuous, because `ℓ_k` is Lipschitz, hence of vanishing mean oscillation
(`UniformContinuous.memVMO`). The remainder `φ(log ‖x‖ / k)` is `log ‖·‖` composed with the
`k⁻¹`-Lipschitz map `t ↦ φ(t / k)`, so its BMO seminorm is at most `2 k⁻¹ ‖log ‖·‖‖_{BMO}`, which
tends to `0` as `k → ∞`. Since the functions of vanishing mean oscillation are closed in BMO
(`TauCeti.memVMO_of_tendsto_bmoSeminorm`), `f` has vanishing mean oscillation.

## Main declarations

* `TauCeti.bmoSeminorm_log_max_one_neg_log_norm_le`: `‖f‖_{BMO} ≤ 4 · 3ⁿ`.
* `TauCeti.memVMO_log_max_one_neg_log_norm`: `f` has vanishing mean oscillation.
* `TauCeti.not_memLp_top_log_max_one_neg_log_norm`: `f` is not essentially bounded.

## References

* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.1.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- **`log log (1 / ‖x‖)` is not essentially bounded** on a nontrivial real normed space, for any
measure that is positive on nonempty open sets. -/
theorem not_memLp_top_log_max_one_neg_log_norm [Nontrivial E] [μ.IsOpenPosMeasure] :
    ¬ MemLp (fun x : E => Real.log (max 1 (-Real.log ‖x‖))) ∞ μ := by
  intro h
  set M := eLpNormEssSup (fun x : E => Real.log (max 1 (-Real.log ‖x‖))) μ
  have hM : M ≠ ∞ := by
    have h' := h.eLpNorm_lt_top
    rw [eLpNorm_exponent_top] at h'
    · exact h'.ne
    · exact h.aestronglyMeasurable
  -- The nonzero points of norm less than `δ = exp (-exp (M + 1))` form a nonempty open set, hence
  -- one of positive measure, on which the function exceeds its essential supremum.
  set δ := Real.exp (-Real.exp (M.toReal + 1))
  have hδ : 0 < δ := Real.exp_pos _
  set U : Set E := ball 0 δ ∩ {0}ᶜ
  have hU : IsOpen U := isOpen_ball.inter isOpen_compl_singleton
  obtain ⟨x, hx⟩ := exists_norm_eq E (by positivity : 0 ≤ δ / 2)
  have hUne : U.Nonempty := by
    refine ⟨x, mem_ball_zero_iff.2 (by rw [hx]; linarith), fun h0 => ?_⟩
    rw [mem_singleton_iff.1 h0, norm_zero] at hx
    linarith
  have hUsub : U ⊆ {x | ¬ ‖Real.log (max 1 (-Real.log ‖x‖))‖ₑ ≤ M} := by
    rintro y ⟨hyδ, hy0⟩
    have hpos : 0 < ‖y‖ := norm_pos_iff.2 (by simpa using hy0)
    -- `-log ‖y‖ > exp (M + 1)`, so the function exceeds `M + 1` at `y`.
    have hlog : Real.exp (M.toReal + 1) < -Real.log ‖y‖ := by
      have := Real.log_lt_log hpos (mem_ball_zero_iff.1 hyδ)
      rw [Real.log_exp] at this
      linarith
    have hval : M.toReal < Real.log (max 1 (-Real.log ‖y‖)) := by
      have h1 : M.toReal + 1 < Real.log (max 1 (-Real.log ‖y‖)) := by
        rw [Real.lt_log_iff_exp_lt (by positivity)]
        exact hlog.trans_le (le_max_right _ _)
      linarith
    simp only [mem_ofPred_eq, not_le]
    rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal hM]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2
      (hval.trans_le (le_abs_self _))
  exact (hU.measure_pos μ hUne).ne' (measure_mono_null hUsub ae_le_eLpNormEssSup)

/-- The function `t ↦ log (max 1 (-t))` is `1`-Lipschitz. -/
private theorem lipschitzWith_log_max_one_neg :
    LipschitzWith 1 fun t : ℝ => Real.log (max 1 (-t)) := by
  simpa [Function.comp_def] using Real.lipschitzWith_log_max_one.comp LipschitzWith.id.neg

/-- The function `t ↦ log (max 1 (-(c t)))` is `|c|`-Lipschitz. -/
private theorem lipschitzWith_log_max_one_neg_mul (c : ℝ) :
    LipschitzWith ‖c‖₊ fun t : ℝ => Real.log (max 1 (-(c * t))) := by
  simpa [Function.comp_def, smul_eq_mul] using
    lipschitzWith_log_max_one_neg.comp (lipschitzWith_smul (β := ℝ) c)

omit [NormedSpace ℝ E] [MeasurableSpace E] in
/-- The truncation `g_k(x) = φ(ℓ_k x) - φ(ℓ_k x / k)` of `log log (1 / ‖x‖)` at height `log k`,
written with `ℓ_k x = log (max ‖x‖ e^{-k})` so that it is continuous at the origin, is uniformly
continuous. -/
private theorem uniformContinuous_log_max_one_neg_sub (k : ℝ) :
    UniformContinuous fun x : E =>
      Real.log (max 1 (-Real.log (max ‖x‖ (Real.exp (-k))))) -
        Real.log (max 1 (-(Real.log (max ‖x‖ (Real.exp (-k))) / k))) := by
  have hℓ : UniformContinuous fun x : E => Real.log (max ‖x‖ (Real.exp (-k))) :=
    ((lipschitzWith_one_norm (E := E)).max_const (Real.exp (-k))).log (Real.exp_pos (-k))
      (fun x => le_max_right ‖x‖ (Real.exp (-k))) |>.uniformContinuous
  have hψ : UniformContinuous fun t : ℝ => Real.log (max 1 (-(t / k))) := by
    simpa only [div_eq_inv_mul] using (lipschitzWith_log_max_one_neg_mul k⁻¹).uniformContinuous
  exact (lipschitzWith_log_max_one_neg.uniformContinuous.comp hℓ).sub (hψ.comp hℓ)

omit [NormedSpace ℝ E] [MeasurableSpace E] in
/-- Off the origin, `log log (1 / ‖x‖)` is the sum of its truncation `g_k` at height `log k` and
of `φ(log ‖x‖ / k)`, for `k ≥ 1`. -/
private theorem log_max_one_neg_log_norm_eq_add {k : ℝ} (hk : 1 ≤ k) {x : E} (hx : x ≠ 0) :
    Real.log (max 1 (-Real.log ‖x‖)) =
      (Real.log (max 1 (-Real.log (max ‖x‖ (Real.exp (-k))))) -
        Real.log (max 1 (-(Real.log (max ‖x‖ (Real.exp (-k))) / k)))) +
        Real.log (max 1 (-(Real.log ‖x‖ / k))) := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hk0 : 0 < k := one_pos.trans_le hk
  rcases le_or_gt (Real.exp (-k)) ‖x‖ with hle | hlt
  · rw [max_eq_left hle]
    ring
  -- Inside the ball of radius `e^{-k}`, `log ‖x‖ < -k`, and every `max` is attained by its second
  -- argument except `max 1 (-(-k / k)) = 1`.
  have hlog : Real.log ‖x‖ < -k := by
    simpa only [Real.log_exp] using Real.log_lt_log hpos hlt
  have hdiv : 1 ≤ -(Real.log ‖x‖ / k) := by
    rw [← neg_div, le_div_iff₀ hk0]
    linarith
  have hnlog : 1 ≤ -Real.log ‖x‖ := by linarith
  have hkk : -(-k / k) = 1 := by field_simp
  simp only [max_eq_right hlt.le, Real.log_exp, hkk, max_eq_right hnlog, max_eq_right hdiv,
    neg_neg, max_eq_right hk, max_self, Real.log_one]
  rw [← neg_div, Real.log_div (by linarith) hk0.ne']
  ring

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-- **`log log (1 / ‖x‖)` has bounded mean oscillation**, with
`‖log (max 1 (-log ‖·‖))‖_{BMO} ≤ 4 · 3ⁿ` on a finite-dimensional real normed space of dimension
`n` with an additive Haar measure. -/
theorem bmoSeminorm_log_max_one_neg_log_norm_le :
    bmoSeminorm (fun x : E => Real.log (max 1 (-Real.log ‖x‖))) μ ≤ 4 * 3 ^ finrank ℝ E :=
  calc bmoSeminorm (fun x : E => Real.log (max 1 (-Real.log ‖x‖))) μ
      ≤ 2 * (1 : ℝ≥0) * bmoSeminorm (fun x : E => Real.log ‖x‖) μ :=
        lipschitzWith_log_max_one_neg.bmoSeminorm_comp_le (f := fun x : E => Real.log ‖x‖)
          (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
    _ ≤ 2 * (1 : ℝ≥0) * (2 * 3 ^ finrank ℝ E) := by gcongr; exact bmoSeminorm_log_norm_le
    _ = 4 * 3 ^ finrank ℝ E := by
        rw [ENNReal.coe_one, mul_one, ← mul_assoc]
        norm_num

/-- The remainder `φ(log ‖x‖ / k)` has BMO seminorm at most `2 k⁻¹ ‖log ‖·‖‖_{BMO}`, which tends
to `0` along `k = n + 1`. -/
private theorem tendsto_bmoSeminorm_log_max_one_neg_inv_mul_log_norm :
    Tendsto (fun n : ℕ => bmoSeminorm
      (fun x : E => Real.log (max 1 (-(((n : ℝ) + 1)⁻¹ * Real.log ‖x‖)))) μ) atTop (𝓝 0) := by
  set B := bmoSeminorm (fun x : E => Real.log ‖x‖) μ
  have hbound (n : ℕ) : bmoSeminorm
      (fun x : E => Real.log (max 1 (-(((n : ℝ) + 1)⁻¹ * Real.log ‖x‖)))) μ ≤
        2 * B * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    refine ((lipschitzWith_log_max_one_neg_mul _).bmoSeminorm_comp_le
      (f := fun x : E => Real.log ‖x‖)
      (Real.measurable_log.comp measurable_norm).aestronglyMeasurable).trans_eq ?_
    have hnn : ‖((n : ℝ) + 1)⁻¹‖₊ = Real.toNNReal (1 / ((n : ℝ) + 1)) := by
      rw [Real.toNNReal_of_nonneg (by positivity)]
      ext
      simp [abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    rw [hnn, ENNReal.ofReal, mul_right_comm]
  have hlim : Tendsto (fun n : ℕ => 2 * B * ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have hB : 2 * B ≠ ∞ := by finiteness [memBMO_log_norm (μ := μ).bmoSeminorm_ne_top]
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat) (Or.inr hB)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hbound

/-- **`log log (1 / ‖x‖)` has vanishing mean oscillation** on a finite-dimensional real normed
space with an additive Haar measure. Here the function is `log (max 1 (-log ‖x‖))`, which is
`log log (1 / ‖x‖)` for `‖x‖ ≤ e⁻¹` and vanishes for larger `‖x‖`; it is not essentially bounded
(`TauCeti.not_memLp_top_log_max_one_neg_log_norm`). -/
theorem memVMO_log_max_one_neg_log_norm :
    MemVMO (fun x : E => Real.log (max 1 (-Real.log ‖x‖))) μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h : (fun x : E => Real.log (max 1 (-Real.log ‖x‖))) = fun _ => 0 := by
      funext x
      simp [Subsingleton.elim x 0]
    rw [h]
    exact memVMO_const 0
  set f : E → ℝ := fun x => Real.log (max 1 (-Real.log ‖x‖))
  have hf : MemBMO f μ := memBMO_log_norm.comp_lipschitzWith lipschitzWith_log_max_one_neg
  -- With `k = n + 1`, split `f` into the truncation `g n` and the remainder `r n = φ(log ‖·‖ / k)`.
  set r : ℕ → E → ℝ := fun n x => Real.log (max 1 (-(((n : ℝ) + 1)⁻¹ * Real.log ‖x‖)))
  set g : ℕ → E → ℝ := fun n x =>
    Real.log (max 1 (-Real.log (max ‖x‖ (Real.exp (-((n : ℝ) + 1)))))) -
      Real.log (max 1 (-(Real.log (max ‖x‖ (Real.exp (-((n : ℝ) + 1)))) / ((n : ℝ) + 1))))
  have hfr (n : ℕ) : f - g n =ᵐ[μ] r n := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (μ := μ) (0 : E))] with x hx
    have h := log_max_one_neg_log_norm_eq_add (le_add_of_nonneg_left n.cast_nonneg)
      (by simpa using hx : x ≠ 0)
    simp only [Pi.sub_apply, f, g, r, inv_mul_eq_div]
    linarith
  -- The truncations are uniformly continuous functions of bounded mean oscillation.
  have hgVMO (n : ℕ) : MemVMO (g n) μ := by
    refine (uniformContinuous_log_max_one_neg_sub ((n : ℝ) + 1)).memVMO ?_
    refine (hf.sub (memBMO_log_norm.comp_lipschitzWith
      (lipschitzWith_log_max_one_neg_mul ((n : ℝ) + 1)⁻¹))).congr_ae ?_
    filter_upwards [hfr n] with x hx
    simp only [Pi.sub_apply, r, g] at hx ⊢
    linarith
  refine memVMO_of_tendsto_bmoSeminorm (l := atTop) hf.locallyIntegrable hgVMO ?_
  simpa only [bmoSeminorm_congr_ae (hfr _)] using
    tendsto_bmoSeminorm_log_max_one_neg_inv_mul_log_norm (μ := μ)

end TauCeti
