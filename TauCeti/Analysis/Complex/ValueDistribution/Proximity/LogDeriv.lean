/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.Poisson.InverseSquare
import TauCeti.Analysis.Complex.Poisson.Logarithm
import TauCeti.MeasureTheory.Integral.Circle.Prod
import TauCeti.MeasureTheory.Integral.PosLog

/-!
# The proximity function of a logarithmic derivative

Let `g` be holomorphic and zero-free on a neighbourhood of the closed disc `closedBall 0 R`. This
file bounds the Nevanlinna proximity function `m(r, g'/g) = proximity (logDeriv g) ⊤ r` on a
smaller circle `0 < r < R` in terms of `m(R, g)`, uniformly in `g`:

`m(r, g'/g) ≤ log⁺ ((m(R, g) / r) * R / (R - r)) + log 2 + exp (-1)` when `‖g 0‖ = 1`.

Estimates of this kind (lemmas on the logarithmic derivative) control `m(r, g'/g)` by the
characteristic of `g` with only a logarithmic loss, and are the analytic input to bounds on the
mean growth of covering maps of punctured planes.

The proof differentiates the Herglotz representation of `log g`
(`AnalyticOnNhd.logDeriv_eq_circleAverage_smul_log_norm`): for `‖z - c‖ < R`,
`g'(z)/g(z)` is the circle average over `‖w - c‖ = R` of `2 (w - c) / (w - z) ^ 2 * log ‖g w‖`.
Averaging the norm of this kernel over the smaller circle, Fubini's theorem and the exact mean
`TauCeti.circleAverage_inv_norm_sub_sq_of_notMem_closedBall` of `‖z - w‖⁻²` give

`circleAverage ‖g'/g‖ c r ≤ 2 R / (R ^ 2 - r ^ 2) * circleAverage |log ‖g‖| c R`.

When `‖g 0‖ = 1`, the mean of `|log ‖g‖|` over `sphere 0 R` is `2 m(R, g)`
(`AnalyticOnNhd.circleAverage_abs_log_norm_of_ne_zero`), and the entropy estimate
`CircleIntegrable.circleAverage_posLog_le_posLog_circleAverage_add` converts the mean of `‖g'/g‖`
into a bound for the mean of `log⁺ ‖g'/g‖`.

## Main results

* `AnalyticOnNhd.circleAverage_norm_logDeriv_le`: the mean of `‖g'/g‖` over `sphere c |r|` is at
  most `2 R / (R ^ 2 - r ^ 2)` times the mean of `|log ‖g‖|` over `sphere c R`, for `|r| < R`.
* `AnalyticOnNhd.proximity_logDeriv_top_le`: the zero-free logarithmic derivative estimate
  `m(r, g'/g) ≤ log⁺ ((m(R, g) / r) * R / (R - r)) + log 2 + exp (-1)` for `‖g 0‖ = 1` and
  `0 < r < R`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), 627–702, Lemma 6.1.7 and its proof (pp. 680–681), where the
  bound is stated with a strict inequality.
* W. K. Hayman, *Meromorphic Functions*, Oxford University Press (1964), §2.3.
-/

public section

open Complex Metric Real Set ValueDistribution

namespace AnalyticOnNhd

variable {g : ℂ → ℂ} {c : ℂ} {r R : ℝ}

/-- The norm of the logarithmic derivative of a function analytic and zero-free on
`closedBall c R` is circle integrable over every circle `sphere c |r|` with `|r| < R`. -/
private theorem circleIntegrable_norm_logDeriv (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hn : ∀ w ∈ closedBall c R, g w ≠ 0) (hr : |r| < R) :
    CircleIntegrable (fun z ↦ ‖logDeriv g z‖) c r := by
  refine ContinuousOn.circleIntegrable' fun z hz ↦ ?_
  have hz' : z ∈ closedBall c R :=
    mem_closedBall_iff_norm.2 ((mem_sphere_iff_norm.1 hz).trans_le hr.le)
  exact ((hg z hz').logDeriv (hn z hz')).continuousAt.norm.continuousWithinAt

/-- The circle mean of the norm of a logarithmic derivative is controlled by the boundary `L¹`
norm of `log ‖g‖`: if `g` is analytic and zero-free on a neighbourhood of `closedBall c R` and
`|r| < R`, then the mean of `‖logDeriv g‖` over `sphere c |r|` is at most `2 R / (R ^ 2 - r ^ 2)`
times the mean of `|log ‖g‖|` over `sphere c R`. -/
theorem circleAverage_norm_logDeriv_le (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hn : ∀ w ∈ closedBall c R, g w ≠ 0) (hr : |r| < R) :
    circleAverage (fun z ↦ ‖logDeriv g z‖) c r ≤
      2 * R / (R ^ 2 - r ^ 2) * circleAverage (fun w ↦ |Real.log ‖g w‖|) c R := by
  have hR : 0 < R := (abs_nonneg r).trans_lt hr
  have hRabs : |R| = R := abs_of_pos hR
  have hball : ∀ z ∈ sphere c |r|, z ∈ ball c R := fun z hz ↦
    mem_ball_iff_norm.2 ((mem_sphere_iff_norm.1 hz).trans_lt hr)
  -- The kernel `K z w` bounds the norm of the integrand of the derivative Herglotz formula.
  set K : ℂ → ℂ → ℝ := fun z w ↦ (2 * R * |Real.log ‖g w‖|) • (‖z - w‖ ^ 2)⁻¹ with hK_def
  have hlog : ContinuousOn (fun w ↦ |Real.log ‖g w‖|) (sphere c |R|) := by
    rw [hRabs]
    exact (continuous_norm.comp_continuousOn
      (hg.continuousOn.mono sphere_subset_closedBall)).log
        (fun w hw ↦ norm_ne_zero_iff.2 (hn w (sphere_subset_closedBall hw))) |>.abs
  have hK : ContinuousOn (Function.uncurry K) (sphere c |r| ×ˢ sphere c |R|) := by
    refine (continuousOn_const.mul (hlog.comp continuousOn_snd
      fun p (hp : p ∈ sphere c |r| ×ˢ sphere c |R|) ↦ hp.2)).smul
      (((continuousOn_fst.sub continuousOn_snd).norm.pow 2).inv₀ fun p hp ↦ ?_)
    have h1 := mem_sphere_iff_norm.1 hp.1
    have h2 := mem_sphere_iff_norm.1 hp.2
    refine pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 fun h ↦ ?_))
    rw [h] at h1
    exact hr.ne (h1.symm.trans (h2.trans hRabs))
  calc circleAverage (fun z ↦ ‖logDeriv g z‖) c r
      ≤ circleAverage (fun z ↦ circleAverage (K z) c R) c r := by
        refine circleAverage_mono (circleIntegrable_norm_logDeriv hg hn hr)
          (Real.circleIntegrable_circleAverage hK) fun z hz ↦ ?_
        rw [hg.logDeriv_eq_circleAverage_smul_log_norm hn (hball z hz)]
        refine norm_circleAverage_le_circleAverage_norm.trans_eq
          (circleAverage_congr_sphere fun w hw ↦ ?_)
        rw [hRabs, mem_sphere_iff_norm] at hw
        simp [hK_def, hw, norm_sub_rev z w, div_eq_mul_inv]
        ring
    _ = circleAverage (fun w ↦ circleAverage (fun z ↦ K z w) c r) c R :=
        Real.circleAverage_circleAverage_swap hK
    _ = circleAverage (fun w ↦ (2 * R / (R ^ 2 - r ^ 2)) • |Real.log ‖g w‖|) c R := by
        refine circleAverage_congr_sphere fun w hw ↦ ?_
        rw [hRabs, mem_sphere_iff_norm] at hw
        have hw' : w ∉ closedBall c |r| := by
          rw [mem_closedBall_iff_norm, hw, not_le]
          exact hr
        simp only [hK_def]
        rw [circleAverage_fun_smul, TauCeti.circleAverage_inv_norm_sub_sq_of_notMem_closedBall hw',
          hw, smul_eq_mul, smul_eq_mul]
        ring
    _ = 2 * R / (R ^ 2 - r ^ 2) * circleAverage (fun w ↦ |Real.log ‖g w‖|) c R := by
        rw [circleAverage_fun_smul, smul_eq_mul]

/-- **The zero-free logarithmic derivative estimate.** If `g` is analytic and zero-free on a
neighbourhood of `closedBall 0 R` with `‖g 0‖ = 1` (for instance `g 0 = 1`), then for `0 < r < R`
the proximity function of `logDeriv g = deriv g / g` satisfies
`m(r, g'/g) ≤ log⁺ ((m(R, g) / r) * R / (R - r)) + log 2 + exp (-1)`. -/
theorem proximity_logDeriv_top_le (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hn : ∀ w ∈ closedBall 0 R, g w ≠ 0) (h0 : ‖g 0‖ = 1) (hr : 0 < r) (hrR : r < R) :
    proximity (logDeriv g) ⊤ r ≤
      log⁺ (proximity g ⊤ R / r * R / (R - r)) + Real.log 2 + Real.exp (-1) := by
  have hR : 0 < R := hr.trans hrR
  have hrR' : |r| < R := (abs_of_pos hr).trans_lt hrR
  set m := proximity g ⊤ R with hm_def
  have hm : 0 ≤ m := proximity_nonneg R
  -- The mean of `‖g'/g‖` over `sphere 0 r` is at most `2 R / (R ^ 2 - r ^ 2) * 2 m(R, g)`.
  have hmean : circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r ≤ 2 * R / (R ^ 2 - r ^ 2) * (2 * m) := by
    have hg' : AnalyticOnNhd ℂ g (closedBall 0 |R|) := by rwa [abs_of_pos hR]
    have hn' : ∀ u ∈ closedBall (0 : ℂ) |R|, g u ≠ 0 := by rwa [abs_of_pos hR]
    have habs := hg'.circleAverage_abs_log_norm_of_ne_zero hn'
    rw [h0, Real.log_one, sub_zero] at habs
    calc circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r
        ≤ 2 * R / (R ^ 2 - r ^ 2) * circleAverage (fun w ↦ |Real.log ‖g w‖|) 0 R :=
          hg.circleAverage_norm_logDeriv_le hn hrR'
      _ = 2 * R / (R ^ 2 - r ^ 2) * (2 * m) := by rw [habs, hm_def, proximity_top]
  -- That bound is at most twice `(m(R, g) / r) * R / (R - r)`, since `2 r ≤ R + r`.
  have hcmp : 2 * R / (R ^ 2 - r ^ 2) * (2 * m) ≤ 2 * (m / r * R / (R - r)) := by
    have hRr : 0 < R - r := sub_pos.2 hrR
    rw [show R ^ 2 - r ^ 2 = (R - r) * (R + r) by ring, div_mul_eq_mul_div, div_le_iff₀
      (by positivity)]
    field_simp
    nlinarith [mul_nonneg (mul_nonneg hm hR.le) hRr.le]
  have hnonneg : 0 ≤ circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r :=
    circleAverage_nonneg_of_nonneg fun _ _ ↦ norm_nonneg _
  calc proximity (logDeriv g) ⊤ r
      ≤ log⁺ (circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r) + Real.exp (-1) := by
        rw [proximity_top]
        exact (circleIntegrable_norm_logDeriv hg hn hrR')
          |>.circleAverage_posLog_le_posLog_circleAverage_add fun _ _ ↦ norm_nonneg _
    _ ≤ log⁺ (2 * (m / r * R / (R - r))) + Real.exp (-1) := by
        gcongr
        · linarith
        · exact hmean.trans hcmp
    _ ≤ log⁺ 2 + log⁺ (m / r * R / (R - r)) + Real.exp (-1) := by
        gcongr
        exact posLog_mul
    _ = log⁺ (m / r * R / (R - r)) + Real.log 2 + Real.exp (-1) := by
        rw [posLog_eq_log (by norm_num)]
        ring

end AnalyticOnNhd
