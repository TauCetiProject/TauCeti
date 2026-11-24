/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Poisson
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.Herglotz
import TauCeti.Analysis.Complex.Poisson.Basic
import TauCeti.Analysis.Complex.Poisson.InverseSquare
import TauCeti.MeasureTheory.Integral.Circle.Prod

/-!
# Herglotz representations of analytic logarithms and logarithmic derivatives

Let `g : ℂ → ℂ` be analytic and zero-free on a neighbourhood of a closed disc `closedBall c R`.
By `AnalyticOnNhd.exists_eqOn_exp_comp_closedBall` and `ContinuousOn.eqOn_of_eqOn_exp_comp` (in
`TauCeti.Analysis.Complex.BranchLogRoot`), `g` admits a holomorphic logarithm `L` on a
neighbourhood of `closedBall c R`, unique among continuous branches on `closedBall c R` once its
value at a single point of the closed disc is fixed.

Because `(L w).re = Real.log ‖g w‖` wherever `Complex.exp (L w) = g w`, applying the Herglotz
formula `DiffContOnCl.circleAverage_herglotzRieszKernel_smul_re_add` to `L` expresses `L`, `g`,
and `logDeriv g` on the open disc `ball c R` purely in terms of the boundary modulus `‖g‖` on
`sphere c R`:

* `DiffContOnCl.circleAverage_herglotzRieszKernel_smul_log_norm_add` and
  `AnalyticOnNhd.exists_eqOn_exp_comp_and_circleAverage`: any holomorphic function `L` on `ball c R`
  continuous on the closure with `Complex.exp ∘ L = g` on `sphere c R` satisfies
  `circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R + (L c).im * I =`
  `L z` for `z ∈ ball c R`; when `g c = 1`, this constructs the analytic logarithm near
  `closedBall c R` normalized by `L c = 0` (unique among continuous branches on `closedBall c R`),
  satisfying `(L z).re = Real.log ‖g z‖` on `closedBall c R` and represented on `ball c R` by the
  Herglotz integral of `Real.log ‖g‖`.
* `AnalyticOnNhd.exp_circleAverage_herglotzRieszKernel_smul_log_norm`: exponentiating the
  Herglotz integral gives
  `Complex.exp (circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R) =`
  `g z * ‖g c‖ / g c`, recovering `g z` after multiplication by the unimodular centre phase
  `g c / ‖g c‖`.
* `AnalyticOnNhd.logDeriv_eq_circleAverage_smul_log_norm`: differentiating under the circle
  average (via `CircleIntegrable.hasDerivAt_circleAverage_herglotzRieszKernel_smul`) expresses the
  logarithmic derivative on `ball c R` as
  `logDeriv g z = circleAverage (fun w ↦ (2 * (w - c) / (w - z) ^ 2) • (Real.log ‖g w‖ : ℂ)) c R`,
  without requiring `g c = 1`.
* `AnalyticOnNhd.circleIntegrable_norm_logDeriv`: `‖logDeriv g‖` is circle integrable over every
  circle on which `g` is analytic and zero-free.
* `AnalyticOnNhd.circleAverage_norm_logDeriv_le`: averaging the norm of the derivative Herglotz
  integrand over a smaller circle `sphere c |r|`, `|r| < R`, Fubini's theorem
  (`TauCeti.circleAverage_circleAverage_swap`) and the exact mean
  `TauCeti.circleAverage_inv_norm_sub_sq_of_notMem_closedBall` of `‖z - w‖⁻²` give
  `circleAverage ‖logDeriv g‖ c r ≤ 2 R / (R ^ 2 - r ^ 2) * circleAverage |log ‖g‖| c R`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), proof of Lemma 2.3.1 (pp. 640–641) and Lemma 6.1.7 and its
  proof (pp. 680–681).
* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Chapter 11.
-/

public section

open Complex Filter Metric Real Set Topology

/-! ### Herglotz formula for holomorphic branches of the logarithm -/

/-- **Herglotz formula for a holomorphic logarithm on a disc.** If `L` is holomorphic on `ball c R`
and continuous on its closure, and `Complex.exp ∘ L = g` on `sphere c R`, then on `ball c R`
`L` is the Herglotz–Riesz integral of `Real.log ‖g‖` plus `(L c).im * I`. When `L c = 0`, the
imaginary constant vanishes. -/
theorem DiffContOnCl.circleAverage_herglotzRieszKernel_smul_log_norm_add
    {L g : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hL : DiffContOnCl ℂ L (ball c R))
    (hexp : EqOn (Complex.exp ∘ L) g (sphere c R)) (hz : z ∈ ball c R) :
    Real.circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R +
        (L c).im * I =
      L z := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hsphere : EqOn (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ))
      (fun w ↦ herglotzRieszKernel c z w • ((L w).re : ℂ)) (sphere c |R|) := by
    intro w hw
    rw [abs_of_pos hR] at hw
    have hgw : g w = Complex.exp (L w) := (hexp hw).symm
    simp [hgw, Complex.norm_exp]
  rw [circleAverage_congr_sphere hsphere]
  exact hL.circleAverage_herglotzRieszKernel_smul_re_add hz

namespace AnalyticOnNhd

variable {g G : ℂ → ℂ} {c z : ℂ} {R : ℝ}

/-- **Normalized analytic logarithm and Herglotz representation on a closed disc.** If `g` is
analytic and zero-free on a neighbourhood of `closedBall c R` with `g c = 1`, there exists `L`
analytic on a neighbourhood of `closedBall c R` (unique among continuous branches on
`closedBall c R`) such that `L c = 0`, `Complex.exp ∘ L = g` and `(L z).re = Real.log ‖g z‖` on
`closedBall c R`, and
`L z = circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R` for every
`z ∈ ball c R`. -/
theorem exists_eqOn_exp_comp_and_circleAverage (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hn : ∀ z ∈ closedBall c R, g z ≠ 0) (hgc : g c = 1) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (closedBall c R) ∧ L c = 0 ∧
      EqOn (Complex.exp ∘ L) g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, (L z).re = Real.log ‖g z‖) ∧
      (∀ z ∈ ball c R,
        L z = circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R) ∧
      ∀ L' : ℂ → ℂ, ContinuousOn L' (closedBall c R) → L' c = 0 →
        EqOn (Complex.exp ∘ L') g (closedBall c R) → EqOn L' L (closedBall c R) := by
  obtain ⟨L, hLa, hLc, hLexp⟩ :=
    hg.exists_eqOn_exp_comp_closedBall hn (Complex.exp_zero.trans hgc.symm)
  refine ⟨L, hLa, hLc, hLexp, fun z hz ↦ ?_, fun z hz ↦ ?_, fun L' hL'cont hL'c hL'exp ↦ ?_⟩
  · rw [← hLexp hz, Function.comp_apply, Complex.norm_exp, Real.log_exp]
  · have hcl : DiffContOnCl ℂ L (ball c R) := hLa.differentiableOn.diffContOnCl_ball subset_rfl
    simpa [hLc] using (hcl.circleAverage_herglotzRieszKernel_smul_log_norm_add
      (hLexp.mono sphere_subset_closedBall) hz).symm
  · rcases lt_or_ge R 0 with hRneg | hR
    · simp [closedBall_eq_empty.mpr hRneg]
    · exact hL'cont.eqOn_of_eqOn_exp_comp hLa.continuousOn (convex_closedBall c R).isPreconnected
        (fun _ hz ↦ (hL'exp hz).trans (hLexp hz).symm) (mem_closedBall_self hR)
        (hL'c.trans hLc.symm)

/-- **Exponentiated Herglotz formula for a zero-free analytic function.** If `G` is analytic and
zero-free on a neighbourhood of `closedBall c R` and `z ∈ ball c R`, the exponential of the
Herglotz–Riesz integral of `Real.log ‖G‖` over `sphere c R` equals `G z * ‖G c‖ / G c`. When
`G c = 1`, the right-hand side is `G z`; in general, multiplying by the unimodular phase
`G c / ‖G c‖` reconstructs `G z`. -/
theorem exp_circleAverage_herglotzRieszKernel_smul_log_norm
    (hG : AnalyticOnNhd ℂ G (closedBall c R)) (hn : ∀ w ∈ closedBall c R, G w ≠ 0)
    (hz : z ∈ ball c R) :
    Complex.exp (circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖G w‖ : ℂ)) c R) =
      G z * ‖G c‖ / G c := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hGc : G c ≠ 0 := hn c (mem_closedBall_self hR.le)
  obtain ⟨L, hLa, -, hLexp⟩ :=
    hG.exists_eqOn_exp_comp_closedBall hn (Complex.exp_log hGc)
  have hLcl : DiffContOnCl ℂ L (ball c R) :=
    hLa.differentiableOn.diffContOnCl_ball subset_rfl
  have hherg := hLcl.circleAverage_herglotzRieszKernel_smul_log_norm_add
    (hLexp.mono sphere_subset_closedBall) hz
  have havg : circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖G w‖ : ℂ)) c R =
      L z - (L c).im * I := eq_sub_of_add_eq hherg
  have hexp_c : Complex.exp (L c) = G c := hLexp (mem_closedBall_self hR.le)
  have hexp_z : Complex.exp (L z) = G z := hLexp (ball_subset_closedBall hz)
  have hnorm_c : (‖G c‖ : ℂ) = Complex.exp (L c).re := by
    rw [← hexp_c, Complex.norm_exp, Complex.ofReal_exp]
  have hnorm_ne : (‖G c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hGc)
  have hexp_im : Complex.exp ((L c).im * I) = G c / ‖G c‖ := by
    rw [eq_div_iff hnorm_ne, mul_comm, hnorm_c, ← Complex.exp_add, re_add_im, hexp_c]
  rw [havg, Complex.exp_sub, hexp_z, hexp_im]
  field_simp

/-- **Derivative Herglotz formula for the logarithmic derivative.** If `g` is analytic and
zero-free on a neighbourhood of `closedBall c R`, then at every `z ∈ ball c R`
`logDeriv g z = circleAverage (fun w ↦ (2 * (w - c) / (w - z) ^ 2) • (Real.log ‖g w‖ : ℂ)) c R`.
No normalization `g c = 1` is required. -/
theorem logDeriv_eq_circleAverage_smul_log_norm (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hn : ∀ w ∈ closedBall c R, g w ≠ 0) (hz : z ∈ ball c R) :
    logDeriv g z =
      circleAverage (fun w ↦ (2 * (w - c) / (w - z) ^ 2) • (Real.log ‖g w‖ : ℂ)) c R := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hgc : g c ≠ 0 := hn c (mem_closedBall_self hR.le)
  obtain ⟨L, hLa, -, hLexp⟩ :=
    hg.exists_eqOn_exp_comp_closedBall hn (Complex.exp_log hgc)
  have hLcl : DiffContOnCl ℂ L (ball c R) :=
    hLa.differentiableOn.diffContOnCl_ball subset_rfl
  have hcont_log : ContinuousOn (fun w ↦ (Real.log ‖g w‖ : ℂ)) (sphere c |R|) := by
    rw [abs_of_pos hR]
    refine continuous_ofReal.comp_continuousOn (ContinuousOn.log ?_ ?_)
    · exact continuous_norm.comp_continuousOn (hg.continuousOn.mono sphere_subset_closedBall)
    · intro w hw
      exact norm_ne_zero_iff.mpr (hn w (sphere_subset_closedBall hw))
  have hint : CircleIntegrable (fun w ↦ (Real.log ‖g w‖ : ℂ)) c R := hcont_log.circleIntegrable'
  have hz_not_sphere : z ∉ sphere c |R| := by
    rw [abs_of_pos hR, mem_sphere_iff_norm]
    exact (mem_ball_iff_norm.mp hz).ne
  have hderiv_rhs : HasDerivAt
      (fun u ↦ circleAverage (fun w ↦ herglotzRieszKernel c u w • (Real.log ‖g w‖ : ℂ)) c R +
        (L c).im * I)
      (circleAverage (fun w ↦ (2 * (w - c) / (w - z) ^ 2) • (Real.log ‖g w‖ : ℂ)) c R) z :=
    (hint.hasDerivAt_circleAverage_herglotzRieszKernel_smul hz_not_sphere).add_const _
  have heq_ball : (fun u ↦ circleAverage
      (fun w ↦ herglotzRieszKernel c u w • (Real.log ‖g w‖ : ℂ)) c R + (L c).im * I) =ᶠ[𝓝 z] L :=
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) fun u hu ↦
      hLcl.circleAverage_herglotzRieszKernel_smul_log_norm_add
        (hLexp.mono sphere_subset_closedBall) hu
  rw [← TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball
    (hLa.differentiableOn.mono ball_subset_closedBall) (hLexp.mono ball_subset_closedBall) hz]
  exact (hderiv_rhs.congr_of_eventuallyEq heq_ball.symm).deriv

/-- The norm of the logarithmic derivative of a function analytic and zero-free on a
neighbourhood of the circle `sphere c |r|` is circle integrable over that circle. -/
theorem circleIntegrable_norm_logDeriv {r : ℝ} (hg : AnalyticOnNhd ℂ g (sphere c |r|))
    (hn : ∀ w ∈ sphere c |r|, g w ≠ 0) :
    CircleIntegrable (fun w ↦ ‖logDeriv g w‖) c r :=
  ContinuousOn.circleIntegrable' fun w hw ↦
    ((hg w hw).logDeriv (hn w hw)).continuousAt.norm.continuousWithinAt

/-- The circle mean of the norm of a logarithmic derivative is controlled by the boundary `L¹`
norm of `log ‖g‖`: if `g` is analytic and zero-free on a neighbourhood of `closedBall c R` and
`|r| < R`, then the mean of `‖logDeriv g‖` over `sphere c |r|` is at most `2 R / (R ^ 2 - r ^ 2)`
times the mean of `|log ‖g‖|` over `sphere c R`. -/
theorem circleAverage_norm_logDeriv_le {r : ℝ} (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hn : ∀ w ∈ closedBall c R, g w ≠ 0) (hr : |r| < R) :
    circleAverage (fun z ↦ ‖logDeriv g z‖) c r ≤
      2 * R / (R ^ 2 - r ^ 2) * circleAverage (fun w ↦ |Real.log ‖g w‖|) c R := by
  have hR : 0 < R := (abs_nonneg r).trans_lt hr
  have hRabs : |R| = R := abs_of_pos hR
  have hsub : sphere c |r| ⊆ closedBall c R :=
    sphere_subset_closedBall.trans (closedBall_subset_closedBall hr.le)
  -- Points of the outer circle lie outside the inner closed disc.
  have hout : ∀ w ∈ sphere c R, w ∉ closedBall c |r| := fun w hw hw' ↦
    sphere_disjoint_ball.ne_of_mem hw (closedBall_subset_ball hr hw') rfl
  -- The kernel `K z w` bounds the norm of the integrand of the derivative Herglotz formula.
  set K : ℂ → ℂ → ℝ := fun z w ↦ (2 * R * |Real.log ‖g w‖|) • (‖z - w‖ ^ 2)⁻¹ with hK_def
  have hlog : ContinuousOn (fun w ↦ |Real.log ‖g w‖|) (sphere c R) :=
    (continuous_norm.comp_continuousOn
      (hg.continuousOn.mono sphere_subset_closedBall)).log
        (fun w hw ↦ norm_ne_zero_iff.2 (hn w (sphere_subset_closedBall hw))) |>.abs
  have hK : ContinuousOn (Function.uncurry K) (sphere c |r| ×ˢ sphere c |R|) := by
    rw [hRabs]
    refine (continuousOn_const.mul (hlog.comp continuousOn_snd
      fun p (hp : p ∈ sphere c |r| ×ˢ sphere c R) ↦ hp.2)).smul
      (((continuousOn_fst.sub continuousOn_snd).norm.pow 2).inv₀ fun p hp ↦ ?_)
    refine pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 fun h ↦ ?_))
    exact hout p.2 hp.2 (h ▸ sphere_subset_closedBall hp.1)
  have hKint := hK.integrableOn_uncurry_circleMap
  calc circleAverage (fun z ↦ ‖logDeriv g z‖) c r
      ≤ circleAverage (fun z ↦ circleAverage (K z) c R) c r := by
        refine circleAverage_mono ((hg.mono hsub).circleIntegrable_norm_logDeriv
          fun w hw ↦ hn w (hsub hw)) hKint.circleIntegrable_circleAverage
          fun z hz ↦ ?_
        rw [hg.logDeriv_eq_circleAverage_smul_log_norm hn (sphere_subset_ball hr hz)]
        refine norm_circleAverage_le_circleAverage_norm.trans_eq
          (circleAverage_congr_sphere fun w hw ↦ ?_)
        rw [hRabs, mem_sphere_iff_norm] at hw
        simp only [hK_def, smul_eq_mul, div_eq_mul_inv, Complex.norm_mul, Complex.norm_ofNat,
          norm_inv, norm_pow, norm_real, norm_eq_abs, hw, norm_sub_rev z w]
        ring
    _ = circleAverage (fun w ↦ circleAverage (fun z ↦ K z w) c r) c R :=
        TauCeti.circleAverage_circleAverage_swap hKint
    _ = circleAverage (fun w ↦ (2 * R / (R ^ 2 - r ^ 2)) • |Real.log ‖g w‖|) c R := by
        refine circleAverage_congr_sphere fun w hw ↦ ?_
        rw [hRabs] at hw
        simp only [hK_def]
        rw [circleAverage_fun_smul,
          TauCeti.circleAverage_inv_norm_sub_sq_of_notMem_closedBall (hout w hw),
          mem_sphere_iff_norm.1 hw, smul_eq_mul, smul_eq_mul]
        ring
    _ = 2 * R / (R ^ 2 - r ^ 2) * circleAverage (fun w ↦ |Real.log ‖g w‖|) c R := by
        rw [circleAverage_fun_smul, smul_eq_mul]

end AnalyticOnNhd

/-! ### Check: constant unimodular phase

For the constant `G = fun _ ↦ I` on the closed unit disc, `Real.log ‖G w‖ = 0` on the unit circle,
so the Herglotz integral vanishes and its exponential is `1 = I * ‖I‖ / I`; multiplying by the
centre phase `G 0 / ‖G 0‖ = I` reconstructs `G`. -/

example {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ((I : ℂ) / ‖(I : ℂ)‖) * Complex.exp (circleAverage
      (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖(fun _ : ℂ ↦ I) w‖ : ℂ)) 0 1) = I := by
  have hG : AnalyticOnNhd ℂ (fun _ : ℂ ↦ I) (closedBall 0 1) := analyticOnNhd_const
  rw [hG.exp_circleAverage_herglotzRieszKernel_smul_log_norm (fun _ _ ↦ I_ne_zero) hz]
  simp
