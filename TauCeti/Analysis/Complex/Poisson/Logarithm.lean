/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.Herglotz
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Herglotz representations of analytic logarithms and logarithmic derivatives

Let `g : ℂ → ℂ` be analytic and zero-free on a neighbourhood of a closed disc `closedBall c R`.
Compactness of the closed disc extends `g` to an open concentric disc `ball c R'` (`R < R'`), on
which `TauCeti.exists_differentiableOn_eqOn_exp_comp` supplies a holomorphic logarithm. Choosing
the branch value at the centre yields a holomorphic logarithm `L` on a neighbourhood of
`closedBall c R`, unique on `closedBall c R` once its value at a single point of the closed disc
is fixed.

Because `(L w).re = Real.log ‖g w‖` wherever `Complex.exp (L w) = g w`, applying the Herglotz
formula `DiffContOnCl.circleAverage_herglotzRieszKernel_smul_re_add` to `L` expresses `L`, `g`,
and `logDeriv g` on the open disc `ball c R` purely in terms of the boundary modulus `‖g‖` on
`sphere c R`:

* `DiffContOnCl.circleAverage_herglotzRieszKernel_smul_log_norm_add` and
  `AnalyticOnNhd.exists_eqOn_exp_comp_and_circleAverage`: any holomorphic logarithm `L` of `g` on
  `ball c R` continuous on the closure satisfies
  `circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R + (L c).im * I =`
  `L z` for `z ∈ ball c R`; when `g c = 1`, this constructs the unique analytic logarithm near
  `closedBall c R` normalized by `L c = 0`, satisfying `(L z).re = Real.log ‖g z‖` on
  `closedBall c R` and represented on `ball c R` by the Herglotz integral of `Real.log ‖g‖`.
* `AnalyticOnNhd.exp_circleAverage_herglotzRieszKernel_smul_log_norm`: exponentiating the
  Herglotz integral gives
  `Complex.exp (circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R) =`
  `g z * ‖g c‖ / g c`, recovering `g z` after multiplication by the unimodular centre phase
  `g c / ‖g c‖`.
* `AnalyticOnNhd.logDeriv_eq_circleAverage_smul_log_norm`: differentiating under the circle
  average (via `CircleIntegrable.hasDerivAt_circleAverage_herglotzRieszKernel_smul`, extending
  Mathlib's `hasDerivAt_circleAverage_herglotzRieszKernel_smul` from centre `0` to arbitrary `c`)
  expresses the logarithmic derivative on `ball c R` as
  `logDeriv g z = circleAverage (fun w ↦ (2 * (w - c) / (w - z) ^ 2) • (Real.log ‖g w‖ : ℂ)) c R`,
  without requiring `g c = 1`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), proof of Lemma 2.3.1 (pp. 640–641) and Lemma 6.1.7 (p. 680).
* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Chapter 11.
-/

public section

open Complex Filter MeasureTheory Metric Real Set Topology

/-! ### Derivative of the Herglotz–Riesz integral at an arbitrary centre -/

/-- **Derivative of the Herglotz–Riesz kernel integral** on an arbitrary circle: if `f` is
circle-integrable on `sphere c |R|` and `w ∉ sphere c |R|`, then
`u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c u ζ • f ζ) c R` has derivative
`circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R` at `w`.
This extends `hasDerivAt_circleAverage_herglotzRieszKernel_smul` from centre `0` to `c`. -/
theorem CircleIntegrable.hasDerivAt_circleAverage_herglotzRieszKernel_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {c w : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c u ζ • f ζ) c R)
      (circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R) w := by
  have hf₀ : CircleIntegrable (fun ζ ↦ f (ζ + c)) 0 R := by
    have hmap : (fun θ ↦ f (circleMap 0 R θ + c)) = fun θ ↦ f (circleMap c R θ) := by
      ext θ
      exact congrArg f (by simp [circleMap]; ring)
    simpa only [CircleIntegrable, hmap] using hf
  have hw₀ : w - c ∉ sphere (0 : ℂ) |R| := by
    simpa [mem_sphere_iff_norm] using hw
  have hd := (_root_.hasDerivAt_circleAverage_herglotzRieszKernel_smul hf₀ hw₀).comp_sub_const w c
  have hfun : (fun u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 (u - c) ζ • f (ζ + c)) 0 R) =
      fun u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c u ζ • f ζ) c R := by
    ext u
    conv_rhs => rw [← circleAverage_map_add_const]
    simp [herglotzRieszKernel_add_const]
  have hval : circleAverage (fun ζ ↦ (2 * ζ / (ζ - (w - c)) ^ 2) • f (ζ + c)) 0 R =
      circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R := by
    conv_rhs => rw [← circleAverage_map_add_const]
    congr 1
    ext ζ
    simp only [add_sub_cancel_right]
    congr 2
    ring
  rwa [hfun, hval] at hd

/-! ### Herglotz formula for holomorphic branches of the logarithm -/

/-- **Herglotz formula for a holomorphic logarithm on a disc.** If `L` is holomorphic on `ball c R`
and continuous on its closure, and `Complex.exp ∘ L = g` on `closedBall c R`, then on `ball c R`
`L` is the Herglotz–Riesz integral of `Real.log ‖g‖` plus `(L c).im * I`. When `L c = 0`, the
imaginary constant vanishes. -/
theorem DiffContOnCl.circleAverage_herglotzRieszKernel_smul_log_norm_add
    {L g : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hL : DiffContOnCl ℂ L (ball c R))
    (hexp : EqOn (Complex.exp ∘ L) g (closedBall c R)) (hz : z ∈ ball c R) :
    Real.circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R +
        (L c).im * I =
      L z := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hsphere : EqOn (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ))
      (fun w ↦ herglotzRieszKernel c z w • ((L w).re : ℂ)) (sphere c |R|) := by
    intro w hw
    rw [abs_of_pos hR] at hw
    have hgw : g w = Complex.exp (L w) := (hexp (sphere_subset_closedBall hw)).symm
    simp [hgw, Complex.norm_exp]
  rw [circleAverage_congr_sphere hsphere]
  exact hL.circleAverage_herglotzRieszKernel_smul_re_add hz

namespace AnalyticOnNhd

variable {L L₁ L₂ g G : ℂ → ℂ} {c z z₀ w₀ : ℂ} {R : ℝ}

/-- **Uniqueness of analytic logarithms on a closed disc.** Two functions analytic near
`closedBall c R` whose exponentials agree with `g` on `closedBall c R` and that take the same value
at one point `z₀ ∈ closedBall c R` agree throughout `closedBall c R`. -/
theorem eqOn_closedBall_of_eqOn_exp_comp (hL₁ : AnalyticOnNhd ℂ L₁ (closedBall c R))
    (hL₂ : AnalyticOnNhd ℂ L₂ (closedBall c R))
    (h₁ : EqOn (Complex.exp ∘ L₁) g (closedBall c R))
    (h₂ : EqOn (Complex.exp ∘ L₂) g (closedBall c R)) (hz₀ : z₀ ∈ closedBall c R)
    (heq : L₁ z₀ = L₂ z₀) :
    EqOn L₁ L₂ (closedBall c R) := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_closedBall.mp hz₀)
  rcases hR.eq_or_lt with rfl | hRpos
  · intro z hz
    simp only [closedBall_zero, mem_singleton_iff] at hz hz₀
    rw [hz, ← hz₀, heq]
  · -- On the open disc `deriv (L₁ - L₂) = 0`, so `L₁ - L₂` is constant there and hence on the
    -- closure `closedBall c R`.
    have hderiv : ∀ w ∈ ball c R, deriv (L₁ - L₂) w = 0 := by
      intro w hw
      have hwcl : w ∈ closedBall c R := ball_subset_closedBall hw
      rw [deriv_sub (hL₁ w hwcl).differentiableAt (hL₂ w hwcl).differentiableAt,
        TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball
          (hL₁.differentiableOn.mono ball_subset_closedBall) (h₁.mono ball_subset_closedBall) hw,
        TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball
          (hL₂.differentiableOn.mono ball_subset_closedBall) (h₂.mono ball_subset_closedBall) hw,
        sub_self]
    have hball : EqOn (L₁ - L₂) (fun _ ↦ (L₁ - L₂) c) (ball c R) := fun w hw ↦
      isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
        ((hL₁.sub hL₂).differentiableOn.mono ball_subset_closedBall) hderiv hw (mem_ball_self hRpos)
    have hcl : EqOn (L₁ - L₂) (fun _ ↦ (L₁ - L₂) c) (closedBall c R) := by
      rw [← closure_ball c hRpos.ne']
      exact hball.of_subset_closure
        (by rw [closure_ball c hRpos.ne']; exact (hL₁.sub hL₂).continuousOn)
        continuousOn_const subset_closure subset_rfl
    intro z hz
    have hz_eq := hcl hz
    have hz₀_eq := hcl hz₀
    simp only [Pi.sub_apply, heq, sub_self] at hz_eq hz₀_eq
    exact sub_eq_zero.mp (hz_eq.trans hz₀_eq.symm)

/-- **Existence of an analytic logarithm on a closed disc.** If `g` is analytic and zero-free on a
neighbourhood of `closedBall c R` and `Complex.exp w₀ = g c`, there exists `L` analytic on a
neighbourhood of `closedBall c R` with `L c = w₀` and `Complex.exp ∘ L = g` on `closedBall c R`. -/
theorem exists_eqOn_exp_comp_closedBall (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hn : ∀ z ∈ closedBall c R, g z ≠ 0) (hw₀ : Complex.exp w₀ = g c) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (closedBall c R) ∧ L c = w₀ ∧
      EqOn (Complex.exp ∘ L) g (closedBall c R) := by
  rcases lt_or_ge R 0 with hRneg | hR
  · exact ⟨fun _ ↦ w₀, analyticOnNhd_const, rfl, by simp [closedBall_eq_empty.mpr hRneg]⟩
  have hopen : IsOpen {z : ℂ | AnalyticAt ℂ g z ∧ g z ≠ 0} :=
    isOpen_iff_eventually.2 fun z hz ↦
      hz.1.eventually_analyticAt.and (hz.1.continuousAt.eventually_ne hz.2)
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c R).exists_thickening_subset_open hopen
    fun z hz ↦ ⟨hg z hz, hn z hz⟩
  rw [thickening_closedBall hδ hR, add_comm] at hsub
  have hRδ : 0 < R + δ := by linarith
  have hsc : IsSimplyConnected (ball c (R + δ)) :=
    (convex_ball c (R + δ)).isSimplyConnected ⟨c, mem_ball_self hRδ⟩
  have hgd : DifferentiableOn ℂ g (ball c (R + δ)) := fun z hz ↦
    (hsub hz).1.differentiableAt.differentiableWithinAt
  have hg₀ : (0 : ℂ) ∉ g '' ball c (R + δ) := by
    rintro ⟨z, hz, hz0⟩
    exact (hsub hz).2 hz0
  obtain ⟨L₀, hL₀d, hL₀exp⟩ :=
    TauCeti.exists_differentiableOn_eqOn_exp_comp hsc isOpen_ball hgd hg₀
  have hL₀a : AnalyticOnNhd ℂ L₀ (closedBall c R) :=
    (hL₀d.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball (by linarith))
  refine ⟨fun z ↦ L₀ z - L₀ c + w₀, (hL₀a.sub analyticOnNhd_const).add analyticOnNhd_const,
    by ring, fun z hz ↦ ?_⟩
  have hzc : z ∈ ball c (R + δ) := closedBall_subset_ball (by linarith) hz
  have hcc : c ∈ ball c (R + δ) := mem_ball_self hRδ
  have hexpc : Complex.exp (L₀ c) = g c := hL₀exp hcc
  have hexpz : Complex.exp (L₀ z) = g z := hL₀exp hzc
  simp only [Function.comp_apply, Complex.exp_add, Complex.exp_sub, hexpz, hexpc, hw₀]
  exact div_mul_cancel₀ (g z) (hn c (mem_closedBall_self hR))

/-- **Normalized analytic logarithm and Herglotz representation on a closed disc.** If `g` is
analytic and zero-free on a neighbourhood of `closedBall c R` with `g c = 1`, there exists `L`
analytic on a neighbourhood of `closedBall c R` (unique on `closedBall c R`) such that `L c = 0`,
`Complex.exp ∘ L = g` and `(L z).re = Real.log ‖g z‖` on `closedBall c R`, and
`L z = circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R` for every
`z ∈ ball c R`. -/
theorem exists_eqOn_exp_comp_and_circleAverage (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hn : ∀ z ∈ closedBall c R, g z ≠ 0) (hgc : g c = 1) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (closedBall c R) ∧ L c = 0 ∧
      EqOn (Complex.exp ∘ L) g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, (L z).re = Real.log ‖g z‖) ∧
      (∀ z ∈ ball c R,
        L z = circleAverage (fun w ↦ herglotzRieszKernel c z w • (Real.log ‖g w‖ : ℂ)) c R) ∧
      ∀ L' : ℂ → ℂ, AnalyticOnNhd ℂ L' (closedBall c R) → L' c = 0 →
        EqOn (Complex.exp ∘ L') g (closedBall c R) → EqOn L' L (closedBall c R) := by
  obtain ⟨L, hLa, hLc, hLexp⟩ :=
    hg.exists_eqOn_exp_comp_closedBall hn (Complex.exp_zero.trans hgc.symm)
  refine ⟨L, hLa, hLc, hLexp, fun z hz ↦ ?_, fun z hz ↦ ?_, fun L' hL'a hL'c hL'exp ↦ ?_⟩
  · rw [← hLexp hz, Function.comp_apply, Complex.norm_exp, Real.log_exp]
  · have hcl : DiffContOnCl ℂ L (ball c R) := hLa.differentiableOn.diffContOnCl_ball subset_rfl
    simpa [hLc] using (hcl.circleAverage_herglotzRieszKernel_smul_log_norm_add hLexp hz).symm
  · rcases lt_or_ge R 0 with hRneg | hR
    · simp [closedBall_eq_empty.mpr hRneg]
    · exact hL'a.eqOn_closedBall_of_eqOn_exp_comp hLa hL'exp hLexp (mem_closedBall_self hR)
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
  have hherg := hLcl.circleAverage_herglotzRieszKernel_smul_log_norm_add hLexp hz
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
      hLcl.circleAverage_herglotzRieszKernel_smul_log_norm_add hLexp hu
  rw [← TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball
    (hLa.differentiableOn.mono ball_subset_closedBall) (hLexp.mono ball_subset_closedBall) hz]
  exact (hderiv_rhs.congr_of_eventuallyEq heq_ball.symm).deriv

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
