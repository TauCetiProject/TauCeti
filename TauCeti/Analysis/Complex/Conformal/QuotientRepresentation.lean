/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import TauCeti.Analysis.Complex.Conformal.BlaschkeProduct
import TauCeti.Analysis.Complex.Herglotz.Logarithm
import TauCeti.Analysis.Complex.RadialUniqueness

/-!
# Nevanlinna's quotient representation and its optimality

Let `g` be analytic on a neighbourhood of a closed disc `closedBall 0 R`. Nevanlinna's **quotient
representation** constructs an analytic multiplier `h` near `closedBall 0 R`, normalized by
`h 0 = 1`, that cancels the large values of `g` so that both `log ‖h‖` and `log ‖h * g‖` are
uniformly bounded on `closedBall 0 R` (and in particular on `sphere 0 R`) by the Nevanlinna
proximity `ValueDistribution.proximity g ⊤ R + ε`.

The representation rests on a sharper subdisc estimate: for any `s < r` with `g` analytic near
`closedBall 0 r`, the explicit Herglotz–Riesz multiplier
`h(z) = exp (m(r, g) - circleAverage (fun w ↦ herglotzRieszKernel 0 z w • log⁺ ‖g w‖) 0 r)`
is analytic near `closedBall 0 s`, satisfies `h 0 = 1`, and obeys both `log ‖h z‖ ≤ m(r, g)` and
`log ‖h z * g z‖ ≤ m(r, g)` on `closedBall 0 s` with no nonvanishing assumption on `sphere 0 r`.
Thickening `closedBall 0 R` inside the open analyticity locus of `g` and choosing `r > R` close
enough that `m(r, g) ≤ m(R, g) + ε` then gives Nevanlinna's quotient representation on
`closedBall 0 R` itself.

Conversely, the proximity bound `m(r, g)` is **optimal**: for any `h` analytic near
`closedBall 0 |r|` with `1 ≤ ‖h 0‖`, any uniform upper bound `M` on `log ‖h‖` and `log ‖h * g‖`
along `sphere 0 |r|` satisfies `m(r, g) ≤ M`.

## Main results

* `AnalyticOnNhd.exists_analyticOnNhd_closedBall_log_norm_le_proximity_top`: on any strict subdisc
  `closedBall 0 s` (`s < r`), `g` admits an analytic multiplier `h` with `h 0 = 1` bounding both
  `log ‖h‖` and `log ‖h * g‖` by `ValueDistribution.proximity g ⊤ r`.
* `AnalyticOnNhd.exists_analyticOnNhd_closedBall_log_norm_le_proximity_top_add`: **Nevanlinna's
  quotient representation** (pointwise closed-disc form) bounding `log ‖h‖` and `log ‖h * g‖` on
  `closedBall 0 R` by `ValueDistribution.proximity g ⊤ R + ε` for every `ε > 0`.
* `AnalyticOnNhd.exists_analyticOnNhd_closedBall_max_sSup_log_norm_le_proximity_top_add`:
  **Nevanlinna's quotient representation** (boundary logarithmic-supremum form) bounding
  `max (sSup ((log ‖h ·‖) '' sphere 0 R)) (sSup ((log ‖h · * g ·‖) '' sphere 0 R))` by
  `ValueDistribution.proximity g ⊤ R + ε` for `0 ≤ R` and `ε > 0`.
* `AnalyticOnNhd.proximity_top_le_of_log_norm_le` and
  `AnalyticOnNhd.proximity_top_le_max_sSup_log_norm`: **optimality of the quotient bound**, showing
  that `ValueDistribution.proximity g ⊤ r` is a lower bound for any uniform bound (and, when
  `log ‖h * g‖` is bounded above on `sphere 0 |r|`, for the maximum of the two boundary logarithmic
  suprema) over analytic multipliers `h` on `closedBall 0 |r|` with `1 ≤ ‖h 0‖`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), Lemma 2.3.1 and Remark 2.3.3, pp. 639–641.
* R. Nevanlinna, *Analytic Functions*, Springer, 1970.
-/

public section

open Complex Filter MeasureTheory Metric Real Set Topology

namespace AnalyticOnNhd

/-- Auxiliary Nevanlinna denominator on `ball 0 r`, defined from the proximity `m(r, g)` and the
Herglotz–Riesz integral of `log⁺ ‖g‖` over `sphere 0 r`. -/
private noncomputable def nevanlinnaMultiplierAux (g : ℂ → ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((ValueDistribution.proximity g ⊤ r : ℂ) -
    circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (log⁺ ‖g w‖ : ℂ)) 0 r)

/-- Analyticity on `ball 0 r`, normalization `h 0 = 1`, and upper bound `‖h z‖ ≤ exp (m(r, g))` for
`nevanlinnaMultiplierAux g r`. -/
private lemma analyticOnNhd_nevanlinnaMultiplierAux_and_zero_and_norm_le {g : ℂ → ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hr : 0 < r) :
    AnalyticOnNhd ℂ (nevanlinnaMultiplierAux g r) (ball 0 r) ∧
      nevanlinnaMultiplierAux g r 0 = 1 ∧
      ∀ z ∈ ball 0 r,
        ‖nevanlinnaMultiplierAux g r z‖ ≤ Real.exp (ValueDistribution.proximity g ⊤ r) := by
  have hcont : ContinuousOn (fun w ↦ log⁺ ‖g w‖) (sphere 0 |r|) :=
    continuous_posLog.comp_continuousOn
      (hg.continuousOn.mono (by rw [abs_of_pos hr]; exact sphere_subset_closedBall)).norm
  have hint : CircleIntegrable (fun w ↦ log⁺ ‖g w‖) 0 r := hcont.circleIntegrable'
  have hintC : CircleIntegrable (fun w ↦ (log⁺ ‖g w‖ : ℂ)) 0 r :=
    (continuous_ofReal.comp_continuousOn hcont).circleIntegrable'
  have hball_compl : ball (0 : ℂ) r ⊆ (sphere 0 |r|)ᶜ := fun z hz hzs ↦ by
    rw [abs_of_pos hr] at hzs
    exact Set.disjoint_right.mp sphere_disjoint_ball hz hzs
  have hH : AnalyticOnNhd ℂ
      (fun z ↦ circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (log⁺ ‖g w‖ : ℂ)) 0 r)
      (ball 0 r) :=
    hintC.analyticOnNhd_circleAverage_herglotzRieszKernel_smul.mono hball_compl
  refine ⟨fun z hz ↦ (analyticAt_const.sub (hH z hz)).cexp, ?_, fun z hz ↦ ?_⟩
  · have hsphere : EqOn (fun w ↦ herglotzRieszKernel 0 0 w • (log⁺ ‖g w‖ : ℂ))
        (ofRealCLM ∘ fun w ↦ log⁺ ‖g w‖) (sphere 0 |r|) := fun w hw ↦ by
      have hw0 : w ≠ 0 := ne_of_mem_sphere hw (abs_pos.2 hr.ne').ne'
      simp [herglotzRieszKernel_def, hw0]
    rw [nevanlinnaMultiplierAux, circleAverage_congr_sphere hsphere,
      ofRealCLM.circleAverage_comp_comm hint, ofRealCLM_apply, ValueDistribution.proximity_top,
      sub_self, Complex.exp_zero]
  · rw [nevanlinnaMultiplierAux, Complex.norm_exp, sub_re, ofReal_re]
    exact Real.exp_le_exp.2 (sub_le_self _
      (hint.re_circleAverage_herglotzRieszKernel_smul_nonneg hz fun _ _ ↦ posLog_nonneg))

/-- On `ball 0 r`, `‖nevanlinnaMultiplierAux g r z * g z‖ ≤ exp (m(r, g))` whenever `g` has no zeros
on the bounding circle `sphere 0 r`. -/
private lemma norm_nevanlinnaMultiplierAux_mul_le_of_sphere_ne_zero {g : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hsphere : ∀ w ∈ sphere 0 r, g w ≠ 0)
    (hz : z ∈ ball 0 r) :
    ‖nevanlinnaMultiplierAux g r z * g z‖ ≤ Real.exp (ValueDistribution.proximity g ⊤ r) := by
  have hr : 0 < r := pos_of_mem_ball hz
  obtain ⟨k, a, n, G, ha, hG, hG0, hfac⟩ := hg.exists_blaschkeProduct_mul_eqOn_closedBall hsphere
  have hGz : ‖G z‖ = Real.exp
      (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r).re := by
    have hexp := congrArg (‖·‖) (hG.exp_circleAverage_herglotzRieszKernel_smul_log_norm hG0 hz)
    have hG0_ne : ‖G 0‖ ≠ 0 := norm_ne_zero_iff.2 (hG0 0 (mem_closedBall_self hr.le))
    rw [Complex.norm_exp, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), mul_div_cancel_right₀ _ hG0_ne] at hexp
    exact hexp.symm
  have hBz : ‖TauCeti.blaschkeProduct a n (z / r)‖ ≤ 1 :=
    TauCeti.norm_blaschkeProduct_le_one (fun i ↦ (ha i).le) (by
      rw [norm_div, Complex.norm_of_nonneg hr.le, div_le_one hr]
      exact (mem_ball_zero_iff.1 hz).le)
  have hint_pos : CircleIntegrable (fun w ↦ log⁺ ‖g w‖) 0 r :=
    (continuous_posLog.comp_continuousOn
      (hg.continuousOn.mono (by rw [abs_of_pos hr]; exact sphere_subset_closedBall)).norm
      ).circleIntegrable'
  have hint_G : CircleIntegrable (fun w ↦ Real.log ‖G w‖) 0 r :=
    (ContinuousOn.log
      (hG.continuousOn.mono (by rw [abs_of_pos hr]; exact sphere_subset_closedBall)).norm
      fun w hw ↦ norm_ne_zero_iff.2
        (hG0 w (sphere_subset_closedBall (abs_of_pos hr ▸ hw)))).circleIntegrable'
  have hle_re :
      (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r).re ≤
        (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (log⁺ ‖g w‖ : ℂ)) 0 r).re :=
    hint_G.re_circleAverage_herglotzRieszKernel_smul_mono hint_pos hz fun w hw ↦ by
      have hBw : ‖TauCeti.blaschkeProduct a n (w / r)‖ = 1 :=
        TauCeti.norm_blaschkeProduct_eq_one (fun i ↦ (ha i).le) (by
          rw [norm_div, Complex.norm_of_nonneg hr.le, mem_sphere_zero_iff_norm.1 hw,
            div_self hr.ne'])
      have hnorm_eq : ‖g w‖ = ‖G w‖ := by
        rw [hfac w (sphere_subset_closedBall hw), norm_mul, hBw, one_mul]
      rw [← hnorm_eq]
      exact le_max_right 0 (Real.log ‖g w‖)
  rw [hfac z (ball_subset_closedBall hz), ← mul_assoc, norm_mul, norm_mul, hGz,
    nevanlinnaMultiplierAux, Complex.norm_exp, sub_re, ofReal_re]
  calc
    Real.exp (ValueDistribution.proximity g ⊤ r -
        (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (log⁺ ‖g w‖ : ℂ)) 0 r).re) *
      ‖TauCeti.blaschkeProduct a n (z / r)‖ *
      Real.exp (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r).re
      ≤ Real.exp (ValueDistribution.proximity g ⊤ r -
          (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (log⁺ ‖g w‖ : ℂ)) 0 r).re) * 1 *
        Real.exp
          (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r).re := by
      gcongr
    _ ≤ Real.exp (ValueDistribution.proximity g ⊤ r) := by
      rw [mul_one, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)

/-- Radial continuity of both `ValueDistribution.proximity g ⊤` and
`ρ ↦ nevanlinnaMultiplierAux g ρ z` across `[r₀, r]` when `‖z‖ < r₀ ≤ r`. -/
private lemma continuousOn_proximity_and_nevanlinnaMultiplierAux {g : ℂ → ℂ} {r₀ r : ℝ} {z : ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hr₀_nn : 0 ≤ r₀) (hzr₀ : ‖z‖ < r₀) :
    ContinuousOn (ValueDistribution.proximity g ⊤) (Icc r₀ r) ∧
      ContinuousOn (fun ρ ↦ nevanlinnaMultiplierAux g ρ z) (Icc r₀ r) := by
  have hIcc_nn : ∀ ρ ∈ Icc r₀ r, 0 ≤ ρ := fun ρ hρ ↦ hr₀_nn.trans hρ.1
  have hann_sub : {w : ℂ | ‖w - 0‖ ∈ Icc r₀ r} ⊆ closedBall 0 r := fun w hw ↦ by
    simpa [mem_closedBall_zero_iff] using hw.2
  have hprox : ContinuousOn (ValueDistribution.proximity g ⊤) (Icc r₀ r) :=
    (continuous_posLog.comp_continuousOn (hg.continuousOn.mono hann_sub).norm).circleAverage
      hIcc_nn
  refine ⟨hprox, ?_⟩
  have hK : ContinuousOn (herglotzRieszKernel 0 z) {w : ℂ | ‖w - 0‖ ∈ Icc r₀ r} := by
    rw [herglotzRieszKernel_fun_def]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw ↦ ?_
    have hw_norm : r₀ ≤ ‖w‖ := by simpa using hw.1
    rw [sub_sub_sub_cancel_right, sub_ne_zero]
    rintro rfl
    linarith
  have hH : ContinuousOn
      (fun ρ ↦ circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (log⁺ ‖g w‖ : ℂ)) 0 ρ)
      (Icc r₀ r) :=
    (hK.smul (continuous_ofReal.comp_continuousOn
      (continuous_posLog.comp_continuousOn (hg.continuousOn.mono hann_sub).norm))).circleAverage
      hIcc_nn
  exact Complex.continuous_exp.comp_continuousOn
    ((continuous_ofReal.comp_continuousOn hprox).sub hH)

/-- Radial continuity removes the boundary nonvanishing assumption from
`norm_nevanlinnaMultiplierAux_mul_le_of_sphere_ne_zero` on every strict subdisc `closedBall 0 s`
(`0 ≤ s < r`). -/
private lemma norm_nevanlinnaMultiplierAux_mul_le {g : ℂ → ℂ} {s r : ℝ} {z : ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hs : 0 ≤ s) (hsr : s < r)
    (hz : z ∈ closedBall 0 s) :
    ‖nevanlinnaMultiplierAux g r z * g z‖ ≤ Real.exp (ValueDistribution.proximity g ⊤ r) := by
  rcases hg.eqOn_zero_or_eventually_ne_zero_of_preconnected (convex_closedBall 0 r).isPreconnected
    with hg0 | hcod
  · rw [hg0 (closedBall_subset_closedBall hsr.le hz), Pi.zero_apply, mul_zero, norm_zero]
    exact (Real.exp_pos _).le
  · have hfin : (closedBall 0 r \ {w | g w ≠ 0}).Finite :=
      (isCompact_closedBall 0 r).finite_sdiff_of_mem_codiscreteWithin hcod
    let t : Set ℝ := ((fun w : ℂ ↦ ‖w‖) '' (closedBall 0 r \ {w | g w ≠ 0})) ∩ Iio r
    have ht_open : IsOpen tᶜ := ((hfin.image _).inter_of_left _).isClosed.isOpen_compl
    obtain ⟨δ, hδ, hball_t⟩ := Metric.isOpen_iff.1 ht_open r fun h ↦ h.2.ne rfl
    set r₀ : ℝ := max ((s + r) / 2) (r - δ / 2)
    have hsr₀ : s < r₀ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hr₀r : r₀ < r := max_lt (by linarith) (by linarith)
    obtain ⟨hprox_cont, hmult_cont⟩ := hg.continuousOn_proximity_and_nevanlinnaMultiplierAux
      (hs.trans hsr₀.le) ((mem_closedBall_zero_iff.1 hz).trans_lt hsr₀)
    have hLHS_cont : ContinuousOn (fun ρ ↦ ‖nevanlinnaMultiplierAux g ρ z * g z‖) (Icc r₀ r) :=
      (hmult_cont.mul_const (g z)).norm
    have hRHS_cont : ContinuousOn (fun ρ ↦ Real.exp (ValueDistribution.proximity g ⊤ ρ))
        (Icc r₀ r) :=
      Real.continuous_exp.comp_continuousOn hprox_cont
    have hr_cl : r ∈ closure (Ioo r₀ r) := by
      rw [closure_Ioo hr₀r.ne]
      exact right_mem_Icc.2 hr₀r.le
    have : (𝓝[Ioo r₀ r] r).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hr_cl
    refine le_of_tendsto_of_tendsto
      ((hLHS_cont r (right_mem_Icc.2 hr₀r.le)).mono_left (nhdsWithin_mono r Ioo_subset_Icc_self))
      ((hRHS_cont r (right_mem_Icc.2 hr₀r.le)).mono_left (nhdsWithin_mono r Ioo_subset_Icc_self))
      (eventually_nhdsWithin_iff.2 (Eventually.of_forall fun ρ hρ ↦ ?_))
    refine norm_nevanlinnaMultiplierAux_mul_le_of_sphere_ne_zero
      (hg.mono (closedBall_subset_closedBall hρ.2.le)) (fun w hw hgw ↦ ?_)
      (mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hz).trans_lt (hsr₀.trans hρ.1)))
    have hρ_ball : ρ ∈ ball r δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hρ.2)]
      have hmax : r - δ / 2 < ρ := (le_max_right _ _).trans_lt hρ.1
      linarith
    exact hball_t hρ_ball
      ⟨⟨w, ⟨closedBall_subset_closedBall hρ.2.le (sphere_subset_closedBall hw), not_not.2 hgw⟩,
        mem_sphere_zero_iff_norm.1 hw⟩, hρ.2⟩

/-- **Subdisc Nevanlinna quotient multiplier.** If `g` is analytic on a neighbourhood of
`closedBall 0 r` and `s < r`, there exists `h` analytic on a neighbourhood of `closedBall 0 s` with
`h 0 = 1` such that both `log ‖h z‖` and `log ‖h z * g z‖` are bounded on `closedBall 0 s` by
`ValueDistribution.proximity g ⊤ r`. -/
theorem exists_analyticOnNhd_closedBall_log_norm_le_proximity_top {g : ℂ → ℂ} {s r : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hsr : s < r) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 s) ∧ h 0 = 1 ∧
      (∀ z ∈ closedBall 0 s, Real.log ‖h z‖ ≤ ValueDistribution.proximity g ⊤ r) ∧
      ∀ z ∈ closedBall 0 s, Real.log ‖h z * g z‖ ≤ ValueDistribution.proximity g ⊤ r := by
  rcases lt_or_ge s 0 with hs | hs
  · refine ⟨1, analyticOnNhd_const, rfl, ?_, ?_⟩ <;> simp [closedBall_eq_empty.2 hs]
  · have hr : 0 < r := lt_of_le_of_lt hs hsr
    obtain ⟨hha, hh0, hh_norm⟩ := hg.analyticOnNhd_nevanlinnaMultiplierAux_and_zero_and_norm_le hr
    have hprox_nn : 0 ≤ ValueDistribution.proximity g ⊤ r :=
      ValueDistribution.proximity_nonneg (f := g) (a := ⊤) r
    refine ⟨nevanlinnaMultiplierAux g r, hha.mono (closedBall_subset_ball hsr), hh0,
      fun z hz ↦ ?_, fun z hz ↦ ?_⟩
    · rcases eq_or_ne (nevanlinnaMultiplierAux g r z) 0 with h0 | h0
      · simpa [h0] using hprox_nn
      · exact (Real.log_le_iff_le_exp (norm_pos_iff.2 h0)).2
          (hh_norm z (closedBall_subset_ball hsr hz))
    · rcases eq_or_ne (nevanlinnaMultiplierAux g r z * g z) 0 with h0 | h0
      · simpa [h0] using hprox_nn
      · exact (Real.log_le_iff_le_exp (norm_pos_iff.2 h0)).2
          (hg.norm_nevanlinnaMultiplierAux_mul_le hs hsr hz)

/-- **Nevanlinna's quotient representation** (closed-disc pointwise form). If `g` is analytic on a
neighbourhood of `closedBall 0 R` and `0 < ε`, there exists `h` analytic on a neighbourhood of
`closedBall 0 R` with `h 0 = 1` such that `log ‖h z‖ ≤ ValueDistribution.proximity g ⊤ R + ε` and
`log ‖h z * g z‖ ≤ ValueDistribution.proximity g ⊤ R + ε` for every `z ∈ closedBall 0 R`. -/
theorem exists_analyticOnNhd_closedBall_log_norm_le_proximity_top_add {g : ℂ → ℂ} {R ε : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1 ∧
      (∀ z ∈ closedBall 0 R, Real.log ‖h z‖ ≤ ValueDistribution.proximity g ⊤ R + ε) ∧
      ∀ z ∈ closedBall 0 R, Real.log ‖h z * g z‖ ≤ ValueDistribution.proximity g ⊤ R + ε := by
  rcases lt_or_ge R 0 with hR | hR
  · refine ⟨1, analyticOnNhd_const, rfl, ?_, ?_⟩ <;> simp [closedBall_eq_empty.2 hR]
  · obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall 0 R).exists_thickening_subset_open
      (isOpen_analyticAt ℂ g) hg
    rw [thickening_closedBall hδ hR] at hsub
    set R₁ : ℝ := R + δ / 2 with hR₁_def
    have hRR₁ : R < R₁ := by linarith
    have hg₁ : AnalyticOnNhd ℂ g (closedBall 0 R₁) := fun z hz ↦
      hsub (closedBall_subset_ball (by linarith : R₁ < δ + R) hz)
    have hprox_cont : ContinuousOn (ValueDistribution.proximity g ⊤) (Icc R R₁) :=
      (continuous_posLog.comp_continuousOn
        (hg₁.continuousOn.mono fun w hw ↦ by simpa [mem_closedBall_zero_iff] using hw.2).norm
        ).circleAverage fun r hr ↦ hR.trans hr.1
    obtain ⟨η, hη, hnear⟩ := Metric.continuousWithinAt_iff.1
      (hprox_cont R (left_mem_Icc.2 hRR₁.le)) ε hε
    set r : ℝ := min R₁ (R + η / 2)
    have hRr : R < r := lt_min hRR₁ (by linarith)
    have hr_mem : r ∈ Icc R R₁ := ⟨hRr.le, min_le_left _ _⟩
    have hr_dist : dist r R < η := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 hRr)]
      have : r ≤ R + η / 2 := min_le_right _ _
      linarith
    have hprox_le : ValueDistribution.proximity g ⊤ r ≤ ValueDistribution.proximity g ⊤ R + ε := by
      have habs := Real.dist_eq _ _ ▸ hnear hr_mem hr_dist
      linarith [(abs_lt.1 habs).2]
    obtain ⟨h, hha, hh0, hh₁, hh₂⟩ :=
      (hg₁.mono (closedBall_subset_closedBall hr_mem.2)
        ).exists_analyticOnNhd_closedBall_log_norm_le_proximity_top hRr
    exact ⟨h, hha, hh0, fun z hz ↦ (hh₁ z hz).trans hprox_le, fun z hz ↦ (hh₂ z hz).trans hprox_le⟩

/-- **Nevanlinna's quotient representation** (boundary logarithmic-supremum form). If `g` is
analytic on a neighbourhood of `closedBall 0 R` and `0 < ε`, there exists `h` analytic on a
neighbourhood of `closedBall 0 R` with `h 0 = 1` such that the maximum of the boundary suprema of
`log ‖h‖` and `log ‖h * g‖` over `sphere 0 R` is at most `ValueDistribution.proximity g ⊤ R + ε`. -/
theorem exists_analyticOnNhd_closedBall_max_sSup_log_norm_le_proximity_top_add {g : ℂ → ℂ}
    {R ε : ℝ} (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1 ∧
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere 0 R))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere 0 R)) ≤
        ValueDistribution.proximity g ⊤ R + ε := by
  rcases lt_or_ge R 0 with hR | hR
  · refine ⟨1, analyticOnNhd_const, rfl, ?_⟩
    have hprox : 0 ≤ ValueDistribution.proximity g ⊤ R :=
      ValueDistribution.proximity_nonneg (f := g) (a := ⊤) R
    simp [sphere_eq_empty_of_neg hR, add_nonneg hprox hε.le]
  · obtain ⟨h, hha, hh0, hh₁, hh₂⟩ :=
      hg.exists_analyticOnNhd_closedBall_log_norm_le_proximity_top_add hε
    have hne : (sphere (0 : ℂ) R).Nonempty := ⟨R, by simp [abs_of_nonneg hR]⟩
    refine ⟨h, hha, hh0, max_le ?_ ?_⟩
    · exact csSup_le (hne.image _)
        (forall_mem_image.2 fun z hz ↦ hh₁ z (sphere_subset_closedBall hz))
    · exact csSup_le (hne.image _)
        (forall_mem_image.2 fun z hz ↦ hh₂ z (sphere_subset_closedBall hz))

/-- For nonzero `r` and circle-integrable `log⁺ ‖g‖`, uniform bounds on `log ‖h‖` and `log ‖h * g‖`
along `sphere 0 |r|` bound `m(r, g) + circleAverage (log ‖h ·‖) 0 r` by `M` across the isolated
zeros of `h`. -/
private lemma proximity_top_add_circleAverage_log_norm_le {h g : ℂ → ℂ} {r M : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 |r|)) (hh0_ne : h 0 ≠ 0) (hr : r ≠ 0)
    (hg_int : CircleIntegrable (fun z ↦ log⁺ ‖g z‖) 0 r)
    (hM₁ : ∀ z ∈ sphere 0 |r|, Real.log ‖h z‖ ≤ M)
    (hM₂ : ∀ z ∈ sphere 0 |r|, Real.log ‖h z * g z‖ ≤ M) :
    ValueDistribution.proximity g ⊤ r + circleAverage (fun z ↦ Real.log ‖h z‖) 0 r ≤ M := by
  classical
  have hh_int : CircleIntegrable (fun z ↦ Real.log ‖h z‖) 0 r :=
    (hh.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  let q : ℂ → ℝ := fun z ↦ if h z = 0 then M else log⁺ ‖g z‖ + Real.log ‖h z‖
  have hcod_cb : ∀ᶠ z in codiscreteWithin (closedBall 0 |r|), h z ≠ 0 :=
    (hh.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_closedBall 0 |r|).isPreconnected).resolve_left fun hzero ↦ hh0_ne (hzero (by simp))
  have hcod : q =ᶠ[codiscreteWithin (sphere 0 |r|)] fun z ↦ log⁺ ‖g z‖ + Real.log ‖h z‖ := by
    filter_upwards [codiscreteWithin_mono sphere_subset_closedBall hcod_cb] with z hz
    exact ite_eq_right hz
  have hq_ae : (fun θ ↦ q (circleMap 0 r θ)) =ᵐ[volume.restrict (uIoc 0 (2 * π))]
      fun θ ↦ log⁺ ‖g (circleMap 0 r θ)‖ + Real.log ‖h (circleMap 0 r θ)‖ := by
    refine ae_restrict_le_codiscreteWithin measurableSet_uIoc ?_
    exact codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete hr hcod)
  have hq_int : CircleIntegrable q 0 r := (hg_int.add hh_int).congr_ae hq_ae.symm
  have hq_le : ∀ z ∈ sphere 0 |r|, q z ≤ M := fun z hz ↦ by
    dsimp only [q]
    split_ifs with hhz
    · exact le_rfl
    · rcases eq_or_ne (g z) 0 with hgz | hgz
      · simpa [hgz] using hM₁ z hz
      · have hmul : Real.log ‖g z‖ + Real.log ‖h z‖ ≤ M := by
          rw [add_comm, ← Real.log_mul (norm_ne_zero_iff.2 hhz) (norm_ne_zero_iff.2 hgz),
            ← norm_mul]
          exact hM₂ z hz
        rcases le_total 0 (Real.log ‖g z‖) with hlg | hlg
        · simpa [posLog, hlg] using hmul
        · simpa [posLog, hlg] using hM₁ z hz
  rw [ValueDistribution.proximity_top, ← circleAverage_fun_add hg_int hh_int,
    ← circleAverage_congr_codiscreteWithin hcod hr]
  exact circleAverage_mono_on_of_le_circle hq_int hq_le

/-- **Optimality of the Nevanlinna quotient bound.** Let `h` be analytic on a neighbourhood of
`closedBall 0 |r|` with `1 ≤ ‖h 0‖`. If `log ‖h z‖ ≤ M` and `log ‖h z * g z‖ ≤ M` for every
`z ∈ sphere 0 |r|`, then `ValueDistribution.proximity g ⊤ r ≤ M`. -/
theorem proximity_top_le_of_log_norm_le {h g : ℂ → ℂ} {r M : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 |r|)) (hh0 : 1 ≤ ‖h 0‖)
    (hM₁ : ∀ z ∈ sphere 0 |r|, Real.log ‖h z‖ ≤ M)
    (hM₂ : ∀ z ∈ sphere 0 |r|, Real.log ‖h z * g z‖ ≤ M) :
    ValueDistribution.proximity g ⊤ r ≤ M := by
  have hh0_ne : h 0 ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans_le hh0)
  rcases eq_or_ne r 0 with rfl | hr
  · have h0s : (0 : ℂ) ∈ sphere 0 |0| := by simp
    have hM_nn : 0 ≤ M := (Real.log_nonneg hh0).trans (hM₁ 0 h0s)
    rw [ValueDistribution.proximity_top, circleAverage_zero]
    rcases eq_or_ne (g 0) 0 with hg0 | hg0
    · simpa [hg0] using hM_nn
    · refine max_le hM_nn ((Real.log_le_log (norm_pos_iff.2 hg0) ?_).trans (hM₂ 0 h0s))
      rw [norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hh0
  · have hh_avg_nn : 0 ≤ circleAverage (fun z ↦ Real.log ‖h z‖) 0 r := by
      have hjensen := hh.le_circleAverage_log_norm hr
      have h0cb : (0 : ℂ) ∈ closedBall 0 |r| := by simp
      have hord : analyticOrderNatAt h 0 = 0 := by
        rw [analyticOrderNatAt, (hh 0 h0cb).analyticOrderAt_eq_zero.2 hh0_ne, ENat.toNat_zero]
      rw [hord, Nat.cast_zero, zero_mul, zero_add,
        (hh 0 h0cb).meromorphicTrailingCoeffAt_of_ne_zero hh0_ne] at hjensen
      exact (Real.log_nonneg hh0).trans hjensen
    by_cases hg_int : CircleIntegrable (fun z ↦ log⁺ ‖g z‖) 0 r
    · linarith [hh.proximity_top_add_circleAverage_log_norm_le hh0_ne hr hg_int hM₁ hM₂]
    · rw [ValueDistribution.proximity_top, circleAverage.integral_undef hg_int]
      exact hh_avg_nn.trans (circleAverage_mono_on_of_le_circle
        (hh.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm hM₁)

/-- **Optimality of the Nevanlinna quotient bound** (boundary logarithmic-supremum form). If `h` is
analytic on a neighbourhood of `closedBall 0 |r|` with `1 ≤ ‖h 0‖` and `log ‖h * g‖` is bounded
above on `sphere 0 |r|` (in particular whenever `g` is continuous on `sphere 0 |r|`), then
`ValueDistribution.proximity g ⊤ r` is at most the maximum of the boundary suprema of `log ‖h‖` and
`log ‖h * g‖` over `sphere 0 |r|`. -/
theorem proximity_top_le_max_sSup_log_norm {h g : ℂ → ℂ} {r : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 |r|)) (hh0 : 1 ≤ ‖h 0‖)
    (hbdd : BddAbove ((fun z ↦ Real.log ‖h z * g z‖) '' sphere 0 |r|)) :
    ValueDistribution.proximity g ⊤ r ≤
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere 0 |r|))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere 0 |r|)) := by
  have hbdd_h : BddAbove ((fun z ↦ Real.log ‖h z‖) '' sphere 0 |r|) := by
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) |r|).bddAbove_image
      (continuous_posLog.comp_continuousOn (hh.continuousOn.mono sphere_subset_closedBall).norm)
    exact ⟨C, forall_mem_image.2 fun z hz ↦
      (le_max_right 0 _).trans (hC (mem_image_of_mem _ hz))⟩
  refine hh.proximity_top_le_of_log_norm_le hh0 (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · exact (le_csSup hbdd_h (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  · exact (le_csSup hbdd (mem_image_of_mem _ hz)).trans (le_max_right _ _)

end AnalyticOnNhd

/-! ### Examples -/

/-- Unit-disc specialization of Nevanlinna's quotient representation: any `g` analytic near
`closedBall 0 1` admits, for every `ε > 0`, an analytic multiplier `h` near `closedBall 0 1` with
`h 0 = 1` and boundary logarithmic suprema bounded by `m(1, g) + ε`. -/
example (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (closedBall 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 1) ∧ h 0 = 1 ∧
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere 0 1))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere 0 1)) ≤
        ValueDistribution.proximity g ⊤ 1 + ε :=
  hg.exists_analyticOnNhd_closedBall_max_sSup_log_norm_le_proximity_top_add hε

/-- Unit-disc specialization of optimality for two functions analytic near `closedBall 0 1` with
`h 0 = 1`. -/
example (g h : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) (hh0 : h 0 = 1) :
    ValueDistribution.proximity g ⊤ 1 ≤
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere 0 1))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere 0 1)) := by
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|) := by simpa using hh
  have hbdd : BddAbove ((fun z ↦ Real.log ‖h z * g z‖) '' sphere 0 |(1 : ℝ)|) := by
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) |(1 : ℝ)|).bddAbove_image
      (continuous_posLog.comp_continuousOn
        ((hh'.mul (by simpa using hg)).continuousOn.mono sphere_subset_closedBall).norm)
    exact ⟨C, forall_mem_image.2 fun z hz ↦
      (le_max_right 0 _).trans (hC (mem_image_of_mem _ hz))⟩
  simpa using hh'.proximity_top_le_max_sSup_log_norm (by simp [hh0]) hbdd

/-- For `g = h = 1` on `sphere 0 1`, both boundary logarithmic suprema and `m(1, 1)` vanish, so the
optimality inequality holds with equality `0 = 0`. -/
example :
    let g : ℂ → ℂ := fun _ ↦ 1
    let h : ℂ → ℂ := fun _ ↦ 1
    ValueDistribution.proximity g ⊤ 1 = 0 ∧
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere 0 1))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere 0 1)) = 0 := by
  dsimp only
  exact ⟨by simp, by simp⟩
