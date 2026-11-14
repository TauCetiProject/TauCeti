/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Poisson
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.Herglotz.Basic
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Herglotz representation of analytic logarithms and logarithmic derivatives

Let `g` be analytic and zero-free on a neighbourhood of a closed disc `closedBall c R`. When
`g c = 1`, `g` admits a unique analytic logarithm `L` on `closedBall c R` normalized by `L c = 0`.
Its real part is `log ‖g‖` on the closed disc, and on the open disc `ball c R` the Herglotz
formula recovers `L` from `log ‖g‖` on the boundary circle alone:

`L w = circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (log ‖g ζ‖ : ℂ)) c R`.

Dropping the normalization `g c = 1` shifts the Herglotz integral of `log ‖g‖` by the real
constant `log ‖g c‖`. Two consequences follow for any zero-free `g` analytic near `closedBall c R`
and any `w ∈ ball c R`:

* **Exponential phase identity:** the exponential of the Herglotz integral of `log ‖g‖` equals
  `g w * ‖g c‖ / g c`, so reconstructing `g w` requires the unimodular phase factor `g c / ‖g c‖`.
* **Differentiated Herglotz formula:** differentiating under the circle average expresses the
  logarithmic derivative `logDeriv g w = g' w / g w` directly in terms of boundary values of
  `log ‖g‖` against the differentiated kernel `2 * (ζ - c) / (ζ - w) ^ 2`.

## Main results

* `CircleIntegrable.map_add_const`,
  `CircleIntegrable.re_circleAverage_herglotzRieszKernel_smul_nonneg`,
  `CircleIntegrable.re_circleAverage_herglotzRieszKernel_smul_mono`,
  `CircleIntegrable.hasDerivAt_circleAverage_herglotzRieszKernel_smul`,
  `CircleIntegrable.differentiableOn_circleAverage_herglotzRieszKernel_smul`, and
  `CircleIntegrable.analyticOnNhd_circleAverage_herglotzRieszKernel_smul`: translation invariance,
  interior positivity and monotonicity of the real part, derivative, and analyticity of the
  Herglotz–Riesz integral on an arbitrary circle.
* `AnalyticOnNhd.eqOn_closedBall_of_eqOn_exp_comp`: an analytic logarithm on `closedBall c R` is
  uniquely determined by its value at the centre.
* `AnalyticOnNhd.exists_analyticOnNhd_closedBall_eqOn_exp_comp`: existence and Herglotz–Riesz
  integral representation of the normalized analytic logarithm when `g c = 1`.
* `AnalyticOnNhd.exp_circleAverage_herglotzRieszKernel_smul_log_norm`: exponential of the
  Herglotz–Riesz integral of `log ‖g‖`, exhibiting the phase factor `‖g c‖ / g c`.
* `AnalyticOnNhd.logDeriv_eq_circleAverage_smul_log_norm`: the differentiated Herglotz formula for
  `logDeriv g`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), proof of Lemma 2.3.1 and Lemma 6.1.7.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Chapter 11.
-/

public section

open Complex MeasureTheory Metric Real Set Filter Topology

namespace CircleIntegrable

/-- Circle integrability on `sphere c |R|` transfers to `sphere 0 |R|` by translating by `c`
(companion to `Real.circleAverage_map_add_const`). -/
theorem map_add_const {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    CircleIntegrable (fun ζ ↦ f (ζ + c)) 0 R := by
  have hmap : (fun θ ↦ f (circleMap 0 R θ + c)) = fun θ ↦ f (circleMap c R θ) := by
    ext θ
    simp [circleMap, add_comm]
  simpa only [CircleIntegrable, hmap] using hf

/-- Nonnegative circle-integrable real boundary data on `sphere c R` have nonnegative real part
after integration against `herglotzRieszKernel c w` at any interior point `w ∈ ball c R`. -/
theorem re_circleAverage_herglotzRieszKernel_smul_nonneg {u : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hu : CircleIntegrable u c R) (hw : w ∈ ball c R) (hnonneg : ∀ ζ ∈ sphere c R, 0 ≤ u ζ) :
    0 ≤ (circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (u ζ : ℂ)) c R).re := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hw₀ : w - c ∈ ball (0 : ℂ) R := by simpa [mem_ball, dist_eq_norm] using hw
  have hw₀s : w - c ∉ sphere (0 : ℂ) |R| := by
    rw [abs_of_pos hR]
    exact Set.disjoint_right.mp sphere_disjoint_ball hw₀
  have hshift : circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (u ζ : ℂ)) c R =
      circleAverage (fun ζ ↦ herglotzRieszKernel 0 (w - c) ζ • (u (ζ + c) : ℂ)) 0 R := by
    rw [← circleAverage_map_add_const]
    simp [herglotzRieszKernel_add_const]
  rw [hshift, re_circleAverage_herglotzRieszKernel_smul hu.map_add_const hw₀s]
  refine circleAverage_nonneg_of_nonneg fun ζ hζ ↦ ?_
  rw [abs_of_pos hR] at hζ
  have hre : 0 ≤ (herglotzRieszKernel 0 (w - c) ζ).re := by
    have hlow : 0 ≤ (R - ‖w - c - 0‖) / (R + ‖w - c - 0‖) :=
      div_nonneg (sub_nonneg.2 (by simpa using (mem_ball_zero_iff.1 hw₀).le)) (by positivity)
    exact hlow.trans (by simpa [herglotzRieszKernel_def] using le_re_herglotzRieszKernel hζ hw₀)
  exact mul_nonneg hre (hnonneg (ζ + c) (by simpa [mem_sphere, dist_eq_norm] using hζ))

/-- Pointwise order on `sphere c R` between circle-integrable real functions is preserved by the
real part of the Herglotz–Riesz integral at any interior point `w ∈ ball c R`. -/
theorem re_circleAverage_herglotzRieszKernel_smul_mono {u₁ u₂ : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hu₁ : CircleIntegrable u₁ c R) (hu₂ : CircleIntegrable u₂ c R) (hw : w ∈ ball c R)
    (hle : ∀ ζ ∈ sphere c R, u₁ ζ ≤ u₂ ζ) :
    (circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (u₁ ζ : ℂ)) c R).re ≤
      (circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (u₂ ζ : ℂ)) c R).re := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hK : ContinuousOn (herglotzRieszKernel c w) (sphere c |R|) :=
    continuousOn_herglotzRieszKernel_sphere (by
      rw [abs_of_pos hR]; exact Set.disjoint_right.mp sphere_disjoint_ball hw)
  have hu₁C : CircleIntegrable (fun ζ ↦ (u₁ ζ : ℂ)) c R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hu₁ ⊢
    exact Complex.ofRealCLM.integrable_comp hu₁
  have hu₂C : CircleIntegrable (fun ζ ↦ (u₂ ζ : ℂ)) c R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hu₂ ⊢
    exact Complex.ofRealCLM.integrable_comp hu₂
  have hC₁ : CircleIntegrable (fun ζ ↦ herglotzRieszKernel c w ζ • (u₁ ζ : ℂ)) c R :=
    hu₁C.continuousOn_smul hK
  have hC₂ : CircleIntegrable (fun ζ ↦ herglotzRieszKernel c w ζ • (u₂ ζ : ℂ)) c R :=
    hu₂C.continuousOn_smul hK
  have hnn := (hu₂.sub hu₁).re_circleAverage_herglotzRieszKernel_smul_nonneg hw fun ζ hζ ↦
    sub_nonneg.2 (hle ζ hζ)
  have hsub :
      circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • ((u₂ - u₁) ζ : ℂ)) c R =
        circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (u₂ ζ : ℂ)) c R -
          circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (u₁ ζ : ℂ)) c R := by
    rw [← circleAverage_sub hC₂ hC₁]
    exact circleAverage_congr_sphere fun ζ _ ↦ by simp [mul_sub]
  rw [hsub, sub_re, sub_nonneg] at hnn
  exact hnn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {c w : ℂ} {R : ℝ}

/-- **Derivative of the Herglotz–Riesz kernel integral** on an arbitrary circle: if `f` is circle
integrable on `sphere c |R|` and `w` does not lie on that circle, then the Herglotz–Riesz integral
has derivative `circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R` at `w`. -/
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun z ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c z ζ • f ζ) c R)
      (circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R) w := by
  let f₀ : ℂ → E := fun ζ ↦ f (ζ + c)
  have hf₀ : CircleIntegrable f₀ 0 R := hf.map_add_const
  have hw₀ : w - c ∉ sphere (0 : ℂ) |R| := by
    simpa [mem_sphere, dist_eq_norm] using hw
  have hfun : (fun z ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c z ζ • f ζ) c R) =
      fun z ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 (z - c) ζ • f₀ ζ) 0 R := by
    ext z
    rw [← circleAverage_map_add_const]
    simp [f₀, herglotzRieszKernel_add_const]
  have hd :=
    (_root_.hasDerivAt_circleAverage_herglotzRieszKernel_smul hf₀ hw₀).scomp w
      ((hasDerivAt_id' w).sub_const c)
  rw [hfun]
  refine hd.congr_deriv ?_
  rw [one_smul]
  symm
  rw [← circleAverage_map_add_const]
  refine circleAverage_congr_sphere fun ζ _ ↦ ?_
  have hζ : ζ + c - w = ζ - (w - c) := by ring
  simp [f₀, hζ]

/-- The Herglotz–Riesz kernel integral of a circle-integrable function on `sphere c |R|` is
holomorphic throughout the complement of that circle. -/
theorem differentiableOn_circleAverage_herglotzRieszKernel_smul
    (hf : CircleIntegrable f c R) :
    DifferentiableOn ℂ
      (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • f ζ) c R)
      (sphere c |R|)ᶜ := fun _ hw ↦
  (hf.hasDerivAt_circleAverage_herglotzRieszKernel_smul hw).differentiableAt.differentiableWithinAt

/-- The Herglotz–Riesz kernel integral of a circle-integrable function on `sphere c |R|` into a
complete space is analytic throughout the complement of that circle. -/
theorem analyticOnNhd_circleAverage_herglotzRieszKernel_smul [CompleteSpace E]
    (hf : CircleIntegrable f c R) :
    AnalyticOnNhd ℂ
      (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • f ζ) c R)
      (sphere c |R|)ᶜ :=
  hf.differentiableOn_circleAverage_herglotzRieszKernel_smul.analyticOnNhd
    isClosed_sphere.isOpen_compl

end CircleIntegrable

namespace AnalyticOnNhd

variable {g L₁ L₂ : ℂ → ℂ} {c w : ℂ} {R : ℝ}

/-- Two functions analytic near `closedBall c R` with the same exponential on `closedBall c R` and
the same value at the centre `c` agree everywhere on `closedBall c R`. -/
theorem eqOn_closedBall_of_eqOn_exp_comp
    (hL₁ : AnalyticOnNhd ℂ L₁ (closedBall c R))
    (hL₂ : AnalyticOnNhd ℂ L₂ (closedBall c R))
    (hexp : EqOn (Complex.exp ∘ L₁) (Complex.exp ∘ L₂) (closedBall c R))
    (hc : L₁ c = L₂ c) :
    EqOn L₁ L₂ (closedBall c R) := by
  rcases lt_trichotomy R 0 with hR | rfl | hR
  · simp [closedBall_eq_empty.2 hR]
  · intro z hz
    rw [closedBall_zero, mem_singleton_iff] at hz
    exact hz ▸ hc
  · have hball : EqOn L₁ L₂ (ball c R) :=
      TauCeti.eqOn_of_eqOn_exp_comp isOpen_ball (convex_ball c R).isPreconnected
        (hL₁.differentiableOn.mono ball_subset_closedBall)
        (hL₂.differentiableOn.mono ball_subset_closedBall)
        (hexp.mono ball_subset_closedBall) (fun _ _ ↦ rfl) (mem_ball_self hR) hc
    exact hball.of_subset_closure hL₁.continuousOn hL₂.continuousOn ball_subset_closedBall
      (closure_ball c hR.ne').symm.subset

/-- **Herglotz representation of a normalized analytic logarithm.** If `g` is analytic and
zero-free on a neighbourhood of `closedBall c R` with `g c = 1`, then `g` has an analytic
logarithm `L` on `closedBall c R` with `L c = 0` (unique on `closedBall c R` by
`AnalyticOnNhd.eqOn_closedBall_of_eqOn_exp_comp`), satisfying `(L z).re = log ‖g z‖` on
`closedBall c R` and represented on `ball c R` as the Herglotz–Riesz integral of `log ‖g‖`. -/
theorem exists_analyticOnNhd_closedBall_eqOn_exp_comp
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg0 : ∀ z ∈ closedBall c R, g z ≠ 0) (hgc : g c = 1) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (closedBall c R) ∧ L c = 0 ∧
      EqOn (Complex.exp ∘ L) g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, (L z).re = Real.log ‖g z‖) ∧
      ∀ w ∈ ball c R, L w =
        circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g ζ‖ : ℂ)) c R := by
  rcases lt_or_ge R 0 with hR | hR
  · refine ⟨0, ?_, rfl, ?_, ?_, ?_⟩ <;>
      simp [closedBall_eq_empty.2 hR, ball_eq_empty.2 hR.le]
  -- Thicken `closedBall c R` inside the open zero-free analyticity locus of `g`.
  set U : Set ℂ := {z | AnalyticAt ℂ g z} ∩ g ⁻¹' {0}ᶜ
  have hUo : IsOpen U :=
    (AnalyticOnNhd.continuousOn fun _ hz ↦ hz).isOpen_inter_preimage (isOpen_analyticAt ℂ g)
      isOpen_compl_singleton
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c R).exists_thickening_subset_open hUo
    fun z hz ↦ ⟨hg z hz, hg0 z hz⟩
  rw [thickening_closedBall hδ hR] at hsub
  have hδR : 0 < δ + R := add_pos_of_pos_of_nonneg hδ hR
  have hsc : IsSimplyConnected (ball c (δ + R)) :=
    (convex_ball c (δ + R)).isSimplyConnected ⟨c, mem_ball_self hδR⟩
  have hgd : DifferentiableOn ℂ g (ball c (δ + R)) := fun z hz ↦
    (hsub hz).1.differentiableAt.differentiableWithinAt
  have hg_img : (0 : ℂ) ∉ g '' ball c (δ + R) := by
    rintro ⟨z, hz, hz0⟩
    exact (hsub hz).2 hz0
  obtain ⟨L₀, hL₀d, hL₀exp⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp hsc isOpen_ball hgd
    hg_img
  let L : ℂ → ℂ := fun z ↦ L₀ z - L₀ c
  have hcb_sub : closedBall c R ⊆ ball c (δ + R) := closedBall_subset_ball (lt_add_of_pos_left R hδ)
  have hLa : AnalyticOnNhd ℂ L (closedBall c R) :=
    ((hL₀d.sub_const _).analyticOnNhd isOpen_ball).mono hcb_sub
  have hLc : L c = 0 := sub_self _
  have hLexp : EqOn (Complex.exp ∘ L) g (closedBall c R) := fun z hz ↦ by
    have hz' := hL₀exp (hcb_sub hz)
    have hc' := hL₀exp (mem_ball_self hδR)
    simp only [Function.comp_apply] at hz' hc' ⊢
    rw [hgc] at hc'
    rw [Complex.exp_sub, hz', hc', div_one]
  have hLre : ∀ z ∈ closedBall c R, (L z).re = Real.log ‖g z‖ := fun z hz ↦ by
    have h := congrArg (fun u ↦ Real.log ‖u‖) (hLexp hz)
    simpa [Complex.norm_exp] using h
  refine ⟨L, hLa, hLc, hLexp, hLre, fun w hw ↦ ?_⟩
  have hRpos : 0 < R := pos_of_mem_ball hw
  have hcl : DiffContOnCl ℂ L (ball c R) :=
    (hLa.mono (closure_ball c hRpos.ne').subset).differentiableOn.diffContOnCl
  have hherg := hcl.circleAverage_herglotzRieszKernel_smul_re_add hw
  rw [hLc, zero_im, ofReal_zero, zero_mul, add_zero] at hherg
  rw [← hherg]
  refine circleAverage_congr_sphere fun ζ hζ ↦ ?_
  rw [abs_of_pos hRpos] at hζ
  rw [hLre ζ (sphere_subset_closedBall hζ)]

/-- Decomposition of the Herglotz–Riesz integral of `log ‖g‖` into the normalized analytic
logarithm of `g / g c` plus the constant `log ‖g c‖`. -/
private lemma exists_normalized_log_add_eq_circleAverage
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg0 : ∀ z ∈ closedBall c R, g z ≠ 0) (hR : 0 < R) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (closedBall c R) ∧ L c = 0 ∧
      EqOn (Complex.exp ∘ L) (fun z ↦ g z / g c) (closedBall c R) ∧
      ∀ w ∈ ball c R,
        circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g ζ‖ : ℂ)) c R =
          L w + (Real.log ‖g c‖ : ℂ) := by
  have hgc : g c ≠ 0 := hg0 c (mem_closedBall_self hR.le)
  have hg₁ : AnalyticOnNhd ℂ (fun z ↦ g z / g c) (closedBall c R) :=
    hg.div analyticOnNhd_const fun _ _ ↦ hgc
  obtain ⟨L, hLa, hLc, hLexp, -, hLherg⟩ :=
    hg₁.exists_analyticOnNhd_closedBall_eqOn_exp_comp
      (fun z hz ↦ div_ne_zero (hg0 z hz) hgc) (div_self hgc)
  refine ⟨L, hLa, hLc, hLexp, fun w hw ↦ ?_⟩
  have hcont : ContinuousOn (fun ζ ↦ (Real.log ‖g ζ‖ : ℂ)) (sphere c |R|) := by
    refine continuous_ofReal.comp_continuousOn (ContinuousOn.log ?_ ?_)
    · exact (hg.continuousOn.mono (by rw [abs_of_pos hR]; exact sphere_subset_closedBall)).norm
    · intro ζ hζ
      rw [abs_of_pos hR] at hζ
      exact norm_ne_zero_iff.2 (hg0 ζ (sphere_subset_closedBall hζ))
  have hK : ContinuousOn (herglotzRieszKernel c w) (sphere c |R|) :=
    continuousOn_herglotzRieszKernel_sphere (by
      rw [abs_of_pos hR]
      exact Set.disjoint_right.mp sphere_disjoint_ball hw)
  have hint₁ : CircleIntegrable (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g ζ‖ : ℂ)) c R :=
    hcont.circleIntegrable'.continuousOn_smul hK
  have hint₂ : CircleIntegrable
      (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g c‖ : ℂ)) c R :=
    (continuousOn_const.circleIntegrable').continuousOn_smul hK
  have hconst : circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g c‖ : ℂ)) c R =
      (Real.log ‖g c‖ : ℂ) := by
    have hcl : DiffContOnCl ℂ (fun _ : ℂ ↦ (Real.log ‖g c‖ : ℂ)) (ball c R) :=
      differentiableOn_const _ |>.diffContOnCl
    simpa using hcl.circleAverage_herglotzRieszKernel_smul_re_add hw
  have hsub : L w =
      circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g ζ‖ : ℂ)) c R -
        circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g c‖ : ℂ)) c R := by
    rw [hLherg w hw, ← circleAverage_sub hint₁ hint₂]
    refine circleAverage_congr_sphere fun ζ hζ ↦ ?_
    rw [abs_of_pos hR] at hζ
    have hζ0 : ‖g ζ‖ ≠ 0 := norm_ne_zero_iff.2 (hg0 ζ (sphere_subset_closedBall hζ))
    simp [Real.log_div hζ0 (norm_ne_zero_iff.2 hgc), mul_sub]
  rw [hconst] at hsub
  linear_combination -hsub

/-- **Exponential Herglotz identity and phase factor.** For `g` analytic and zero-free near
`closedBall c R` and `w ∈ ball c R`, the exponential of the Herglotz–Riesz integral of `log ‖g‖`
is `g w * ‖g c‖ / g c`; multiplying by the unimodular constant `g c / ‖g c‖` recovers `g w`. -/
theorem exp_circleAverage_herglotzRieszKernel_smul_log_norm
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg0 : ∀ z ∈ closedBall c R, g z ≠ 0) (hw : w ∈ ball c R) :
    Complex.exp (circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (Real.log ‖g ζ‖ : ℂ)) c R) =
      g w * ‖g c‖ / g c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hgc : g c ≠ 0 := hg0 c (mem_closedBall_self hR.le)
  obtain ⟨L, -, -, hLexp, hherg⟩ := hg.exists_normalized_log_add_eq_circleAverage hg0 hR
  have hw_exp := hLexp (ball_subset_closedBall hw)
  simp only [Function.comp_apply] at hw_exp
  rw [hherg w hw, Complex.exp_add, hw_exp, ← ofReal_exp, Real.exp_log (norm_pos_iff.2 hgc),
    div_mul_eq_mul_div]

/-- **Differentiated Herglotz formula for the logarithmic derivative.** If `g` is analytic and
zero-free near `closedBall c R`, then at every `w ∈ ball c R` its logarithmic derivative
`logDeriv g w = deriv g w / g w` is the circle average of `log ‖g‖` against the differentiated
Herglotz–Riesz kernel `2 * (ζ - c) / (ζ - w) ^ 2`. No normalization at `c` is required. -/
theorem logDeriv_eq_circleAverage_smul_log_norm
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg0 : ∀ z ∈ closedBall c R, g z ≠ 0) (hw : w ∈ ball c R) :
    logDeriv g w =
      circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • (Real.log ‖g ζ‖ : ℂ)) c R := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hgc : g c ≠ 0 := hg0 c (mem_closedBall_self hR.le)
  obtain ⟨L, hLa, -, hLexp, hherg⟩ := hg.exists_normalized_log_add_eq_circleAverage hg0 hR
  have hint : CircleIntegrable (fun ζ ↦ (Real.log ‖g ζ‖ : ℂ)) c R := by
    refine (continuous_ofReal.comp_continuousOn (ContinuousOn.log ?_ ?_)).circleIntegrable'
    · exact (hg.continuousOn.mono (by rw [abs_of_pos hR]; exact sphere_subset_closedBall)).norm
    · intro ζ hζ
      rw [abs_of_pos hR] at hζ
      exact norm_ne_zero_iff.2 (hg0 ζ (sphere_subset_closedBall hζ))
  have hw_not_sphere : w ∉ sphere c |R| := by
    rw [abs_of_pos hR]
    exact Set.disjoint_right.mp sphere_disjoint_ball hw
  have hderiv_H :
      deriv (fun z ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c z ζ • (Real.log ‖g ζ‖ : ℂ)) c R)
        w = circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • (Real.log ‖g ζ‖ : ℂ)) c R :=
    (hint.hasDerivAt_circleAverage_herglotzRieszKernel_smul hw_not_sphere).deriv
  have hev :
      (fun z ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c z ζ • (Real.log ‖g ζ‖ : ℂ)) c R) =ᶠ[𝓝 w]
        fun z ↦ L z + (Real.log ‖g c‖ : ℂ) :=
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) fun z hz ↦ hherg z hz
  rw [← hderiv_H, hev.deriv_eq, deriv_add_const,
    TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_ball
      (hLa.differentiableOn.mono ball_subset_closedBall)
      (hLexp.mono ball_subset_closedBall) hw]
  simp only [div_eq_mul_inv]
  exact (logDeriv_mul_const w (g c)⁻¹ (inv_ne_zero hgc)).symm

end AnalyticOnNhd

/-! ### Examples

For the unimodular constant `G = fun _ ↦ I` on `closedBall 0 r` (`0 < r`), `log ‖G‖` vanishes on
the boundary circle so the Herglotz–Riesz integral is `0` and its exponential is `1`; multiplying
by the phase factor `G 0 / ‖G 0‖ = I` recovers `G z = I`. -/

example {r : ℝ} {z : ℂ} (hz : z ∈ ball 0 r) :
    let G : ℂ → ℂ := fun _ ↦ I
    G 0 / ‖G 0‖ *
      Complex.exp (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r) =
      I := by
  dsimp only
  have hG : AnalyticOnNhd ℂ (fun _ : ℂ ↦ I) (closedBall 0 r) := analyticOnNhd_const
  rw [hG.exp_circleAverage_herglotzRieszKernel_smul_log_norm (fun _ _ ↦ I_ne_zero) hz]
  simp
