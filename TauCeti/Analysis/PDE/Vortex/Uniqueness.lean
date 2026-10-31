/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
public import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Uniqueness of plane vortices with the same zeros

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`. Let `x` and `y` be `C²` solutions of the
plane vortex equation on the whole plane with `|α| → 1` at infinity, and suppose that their
sections differ by a nowhere-vanishing `C²` factor, `α_x = h α_y`, while the zero set of `α_y` has
empty interior. Then `x` is the phase gauge transform of `y` by a `C²` phase `f` with
`h = exp (i f)` (`TauCeti.Vortex.exists_eq_phaseGauge_of_forall_section_eq_mul`).

The argument is Taubes's. Away from the zeros of `α_y`, the scalar equations
`Δ log |α|² = (|α|² - 1) / 4` of the two fields show that `w = log |h|²` satisfies

`Δ w = (p_y² + q_y²) (|h|² - 1)`

(`TauCeti.Vortex.laplacian_log_norm_sq_eq`), and by continuity this holds everywhere. Since `w`
and `|h|² - 1` have the same sign, `w Δ w ≥ 0`, and `w → 0` at infinity, so the Liouville form
of the weak maximum principle forces `w = 0`, that is `|h| = 1`
(`TauCeti.Vortex.norm_eq_one_of_forall_section_eq_mul`). A smooth logarithm of `h` supplies the
phase (`TauCeti.exists_contDiff_eq_exp_ofReal_mul_I`). Finally, wherever `α ≠ 0` the
holomorphicity equation `∂bar_a α = 0` determines the connection from the section
(`TauCeti.Vortex.eq_of_forall_section_eq`), which identifies `x` with the gauge transform of `y`.

Only uniqueness is proved, and the zeros enter through the factor `h`. The sections of two
vortices with the same zeros, counted with multiplicity, differ by such a factor because of the
local holomorphic structure of `∂bar_a`; that comparison, and the existence of a vortex with
prescribed zeros, are not addressed here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology InnerProductSpace Laplacian

/-- If the sections satisfy `α_x = h α_y` at `z`, then `p_x² + q_x² = |h|² (p_y² + q_y²)`. -/
private theorem sq_add_sq_eq_norm_sq_mul {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ}
    {z : ℂ} (hα : (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I)) :
    x z 2 ^ 2 + x z 3 ^ 2 = ‖h z‖ ^ 2 * (y z 2 ^ 2 + y z 3 ^ 2) := by
  have := congrArg normSq hα
  rw [normSq_mul, normSq_add_mul_I, normSq_add_mul_I] at this
  rw [this, Complex.sq_norm]

/-- **The scalar equation for the ratio of two vortex sections.** Let `x` and `y` solve the vortex
equation near `z`, with sections related by `α_x = h α_y` near `z` for a `C²` factor `h` with
`h z ≠ 0`. If `α_y (z) ≠ 0`, then `Δ log |h|² = (p_y² + q_y²) (|h|² - 1)` at `z`. -/
theorem laplacian_log_norm_sq_eq {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ} {z : ℂ}
    (hx : ContDiffAt ℝ 2 x z) (hy : ContDiffAt ℝ 2 y z)
    (hxsol : ∀ᶠ w in 𝓝 z, equation x w = 0) (hysol : ∀ᶠ w in 𝓝 z, equation y w = 0)
    (hh : ContDiffAt ℝ 2 h z) (hhz : h z ≠ 0)
    (hα : ∀ᶠ w in 𝓝 z, (x w 2 + x w 3 * I : ℂ) = h w * (y w 2 + y w 3 * I))
    (hyz : y z 2 ^ 2 + y z 3 ^ 2 ≠ 0) :
    Δ (fun w ↦ Real.log (‖h w‖ ^ 2)) z = (y z 2 ^ 2 + y z 3 ^ 2) * (‖h z‖ ^ 2 - 1) := by
  have hxi := (contDiffAt_piLp _).1 hx
  have hyi := (contDiffAt_piLp _).1 hy
  have hhz' : ‖h z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hhz)
  have hxz : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by
    rw [sq_add_sq_eq_norm_sq_mul hα.self_of_nhds]
    exact mul_ne_zero hhz' hyz
  have hw : ContDiffAt ℝ 2 (fun w ↦ Real.log (‖h w‖ ^ 2)) z := (hh.norm_sq ℝ).log hhz'
  have hℓy : ContDiffAt ℝ 2 (fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2))) z :=
    (contDiffAt_const.mul (((hyi 2).pow 2).add ((hyi 3).pow 2))).log
      (mul_ne_zero four_ne_zero hyz)
  -- Near `z`, `log |α_x|² = log |h|² + log |α_y|²`.
  have hev : (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =ᶠ[𝓝 z]
      (fun w ↦ Real.log (‖h w‖ ^ 2)) + fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2)) := by
    have hy₀ : ∀ᶠ w in 𝓝 z, y w 2 ^ 2 + y w 3 ^ 2 ≠ 0 :=
      (((hyi 2).continuousAt.pow 2).add ((hyi 3).continuousAt.pow 2)).eventually_ne hyz
    filter_upwards [hα, hh.continuousAt.eventually_ne hhz, hy₀] with w hαw hhw hyw
    rw [Pi.add_apply, sq_add_sq_eq_norm_sq_mul hαw, mul_left_comm,
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 hhw)) (mul_ne_zero four_ne_zero hyw)]
  have hΔ := (laplacian_congr_nhds hev).eq_of_nhds
  rw [hw.laplacian_add hℓy,
    laplacian_log_normSq_of_equation_eq_zero ((hxi 0).differentiableAt two_ne_zero)
      ((hxi 1).differentiableAt two_ne_zero) (hxi 2) (hxi 3) hxz hxsol,
    laplacian_log_normSq_of_equation_eq_zero ((hyi 0).differentiableAt two_ne_zero)
      ((hyi 1).differentiableAt two_ne_zero) (hyi 2) (hyi 3) hyz hysol,
    sq_add_sq_eq_norm_sq_mul hα.self_of_nhds] at hΔ
  linarith

/-- **Two vortices whose sections differ by a nonvanishing factor have sections of equal
modulus.** Let `x` and `y` be `C²` solutions of the vortex equation on the plane with `|α| → 1` at
infinity, whose sections satisfy `α_x = h α_y` for a nowhere-vanishing `C²` function `h`. If the
zero set of `α_y` has empty interior, then `|h| = 1` everywhere. -/
theorem norm_eq_one_of_forall_section_eq_mul {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ}
    (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hylim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hh : ContDiff ℝ 2 h) (hh₀ : ∀ z, h z ≠ 0)
    (hα : ∀ z, (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I))
    (hdense : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0}) (z : ℂ) :
    ‖h z‖ = 1 := by
  have hh₀' (z : ℂ) : ‖h z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (hh₀ z))
  have hw : ContDiff ℝ 2 fun z ↦ Real.log (‖h z‖ ^ 2) := (hh.norm_sq ℝ).log hh₀'
  have hyc (i : Fin 4) : Continuous fun z ↦ y z i := ((contDiff_piLp _).1 hy i).continuous
  -- The scalar equation for `w = log |h|²` holds off the zeros of `α_y`, hence everywhere.
  have hΔ : Δ (fun z ↦ Real.log (‖h z‖ ^ 2)) =
      fun z ↦ (y z 2 ^ 2 + y z 3 ^ 2) * (‖h z‖ ^ 2 - 1) :=
    hw.continuous_laplacian.ext_on hdense
      ((((hyc 2).pow 2).add ((hyc 3).pow 2)).mul ((hh.continuous.norm.pow 2).sub continuous_const))
      fun z hz ↦ laplacian_log_norm_sq_eq hx.contDiffAt hy.contDiffAt (.of_forall hxsol)
        (.of_forall hysol) hh.contDiffAt (hh₀ z) (.of_forall hα) hz
  -- Since `log t` and `t - 1` have the same sign, `w Δ w ≥ 0`.
  have hsign (z : ℂ) : 0 ≤ Real.log (‖h z‖ ^ 2) * Δ (fun z ↦ Real.log (‖h z‖ ^ 2)) z := by
    have ht : 0 < ‖h z‖ ^ 2 := lt_of_le_of_ne (by positivity) (hh₀' z).symm
    rw [hΔ, mul_left_comm]
    refine mul_nonneg (by positivity) ?_
    rcases le_total 1 (‖h z‖ ^ 2) with h₁ | h₁
    · exact mul_nonneg (Real.log_nonneg h₁) (sub_nonneg.2 h₁)
    · exact mul_nonneg_of_nonpos_of_nonpos (Real.log_nonpos ht.le h₁) (sub_nonpos.2 h₁)
  -- At infinity `|h|² = |α_x|² / |α_y|² → 1`, so `w → 0`.
  have hlim : Tendsto (fun z ↦ Real.log (‖h z‖ ^ 2)) (cocompact ℂ) (𝓝 0) := by
    have hnorm : Tendsto (fun z ↦ ‖h z‖ ^ 2) (cocompact ℂ) (𝓝 1) := by
      have hdiv := hxlim.div hylim one_ne_zero
      rw [div_one] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [hylim.eventually_ne one_ne_zero] with z hz
      rw [Pi.div_apply, div_eq_iff hz, sq_add_sq_eq_norm_sq_mul (hα z)]
      ring
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hnorm
    rwa [Real.log_one] at hlog
  have hw₀ := congrFun (eq_zero_of_tendsto_cocompact_of_mul_laplacian_nonneg hw hsign hlim) z
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
    (Real.eq_one_of_pos_of_log_eq_zero (lt_of_le_of_ne (by positivity) (hh₀' z).symm) hw₀)

/-- **The section of a vortex determines its connection where it does not vanish.** If two fields
satisfy the holomorphicity equation `∂bar_a α = 0`, have continuous components and the same
section, and the zero set of that section has empty interior, then the fields are equal. -/
theorem eq_of_forall_section_eq {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ∀ i, Continuous fun z ↦ x z i) (hy : ∀ i, Continuous fun z ↦ y z i)
    (hxsol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hysol : ∀ z, equation y z 1 = 0 ∧ equation y z 2 = 0)
    (h₂ : ∀ z, x z 2 = y z 2) (h₃ : ∀ z, x z 3 = y z 3)
    (hdense : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0}) : x = y := by
  -- Off the zeros of the section, the two holomorphicity equations are a nondegenerate linear
  -- system for the difference of the connections.
  have hb (z : ℂ) (hz : y z 2 ^ 2 + y z 3 ^ 2 ≠ 0) : x z 0 = y z 0 ∧ x z 1 = y z 1 := by
    obtain ⟨hx₁, hx₂⟩ := hxsol z
    obtain ⟨hy₁, hy₂⟩ := hysol z
    simp only [equation_apply_one, equation_apply_two, h₂, h₃] at hx₁ hx₂ hy₁ hy₂
    have e₀ : (x z 0 - y z 0) * (y z 2 ^ 2 + y z 3 ^ 2) = 0 := by
      linear_combination -y z 3 * (hx₁ - hy₁) + y z 2 * (hx₂ - hy₂)
    have e₁ : (x z 1 - y z 1) * (y z 2 ^ 2 + y z 3 ^ 2) = 0 := by
      linear_combination -y z 2 * (hx₁ - hy₁) - y z 3 * (hx₂ - hy₂)
    exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 e₀).resolve_right hz),
      sub_eq_zero.1 ((mul_eq_zero.1 e₁).resolve_right hz)⟩
  have h₀ := (hx 0).ext_on hdense (hy 0) fun z hz ↦ (hb z hz).1
  have h₁ := (hx 1).ext_on hdense (hy 1) fun z hz ↦ (hb z hz).2
  ext z i
  fin_cases i
  exacts [congrFun h₀ z, congrFun h₁ z, h₂ z, h₃ z]

/-- **Uniqueness of plane vortices with the same zeros, modulo gauge.** Let `x` and `y` be `C²`
solutions of the vortex equation on the plane with `|α| → 1` at infinity, whose sections satisfy
`α_x = h α_y` for a nowhere-vanishing `C²` function `h`, and suppose the zero set of `α_y` has
empty interior. Then `h = exp (i f)` for a `C²` real phase `f`, and `x` is the phase gauge
transform of `y` by `f`. -/
theorem exists_eq_phaseGauge_of_forall_section_eq_mul {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    {h : ℂ → ℂ} (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hylim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hh : ContDiff ℝ 2 h) (hh₀ : ∀ z, h z ≠ 0)
    (hα : ∀ z, (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I))
    (hdense : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0}) :
    ∃ f : ℂ → ℝ, ContDiff ℝ 2 f ∧ (∀ z, h z = exp (f z * I)) ∧ x = phaseGauge y f := by
  have hnorm := norm_eq_one_of_forall_section_eq_mul hx hy hxsol hysol hxlim hylim hh hh₀ hα
    hdense
  obtain ⟨f, hf, hhf⟩ := exists_contDiff_eq_exp_ofReal_mul_I hh hnorm
  refine ⟨f, hf, hhf, ?_⟩
  -- The gauge transform of `y` has the section of `x` and solves the vortex equation.
  have hyd (z : ℂ) (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    (((contDiff_piLp _).1 hy i).differentiable two_ne_zero) z
  have hsec (z : ℂ) : x z 2 = phaseGauge y f z 2 ∧ x z 3 = phaseGauge y f z 3 := by
    have h₂ := congrArg re (hα z)
    have h₃ := congrArg im (hα z)
    simp only [hhf z, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] at h₂ h₃
    rw [phaseGauge_apply_two, phaseGauge_apply_three]
    constructor <;> linarith
  have hfd : Continuous fun z ↦ fderiv ℝ f z := hf.continuous_fderiv two_ne_zero
  refine eq_of_forall_section_eq (fun i ↦ ((contDiff_piLp _).1 hx i).continuous)
    (fun i ↦ ?_) (fun z ↦ ⟨by simp [hxsol z], by simp [hxsol z]⟩) (fun z ↦ ?_)
    (fun z ↦ (hsec z).1) (fun z ↦ (hsec z).2) ?_
  · have hyc (j : Fin 4) : Continuous fun z ↦ y z j := ((contDiff_piLp _).1 hy j).continuous
    have hfc : Continuous f := hf.continuous
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, phaseGauge_apply_zero,
        phaseGauge_apply_one, phaseGauge_apply_two, phaseGauge_apply_three] <;>
      fun_prop
  · have hsol := (equation_phaseGauge_eq_zero_iff (hyd z) hf.contDiffAt).2 (hysol z)
    exact ⟨by simp [hsol], by simp [hsol]⟩
  · -- `α_x` and `α_y` have the same modulus, so they have the same zeros.
    refine hdense.mono fun z hz ↦ ?_
    have hsq : phaseGauge y f z 2 ^ 2 + phaseGauge y f z 3 ^ 2 = y z 2 ^ 2 + y z 3 ^ 2 := by
      rw [phaseGauge_apply_two, phaseGauge_apply_three]
      linear_combination (y z 2 ^ 2 + y z 3 ^ 2) * Real.sin_sq_add_cos_sq (f z)
    rw [Set.mem_ofPred_eq] at hz ⊢
    rwa [hsq]

end TauCeti.Vortex
