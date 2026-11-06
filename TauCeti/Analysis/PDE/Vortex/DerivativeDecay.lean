/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Energy
import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import TauCeti.Analysis.InnerProductSpace.Laplacian.Liouville
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Exponential decay of the covariant derivative of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. For a vortex on the
whole plane with `|α| → 1` at infinity, the modulus defect and the curvature decay exponentially
at every rate `c < 1 / 2` (`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`). This file proves the
same decay for the covariant derivative of the section: for every `c < 1 / 2` there is `K` with

`|∇_v α(z)| ≤ K |v| exp (-c |z|)`.

Together with the curvature bound, this is exponential decay of the gauge-invariant first
derivatives of a vortex. The derivative of `|α|²` decays at the same rate.

The decay of `∇α` is classical (Jaffe and Taubes, Chapter III). The proof here differentiates the
scalar equation. Outside a disc where `α ≠ 0`, the scalar equation
`Δ log |α|² = (|α|² - 1) / 4` (`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`) can be
differentiated, since the Laplacian commutes with directional derivatives
(`ContDiffAt.laplacian_fderiv_apply`). So each directional derivative `f = ∂_v log |α|²`
solves the linear screened equation

`Δ f = (|α|² / 4) f`

(`TauCeti.Vortex.laplacian_fderiv_log_normSq_apply`). Pointwise
`(∂_v |α|²)² ≤ 4 |α|² |∇_v α|²`, so `f` is square-integrable outside the disc by the finiteness of
the covariant kinetic energy (`TauCeti.Vortex.integrable_covariantDerivative_norm_sq`). Its square
is subharmonic there, so the sub-mean-value inequality makes `f` tend to zero at infinity
(`TauCeti.tendsto_cocompact_of_integrableOn_of_laplacian_nonneg`). Since `|α|² / 4 ≥ c²` outside a
large disc, comparison with the barrier `exp (-c |z|)`
(`TauCeti.abs_le_mul_exp_of_laplacian_eq_mul`) gives `|f| ≤ K exp (-c |z|)`. Because
`∂bar_a α = 0`, the covariant derivative is complex linear
(`TauCeti.Vortex.covariantDerivative_eq_mul_covariantDerivative_one`) and
`|d |α|²|² = 4 |α|² |∇₁ α|²`. Hence `|∇₁ α|² = |α|² |d log |α|²|² / 4 ≤ |d log |α|²|² / 4`
outside the disc, and the covariant derivative is bounded on the remaining compact disc.

These are pointwise estimates of gauge-invariant quantities. No winding gauge is chosen, so they
say nothing directly about the decay of the connection coefficients or of the phase of `α`.

## Main results

* `TauCeti.Vortex.laplacian_fderiv_log_normSq_apply`: `Δ (∂_v log |α|²) = (|α|² / 4) ∂_v log |α|²`
  where `α ≠ 0`.
* `TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp`: `|∇_v α(z)| ≤ K |v| exp (-c |z|)`
  for every `c < 1 / 2`.
* `TauCeti.Vortex.exists_abs_fderiv_normSq_le_mul_exp`: `|∂_v |α|²(z)| ≤ K |v| exp (-c |z|)` for
  every `c < 1 / 2`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory Topology InnerProductSpace Laplacian

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The derivative of `|α|²` is bounded by the covariant derivative:
`(∂_v |α|²)² ≤ 4 |α|² |∇_v α|²`. -/
private theorem sq_fderiv_normSq_le {z : ℂ} (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z v ^ 2 ≤
      4 * (4 * (x z 2 ^ 2 + x z 3 ^ 2)) * ‖covariantDerivative x z v‖ ^ 2 := by
  rw [fderiv_normSq_apply hp hq, sq_norm_covariantDerivative hp hq]
  nlinarith [sq_nonneg (x z 2 * (fderiv ℝ (fun w ↦ x w 3) z v +
      (x z 0 * v.re + x z 1 * v.im) * x z 2) -
    x z 3 * (fderiv ℝ (fun w ↦ x w 2) z v - (x z 0 * v.re + x z 1 * v.im) * x z 3))]

/-- Where `∂bar_a α = 0`, the derivative of `|α|²` and the covariant derivative are related by
`(∂₁ |α|²)² + (∂₂ |α|²)² = 4 |α|² |∇₁ α|²`. -/
private theorem sq_fderiv_normSq_add_sq_fderiv_normSq {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z 1 ^ 2 +
        fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z I ^ 2 =
      4 * (4 * (x z 2 ^ 2 + x z 3 ^ 2)) * ‖covariantDerivative x z 1‖ ^ 2 := by
  rw [fderiv_normSq_apply hp hq, fderiv_normSq_apply hp hq, sq_norm_covariantDerivative hp hq]
  rw [equation_apply_one] at h₁
  rw [equation_apply_two] at h₂
  -- The rows `∂bar_a α = 0` express the `∂₂` derivatives of `p` and `q` through the `∂₁` ones.
  have hPI : fderiv ℝ (fun w ↦ x w 2) z I =
      -fderiv ℝ (fun w ↦ x w 3) z 1 - x z 0 * x z 2 + x z 1 * x z 3 := by linarith
  have hQI : fderiv ℝ (fun w ↦ x w 3) z I =
      fderiv ℝ (fun w ↦ x w 2) z 1 - x z 0 * x z 3 - x z 1 * x z 2 := by linarith
  simp only [one_re, one_im, mul_one, mul_zero, add_zero, hPI, hQI]
  ring

/-- **The differentiated scalar equation.** Let `x` solve the vortex equation near a point `z`
where `α ≠ 0`, with `C³` section components. Then every directional derivative
`f = ∂_v log |α|²` solves the screened equation `Δ f = (|α|² / 4) f` at `z`. -/
theorem laplacian_fderiv_log_normSq_apply {z : ℂ}
    (hb₁ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (fun w ↦ x w 0) w)
    (hb₂ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (fun w ↦ x w 1) w)
    (hp : ContDiffAt ℝ 3 (fun w ↦ x w 2) z) (hq : ContDiffAt ℝ 3 (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0) (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) (v : ℂ) :
    Δ (fun w ↦ fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) w v) z =
      4 * (x z 2 ^ 2 + x z 3 ^ 2) / 4 *
        fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z v := by
  have hs : ContDiffAt ℝ 3 (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z :=
    contDiffAt_const.mul ((hp.pow 2).add (hq.pow 2))
  have hs₀ : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≠ 0 := mul_ne_zero four_ne_zero hα
  rw [(hs.log hs₀).laplacian_fderiv_apply v]
  -- Near `z` the Laplacian of `log |α|²` is `(|α|² - 1) / 4`, by the scalar equation.
  have hΔ : Δ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =ᶠ[𝓝 z]
      fun w ↦ (4 * (x w 2 ^ 2 + x w 3 ^ 2) - 1) / 4 := by
    filter_upwards [hb₁, hb₂, hp.eventually (by simp), hq.eventually (by simp),
      hsol.eventually_nhds, hs.continuousAt.eventually_ne hs₀] with w hw₁ hw₂ hwp hwq hwsol hws
    exact laplacian_log_normSq_of_equation_eq_zero hw₁ hw₂ (hwp.of_le (by norm_num))
      (hwq.of_le (by norm_num)) (fun h ↦ hws (by simp [h])) hwsol
  have hsd := hs.differentiableAt (by norm_num)
  have hd : HasFDerivAt (fun w ↦ (4 * (x w 2 ^ 2 + x w 3 ^ 2) - 1) / 4)
      ((4⁻¹ : ℝ) • fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z) z := by
    simpa only [div_eq_inv_mul] using (hsd.hasFDerivAt.sub_const 1).const_mul (4⁻¹ : ℝ)
  rw [hΔ.fderiv_eq, hd.fderiv, fderiv.log hsd hs₀]
  simp only [smul_apply, smul_eq_mul]
  field_simp

/-- At a vortex, `|∇_v α| = |v| |∇₁ α|`. -/
private theorem norm_covariantDerivative_eq_mul_norm {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hsol : equation x z = 0) (v : ℂ) :
    ‖covariantDerivative x z v‖ = ‖v‖ * ‖covariantDerivative x z 1‖ := by
  rw [covariantDerivative_eq_mul_covariantDerivative_one hp hq (by simp [hsol]) (by simp [hsol]),
    norm_mul]

/-- Where `α ≠ 0`, each directional derivative of `log |α|²` is `C²`. -/
private theorem contDiffAt_fderiv_log_normSq {z : ℂ} (hp : ContDiff ℝ 3 (fun w ↦ x w 2))
    (hq : ContDiff ℝ 3 (fun w ↦ x w 3)) (hz : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (v : ℂ) :
    ContDiffAt ℝ 2 (fun w ↦ fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) w v) z :=
  (((contDiff_const.mul ((hp.pow 2).add (hq.pow 2))).contDiffAt.log hz.ne').fderiv_right
    (m := 2) (by norm_num)).clm_apply contDiffAt_const

/-- Where `|α|² ≥ 1 / 2` at a vortex, `(∂_v log |α|²)² ≤ 8 |v|² |∇₁ α|²`. -/
private theorem sq_fderiv_log_normSq_le {z : ℂ} (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (hsol : equation x z = 0)
    (hs : 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (v : ℂ) :
    fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z v ^ 2 ≤
      8 * ‖v‖ ^ 2 * ‖covariantDerivative x z 1‖ ^ 2 := by
  have hsd : DifferentiableAt ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z := by fun_prop
  have hle := sq_fderiv_normSq_le hp hq v
  rw [norm_covariantDerivative_eq_mul_norm hp hq hsol v] at hle
  rw [fderiv.log hsd (by positivity), smul_apply, smul_eq_mul, inv_mul_eq_div, div_pow,
    div_le_iff₀ (by positivity)]
  have h1 : 0 ≤ ‖v‖ ^ 2 * ‖covariantDerivative x z 1‖ ^ 2 := by positivity
  nlinarith [mul_nonneg h1 (sub_nonneg.mpr hs)]

/-- Where `0 < |α|² ≤ 1` at a vortex, `4 |∇₁ α|² ≤ (∂₁ log |α|²)² + (∂₂ log |α|²)²`. -/
private theorem four_mul_norm_covariantDerivative_sq_le {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hsol : equation x z = 0) (hs₀ : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hs₁ : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1) :
    4 * ‖covariantDerivative x z 1‖ ^ 2 ≤
      fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 ^ 2 +
        fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I ^ 2 := by
  have hsd : DifferentiableAt ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z := by fun_prop
  have hid := sq_fderiv_normSq_add_sq_fderiv_normSq hp hq (by simp [hsol]) (by simp [hsol])
  rw [fderiv.log hsd hs₀.ne', smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  set s := 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  set a := fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z 1
  set b := fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z I
  -- `4 s |∇₁ α|² = a² + b²`, so `4 |∇₁ α|² = (a² + b²) / s ≤ (a² + b²) / s²`.
  have hs₂ : s ^ 2 ≤ s := by nlinarith
  rw [mul_pow, mul_pow, ← mul_add, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hs₂ (sq_nonneg ‖covariantDerivative x z 1‖)]

/-- Outside a disc where `|α|² ≥ 1 / 2`, each directional derivative `∂_v log |α|²` of a vortex
with `|α| → 1` tends to zero at infinity. -/
private theorem tendsto_fderiv_log_normSq_cocompact
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {R : ℝ}
    (hsR : ∀ z, R ≤ ‖z‖ → 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (v : ℂ) :
    Tendsto (fun z ↦ fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z v)
      (cocompact ℂ) (𝓝 0) := by
  set f := fun z ↦ fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z v
  have hpos : ∀ z, R ≤ ‖z‖ → 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := fun z hz ↦ by
    linarith [hsR z hz]
  have hf2 : ∀ z, R < ‖z‖ → ContDiffAt ℝ 2 f z := fun z hz ↦
    contDiffAt_fderiv_log_normSq hp hq (hpos z hz.le) v
  -- Off the disc, `f² ≤ 8 |v|² |∇₁ α|²`, which is integrable by finiteness of energy.
  have hmeas : MeasurableSet {z : ℂ | R < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hint : IntegrableOn (fun z ↦ ‖f z‖ ^ 2) {z : ℂ | R < ‖z‖} := by
    refine Integrable.mono'
      (((integrable_covariantDerivative_norm_sq volume hb₁ hb₂ (hp.of_le (by norm_num))
        (hq.of_le (by norm_num)) hsol hlim).const_mul (8 * ‖v‖ ^ 2)).integrableOn)
      (ContinuousOn.aestronglyMeasurable (fun z hz ↦
        ((hf2 z hz).continuousAt.norm.pow 2).continuousWithinAt) hmeas)
      (ae_restrict_of_forall_mem hmeas fun z hz ↦ ?_)
    have hle := sq_fderiv_log_normSq_le (hp.differentiable (by norm_num) z)
      (hq.differentiable (by norm_num) z) (hsol z) (hsR z (le_of_lt hz)) v
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs]
    nlinarith [mul_nonneg (sq_nonneg ‖v‖) (sq_nonneg ‖covariantDerivative x z I‖)]
  -- Off the disc `Δ f = (|α|² / 4) f`, so `f²` is subharmonic there.
  have hΔsq : ∀ z, R < ‖z‖ → 0 ≤ Δ (fun w ↦ ‖f w‖ ^ 2) z := fun z hz ↦ by
    have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := fun h ↦ by linarith [hpos z hz.le, h]
    rw [(hf2 z hz).laplacian_norm_sq orthonormalBasisOneI,
      laplacian_fderiv_log_normSq_apply (.of_forall fun w ↦ hb₁ w) (.of_forall fun w ↦ hb₂ w)
        hp.contDiffAt hq.contDiffAt hα (.of_forall hsol) v, RCLike.inner_apply, conj_trivial]
    have := hpos z hz.le
    have : 0 ≤ f z * (4 * (x z 2 ^ 2 + x z 3 ^ 2) / 4 * f z) := by nlinarith [sq_nonneg (f z)]
    have : 0 ≤ ∑ i, ‖fderiv ℝ f z (orthonormalBasisOneI i)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  have hsq := tendsto_cocompact_of_integrableOn_of_laplacian_nonneg
    (fun z hz ↦ ((hf2 z hz).norm_sq ℝ)) hint (fun z _ ↦ by positivity) hΔsq
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using (Real.continuous_sqrt.tendsto 0).comp hsq

/-- Outside a disc where `|α|² ≥ max (1 / 2) (4 c²)`, each directional derivative
`∂_v log |α|²` of a vortex with `|α| → 1` decays at the rate `c`. -/
private theorem exists_abs_fderiv_log_normSq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c R : ℝ}
    (hc₀ : 0 ≤ c) (hR : 0 < R)
    (hsR : ∀ z, R ≤ ‖z‖ → 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) ∧
      4 * c ^ 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (v : ℂ) :
    ∃ K, ∀ z, R ≤ ‖z‖ →
      |fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z v| ≤
        K * Real.exp (-(c * ‖z‖)) := by
  set f := fun z ↦ fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z v
  have hpos : ∀ z, R ≤ ‖z‖ → 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := fun z hz ↦ by
    linarith [(hsR z hz).1]
  have hf2 : ∀ z, R ≤ ‖z‖ → ContDiffAt ℝ 2 f z := fun z hz ↦
    contDiffAt_fderiv_log_normSq hp hq (hpos z hz) v
  have hfcont : ContinuousOn f {z | R ≤ ‖z‖} := fun z hz ↦
    (hf2 z hz).continuousAt.continuousWithinAt
  -- Compare with the barrier for the screened operator `-Δ + |α|² / 4`.
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hfcont.mono fun z hz ↦ by simp [mem_sphere_zero_iff_norm.mp hz])
  refine ⟨max M 0 * Real.exp (c * R), fun z hz ↦ ?_⟩
  have hdecay := abs_le_mul_exp_of_laplacian_eq_mul
    (V := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) / 4) hR hc₀ (le_max_right M 0) hfcont
    (fun w hw ↦ hf2 w hw.le) (fun w hw ↦ by linarith [(hsR w hw.le).2])
    (fun w hw ↦ laplacian_fderiv_log_normSq_apply (.of_forall fun w ↦ hb₁ w)
      (.of_forall fun w ↦ hb₂ w) hp.contDiffAt hq.contDiffAt
      (fun h ↦ by linarith [hpos w hw.le, h]) (.of_forall hsol) v)
    (fun w hw ↦ by
      have := hM w (mem_sphere_zero_iff_norm.mpr hw)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _))
    (tendsto_fderiv_log_normSq_cocompact hb₁ hb₂ hp hq hsol hlim (fun w hw ↦ (hsR w hw).1) v) hz
  rwa [exp_neg_mul_sub, ← mul_assoc] at hdecay

/-- The case `0 ≤ c` and `v = 1` of `exists_norm_covariantDerivative_le_mul_exp`. -/
private theorem exists_norm_covariantDerivative_one_le_mul_exp_of_nonneg
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K, 0 ≤ K ∧ ∀ z, ‖covariantDerivative x z 1‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  -- Outside a disc of radius `R`, `|α|² > max (1 / 2) (4 c²)`.
  have ht : max (1 / 2) (4 * c ^ 2) < 1 := max_lt (by norm_num) (by nlinarith)
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hlim.eventually (lt_mem_nhds ht))
  set R := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hsR : ∀ z, R ≤ ‖z‖ → 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) ∧
      4 * c ^ 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) := fun z hz ↦
    have h := hR₀ ((le_max_left _ _).trans hz)
    ⟨(le_max_left _ _).trans h.le, (le_max_right _ _).trans h.le⟩
  obtain ⟨K₁, hK₁⟩ := exists_abs_fderiv_log_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc₀ hR hsR 1
  obtain ⟨K₂, hK₂⟩ := exists_abs_fderiv_log_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc₀ hR hsR I
  -- Inside the disc, the covariant derivative is bounded by continuity.
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (continuous_covariantDerivative hb₁.continuous hb₂.continuous (hp.of_le (by norm_num))
      (hq.of_le (by norm_num)) 1).continuousOn
  refine ⟨max (|K₁| + |K₂|) (max M 0 * Real.exp (c * R)), by positivity, fun z ↦ ?_⟩
  have he : 0 < Real.exp (-(c * ‖z‖)) := Real.exp_pos _
  rcases le_or_gt R ‖z‖ with hz | hz
  · -- Outside the disc, `4 |∇₁ α|² ≤ |d log |α|²|²`.
    have h4 := four_mul_norm_covariantDerivative_sq_le (hp.differentiable (by norm_num) z)
      (hq.differentiable (by norm_num) z) (hsol z) (by linarith [(hsR z hz).1])
      (normSq_le_one_of_tendsto hb₁ hb₂ (hp.of_le (by norm_num)) (hq.of_le (by norm_num))
        hsol hlim z)
    have ha := pow_le_pow_left₀ (abs_nonneg _)
      ((hK₁ z hz).trans (mul_le_mul_of_nonneg_right (le_abs_self _) he.le)) 2
    have hb := pow_le_pow_left₀ (abs_nonneg _)
      ((hK₂ z hz).trans (mul_le_mul_of_nonneg_right (le_abs_self _) he.le)) 2
    rw [sq_abs] at ha hb
    have hsq : ‖covariantDerivative x z 1‖ ^ 2 ≤ ((|K₁| + |K₂|) * Real.exp (-(c * ‖z‖))) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg K₁) he.le) (mul_nonneg (abs_nonneg K₂) he.le)]
    exact ((pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) he.le)
  · calc ‖covariantDerivative x z 1‖ ≤ max M 0 := (hM z (mem_closedBall_zero_iff.mpr hz.le)).trans
          (le_max_left _ _)
      _ ≤ max M 0 * Real.exp (c * R) * Real.exp (-(c * ‖z‖)) := by
        rw [mul_assoc, ← exp_neg_mul_sub]
        exact le_mul_of_one_le_right (le_max_right _ _) (Real.one_le_exp (by nlinarith))
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) he.le

/-- **Exponential decay of the covariant derivative of a plane vortex.** A vortex on the whole
plane, with differentiable connection, `C³` section and `|α| → 1` at infinity, has
`|∇_v α(z)| ≤ K |v| exp (-c |z|)` for every rate `c < 1 / 2`, with a constant `K` depending on
`c`. -/
theorem exists_norm_covariantDerivative_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z v, ‖covariantDerivative x z v‖ ≤ K * ‖v‖ * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK₀, hK⟩ := exists_norm_covariantDerivative_one_le_mul_exp_of_nonneg hb₁ hb₂ hp hq
    hsol hlim (le_max_right c 0) (max_lt hc (by norm_num))
  refine ⟨K, fun z v ↦ ?_⟩
  rw [norm_covariantDerivative_eq_mul_norm (hp.differentiable (by norm_num) z)
    (hq.differentiable (by norm_num) z) (hsol z) v]
  have hexp : Real.exp (-(max c 0 * ‖z‖)) ≤ Real.exp (-(c * ‖z‖)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (norm_nonneg _)))
  nlinarith [mul_le_mul_of_nonneg_left (hK z) (norm_nonneg v),
    mul_le_mul_of_nonneg_left hexp (mul_nonneg hK₀ (norm_nonneg v))]

/-- **Exponential decay of the derivative of `|α|²`.** A vortex on the whole plane, with
differentiable connection, `C³` section and `|α| → 1` at infinity, has
`|∂_v |α|²(z)| ≤ K |v| exp (-c |z|)` for every rate `c < 1 / 2`, with a constant `K` depending on
`c`. -/
theorem exists_abs_fderiv_normSq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z v, |fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z v| ≤
      K * ‖v‖ * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := exists_norm_covariantDerivative_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
  refine ⟨2 * K, fun z v ↦ ?_⟩
  -- `(∂_v |α|²)² ≤ 4 |α|² |∇_v α|² ≤ 4 |∇_v α|²`, since `|α| ≤ 1`.
  have hle := sq_fderiv_normSq_le (hp.differentiable (by norm_num) z)
    (hq.differentiable (by norm_num) z) v
  have hs₁ := normSq_le_one_of_tendsto hb₁ hb₂ (hp.of_le (by norm_num)) (hq.of_le (by norm_num))
    hsol hlim z
  have hKz := hK z v
  have hnn : 0 ≤ K * ‖v‖ * Real.exp (-(c * ‖z‖)) := (norm_nonneg _).trans hKz
  rw [← pow_le_pow_iff_left₀ (abs_nonneg _) (by linarith) two_ne_zero, sq_abs]
  have hcov : ‖covariantDerivative x z v‖ ^ 2 ≤ (K * ‖v‖ * Real.exp (-(c * ‖z‖))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hKz 2
  nlinarith [mul_le_mul_of_nonneg_right hs₁ (sq_nonneg ‖covariantDerivative x z v‖)]

end TauCeti.Vortex
