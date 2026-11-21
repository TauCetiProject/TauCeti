/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Projection
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Continuous data do not give `C²` solutions of Poisson's equation

The interior Schauder estimate bounds the `α`-Hölder seminorm of `D²u` by the `α`-Hölder seminorm of
`Δu`, for `0 < α < 1`. This file shows that the exponent `α > 0` cannot be dropped: there is a
function `f`, continuous near the origin, such that Poisson's equation `Δv = f` has no `C²` solution
on any neighbourhood of the origin (Gilbarg–Trudinger, Problem 4.9).

Let `E` be a finite-dimensional real inner product space and let `e₀, e₁` be orthonormal, so that
`dim E ≥ 2`. The function

`u(x) = (⟪e₀, x⟫² - ⟪e₁, x⟫²) √(-log ‖x‖)` (`TauCeti.PDE.quadraticSqrtNegLog`)

is smooth on the punctured unit ball, continuous everywhere and vanishes at the origin. With
`L = -log ‖x‖` and `n = dim E`, its Laplacian on the punctured unit ball is

`Δu(x) = -((⟪e₀, x⟫² - ⟪e₁, x⟫²) / ‖x‖²) ((n + 2) / (2 √L) + 1 / (4 L √L))`

(`TauCeti.PDE.laplacian_quadraticSqrtNegLog`). The first factor is bounded by `1` and the second
tends to `0` as `x → 0`, so this formula, which takes the value `0` at the origin, defines a
function `f = TauCeti.PDE.laplacianQuadraticSqrtNegLog` continuous on the unit ball
(`TauCeti.PDE.continuousOn_laplacianQuadraticSqrtNegLog`). Its modulus of continuity at the origin
is only logarithmic: on the line through `e₁`, `f(t e₁)` is of exact order `(-log |t|)^(-1/2)`.

Yet `u` is not `C²` at the origin (`TauCeti.PDE.not_contDiffAt_quadraticSqrtNegLog`): along the line
through `e₁`, `u(t e₁) = -t² √(-log |t|)`, which is not `O(t²)`. Moreover `Δu = f` holds in the
sense of distributions across the origin
(`TauCeti.PDE.integral_laplacian_smul_quadraticSqrtNegLog`), so any `C²` solution `v` of `Δv = f`
near the origin would differ from `u` by a weakly harmonic function, which is smooth by Weyl's
lemma, and `u` would be `C²` at the origin. Hence no such `v` exists
(`TauCeti.PDE.not_exists_contDiffOn_laplacian_eq_laplacianQuadraticSqrtNegLog`).

## The distributional Laplacian across the origin

The approximants `uₜ(x) = (⟪e₀, x⟫² - ⟪e₁, x⟫²) F(‖x‖² + t)`, `t > 0`, with
`F(s) = √(-log s / 2)`, are smooth where `‖x‖² + t < 1`, and `u₀ = u`. Writing `h` for the harmonic
quadratic factor, `Δh = 0` and `⟪∇h, x⟫ = 2h` give

`Δuₜ(x) = h(x) (4 ‖x‖² F''(s) + (2n + 8) F'(s))`, `s = ‖x‖² + t`,

and since `|h(x)| ≤ ‖x‖² ≤ s`, this is bounded uniformly in `t` on every smaller ball. Green's
identity for `uₜ` and dominated convergence as `t → 0` give `∫ Δφ u = ∫ φ f` for every test
function `φ` on an open subset of the unit ball, whose support lies in a smaller ball.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Problem 4.9.
-/

public section

noncomputable section

namespace TauCeti.PDE

open InnerProductSpace MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped Laplacian Gradient Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The radial profile `F(s) = √(-log s / 2)` -/

/-- The function `-log s / 2`, so that `-log ‖x‖ = M (‖x‖²)`. -/
private def M (s : ℝ) : ℝ := -Real.log s / 2

/-- The radial profile `F(s) = √(-log s / 2)`. -/
private def F (s : ℝ) : ℝ := √(M s)

/-- The derivative of `F` on `(0, 1)`. -/
private def F' (s : ℝ) : ℝ := -1 / (4 * s * √(M s))

/-- The second derivative of `F` on `(0, 1)`. -/
private def F'' (s : ℝ) : ℝ := 1 / (4 * s ^ 2 * √(M s)) - 1 / (16 * s ^ 2 * M s * √(M s))

private theorem M_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < M s := by
  have := Real.log_neg hs0 hs1
  simp only [M]
  linarith

private theorem hasDerivAt_M {s : ℝ} (hs0 : 0 < s) : HasDerivAt M (-1 / (2 * s)) s := by
  refine ((((Real.hasDerivAt_log hs0.ne').neg).div_const 2).congr_deriv ?_ :
    HasDerivAt (fun t ↦ -Real.log t / 2) _ s)
  field_simp

private theorem hasDerivAt_F {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : HasDerivAt F (F' s) s := by
  have hM := M_pos hs0 hs1
  refine ((hasDerivAt_M hs0).sqrt hM.ne').congr_deriv ?_
  have : √(M s) ≠ 0 := (Real.sqrt_pos.2 hM).ne'
  simp only [F']
  field_simp
  norm_num

private theorem hasDerivAt_F' {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : HasDerivAt F' (F'' s) s := by
  have hM := M_pos hs0 hs1
  have : 0 < √(M s) := Real.sqrt_pos.2 hM
  have h1 : HasDerivAt (fun t ↦ 4 * t * √(M t))
      (4 * √(M s) + 4 * s * (-1 / (2 * s) / (2 * √(M s)))) s := by
    simpa using ((hasDerivAt_id s).const_mul 4).fun_mul ((hasDerivAt_M hs0).sqrt hM.ne')
  refine (((h1.inv (by positivity)).const_mul (-1)).congr_deriv ?_ :
    HasDerivAt (fun t ↦ -1 * (4 * t * √(M t))⁻¹) _ s).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ by simp [F', div_eq_mul_inv])
  have hsq2 : √(M s) ^ 2 = M s := Real.sq_sqrt hM.le
  simp only [F'']
  field_simp
  rw [hsq2]
  ring

private theorem deriv_F {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : deriv F s = F' s :=
  (hasDerivAt_F hs0 hs1).deriv

private theorem deriv_deriv_F {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    deriv (deriv F) s = F'' s := by
  have : deriv F =ᶠ[𝓝 s] F' := by
    filter_upwards [Ioo_mem_nhds hs0 hs1] with r hr using deriv_F hr.1 hr.2
  rw [this.deriv_eq, (hasDerivAt_F' hs0 hs1).deriv]

private theorem contDiffAt_F {n : WithTop ℕ∞} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffAt ℝ n F s :=
  (((Real.contDiffAt_log.2 hs0.ne').neg).div_const 2).sqrt (M_pos hs0 hs1).ne'

private theorem continuousAt_F {s : ℝ} (hs0 : 0 < s) : ContinuousAt F s :=
  ((Real.continuousAt_log hs0.ne').neg.div_const 2).sqrt

private theorem continuousAt_F'' {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : ContinuousAt F'' s := by
  have hM : ContinuousAt M s := (Real.continuousAt_log hs0.ne').neg.div_const 2
  have : 0 < √(M s) := Real.sqrt_pos.2 (M_pos hs0 hs1)
  have hMs := M_pos hs0 hs1
  refine ContinuousAt.sub ?_ ?_
  · exact continuousAt_const.div (by fun_prop) (by positivity)
  · exact continuousAt_const.div (by fun_prop) (by positivity)

private theorem F_nonneg (s : ℝ) : 0 ≤ F s := Real.sqrt_nonneg _

/-- `F` is antitone on the positive reals. -/
private theorem F_le_F {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') : F s' ≤ F s := by
  simp only [F, M]
  gcongr

/-- `F(r²) = √(-log r)`. -/
private theorem F_sq (r : ℝ) : F (r ^ 2) = √(-Real.log r) := by
  simp only [F, M, Real.log_pow]
  congr 1
  ring

/-! ### The harmonic quadratic factor -/

/-- The harmonic quadratic polynomial `⟪e₀, x⟫² - ⟪e₁, x⟫²`. -/
private def quad (e : Fin 2 → E) (x : E) : ℝ := ⟪e 0, x⟫_ℝ ^ 2 - ⟪e 1, x⟫_ℝ ^ 2

private theorem contDiff_quad {n : WithTop ℕ∞} (e : Fin 2 → E) : ContDiff ℝ n (quad e) :=
  (contDiff_inner_sq (e 0)).sub (contDiff_inner_sq (e 1))

private theorem hasFDerivAt_quad (e : Fin 2 → E) (x : E) : HasFDerivAt (quad e)
    ((2 * ⟪e 0, x⟫_ℝ) • innerSL ℝ (e 0) - (2 * ⟪e 1, x⟫_ℝ) • innerSL ℝ (e 1)) x := by
  have h0 := ((innerSL ℝ (e 0)).hasFDerivAt (x := x)).pow 2
  have h1 := ((innerSL ℝ (e 1)).hasFDerivAt (x := x)).pow 2
  convert h0.sub h1 using 1
  · funext y
    simp [quad]
  · simp

/-- Euler's identity for the homogeneous quadratic `quad e`. -/
private theorem fderiv_quad_self (e : Fin 2 → E) (x : E) :
    fderiv ℝ (quad e) x x = 2 * quad e x := by
  rw [(hasFDerivAt_quad e x).fderiv]
  simp only [sub_apply, smul_apply, coe_innerSL_apply, smul_eq_mul, quad]
  ring

private theorem abs_quad_le {e : Fin 2 → E} (he : Orthonormal ℝ e) (x : E) :
    |quad e x| ≤ ‖x‖ ^ 2 := by
  have := he.sum_inner_products_le (s := Finset.univ) (x := x)
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at this
  rw [quad, abs_le]
  constructor <;> nlinarith [sq_nonneg ⟪e 0, x⟫_ℝ, sq_nonneg ⟪e 1, x⟫_ℝ]

@[simp]
private theorem quad_zero (e : Fin 2 → E) : quad e 0 = 0 := by
  simp [quad]

/-! ### The function and its Laplacian -/

/-- The function `u(x) = (⟪e₀, x⟫² - ⟪e₁, x⟫²) √(-log ‖x‖)` of Gilbarg–Trudinger, Problem 4.9.
For orthonormal `e₀, e₁` it is smooth on the punctured unit ball with a Laplacian that extends
continuously to the origin, but it is not `C²` at the origin. -/
def quadraticSqrtNegLog (e : Fin 2 → E) (x : E) : ℝ :=
  (⟪e 0, x⟫_ℝ ^ 2 - ⟪e 1, x⟫_ℝ ^ 2) * √(-Real.log ‖x‖)

theorem quadraticSqrtNegLog_apply (e : Fin 2 → E) (x : E) :
    quadraticSqrtNegLog e x = (⟪e 0, x⟫_ℝ ^ 2 - ⟪e 1, x⟫_ℝ ^ 2) * √(-Real.log ‖x‖) :=
  (rfl)

@[simp]
theorem quadraticSqrtNegLog_zero (e : Fin 2 → E) : quadraticSqrtNegLog e 0 = 0 := by
  simp [quadraticSqrtNegLog]

/-- The Laplacian of `TauCeti.PDE.quadraticSqrtNegLog e` on the punctured unit ball,
`-((⟪e₀, x⟫² - ⟪e₁, x⟫²) / ‖x‖²) ((n + 2) / (2 √L) + 1 / (4 L √L))` with `L = -log ‖x‖` and
`n = dim E`. The formula takes the value `0` at the origin, where it is continuous. -/
def laplacianQuadraticSqrtNegLog (e : Fin 2 → E) (x : E) : ℝ :=
  -((⟪e 0, x⟫_ℝ ^ 2 - ⟪e 1, x⟫_ℝ ^ 2) / ‖x‖ ^ 2) *
    ((Module.finrank ℝ E + 2) / (2 * √(-Real.log ‖x‖)) +
      1 / (4 * -Real.log ‖x‖ * √(-Real.log ‖x‖)))

theorem laplacianQuadraticSqrtNegLog_apply (e : Fin 2 → E) (x : E) :
    laplacianQuadraticSqrtNegLog e x = -((⟪e 0, x⟫_ℝ ^ 2 - ⟪e 1, x⟫_ℝ ^ 2) / ‖x‖ ^ 2) *
      ((Module.finrank ℝ E + 2) / (2 * √(-Real.log ‖x‖)) +
        1 / (4 * -Real.log ‖x‖ * √(-Real.log ‖x‖))) :=
  (rfl)

@[simp]
theorem laplacianQuadraticSqrtNegLog_zero (e : Fin 2 → E) :
    laplacianQuadraticSqrtNegLog e 0 = 0 := by
  simp [laplacianQuadraticSqrtNegLog]

/-- The approximants `uₜ(x) = h(x) F(‖x‖² + t)`; `u₀` is `TauCeti.PDE.quadraticSqrtNegLog e`. -/
private def approx (e : Fin 2 → E) (t : ℝ) (x : E) : ℝ := quad e x * F (‖x‖ ^ 2 + t)

private theorem approx_zero (e : Fin 2 → E) : approx e 0 = quadraticSqrtNegLog e := by
  funext x
  simp [approx, quadraticSqrtNegLog, quad, F_sq]

/-- The explicit Laplacian of the approximant `uₜ`. -/
private def approxLaplacian (e : Fin 2 → E) (t : ℝ) (x : E) : ℝ :=
  quad e x * (4 * ‖x‖ ^ 2 * F'' (‖x‖ ^ 2 + t) +
    (2 * Module.finrank ℝ E + 8) * F' (‖x‖ ^ 2 + t))

private theorem contDiffAt_approx {n : WithTop ℕ∞} (e : Fin 2 → E) {t : ℝ} {x : E}
    (hs0 : 0 < ‖x‖ ^ 2 + t) (hs1 : ‖x‖ ^ 2 + t < 1) : ContDiffAt ℝ n (approx e t) x := by
  have hq : ContDiffAt ℝ n (fun y : E ↦ ‖y‖ ^ 2 + t) x :=
    ((contDiff_norm_sq ℝ).add contDiff_const).contDiffAt
  have hG : ContDiffAt ℝ n (F ∘ fun y : E ↦ ‖y‖ ^ 2 + t) x := (contDiffAt_F hs0 hs1).comp x hq
  exact (contDiff_quad e).contDiffAt.mul hG

omit [InnerProductSpace ℝ E] in
/-- On the punctured unit ball, `-log ‖x‖` is positive. -/
private theorem neg_log_norm_pos {x : E} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) : 0 < -Real.log ‖x‖ :=
  neg_pos.2 (Real.log_neg (norm_pos_iff.2 hx0) hx1)

omit [InnerProductSpace ℝ E] in
/-- On the punctured unit ball, the argument `‖x‖² + 0` of `F` for `u₀` lies in `(0, 1)`. -/
private theorem norm_sq_add_zero_mem_Ioo {x : E} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) :
    0 < ‖x‖ ^ 2 + 0 ∧ ‖x‖ ^ 2 + 0 < 1 := by
  have := norm_pos_iff.2 hx0
  exact ⟨by positivity, by simpa using pow_lt_one₀ (norm_nonneg x) hx1 two_ne_zero⟩

private theorem approxLaplacian_zero_eq {e : Fin 2 → E} {x : E} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) :
    approxLaplacian e 0 x = laplacianQuadraticSqrtNegLog e x := by
  have hL := neg_log_norm_pos hx0 hx1
  have hMx : M (‖x‖ ^ 2 + 0) = -Real.log ‖x‖ := by
    simp only [add_zero, M, Real.log_pow]
    ring
  have : 0 < √(-Real.log ‖x‖) := Real.sqrt_pos.2 hL
  simp only [approxLaplacian, F'', F', hMx, laplacianQuadraticSqrtNegLog, quad]
  field_simp
  ring

/-- `u` is smooth on the punctured unit ball. -/
theorem contDiffAt_quadraticSqrtNegLog {n : WithTop ℕ∞} (e : Fin 2 → E) {x : E} (hx0 : x ≠ 0)
    (hx1 : ‖x‖ < 1) : ContDiffAt ℝ n (quadraticSqrtNegLog e) x := by
  obtain ⟨hs0, hs1⟩ := norm_sq_add_zero_mem_Ioo hx0 hx1
  rw [← approx_zero]
  exact contDiffAt_approx e hs0 hs1

/-! ### Continuity -/

private theorem sqrt_neg_log_le {r : ℝ} (hr : 0 < r) : √(-Real.log r) ≤ 1 + r⁻¹ := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
  rw [Real.log_inv] at h
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [inv_pos.2 hr]

/-- `u` is small at the origin: `|u(x)| ≤ ‖x‖ + ‖x‖²`. -/
theorem abs_quadraticSqrtNegLog_le {e : Fin 2 → E} (he : Orthonormal ℝ e) (x : E) :
    |quadraticSqrtNegLog e x| ≤ ‖x‖ + ‖x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [quadraticSqrtNegLog, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc |⟪e 0, x⟫_ℝ ^ 2 - ⟪e 1, x⟫_ℝ ^ 2| * √(-Real.log ‖x‖) ≤ ‖x‖ ^ 2 * (1 + ‖x‖⁻¹) :=
        mul_le_mul (abs_quad_le he x) (sqrt_neg_log_le hr) (Real.sqrt_nonneg _) (by positivity)
    _ = ‖x‖ + ‖x‖ ^ 2 := by field_simp; ring

/-- `u` is continuous, also at the origin, where `|u(x)| ≤ ‖x‖ + ‖x‖²`. -/
theorem continuous_quadraticSqrtNegLog {e : Fin 2 → E} (he : Orthonormal ℝ e) :
    Continuous (quadraticSqrtNegLog e) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, quadraticSqrtNegLog_zero, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun y ↦ (abs_quadraticSqrtNegLog_le he y)) ?_
    have hc : Continuous fun y : E ↦ ‖y‖ + ‖y‖ ^ 2 := by fun_prop
    simpa using hc.tendsto (0 : E)
  · have hlog : ContinuousAt (fun y : E ↦ Real.log ‖y‖) x :=
      (Real.continuousAt_log (norm_ne_zero_iff.2 hx)).comp continuous_norm.continuousAt
    exact ((contDiff_quad (n := 0) e).continuous.continuousAt).mul hlog.neg.sqrt

/-- At the origin, `|f(x)| ≤ (n + 2) / (2 √L) + 1 / (4 L √L)` with `L = -log ‖x‖ → ∞`. -/
private theorem tendsto_laplacianQuadraticSqrtNegLog_zero {e : Fin 2 → E}
    (he : Orthonormal ℝ e) : Tendsto (laplacianQuadraticSqrtNegLog e) (𝓝[≠] 0) (𝓝 0) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- The bound `|f| ≤ g(L)` with `g(L) = (n + 2) / (2 √L) + 1 / (4 L √L) → 0` as `L → ∞`.
  set g : ℝ → ℝ := fun L ↦ (n + 2) / (2 * √L) + 1 / (4 * L * √L)
  have hg : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ ↦ (√L)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    have h2 : Tendsto (fun L : ℝ ↦ (L * √L)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_id.atTop_mul_atTop₀ Real.tendsto_sqrt_atTop)
    have := (h1.const_mul ((n + 2) / 2)).add (h2.const_mul (1 / 4))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun L ↦ ?_
    simp only [g]
    field_simp
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (hg.comp (tendsto_neg_atBot_atTop.comp
      (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero)))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : E) one_pos)]
    with y hy0 hy1
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hL := neg_log_norm_pos hy0 (mem_ball_zero_iff.1 hy1)
  have hq : |(⟪e 0, y⟫_ℝ ^ 2 - ⟪e 1, y⟫_ℝ ^ 2) / ‖y‖ ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖y‖ ^ 2)]
    exact div_le_one_of_le₀ (abs_quad_le he y) (by positivity)
  have hg0 : 0 ≤ (n + 2) / (2 * √(-Real.log ‖y‖)) +
      1 / (4 * -Real.log ‖y‖ * √(-Real.log ‖y‖)) :=
    add_nonneg (div_nonneg (by positivity) (by positivity))
      (div_nonneg zero_le_one (mul_nonneg (by linarith) (Real.sqrt_nonneg _)))
  simp only [Function.comp_apply, laplacianQuadraticSqrtNegLog, norm_mul, norm_neg,
    Real.norm_eq_abs]
  rw [abs_of_nonneg hg0]
  exact mul_le_of_le_one_left (by positivity) hq

/-- The Laplacian `TauCeti.PDE.laplacianQuadraticSqrtNegLog e` is continuous on the unit ball,
also at the origin, where it is `O((-log ‖x‖)^(-1/2))`. -/
theorem continuousOn_laplacianQuadraticSqrtNegLog {e : Fin 2 → E} (he : Orthonormal ℝ e) :
    ContinuousOn (laplacianQuadraticSqrtNegLog e) (ball 0 1) := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  refine ContinuousAt.continuousWithinAt ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, laplacianQuadraticSqrtNegLog_zero]
    exact tendsto_laplacianQuadraticSqrtNegLog_zero he
  · have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hL := neg_log_norm_pos hx0 hx
    have hsq : 0 < √(-Real.log ‖x‖) := Real.sqrt_pos.2 hL
    have hlog : ContinuousAt (fun y : E ↦ -Real.log ‖y‖) x :=
      ((Real.continuousAt_log hr.ne').comp continuous_norm.continuousAt).neg
    have hq : ContinuousAt (fun y : E ↦ ⟪e 0, y⟫_ℝ ^ 2 - ⟪e 1, y⟫_ℝ ^ 2) x :=
      (contDiff_quad (n := 0) e).continuous.continuousAt
    refine (((hq.div (by fun_prop) (by positivity)).neg).mul ?_)
    exact (continuousAt_const.div (continuousAt_const.mul hlog.sqrt)
      (mul_pos two_pos hsq).ne').add
      (continuousAt_const.div ((continuousAt_const.mul hlog).mul hlog.sqrt)
        (mul_pos (mul_pos four_pos hL) hsq).ne')

/-! ### `u` is not `C²` at the origin -/

/-- **`u` is not `C²` at the origin**: on the line through `e₁`, `u(t e₁) = -t² √(-log |t|)`,
whereas a `C²` function vanishing at `0` together with its derivative is `O(t²)`. -/
theorem not_contDiffAt_quadraticSqrtNegLog {e : Fin 2 → E} (he : Orthonormal ℝ e) :
    ¬ ContDiffAt ℝ 2 (quadraticSqrtNegLog e) 0 := by
  intro hu
  have h01 : ⟪e 0, e 1⟫_ℝ = 0 := he.2 (by decide)
  set φ : ℝ → ℝ := fun t ↦ quadraticSqrtNegLog e (t • e 1) with hφ_def
  have hφ_eq (t : ℝ) : φ t = -(t ^ 2 * √(-Real.log |t|)) := by
    simp [hφ_def, quadraticSqrtNegLog, inner_smul_right, h01, he.1 1, norm_smul]
  have hφ : ContDiffAt ℝ 2 φ 0 := by
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ t • e 1) 0 :=
      (contDiff_id.smul contDiff_const).contDiffAt
    have hu' : ContDiffAt ℝ 2 (quadraticSqrtNegLog e) ((0 : ℝ) • e 1) := by simpa using hu
    exact hu'.comp 0 hline
  -- `φ` is even, so `fderiv φ 0 = 0`; as `fderiv φ` is differentiable at `0`,
  -- `isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero` gives `φ = O(t²)`.
  have hd0 : deriv φ 0 = 0 := by
    have := deriv_comp_neg (f := φ) (x := 0)
    simp only [show ∀ t, φ (-t) = φ t from fun t ↦ by simp [hφ_eq], neg_zero] at this
    linarith
  have hO : φ =O[𝓝 0] fun t ↦ ‖t - 0‖ ^ ((1 : ℝ) + 1) := by
    refine isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero zero_le_one
      ((hφ.eventually (by simp)).mono fun s hs ↦ hs.differentiableAt (by simp)) ?_
      (by simp [hφ_eq])
    have hf0 : fderiv ℝ φ 0 = 0 := by
      rw [← toSpanSingleton_deriv, hd0]
      simp
    simpa [hf0] using ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).isBigO_sub.norm_right
  obtain ⟨K, hK⟩ := hO.bound
  -- Near `0⁺` this says `√(-log t) ≤ K`, but `√(-log t) → ∞` as `t → 0⁺`.
  have hlim : Tendsto (fun t : ℝ ↦ √(-Real.log t)) (𝓝[>] 0) atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  obtain ⟨t, ht1, ht, ht0 : 0 < t⟩ :=
    ((hlim.eventually_gt_atTop K).and ((hK.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin)).exists
  have hφt : ‖φ t‖ = t ^ 2 * √(-Real.log t) := by
    rw [hφ_eq, norm_neg, abs_of_pos ht0, Real.norm_of_nonneg (by positivity)]
  have hpow : ‖‖t - 0‖ ^ ((1 : ℝ) + 1)‖ = t ^ 2 := by
    norm_num [abs_of_pos ht0]
  rw [hφt, hpow] at ht
  have : √(-Real.log t) ≤ K := le_of_mul_le_mul_left (by linarith) (pow_pos ht0 2)
  linarith

/-! ### The distributional Laplacian across the origin -/

/-- On the unit ball, the approximants are dominated by `|u|`. -/
private theorem abs_approx_le (e : Fin 2 → E) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    |approx e t x| ≤ |quadraticSqrtNegLog e x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [approx]
  rw [← approx_zero, approx, approx, abs_mul, abs_mul]
  have hs : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx
    positivity
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_of_nonneg (F_nonneg _), abs_of_nonneg (F_nonneg _)]
  exact F_le_F (by simpa using hs) (by linarith)

/-- A uniform bound for the Laplacians of the approximants on a ball `‖x‖² + t ≤ s₀ < 1`. -/
private theorem abs_approxLaplacian_le (e : Fin 2 → E) (he : Orthonormal ℝ e) {s₀ t : ℝ}
    (hs₀ : s₀ < 1) (ht : 0 ≤ t) {x : E} (hs0 : 0 < ‖x‖ ^ 2 + t) (hs : ‖x‖ ^ 2 + t ≤ s₀) :
    |approxLaplacian e t x| ≤ ((Module.finrank ℝ E + 4) / 2 + 1) / √(M s₀) +
      1 / (4 * (M s₀ * √(M s₀))) := by
  set s := ‖x‖ ^ 2 + t with hs_def
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hs1 : s < 1 := hs.trans_lt hs₀
  have hM₀ : 0 < M s₀ := M_pos (hs0.trans_le hs) hs₀
  have hM : 0 < M s := M_pos hs0 hs1
  have hMM : M s₀ ≤ M s := by
    simp only [M]
    gcongr
  have hsq₀ : 0 < √(M s₀) := Real.sqrt_pos.2 hM₀
  have : 0 < √(M s) := Real.sqrt_pos.2 hM
  have hsqle : √(M s₀) ≤ √(M s) := Real.sqrt_le_sqrt hMM
  set a := 1 / √(M s)
  set b := 1 / (M s * √(M s))
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha : a ≤ 1 / √(M s₀) := one_div_le_one_div_of_le hsq₀ hsqle
  have hb : b ≤ 1 / (M s₀ * √(M s₀)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul hMM hsqle hsq₀.le hM.le)
  have hA : |quad e x / s| ≤ 1 := by
    rw [abs_div, abs_of_pos hs0]
    exact div_le_one_of_le₀ ((abs_quad_le he x).trans (by simp [s, ht])) hs0.le
  have hB0 : 0 ≤ ‖x‖ ^ 2 / s := by positivity
  have hB1 : ‖x‖ ^ 2 / s ≤ 1 := div_le_one_of_le₀ (by simp [s, ht]) hs0.le
  have heq : approxLaplacian e t x =
      quad e x / s * (‖x‖ ^ 2 / s * (a - b / 4) - (n + 4) / 2 * a) := by
    simp only [approxLaplacian, F'', F', a, b, n]
    rw [← hs_def]
    field_simp
    ring
  rw [heq, abs_mul]
  have hinner : |‖x‖ ^ 2 / s * (a - b / 4) - (n + 4) / 2 * a| ≤ a + b / 4 + (n + 4) / 2 * a := by
    have hn : 0 ≤ n := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hB0 ha0, mul_nonneg hB0 hb0, mul_nonneg hn ha0]
  calc |quad e x / s| * |‖x‖ ^ 2 / s * (a - b / 4) - (n + 4) / 2 * a|
      ≤ 1 * (a + b / 4 + (n + 4) / 2 * a) := mul_le_mul hA hinner (abs_nonneg _) zero_le_one
    _ = ((n + 4) / 2 + 1) * a + 1 / 4 * b := by ring
    _ ≤ ((n + 4) / 2 + 1) * (1 / √(M s₀)) + 1 / 4 * (1 / (M s₀ * √(M s₀))) := by
        have : 0 ≤ n := Nat.cast_nonneg _
        gcongr
    _ = _ := by ring

private theorem measurable_approx (e : Fin 2 → E) (t : ℝ) [MeasurableSpace E] [BorelSpace E] :
    Measurable (approx e t) := by
  have hq : Measurable (quad e) := (contDiff_quad (n := 0) e).continuous.measurable
  unfold approx F M
  fun_prop

private theorem measurable_approxLaplacian (e : Fin 2 → E) (t : ℝ) [MeasurableSpace E]
    [BorelSpace E] : Measurable (approxLaplacian e t) := by
  have hq : Measurable (quad e) := (contDiff_quad (n := 0) e).continuous.measurable
  unfold approxLaplacian F' F'' M
  fun_prop

variable [FiniteDimensional ℝ E]

private theorem laplacian_quad {e : Fin 2 → E} (he : Orthonormal ℝ e) (x : E) :
    Δ (quad e) x = 0 := by
  rw [show quad e = fun y ↦ ⟪e 0, y⟫_ℝ ^ 2 - ⟪e 1, y⟫_ℝ ^ 2 from rfl]
  simp [he.1 0, he.1 1]

/-- **The Laplacian of the approximant** `uₜ(x) = h(x) F(‖x‖² + t)`: since `h` is harmonic and
homogeneous of degree `2`, `Δuₜ = h (4 ‖x‖² F''(s) + (2n + 8) F'(s))` with `s = ‖x‖² + t`. -/
private theorem laplacian_approx {e : Fin 2 → E} (he : Orthonormal ℝ e) {t : ℝ} {x : E}
    (hs0 : 0 < ‖x‖ ^ 2 + t) (hs1 : ‖x‖ ^ 2 + t < 1) :
    Δ (approx e t) x = approxLaplacian e t x := by
  set q : E → ℝ := fun y ↦ ‖y‖ ^ 2 + t with hq_def
  have hnsq : ContDiff ℝ 2 (fun y : E ↦ ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have hq : ContDiffAt ℝ 2 q x := (hnsq.add contDiff_const).contDiffAt
  have hFq : ContDiffAt ℝ 2 F (q x) := contDiffAt_F hs0 hs1
  have hqd : HasFDerivAt q ((2 : ℝ) • innerSL ℝ x) x := by
    have := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t
    rwa [ofNat_smul_eq_nsmul ℝ 2]
  have hGd : HasFDerivAt (F ∘ q) (F' (q x) • (2 : ℝ) • innerSL ℝ x) x :=
    (hasDerivAt_F hs0 hs1).comp_hasFDerivAt x hqd
  -- `ContDiffAt.laplacian_add` is stated for a `Pi` sum `f₁ + f₂`, which `q` unfolds to.
  have hΔq : Δ q x = 2 * Module.finrank ℝ E := by
    rw [hq_def, show (fun y : E ↦ ‖y‖ ^ 2 + t) = (fun y : E ↦ ‖y‖ ^ 2) + fun _ ↦ t from rfl,
      hnsq.contDiffAt.laplacian_add contDiff_const.contDiffAt]
    simp
  have hgq : ‖∇ q x‖ = 2 * ‖x‖ := by
    rw [TauCeti.norm_gradient_eq_norm_fderiv, hqd.fderiv, norm_smul, innerSL_apply_norm]
    norm_num
  -- The radial factor, by the chain rule through `q`.
  have hΔG : Δ (F ∘ q) x = F'' (q x) * (4 * ‖x‖ ^ 2) + F' (q x) * (2 * Module.finrank ℝ E) := by
    rw [hFq.laplacian_comp hq, hgq, hΔq, deriv_deriv_F hs0 hs1, deriv_F hs0 hs1]
    ring
  -- The cross term, by Euler's identity `⟪∇h, x⟫ = 2 h`.
  have hinner : ⟪∇ (quad e) x, ∇ (F ∘ q) x⟫_ℝ = 4 * F' (q x) * quad e x := by
    rw [real_inner_comm, inner_gradient_left, hGd.fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [real_inner_comm, inner_gradient_left, fderiv_quad_self]
    ring
  have := (contDiff_quad e).contDiffAt.laplacian_fun_mul (hFq.comp x hq)
  simp only [Function.comp_def] at this hΔG hinner
  unfold approx
  rw [this, hΔG, hinner, laplacian_quad he, approxLaplacian]
  ring

/-- **The Laplacian of `u`** on the punctured unit ball is
`TauCeti.PDE.laplacianQuadraticSqrtNegLog e`. -/
theorem laplacian_quadraticSqrtNegLog {e : Fin 2 → E} (he : Orthonormal ℝ e) {x : E} (hx0 : x ≠ 0)
    (hx1 : ‖x‖ < 1) : Δ (quadraticSqrtNegLog e) x = laplacianQuadraticSqrtNegLog e x := by
  obtain ⟨hs0, hs1⟩ := norm_sq_add_zero_mem_Ioo hx0 hx1
  rw [← approx_zero, laplacian_approx he hs0 hs1, approxLaplacian_zero_eq hx0 hx1]

section Distribution

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- Dominated convergence for `∫ Δφ uₜ` as `t → 0⁺`, with the bound `|uₜ| ≤ |u| ≤ ‖x‖ + ‖x‖²`. -/
private theorem tendsto_integral_laplacian_smul_approx {e : Fin 2 → E} (he : Orthonormal ℝ e)
    (φ : 𝓓(Ω, ℝ)) : Tendsto (fun t ↦ ∫ x, Δ (φ : E → ℝ) x • approx e t x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, Δ (φ : E → ℝ) x • quadraticSqrtNegLog e x ∂μ)) := by
  have hΔφc : Continuous (Δ (φ : E → ℝ)) := (φ.contDiff.of_le (by simp)).continuous_laplacian
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖Δ (φ : E → ℝ) x‖ * (‖x‖ + ‖x‖ ^ 2))
    (Eventually.of_forall fun t ↦
      (hΔφc.aestronglyMeasurable.smul (measurable_approx e t).aestronglyMeasurable))
    ?_ ?_ (Eventually.of_forall fun x ↦ ?_)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine Eventually.of_forall fun x ↦ ?_
    rw [norm_smul, Real.norm_eq_abs (approx e t x)]
    gcongr
    exact (abs_approx_le e (le_of_lt ht) x).trans (abs_quadraticSqrtNegLog_le he x)
  · exact (hΔφc.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.laplacian.norm.mul_right)
  · rw [← approx_zero]
    refine Tendsto.const_smul ?_ _
    rcases eq_or_ne x 0 with rfl | hx
    · simp [approx]
    · have hx2 : 0 < ‖x‖ ^ 2 + 0 := by
        have := norm_pos_iff.2 hx
        positivity
      have hcont : ContinuousAt (fun t ↦ approx e t x) 0 :=
        continuousAt_const.mul ((continuousAt_F hx2).comp (continuousAt_const.add continuousAt_id))
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds

omit [FiniteDimensional ℝ E] in
/-- Dominated convergence for `∫ φ Δuₜ` as `t → 0⁺`, with the uniform bound on `Δuₜ` on the
support of `φ`, where `‖x‖² + t ≤ s₀ < 1` for `0 < t < δ`. -/
private theorem tendsto_integral_smul_approxLaplacian {e : Fin 2 → E} (he : Orthonormal ℝ e)
    {δ s₀ : ℝ} (hδ : 0 < δ) (hs₀ : s₀ < 1)
    (hrange : ∀ t ∈ Ioo 0 δ, ∀ x ∈ (Ω : Set E), 0 < ‖x‖ ^ 2 + t ∧ ‖x‖ ^ 2 + t ≤ s₀)
    (φ : 𝓓(Ω, ℝ)) : Tendsto (fun t ↦ ∫ x, (φ : E → ℝ) x • approxLaplacian e t x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, (φ : E → ℝ) x • laplacianQuadraticSqrtNegLog e x ∂μ)) := by
  set C := ((Module.finrank ℝ E + 4) / 2 + 1) / √(M s₀) + 1 / (4 * (M s₀ * √(M s₀)))
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖(φ : E → ℝ) x‖ * C)
    (Eventually.of_forall fun t ↦
      (φ.continuous.aestronglyMeasurable.smul
        (measurable_approxLaplacian e t).aestronglyMeasurable))
    ?_ ?_ (Eventually.of_forall fun x ↦ ?_)
  · filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    refine Eventually.of_forall fun x ↦ ?_
    rw [norm_smul, Real.norm_eq_abs (approxLaplacian e t x)]
    by_cases hx : x ∈ (Ω : Set E)
    · gcongr
      exact abs_approxLaplacian_le e he hs₀ ht.1.le (hrange t ht x hx).1 (hrange t ht x hx).2
    · simp [φ.zero_on_compl hx]
  · exact (φ.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
      φ.hasCompactSupport.norm.mul_right
  · by_cases hx : x ∈ (Ω : Set E)
    swap
    · simp [φ.zero_on_compl hx]
    refine Tendsto.const_smul ?_ _
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [approxLaplacian]
    have hx1 : ‖x‖ < 1 := by
      have := (hrange (δ / 2) ⟨half_pos hδ, half_lt_self hδ⟩ x hx).2
      exact (sq_lt_one_iff₀ (norm_nonneg x)).1 (by linarith)
    obtain ⟨hx2, hx3⟩ := norm_sq_add_zero_mem_Ioo hx0 hx1
    have hshift : ContinuousAt (fun t : ℝ ↦ ‖x‖ ^ 2 + t) 0 :=
      continuousAt_const.add continuousAt_id
    have hcont : ContinuousAt (fun t ↦ approxLaplacian e t x) 0 :=
      continuousAt_const.mul
        ((continuousAt_const.mul ((continuousAt_F'' hx2 hx3).comp hshift)).add
          (continuousAt_const.mul ((hasDerivAt_F' hx2 hx3).continuousAt.comp hshift)))
    rw [← approxLaplacian_zero_eq hx0 hx1]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- `∫ Δφ u = ∫ φ f` for test functions on an open set `Ω` contained in a ball `B(0, r)` with
`r < 1`, where the approximants `uₜ` are smooth for all small `t > 0`. -/
private theorem integral_laplacian_smul_quadraticSqrtNegLog_of_subset_ball {e : Fin 2 → E}
    (he : Orthonormal ℝ e) {r : ℝ} (hr : r < 1) (hΩ : (Ω : Set E) ⊆ ball 0 r) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • quadraticSqrtNegLog e x ∂μ =
      ∫ x, (φ : E → ℝ) x • laplacianQuadraticSqrtNegLog e x ∂μ := by
  -- Reduce to `0 ≤ r`, and choose the range `0 < t < δ` of the approximation parameter, on
  -- which `‖x‖² + t ≤ s₀ < 1` for `x ∈ Ω`.
  obtain ⟨ρ, hρ0, hρ1, hΩρ⟩ : ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ (Ω : Set E) ⊆ ball 0 ρ :=
    ⟨max r 0, le_max_right _ _, max_lt hr one_pos, hΩ.trans (ball_subset_ball (le_max_left _ _))⟩
  set δ := (1 - ρ ^ 2) / 2
  set s₀ := (1 + ρ ^ 2) / 2
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hs₀ : s₀ < 1 := by simp only [s₀]; linarith
  have hrange : ∀ t ∈ Ioo 0 δ, ∀ x ∈ (Ω : Set E), 0 < ‖x‖ ^ 2 + t ∧ ‖x‖ ^ 2 + t ≤ s₀ := by
    intro t ht x hx
    have := mem_ball_zero_iff.1 (hΩρ hx)
    have hx2 : ‖x‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg x]
    refine ⟨by have := ht.1; positivity, ?_⟩
    simp only [s₀, δ] at ht ⊢
    linarith [ht.2]
  -- Green's identity for each approximant, then pass to the limit `t → 0⁺` on both sides.
  have hgreen : ∀ t ∈ Ioo 0 δ, ∫ x, Δ (φ : E → ℝ) x • approx e t x ∂μ =
      ∫ x, (φ : E → ℝ) x • approxLaplacian e t x ∂μ := by
    intro t ht
    have hs (x) (hx : x ∈ (Ω : Set E)) := hrange t ht x hx
    have hc : ContDiffOn ℝ 2 (approx e t) Ω := fun x hx ↦
      (contDiffAt_approx e (hs x hx).1 ((hs x hx).2.trans_lt hs₀)).contDiffWithinAt
    rw [hc.integral_laplacian_smul_eq_integral_smul_laplacian φ]
    exact φ.integral_smul_congr_of_eqOn fun x hx ↦
      laplacian_approx he (hs x hx).1 ((hs x hx).2.trans_lt hs₀)
  exact tendsto_nhds_unique ((tendsto_integral_laplacian_smul_approx he φ).congr'
      (by filter_upwards [Ioo_mem_nhdsGT hδ] with t ht using hgreen t ht))
    (tendsto_integral_smul_approxLaplacian he hδ hs₀ hrange φ)

variable (μ) in
/-- **`Δu = f` in the sense of distributions**, also across the origin: for every test function
`φ` on an open subset `Ω` of the unit ball, `∫ Δφ u = ∫ φ f`, where `f` is
`TauCeti.PDE.laplacianQuadraticSqrtNegLog e`. -/
theorem integral_laplacian_smul_quadraticSqrtNegLog {e : Fin 2 → E} (he : Orthonormal ℝ e)
    (hΩ : (Ω : Set E) ⊆ ball 0 1) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • quadraticSqrtNegLog e x ∂μ =
      ∫ x, (φ : E → ℝ) x • laplacianQuadraticSqrtNegLog e x ∂μ := by
  -- The compact support of `φ` lies in a smaller ball `B(0, r)`, on which `φ` is a test function.
  obtain ⟨r, hr, hφr⟩ := exists_lt_subset_ball (isClosed_tsupport _) (φ.tsupport_subset.trans hΩ)
  let ψ : 𝓓((⟨ball (0 : E) r, isOpen_ball⟩ : Opens E), ℝ) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, hφr⟩
  have hψ : (ψ : E → ℝ) = φ := TestFunction.coe_mk
  rw [← hψ]
  exact integral_laplacian_smul_quadraticSqrtNegLog_of_subset_ball he hr subset_rfl ψ

end Distribution

/-! ### No `C²` solution -/

/-- **Continuous data do not give `C²` solutions of Poisson's equation** (Gilbarg–Trudinger,
Problem 4.9). The function `f = TauCeti.PDE.laplacianQuadraticSqrtNegLog e` is continuous on the
unit ball (`TauCeti.PDE.continuousOn_laplacianQuadraticSqrtNegLog`), but on no neighbourhood `U` of
the origin is there a function `v`, `C²` on `U`, with `Δv = f` on `U`. Hence the interior Schauder
estimate has no analogue for the exponent `α = 0`. -/
theorem not_exists_contDiffOn_laplacian_eq_laplacianQuadraticSqrtNegLog {e : Fin 2 → E}
    (he : Orthonormal ℝ e) {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    ¬ ∃ v : E → ℝ, ContDiffOn ℝ 2 v U ∧ EqOn (Δ v) (laplacianQuadraticSqrtNegLog e) U := by
  rintro ⟨v, hv, hΔv⟩
  borelize E
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.1 hU
  set ρ' := min ρ 1
  have hρ' : 0 < ρ' := lt_min hρ one_pos
  let Ω : Opens E := ⟨ball 0 ρ', isOpen_ball⟩
  have hΩU : (Ω : Set E) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hρU
  have h0Ω : (0 : E) ∈ (Ω : Set E) := mem_ball_self hρ'
  have hvΩ : ContDiffOn ℝ 2 v Ω := hv.mono hΩU
  set u := quadraticSqrtNegLog e
  have hu : Continuous u := continuous_quadraticSqrtNegLog he
  -- `v - u` is weakly harmonic on `Ω`, since `Δv = f = Δu` in the sense of distributions.
  have hw : WeaklyHarmonicOn (Measure.addHaar : Measure E) Ω (v - u) := by
    refine TauCeti.weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq
      (hvΩ.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
      (hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) fun φ ↦ ?_
    rw [hvΩ.integral_laplacian_smul_eq_integral_smul_laplacian φ,
      integral_laplacian_smul_quadraticSqrtNegLog _ he (ball_subset_ball (min_le_right _ _)) φ]
    exact φ.integral_smul_congr_of_eqOn (hΔv.mono hΩU)
  -- By Weyl's lemma `v - u` is harmonic, hence `C²`, and then so is `u = v - (v - u)`.
  have hharm := (TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn
    (hvΩ.continuousOn.sub hu.continuousOn)).2 hw
  have hv0 : ContDiffAt ℝ 2 v 0 := hvΩ.contDiffAt (Ω.isOpen.mem_nhds h0Ω)
  have hu0 : ContDiffAt ℝ 2 u 0 := by
    have := hv0.sub (hharm 0 h0Ω).1
    simpa using this
  exact not_contDiffAt_quadraticSqrtNegLog he hu0

end TauCeti.PDE
