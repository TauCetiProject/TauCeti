/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Projection
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Poisson's equation with continuous data has no `C²` solution in general

The interior Schauder estimate bounds the Hölder seminorm of `D²u` by that of `Δu` (in
`TauCeti.PDE`,
`exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv_of_mul_rpow_le`).
This file shows that the Hölder hypothesis on the datum cannot be weakened to continuity: in every
finite-dimensional real inner product space of dimension at least `2` there is a continuous `f`
for which `Δv = f` has no `C²` solution on any neighbourhood of the origin
(`TauCeti.PDE.exists_continuous_forall_not_exists_contDiffOn_laplacian_eq`).

## The example

Fix orthonormal `e₁`, `e₂`, let `P x = ⟪e₁, x⟫² - ⟪e₂, x⟫²`, a harmonic quadratic, and let
`u x = P x √(-log ‖x‖)`. In the punctured ball of radius `e⁻¹`, `Δu = f` with

`f x = -(P x / ‖x‖²) ((n + 2) / (2 √(-log ‖x‖)) + 1 / (4 √(-log ‖x‖)³))`, `n = dim E`,

and `f` tends to `0` at the origin because `|P x| ≤ ‖x‖²`. Along the line through `e₁`, however,
`u` is `τ² √(-log |τ|)`, whose second derivative grows like `2 √(-log |τ|)`. In the plane, with
the standard basis, `u` is the function `(x₁² - x₂²) (-log |x|)^{1/2}` of Gilbarg–Trudinger,
Problem 4.9.

## The argument

If `v` were a `C²` solution of `Δv = f` near the origin, `u - v` would be harmonic there and `u`
would be `C²`. The point is that `u` solves `Δu = f` across the origin in the sense of
distributions. The functions `u_δ x = P x √(-log (‖x‖² + δ) / 2)`, `δ > 0`, are smooth near the
origin, so Green's identity `∫ Δφ u_δ = ∫ φ Δu_δ` holds for every test function `φ`. As `δ → 0`,
`u_δ → u` and `Δu_δ → f` pointwise and boundedly, so `∫ Δφ u = ∫ φ f`. Since `∫ Δφ v = ∫ φ f` as
well, `u - v` is weakly harmonic, hence harmonic by Weyl's lemma
(`TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn`). But a `C²` function `u` would have, along the line
through `e₁`, a derivative differentiable at `0`, while the difference quotients of that derivative
at `0` are `2 √(-log t) - 1 / (2 √(-log t))`, which are unbounded.

## Main declarations

* `TauCeti.PDE.exists_continuous_forall_not_exists_contDiffOn_laplacian_eq`: a continuous datum
  `f` for which `Δv = f` has no `C²` solution near the origin.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Problem 4.9.
-/

public section

noncomputable section

namespace TauCeti.PDE

open InnerProductSpace Laplacian Filter Metric MeasureTheory Set Topology TopologicalSpace
open scoped Gradient Distributions

/-! ### The radial factor `G t = √(-log t / 2)` -/

/-- The radial factor `G t = √(-log t / 2)`, so that `G (‖x‖²) = √(-log ‖x‖)`. -/
private def sqrtNegLog (t : ℝ) : ℝ := √(-Real.log t / 2)

/-- The first derivative of `sqrtNegLog` on `(0, 1)`. -/
private def sqrtNegLog₁ (t : ℝ) : ℝ := -1 / (4 * t * sqrtNegLog t)

/-- The second derivative of `sqrtNegLog` on `(0, 1)`. -/
private def sqrtNegLog₂ (t : ℝ) : ℝ :=
  1 / (4 * t ^ 2 * sqrtNegLog t) - 1 / (16 * t ^ 2 * sqrtNegLog t ^ 3)

private theorem sqrtNegLog_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < sqrtNegLog t :=
  Real.sqrt_pos.2 (by have := Real.log_neg ht0 ht1; linarith)

private theorem sqrtNegLog_nonneg (t : ℝ) : 0 ≤ sqrtNegLog t := Real.sqrt_nonneg _

private theorem sqrtNegLog_sq {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    sqrtNegLog t ^ 2 = -Real.log t / 2 :=
  Real.sq_sqrt (by have := Real.log_nonpos ht0.le ht1; linarith)

private theorem hasDerivAt_sqrtNegLog {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt sqrtNegLog (sqrtNegLog₁ t) t := by
  have hG := sqrtNegLog_pos ht0 ht1
  have h := (((Real.hasDerivAt_log ht0.ne').neg).div_const 2).sqrt (Real.sqrt_pos.1 hG).ne'
  convert h using 1
  · funext y
    simp only [sqrtNegLog, Pi.neg_apply]
  · simp only [sqrtNegLog₁, sqrtNegLog, Pi.neg_apply] at hG ⊢
    field_simp
    norm_num

private theorem hasDerivAt_sqrtNegLog₁ {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt sqrtNegLog₁ (sqrtNegLog₂ t) t := by
  have hG := sqrtNegLog_pos ht0 ht1
  have h₁ : HasDerivAt (fun s ↦ 4 * s * sqrtNegLog s)
      (4 * sqrtNegLog t + 4 * t * sqrtNegLog₁ t) t := by
    have h := ((hasDerivAt_id t).const_mul 4).mul (hasDerivAt_sqrtNegLog ht0 ht1)
    simp only [id, mul_one] at h
    exact h
  have h₂ := (h₁.inv (by positivity)).neg
  have hfun : sqrtNegLog₁ = fun s ↦ -(4 * s * sqrtNegLog s)⁻¹ := by
    funext s
    rw [sqrtNegLog₁, neg_div, one_div]
  rw [hfun]
  convert h₂ using 1
  simp only [sqrtNegLog₂, sqrtNegLog₁]
  field_simp
  ring

private theorem contDiffAt_sqrtNegLog {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {n : ℕ∞} :
    ContDiffAt ℝ n sqrtNegLog t :=
  (Real.contDiffAt_sqrt (Real.sqrt_pos.1 (sqrtNegLog_pos ht0 ht1)).ne').comp t
    ((Real.contDiffAt_log.2 ht0.ne').neg.div_const 2)

private theorem deriv_sqrtNegLog {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    deriv sqrtNegLog t = sqrtNegLog₁ t :=
  (hasDerivAt_sqrtNegLog ht0 ht1).deriv

private theorem deriv_deriv_sqrtNegLog {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    deriv (deriv sqrtNegLog) t = sqrtNegLog₂ t := by
  have hev : deriv sqrtNegLog =ᶠ[𝓝 t] sqrtNegLog₁ := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs using deriv_sqrtNegLog hs.1 hs.2
  rw [hev.deriv_eq, (hasDerivAt_sqrtNegLog₁ ht0 ht1).deriv]

private theorem sqrtNegLog_antitoneOn {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    sqrtNegLog t ≤ sqrtNegLog s :=
  Real.sqrt_le_sqrt (by have := Real.log_le_log hs hst; linarith)

private theorem one_le_sqrtNegLog {t : ℝ} (ht0 : 0 < t) (ht : t ≤ Real.exp (-2)) :
    1 ≤ sqrtNegLog t := by
  have := (Real.log_le_log ht0 ht).trans_eq (Real.log_exp (-2))
  exact Real.one_le_sqrt.2 (by linarith)

/-- `t √(-log t / 2) ≤ √t` on `(0, 1]`, since `-log t ≤ 1 / t`. -/
private theorem mul_sqrtNegLog_le_sqrt {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * sqrtNegLog t ≤ √t := by
  refine Real.le_sqrt_of_sq_le ?_
  have hlog : -Real.log t ≤ 1 / t := by
    have := Real.log_le_sub_one_of_pos (one_div_pos.2 ht0)
    rw [one_div, Real.log_inv] at this
    rw [one_div]
    linarith
  rw [mul_pow, sqrtNegLog_sq ht0 ht1]
  calc t ^ 2 * (-Real.log t / 2) ≤ t ^ 2 * (1 / t / 2) := by gcongr
    _ ≤ t := by field_simp; nlinarith

private theorem continuousAt_sqrtNegLog {t : ℝ} (ht : t ≠ 0) : ContinuousAt sqrtNegLog t :=
  ((Real.continuousAt_log ht).neg.div_const 2).sqrt

private theorem continuousAt_sqrtNegLog₂ {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ContinuousAt sqrtNegLog₂ t := by
  have hG := sqrtNegLog_pos ht0 ht1
  have hc := continuousAt_sqrtNegLog ht0.ne'
  have h₁ : ContinuousAt (fun s ↦ 4 * s ^ 2 * sqrtNegLog s) t :=
    (continuousAt_const.mul (continuousAt_id.pow 2)).mul hc
  have h₂ : ContinuousAt (fun s ↦ 16 * s ^ 2 * sqrtNegLog s ^ 3) t :=
    (continuousAt_const.mul (continuousAt_id.pow 2)).mul (hc.pow 3)
  exact (continuousAt_const.div h₁ (by positivity)).sub
    (continuousAt_const.div h₂ (by positivity))

/-! ### The harmonic quadratic `⟪e₁, x⟫² - ⟪e₂, x⟫²` -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic `⟪e₁, x⟫² - ⟪e₂, x⟫²`, harmonic when `‖e₁‖ = ‖e₂‖`. -/
private def quad (e₁ e₂ x : E) : ℝ := ⟪e₁, x⟫_ℝ ^ 2 - ⟪e₂, x⟫_ℝ ^ 2

private theorem quad_eq_sub (e₁ e₂ : E) :
    quad e₁ e₂ = (fun y : E ↦ ⟪e₁, y⟫_ℝ ^ 2) - fun y : E ↦ ⟪e₂, y⟫_ℝ ^ 2 := rfl

private theorem contDiff_inner_sq (a : E) {n : ℕ∞} : ContDiff ℝ n fun y : E ↦ ⟪a, y⟫_ℝ ^ 2 :=
  (contDiff_const.inner ℝ contDiff_id).pow 2

private theorem contDiff_quad (e₁ e₂ : E) {n : ℕ∞} : ContDiff ℝ n (quad e₁ e₂) :=
  (contDiff_inner_sq e₁).sub (contDiff_inner_sq e₂)

private theorem hasFDerivAt_inner_sq (a x : E) :
    HasFDerivAt (fun y : E ↦ ⟪a, y⟫_ℝ ^ 2) ((2 * ⟪a, x⟫_ℝ) • innerSL ℝ a) x := by
  simpa using ((innerSL ℝ a).hasFDerivAt (x := x)).pow 2

private theorem hasFDerivAt_quad (e₁ e₂ x : E) :
    HasFDerivAt (quad e₁ e₂)
      ((2 * ⟪e₁, x⟫_ℝ) • innerSL ℝ e₁ - (2 * ⟪e₂, x⟫_ℝ) • innerSL ℝ e₂) x := by
  rw [quad_eq_sub]
  exact (hasFDerivAt_inner_sq e₁ x).sub (hasFDerivAt_inner_sq e₂ x)

private theorem fderiv_quad_self (e₁ e₂ x : E) : fderiv ℝ (quad e₁ e₂) x x = 2 * quad e₁ e₂ x := by
  rw [(hasFDerivAt_quad e₁ e₂ x).fderiv, quad]
  simp
  ring

variable [FiniteDimensional ℝ E]

/-- For a unit vector `a`, `⟪a, x⟫²` is the squared norm of the projection onto `ℝ a`, so its
Laplacian is twice the rank `1` of that projection. -/
private theorem laplacian_inner_sq {a : E} (ha : ‖a‖ = 1) (x : E) :
    Δ (fun y : E ↦ ⟪a, y⟫_ℝ ^ 2) x = 2 := by
  have h : (fun y : E ↦ ⟪a, y⟫_ℝ ^ 2) = fun y ↦ ‖(ℝ ∙ a).starProjection y‖ ^ 2 := by
    funext y
    rw [Submodule.starProjection_singleton, norm_smul, ha]
    simp
  rw [h, Submodule.laplacian_norm_starProjection_sq,
    finrank_span_singleton (norm_ne_zero_iff.1 (ha.trans_ne one_ne_zero))]
  norm_num

private theorem laplacian_quad {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (x : E) :
    Δ (quad e₁ e₂) x = 0 := by
  rw [quad_eq_sub, (contDiff_inner_sq e₁).contDiffAt.laplacian_sub
    (contDiff_inner_sq e₂).contDiffAt, laplacian_inner_sq he₁, laplacian_inner_sq he₂, sub_self]

/-! ### The approximants and their Laplacians -/

/-- The approximant `u_δ x = (⟪e₁, x⟫² - ⟪e₂, x⟫²) √(-log (‖x‖² + δ) / 2)`, smooth near the
origin for `δ > 0`. For `δ = 0` it is `(⟪e₁, x⟫² - ⟪e₂, x⟫²) √(-log ‖x‖)`, which is not `C²` at
the origin (`not_contDiffOn_approx_zero`). -/
private def approx (e₁ e₂ : E) (δ : ℝ) (x : E) : ℝ := quad e₁ e₂ x * sqrtNegLog (‖x‖ ^ 2 + δ)

/-- The Laplacian of `approx e₁ e₂ δ` where `0 < ‖x‖² + δ < 1`. -/
private def lapApprox (e₁ e₂ : E) (δ : ℝ) (x : E) : ℝ :=
  quad e₁ e₂ x * (4 * ‖x‖ ^ 2 * sqrtNegLog₂ (‖x‖ ^ 2 + δ) +
    (2 * Module.finrank ℝ E + 8) * sqrtNegLog₁ (‖x‖ ^ 2 + δ))

omit [FiniteDimensional ℝ E] in
private theorem contDiffAt_approx (e₁ e₂ : E) {δ : ℝ} {x : E} (h0 : 0 < ‖x‖ ^ 2 + δ)
    (h1 : ‖x‖ ^ 2 + δ < 1) {n : ℕ∞} : ContDiffAt ℝ n (approx e₁ e₂ δ) x :=
  (contDiff_quad e₁ e₂).contDiffAt.mul <| (contDiffAt_sqrtNegLog h0 h1).comp
    (f := fun y : E ↦ ‖y‖ ^ 2 + δ) x ((contDiff_norm_sq ℝ).add contDiff_const).contDiffAt

private theorem laplacian_approx {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) {δ : ℝ} {x : E}
    (h0 : 0 < ‖x‖ ^ 2 + δ) (h1 : ‖x‖ ^ 2 + δ < 1) :
    Δ (approx e₁ e₂ δ) x = lapApprox e₁ e₂ δ x := by
  set N : E → ℝ := fun y ↦ ‖y‖ ^ 2 + δ
  have hN : ContDiff ℝ 2 N := (contDiff_norm_sq ℝ).add contDiff_const
  have hNd : HasFDerivAt N (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const δ
  have hG := contDiffAt_sqrtNegLog (n := 2) h0 h1
  have hR : ContDiffAt ℝ 2 (sqrtNegLog ∘ N) x := hG.comp x hN.contDiffAt
  -- The Laplacian of the radial factor.
  have hΔN : Δ N x = 2 * Module.finrank ℝ E := by
    rw [show N = (fun y : E ↦ ‖y‖ ^ 2) + fun _ ↦ δ from rfl,
      (contDiff_norm_sq ℝ).contDiffAt.laplacian_add contDiffAt_const, laplacian_norm_sq]
    simp
  have hgradN : ‖∇ N x‖ = 2 * ‖x‖ := by
    rw [norm_gradient_eq_norm_fderiv, hNd.fderiv, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
      innerSL_apply_norm]
    norm_num
  have hΔR : Δ (sqrtNegLog ∘ N) x =
      4 * ‖x‖ ^ 2 * sqrtNegLog₂ (‖x‖ ^ 2 + δ) +
        2 * Module.finrank ℝ E * sqrtNegLog₁ (‖x‖ ^ 2 + δ) := by
    rw [hG.laplacian_comp (q := N) hN.contDiffAt, hgradN, hΔN, deriv_deriv_sqrtNegLog h0 h1,
      deriv_sqrtNegLog h0 h1]
    ring
  -- The mixed term, by Euler's identity `⟪x, ∇P x⟫ = 2 P x` for the quadratic.
  have hmix : ⟪∇ (quad e₁ e₂) x, ∇ (sqrtNegLog ∘ N) x⟫_ℝ =
      4 * sqrtNegLog₁ (‖x‖ ^ 2 + δ) * quad e₁ e₂ x := by
    rw [inner_gradient_right, conj_trivial,
      ((hasDerivAt_sqrtNegLog h0 h1).comp_hasFDerivAt x hNd).fderiv]
    simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul,
      inner_gradient_right, conj_trivial, fderiv_quad_self]
    ring
  rw [show approx e₁ e₂ δ = fun y ↦ quad e₁ e₂ y * (sqrtNegLog ∘ N) y from rfl,
    (contDiff_quad e₁ e₂).contDiffAt.laplacian_fun_mul hR, hΔR, hmix, laplacian_quad he₁ he₂ x,
    lapApprox]
  ring

/-! ### Uniform bounds and limits as `δ → 0` -/

omit [FiniteDimensional ℝ E] in
private theorem abs_quad_le {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (x : E) :
    |quad e₁ e₂ x| ≤ ‖x‖ ^ 2 := by
  have h (e : E) (he : ‖e‖ = 1) : ⟪e, x⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 := by
    have := abs_real_inner_le_norm e x
    rw [he, one_mul] at this
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  rw [quad, abs_le]
  constructor <;> nlinarith [h e₁ he₁, h e₂ he₂, sq_nonneg ⟪e₁, x⟫_ℝ, sq_nonneg ⟪e₂, x⟫_ℝ]

omit [FiniteDimensional ℝ E] in
/-- The approximants are bounded by `‖x‖` on the closed unit ball, uniformly in `δ ≥ 0`. -/
private theorem abs_approx_le {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) {δ : ℝ}
    (hδ : 0 ≤ δ) {x : E} (hx : ‖x‖ ≤ 1) : |approx e₁ e₂ δ x| ≤ ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [approx, quad]
  have ht : 0 < ‖x‖ ^ 2 := by positivity
  have ht1 : ‖x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg x) hx
  rw [approx, abs_mul, abs_of_nonneg (sqrtNegLog_nonneg _)]
  calc |quad e₁ e₂ x| * sqrtNegLog (‖x‖ ^ 2 + δ) ≤ ‖x‖ ^ 2 * sqrtNegLog (‖x‖ ^ 2) :=
        mul_le_mul (abs_quad_le he₁ he₂ x) (sqrtNegLog_antitoneOn ht (by linarith))
          (sqrtNegLog_nonneg _) (by positivity)
    _ ≤ √(‖x‖ ^ 2) := mul_sqrtNegLog_le_sqrt ht ht1
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg x)

omit [FiniteDimensional ℝ E] in
/-- The Laplacians of the approximants are bounded uniformly in `δ` near the origin. -/
private theorem abs_lapApprox_le {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) {δ : ℝ}
    (hδ : 0 ≤ δ) {x : E} (h0 : 0 < ‖x‖ ^ 2 + δ) (h : ‖x‖ ^ 2 + δ ≤ Real.exp (-2)) :
    |lapApprox e₁ e₂ δ x| ≤ Module.finrank ℝ E + 5 := by
  set q := ‖x‖ ^ 2 + δ with hq
  have hG : 1 ≤ sqrtNegLog q := one_le_sqrtNegLog h0 h
  have hG0 : 0 < sqrtNegLog q := one_pos.trans_le hG
  have hP : |quad e₁ e₂ x| ≤ q := (abs_quad_le he₁ he₂ x).trans (by linarith)
  have heq : lapApprox e₁ e₂ δ x = quad e₁ e₂ x / q *
      (‖x‖ ^ 2 / q * (1 / sqrtNegLog q - 1 / (4 * sqrtNegLog q ^ 3)) -
        (Module.finrank ℝ E + 4) / (2 * sqrtNegLog q)) := by
    simp only [lapApprox, sqrtNegLog₁, sqrtNegLog₂, ← hq]
    field_simp
    ring
  have ha : |quad e₁ e₂ x / q| ≤ 1 := by
    rw [abs_div, abs_of_pos h0]
    exact div_le_one_of_le₀ hP h0.le
  have hb : |‖x‖ ^ 2 / q| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ (by linarith) h0.le
  have hc : |1 / sqrtNegLog q - 1 / (4 * sqrtNegLog q ^ 3)| ≤ 1 := by
    have h₁ : 1 / sqrtNegLog q ≤ 1 := (div_le_one hG0).2 hG
    have h₂ : 0 < 1 / (4 * sqrtNegLog q ^ 3) := by positivity
    have h₃ : 1 / (4 * sqrtNegLog q ^ 3) ≤ 1 / sqrtNegLog q := by
      gcongr
      linarith [le_self_pow₀ hG (by norm_num : (3 : ℕ) ≠ 0)]
    rw [abs_le]
    constructor <;> linarith
  have hd : |(Module.finrank ℝ E + 4 : ℝ) / (2 * sqrtNegLog q)| ≤ Module.finrank ℝ E + 4 := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) (by linarith)
  rw [heq, abs_mul]
  calc |quad e₁ e₂ x / q| * |‖x‖ ^ 2 / q * (1 / sqrtNegLog q - 1 / (4 * sqrtNegLog q ^ 3)) -
        (Module.finrank ℝ E + 4) / (2 * sqrtNegLog q)| ≤
        1 * (1 * 1 + (Module.finrank ℝ E + 4)) := by
        refine mul_le_mul ha ((abs_sub _ _).trans (add_le_add ?_ hd)) (abs_nonneg _) zero_le_one
        rw [abs_mul]
        exact mul_le_mul hb hc (abs_nonneg _) zero_le_one
    _ = Module.finrank ℝ E + 5 := by ring

omit [FiniteDimensional ℝ E] in
private theorem continuousAt_approx (e₁ e₂ : E) {δ : ℝ} {x : E} (h : ‖x‖ ^ 2 + δ ≠ 0) :
    ContinuousAt (approx e₁ e₂ δ) x :=
  (contDiff_quad e₁ e₂ (n := 0)).continuous.continuousAt.mul <| (continuousAt_sqrtNegLog h).comp
    (f := fun y : E ↦ ‖y‖ ^ 2 + δ) (by fun_prop)

omit [FiniteDimensional ℝ E] in
private theorem tendsto_approx (e₁ e₂ : E) (x : E) :
    Tendsto (fun δ ↦ approx e₁ e₂ δ x) (𝓝 0) (𝓝 (approx e₁ e₂ 0 x)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [approx, quad]
  have h : ‖x‖ ^ 2 + 0 ≠ 0 := by positivity
  exact (continuousAt_const.mul ((continuousAt_sqrtNegLog h).comp
    (f := fun δ : ℝ ↦ ‖x‖ ^ 2 + δ) (by fun_prop))).tendsto

omit [FiniteDimensional ℝ E] in
private theorem tendsto_lapApprox (e₁ e₂ : E) {x : E} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    Tendsto (fun δ ↦ lapApprox e₁ e₂ δ x) (𝓝 0) (𝓝 (lapApprox e₁ e₂ 0 x)) := by
  have h0 : 0 < ‖x‖ ^ 2 + 0 := by positivity
  have h1 : ‖x‖ ^ 2 + 0 < 1 := by
    rw [add_zero]
    exact pow_lt_one₀ (norm_nonneg x) hx1 two_ne_zero
  have hq : ContinuousAt (fun δ : ℝ ↦ ‖x‖ ^ 2 + δ) 0 := by fun_prop
  exact (continuousAt_const.mul
    ((continuousAt_const.mul ((continuousAt_sqrtNegLog₂ h0 h1).comp (f := _) hq)).add
      (continuousAt_const.mul
        ((hasDerivAt_sqrtNegLog₁ h0 h1).continuousAt.comp (f := _) hq)))).tendsto

omit [FiniteDimensional ℝ E] in
/-- The function `(⟪e₁, x⟫² - ⟪e₂, x⟫²) √(-log ‖x‖)` is continuous. -/
private theorem continuous_approx_zero {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) :
    Continuous (approx e₁ e₂ 0) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : approx e₁ e₂ 0 0 = 0 := by simp [approx, quad]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm' ?_ tendsto_norm_zero
    filter_upwards [closedBall_mem_nhds (0 : E) one_pos] with y hy
    exact abs_approx_le he₁ he₂ le_rfl (by simpa using hy)
  · exact continuousAt_approx e₁ e₂ (by positivity)

/-! ### The continuous datum -/

/-- The scale `√(max (-log ‖x‖) 1)`, equal to `√(-log ‖x‖)` near the origin and at least `1`. -/
private def datumScale (x : E) : ℝ := √(max (-Real.log ‖x‖) 1)

/-- The continuous datum
`f x = -((⟪e₁, x⟫² - ⟪e₂, x⟫²) / ‖x‖²) ((dim E + 2) / (2 σ) + 1 / (4 σ³))`, `σ = datumScale x`,
the Laplacian of `(⟪e₁, x⟫² - ⟪e₂, x⟫²) √(-log ‖x‖)` near the origin. -/
private def datum (e₁ e₂ x : E) : ℝ :=
  -(quad e₁ e₂ x / ‖x‖ ^ 2) *
    ((Module.finrank ℝ E + 2) / (2 * datumScale x) + 1 / (4 * datumScale x ^ 3))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem one_le_datumScale (x : E) : 1 ≤ datumScale x :=
  Real.one_le_sqrt.2 (le_max_right _ _)

omit [FiniteDimensional ℝ E] in
private theorem datum_zero (e₁ e₂ : E) : datum e₁ e₂ 0 = 0 := by simp [datum, quad]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem tendsto_datumScale : Tendsto (datumScale (E := E)) (𝓝[≠] 0) atTop := by
  have h : Tendsto (fun x : E ↦ -Real.log ‖x‖) (𝓝[≠] 0) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero)
  exact Real.tendsto_sqrt_atTop.comp (tendsto_atTop_mono (fun _ ↦ le_max_left _ _) h)

omit [FiniteDimensional ℝ E] in
private theorem continuous_datum {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) :
    Continuous (datum e₁ e₂) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, datum_zero]
    -- `|f x| ≤ (dim E + 3) / σ` with `σ → ∞` at the origin.
    have hlim : Tendsto (fun y : E ↦ (Module.finrank ℝ E + 3 : ℝ) * (datumScale y)⁻¹)
        (𝓝[≠] 0) (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_datumScale).const_mul
        ((Module.finrank ℝ E : ℝ) + 3)
    refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun y hy ↦ ?_) hlim
    have hy0 : 0 < ‖y‖ ^ 2 := by have : y ≠ 0 := hy; positivity
    have hσ := one_le_datumScale y
    have ha : |quad e₁ e₂ y / ‖y‖ ^ 2| ≤ 1 := by
      rw [abs_div, abs_of_pos hy0]
      exact div_le_one_of_le₀ (abs_quad_le he₁ he₂ y) hy0.le
    have hb : (Module.finrank ℝ E + 2 : ℝ) / (2 * datumScale y) + 1 / (4 * datumScale y ^ 3) ≤
        (Module.finrank ℝ E + 3) * (datumScale y)⁻¹ := by
      have h₃ : 1 / (4 * datumScale y ^ 3) ≤ 1 / datumScale y := by
        gcongr
        linarith [le_self_pow₀ hσ (by norm_num : (3 : ℕ) ≠ 0)]
      have h₂ : (Module.finrank ℝ E + 2 : ℝ) / (2 * datumScale y) ≤
          (Module.finrank ℝ E + 2) / datumScale y := by
        gcongr
        linarith
      calc _ ≤ (Module.finrank ℝ E + 2) / datumScale y + 1 / datumScale y := add_le_add h₂ h₃
        _ = _ := by field_simp; ring
    rw [Real.norm_eq_abs, datum, abs_mul, abs_neg, abs_of_nonneg (by positivity :
      0 ≤ (Module.finrank ℝ E + 2 : ℝ) / (2 * datumScale y) + 1 / (4 * datumScale y ^ 3))]
    exact (mul_le_of_le_one_left (by positivity) ha).trans hb
  · have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hσ : ContinuousAt (datumScale (E := E)) x :=
      (((Real.continuousAt_log hx0).comp continuous_norm.continuousAt).neg.max
        continuousAt_const).sqrt
    have hσ0 := one_pos.trans_le (one_le_datumScale x)
    exact ((((contDiff_quad e₁ e₂ (n := 0)).continuous.continuousAt.div
      (continuous_norm.continuousAt.pow 2) (pow_ne_zero 2 hx0)).neg).mul
      ((continuousAt_const.div (continuousAt_const.mul hσ) (mul_pos two_pos hσ0).ne').add
        (continuousAt_const.div (continuousAt_const.mul (hσ.pow 3))
          (mul_pos four_pos (pow_pos hσ0 3)).ne')))

omit [FiniteDimensional ℝ E] in
/-- Near the origin the Laplacian of `(⟪e₁, x⟫² - ⟪e₂, x⟫²) √(-log ‖x‖)` is the datum. -/
private theorem lapApprox_zero_eq_datum (e₁ e₂ : E) {x : E} (hx : x ≠ 0)
    (hx1 : ‖x‖ ≤ Real.exp (-1)) : lapApprox e₁ e₂ 0 x = datum e₁ e₂ x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hlog : Real.log ‖x‖ ≤ -1 := (Real.log_le_log hn hx1).trans_eq (Real.log_exp _)
  have hσ : sqrtNegLog (‖x‖ ^ 2 + 0) = datumScale x := by
    rw [add_zero, sqrtNegLog, datumScale, Real.log_pow, max_eq_left (by linarith)]
    congr 1
    push_cast
    ring
  have hσ0 : 0 < datumScale x := one_pos.trans_le (one_le_datumScale x)
  simp only [lapApprox, datum, sqrtNegLog₁, sqrtNegLog₂, hσ]
  field_simp
  ring

/-! ### The limit function is a distributional solution -/

/-- The radius `e⁻¹ / 2` of the ball on which the approximation argument runs. -/
private def radius : ℝ := Real.exp (-1) / 2

private theorem radius_pos : 0 < radius := by unfold radius; positivity

private theorem radius_le_exp : radius ≤ Real.exp (-1) := by
  unfold radius
  linarith [Real.exp_pos (-1)]

private theorem radius_le_one : radius ≤ 1 :=
  radius_le_exp.trans (Real.exp_le_one_iff.2 (by norm_num))

private theorem two_mul_radius_sq_le : 2 * radius ^ 2 ≤ Real.exp (-2) := by
  have h : Real.exp (-1) ^ 2 = Real.exp (-2) := by rw [← Real.exp_nat_mul]; norm_num
  unfold radius
  rw [div_pow, h]
  linarith [Real.exp_pos (-2)]

private theorem exp_neg_two_lt_one : Real.exp (-2) < 1 := Real.exp_lt_one_iff.2 (by norm_num)

omit [FiniteDimensional ℝ E] in
private theorem measurable_lapApprox [MeasurableSpace E] [BorelSpace E] (e₁ e₂ : E) (δ : ℝ) :
    Measurable (lapApprox e₁ e₂ δ) := by
  have hq : Measurable (quad e₁ e₂) := (contDiff_quad e₁ e₂ (n := 0)).continuous.measurable
  unfold lapApprox sqrtNegLog₁ sqrtNegLog₂ sqrtNegLog
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem norm_sq_add_le {x : E} (hx : x ∈ ball (0 : E) radius) {δ : ℝ}
    (hδ : δ ≤ radius ^ 2) : ‖x‖ ^ 2 + δ ≤ Real.exp (-2) := by
  have : ‖x‖ ^ 2 < radius ^ 2 := by
    have := mem_ball_zero_iff.1 hx
    gcongr
  linarith [two_mul_radius_sq_le]

/-- Green's identity for the smooth approximants, with their Laplacians made explicit. -/
private theorem integral_laplacian_smul_approx [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) {Ω : Opens E}
    (hΩ : (Ω : Set E) ⊆ ball 0 radius) (φ : 𝓓(Ω, ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ radius ^ 2) :
    ∫ x, Δ (φ : E → ℝ) x • approx e₁ e₂ δ x ∂μ = ∫ x, (φ : E → ℝ) x • lapApprox e₁ e₂ δ x ∂μ := by
  have h0 {x : E} : 0 < ‖x‖ ^ 2 + δ := by positivity
  have h1 {x : E} (hx : x ∈ Ω) : ‖x‖ ^ 2 + δ < 1 :=
    (norm_sq_add_le (hΩ hx) hδ).trans_lt exp_neg_two_lt_one
  have hC : ContDiffOn ℝ 2 (approx e₁ e₂ δ) Ω := fun x hx ↦
    (contDiffAt_approx e₁ e₂ h0 (h1 hx)).contDiffWithinAt
  rw [hC.integral_laplacian_smul_eq_integral_smul_laplacian φ]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ Ω
  · dsimp only
    rw [laplacian_approx he₁ he₂ h0 (h1 hx)]
  · simp [φ.zero_on_compl hx]

omit [FiniteDimensional ℝ E] in
/-- The approximants converge boundedly to the limit function against a test function. -/
private theorem tendsto_integral_smul_approx [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    {Ω : Opens E} (hΩ : (Ω : Set E) ⊆ ball 0 1) (ψ : 𝓓(Ω, ℝ)) {δ : ℕ → ℝ} (hδ0 : ∀ k, 0 < δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k ↦ ∫ x, (ψ : E → ℝ) x • approx e₁ e₂ (δ k) x ∂μ) atTop
      (𝓝 (∫ x, (ψ : E → ℝ) x • approx e₁ e₂ 0 x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖(ψ : E → ℝ) x‖) (fun k ↦ ?_)
    (ψ.continuous.norm.integrable_of_hasCompactSupport ψ.hasCompactSupport.norm)
    (fun k ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
  · have hc : Continuous (approx e₁ e₂ (δ k)) := continuous_iff_continuousAt.2 fun x ↦
      continuousAt_approx e₁ e₂ (by have := hδ0 k; positivity)
    exact (ψ.continuous.smul hc).aestronglyMeasurable
  · by_cases hx : x ∈ Ω
    · rw [norm_smul, Real.norm_eq_abs (approx _ _ _ _)]
      have hx1 : ‖x‖ ≤ 1 := (mem_ball_zero_iff.1 (hΩ hx)).le
      exact mul_le_of_le_one_right (norm_nonneg _)
        ((abs_approx_le he₁ he₂ (hδ0 k).le hx1).trans hx1)
    · simp [ψ.zero_on_compl hx]
  · exact ((tendsto_approx e₁ e₂ x).comp hδ).const_smul _

omit [FiniteDimensional ℝ E] in
/-- The Laplacians of the approximants converge boundedly to the datum against a test
function. -/
private theorem tendsto_integral_smul_lapApprox [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    {Ω : Opens E} (hΩ : (Ω : Set E) ⊆ ball 0 radius) (φ : 𝓓(Ω, ℝ)) {δ : ℕ → ℝ}
    (hδ0 : ∀ k, 0 < δ k) (hδle : ∀ k, δ k ≤ radius ^ 2) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k ↦ ∫ x, (φ : E → ℝ) x • lapApprox e₁ e₂ (δ k) x ∂μ) atTop
      (𝓝 (∫ x, (φ : E → ℝ) x • datum e₁ e₂ x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun x ↦ ‖(φ : E → ℝ) x‖ * (Module.finrank ℝ E + 5)) (fun k ↦ ?_)
    ((φ.continuous.norm.integrable_of_hasCompactSupport φ.hasCompactSupport.norm).mul_const _)
    (fun k ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
  · exact (φ.continuous.measurable.smul (measurable_lapApprox e₁ e₂ _)).aestronglyMeasurable
  · by_cases hx : x ∈ Ω
    · rw [norm_smul, Real.norm_eq_abs (lapApprox _ _ _ _)]
      exact mul_le_mul_of_nonneg_left (abs_lapApprox_le he₁ he₂ (hδ0 k).le
        (by have := hδ0 k; positivity) (norm_sq_add_le (hΩ hx) (hδle k))) (norm_nonneg _)
    · simp [φ.zero_on_compl hx]
  · by_cases hx : x ∈ Ω
    · rcases eq_or_ne x 0 with rfl | hx0
      · simp [lapApprox, datum_zero, quad]
      have hxr := mem_ball_zero_iff.1 (hΩ hx)
      rw [← lapApprox_zero_eq_datum e₁ e₂ hx0 (hxr.le.trans radius_le_exp)]
      exact ((tendsto_lapApprox e₁ e₂ hx0 (hxr.trans_le radius_le_one)).comp hδ).const_smul _
    · simp [φ.zero_on_compl hx]

/-- **The limit function solves `Δu = f` in the sense of distributions** near the origin: Green's
identity holds for the smooth approximants `u_δ`, and as `δ → 0` both sides converge boundedly. -/
private theorem integral_laplacian_smul_approx_zero [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    {Ω : Opens E} (hΩ : (Ω : Set E) ⊆ ball 0 radius) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • approx e₁ e₂ 0 x ∂μ = ∫ x, (φ : E → ℝ) x • datum e₁ e₂ x ∂μ := by
  set δ : ℕ → ℝ := fun k ↦ radius ^ 2 * (1 / ((k : ℝ) + 1)) with hδdef
  have hδ0 (k : ℕ) : 0 < δ k := mul_pos (pow_pos radius_pos 2) (by positivity)
  have hδle (k : ℕ) : δ k ≤ radius ^ 2 :=
    mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by simp))
  have hδ : Tendsto δ atTop (𝓝 0) := by
    rw [hδdef]
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (radius ^ 2)
  -- The Laplacian of `φ` is again a test function on `Ω`.
  set ψ := LineDeriv.laplacianCLM ℝ E 𝓓(Ω, ℝ) φ
  have hψ : ⇑ψ = Δ (φ : E → ℝ) := funext (TestFunction.laplacianCLM_apply φ)
  have hL := tendsto_integral_smul_approx (μ := μ) he₁ he₂ (hΩ.trans (ball_subset_ball
    radius_le_one)) ψ hδ0 hδ
  rw [hψ] at hL
  refine tendsto_nhds_unique hL ?_
  simpa only [integral_laplacian_smul_approx he₁ he₂ hΩ φ (hδ0 _) (hδle _)] using
    tendsto_integral_smul_lapApprox he₁ he₂ hΩ φ hδ0 hδle hδ

/-! ### The limit function is not `C²` at the origin -/

omit [FiniteDimensional ℝ E] in
private theorem approx_zero_smul {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (h12 : ⟪e₂, e₁⟫_ℝ = 0) (τ : ℝ) :
    approx e₁ e₂ 0 (τ • e₁) = τ ^ 2 * sqrtNegLog (τ ^ 2) := by
  simp [approx, quad, inner_smul_right, he₁, h12, norm_smul]

private theorem hasDerivAt_sq_mul_sqrtNegLog_sq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun τ ↦ τ ^ 2 * sqrtNegLog (τ ^ 2))
      (t * (2 * sqrtNegLog (t ^ 2) - 1 / (2 * sqrtNegLog (t ^ 2)))) t := by
  have h0 : 0 < t ^ 2 := by positivity
  have h1 : t ^ 2 < 1 := pow_lt_one₀ ht0.le ht1 two_ne_zero
  have hG := sqrtNegLog_pos h0 h1
  have h := (hasDerivAt_pow 2 t).mul
    ((hasDerivAt_sqrtNegLog h0 h1).comp (h := fun τ : ℝ ↦ τ ^ 2) t (hasDerivAt_pow 2 t))
  convert h using 1
  · rfl
  · simp only [Function.comp_apply, sqrtNegLog₁]
    field_simp
    ring

private theorem tendsto_sqrtNegLog_sq :
    Tendsto (fun t : ℝ ↦ sqrtNegLog (t ^ 2)) (𝓝[>] 0) atTop := by
  have hsq : Tendsto (fun t : ℝ ↦ t ^ 2) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_pow 2).tendsto' 0 0 (by norm_num)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht ↦ pow_pos ht 2)
  have h : Tendsto (fun t : ℝ ↦ -Real.log (t ^ 2) / 2) (𝓝[>] 0) atTop :=
    (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsq)).atTop_div_const two_pos
  exact Real.tendsto_sqrt_atTop.comp h

omit [FiniteDimensional ℝ E] in
/-- The limit function `(⟪e₁, x⟫² - ⟪e₂, x⟫²) √(-log ‖x‖)` is not `C²` on any ball about the
origin. Along the line through `e₁` it is `h τ = τ² √(-log |τ|)`, whose derivative
`2 t √(-log t) - t / (2 √(-log t))` vanishes at `0` but has unbounded difference quotients there. -/
private theorem not_contDiffOn_approx_zero {e₁ e₂ : E} (he₁ : ‖e₁‖ = 1) (h12 : ⟪e₂, e₁⟫_ℝ = 0)
    {r : ℝ} (hr : 0 < r) : ¬ContDiffOn ℝ 2 (approx e₁ e₂ 0) (ball 0 r) := by
  intro hu
  set h : ℝ → ℝ := fun τ ↦ τ ^ 2 * sqrtNegLog (τ ^ 2) with hhdef
  -- `h` is the restriction of the limit function to the line through `e₁`, hence `C²` near `0`.
  have hC : ContDiffAt ℝ 2 h 0 := by
    have hmaps : MapsTo (fun τ : ℝ ↦ τ • e₁) (ball 0 r) (ball 0 r) := fun τ hτ ↦ by
      simpa [norm_smul, he₁] using hτ
    have hcomp : ContDiffOn ℝ 2 h (ball 0 r) :=
      (hu.comp (contDiff_id.smul contDiff_const).contDiffOn hmaps).congr fun τ _ ↦
        (approx_zero_smul he₁ h12 τ).symm
    exact hcomp.contDiffAt (ball_mem_nhds 0 hr)
  -- So `deriv h` is differentiable at `0`, where it vanishes because `h` is even.
  have hd : DifferentiableAt ℝ (deriv h) 0 := by
    have h1 := (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact (h1.clm_apply (differentiableAt_const (1 : ℝ))).congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦ (fderiv_apply_one_eq_deriv (f := h) (x := y)).symm)
  have hd0 : deriv h 0 = 0 := by
    have heven : (fun τ ↦ h (-τ)) = h := by
      funext τ
      simp [hhdef]
    have := deriv_comp_neg (f := h) (x := 0)
    rw [heven, neg_zero] at this
    linarith
  -- The difference quotients `deriv h t / t = 2 G - 1 / (2 G)`, `G = √(-log t)`, are unbounded.
  have hslope := hd.hasDerivAt.tendsto_slope_zero_right
  have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • (deriv h (0 + t) - deriv h 0) =
        2 * sqrtNegLog (t ^ 2) - 1 / (2 * sqrtNegLog (t ^ 2)) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    rw [zero_add, hd0, sub_zero, (hasDerivAt_sq_mul_sqrtNegLog_sq ht.1 ht.2).deriv, smul_eq_mul,
      inv_mul_cancel_left₀ ht.1.ne']
  have hge : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      sqrtNegLog (t ^ 2) ≤ 2 * sqrtNegLog (t ^ 2) - 1 / (2 * sqrtNegLog (t ^ 2)) := by
    filter_upwards [tendsto_sqrtNegLog_sq.eventually_ge_atTop 1] with t ht
    have h₁ : 1 / (2 * sqrtNegLog (t ^ 2)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_mono' _ hge tendsto_sqrtNegLog_sq) _
    (hslope.congr' heq)

/-! ### Continuous data do not give `C²` solutions -/

/-- **Poisson's equation with continuous data need not have a `C²` solution.** In a
finite-dimensional real inner product space of dimension at least `2` there is a continuous
function `f` such that `Δv = f` has no `C²` solution `v` on any neighbourhood of the origin.

For orthonormal `e₁`, `e₂`, `f` is the continuous extension of the Laplacian of
`u x = (⟪e₁, x⟫² - ⟪e₂, x⟫²) √(-log ‖x‖)` from the punctured ball of radius `e⁻¹`: there
`f x = -((⟪e₁, x⟫² - ⟪e₂, x⟫²) / ‖x‖²) ((dim E + 2) / (2 √(-log ‖x‖)) + 1 / (4 √(-log ‖x‖)³))`,
which tends to `0` at the origin, while along the line through `e₁` the second derivative of `u`
grows like `2 √(-log ‖x‖)`. -/
theorem exists_continuous_forall_not_exists_contDiffOn_laplacian_eq
    (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ f : E → ℝ, Continuous f ∧
      ∀ U ∈ 𝓝 (0 : E), ¬∃ v : E → ℝ, ContDiffOn ℝ 2 v U ∧ EqOn (Δ v) f U := by
  borelize E
  set b := stdOrthonormalBasis ℝ E
  set e₁ := b ⟨0, by omega⟩
  set e₂ := b ⟨1, by omega⟩
  have he₁ : ‖e₁‖ = 1 := b.orthonormal.1 _
  have he₂ : ‖e₂‖ = 1 := b.orthonormal.1 _
  have h12 : ⟪e₂, e₁⟫_ℝ = 0 := b.orthonormal.2 (by simp [Fin.ext_iff])
  refine ⟨datum e₁ e₂, continuous_datum he₁ he₂, fun U hU ⟨v, hv, hvf⟩ ↦ ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  set Ω : Opens E := ⟨ball 0 (min r radius), isOpen_ball⟩
  have hΩU : (Ω : Set E) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hrU
  have hΩr : (Ω : Set E) ⊆ ball 0 radius := ball_subset_ball (min_le_right _ _)
  have hvΩ : ContDiffOn ℝ 2 v Ω := hv.mono hΩU
  have hu : Continuous (approx e₁ e₂ 0) := continuous_approx_zero he₁ he₂
  let μ : Measure E := Measure.addHaar
  -- `u - v` is weakly harmonic on `Ω`: both solve `Δ · = f` in the sense of distributions.
  have hw : WeaklyHarmonicOn μ Ω (approx e₁ e₂ 0 - v) := by
    refine weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq
      (hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
      (hvΩ.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) fun φ ↦ ?_
    rw [integral_laplacian_smul_approx_zero he₁ he₂ hΩr,
      hvΩ.integral_laplacian_smul_eq_integral_smul_laplacian φ]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : x ∈ Ω
    · dsimp only
      rw [hvf (hΩU hx)]
    · simp [φ.zero_on_compl hx]
  -- By Weyl's lemma `u - v` is harmonic, so `u = (u - v) + v` would be `C²` on `Ω`.
  have hharm := (harmonicOnNhd_iff_weaklyHarmonicOn (μ := μ)
    (hu.continuousOn.sub hvΩ.continuousOn)).2 hw
  have hC : ContDiffOn ℝ 2 (approx e₁ e₂ 0) Ω := by
    simpa using hharm.contDiffOn.add hvΩ
  exact not_contDiffOn_approx_zero he₁ h12 (lt_min hr radius_pos) hC

end TauCeti.PDE
