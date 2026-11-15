/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Non-stationary phase, uniformly over a family of phases

Let `φ` be a smooth compactly supported function on a finite-dimensional real normed space `E`,
and let `θ x : V →L[ℝ] ℝ` be a smooth family of linear forms on a finite-dimensional parameter
space `V`, so that `x ↦ θ x p` is a phase depending linearly on `p ∈ V`. If the phase has no
stationary point on the support of `φ`, quantitatively

`c ‖p‖ ≤ ‖D_x (θ x p)‖` for `x ∈ supp φ` and `p ∈ S`,

then the oscillatory integral `∫ 𝐞 (-θ x p) φ x dx` decays faster than every power of `‖p‖`,
uniformly for `p ∈ S` (`TauCeti.exists_one_add_norm_pow_mul_norm_integral_le`). This is the
estimate behind the wave front set of a pushforward or a pullback along a smooth map: there the
phase is `⟪Φ x, η⟫ + ⟪x, m⟫` with parameter `p = (η, m)`, and its derivative `Φ'(x)ᵀ η + m`
stays away from zero outside a conic neighbourhood of `m = -Φ'(x)ᵀ η`.

The proof integrates by parts `N` times. Fix a basis `b` of `E` and write `g_i = D_{b_i} (θ · p)`
and `q = ∑ g_i²`. On the support of `φ`, at a unit parameter `p`, the coefficients
`w_i = g_i / q` satisfy `∑ w_i g_i = 1`, so the derivative of `𝐞 (-t θ x p)` along the field
`∑ w_i b_i` is `-2πi t 𝐞 (-t θ x p)`. Moving it onto the amplitude gives

`∫ 𝐞 (-θ x (t p)) f x dx = (2πi t)⁻¹ ∫ 𝐞 (-θ x (t p)) (∑ D_{b_i} (f w_i)) x dx`.

The new amplitude is again supported in the support of `φ`, so this can be iterated. All amplitudes
produced depend jointly smoothly on the unit parameter `p` and on `x`; on the compact set of unit
parameters admitted by the hypothesis, times the support of `φ`, they are bounded, and so the
constants are uniform without tracking any derivative bounds. To keep the coefficients smooth
everywhere, `1 / q` is replaced by a smooth function equal to `1 / q` where `q` is at least its
minimum over that compact set.

## Main declarations

* `TauCeti.exists_one_add_norm_pow_mul_norm_integral_le`: rapid decay of the oscillatory integral
  `∫ 𝐞 (-θ x p) φ x dx` for parameters `p` at which the phase is uniformly non-stationary on the
  support of `φ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §2.
-/

public section

noncomputable section

open MeasureTheory Set Filter Complex Real
open scoped Topology ContDiff FourierTransform

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

namespace NonstationaryPhase

/-- A smooth function equal to `t⁻¹` for `t ≥ δ` and to `0` for `t ≤ δ / 2`. -/
private def recip (δ t : ℝ) : ℝ := smoothTransition (2 * t / δ - 1) * t⁻¹

private theorem contDiff_recip {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (recip δ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t (δ / 2) with ht | ht
  · -- Below `δ / 2` the function vanishes identically.
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [recip, smoothTransition.zero_of_nonpos, zero_mul]
    rw [mem_Iio] at hs
    rw [sub_nonpos, div_le_one hδ]
    linarith
  · have ht0 : t ≠ 0 := (show 0 < t by linarith).ne'
    exact ((smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).div_const δ |>.sub contDiff_const)).contDiffAt).mul
        (contDiffAt_inv ℝ ht0)

private theorem mul_recip {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) : t * recip δ t = 1 := by
  have ht0 : t ≠ 0 := (hδ.trans_le ht).ne'
  rw [recip, smoothTransition.one_of_one_le, one_mul, mul_inv_cancel₀ ht0]
  rw [le_sub_iff_add_le, le_div_iff₀ hδ]
  linarith

variable {θ : E → V →L[ℝ] ℝ}

/-- The derivative of the phase `y ↦ θ y p` is the flip of the derivative of `θ`, applied to
`p`. -/
private theorem fderiv_apply_eq_flip (hθ : Differentiable ℝ θ) (p : V) (x : E) :
    fderiv ℝ (fun y ↦ θ y p) x = (fderiv ℝ θ x).flip p := by
  refine ((hθ x).hasFDerivAt.clm_apply (hasFDerivAt_const p x)).fderiv.trans ?_
  ext v
  simp

variable {ι : Type*} [Fintype ι] (θ) (b : ι → E) (δ : ℝ)

/-- The derivative of the phase `θ · p` in the direction `b i`. -/
private def grad (i : ι) (p : V) (x : E) : ℝ := fderiv ℝ θ x (b i) p

/-- The sum of the squares of the directional derivatives of the phase. -/
private def sq (p : V) (x : E) : ℝ := ∑ i, grad θ b i p x ^ 2

/-- The coefficients `grad i / sq` of the vector field along which the phase grows at unit
speed, made smooth by `recip`. -/
private def field (i : ι) (p : V) (x : E) : ℝ := grad θ b i p x * recip δ (sq θ b p x)

/-- The transpose of the derivative along that vector field. -/
private def op (p : V) (f : E → ℂ) (x : E) : ℂ :=
  ∑ i, fderiv ℝ (fun y ↦ f y * (field θ b δ i p y : ℂ)) x (b i)

variable {θ b δ}

omit [Fintype ι] in
private theorem contDiff_grad (hθ : ContDiff ℝ ∞ θ) (i : ι) :
    ContDiff ℝ ∞ fun z : V × E ↦ grad θ b i z.1 z.2 :=
  (((hθ.fderiv_right (m := ∞) le_rfl).comp contDiff_snd).clm_apply contDiff_const).clm_apply
    contDiff_fst

private theorem contDiff_field (hθ : ContDiff ℝ ∞ θ) (hδ : 0 < δ) (i : ι) :
    ContDiff ℝ ∞ fun z : V × E ↦ field θ b δ i z.1 z.2 :=
  (contDiff_grad hθ i).mul ((contDiff_recip hδ).comp
    (ContDiff.sum fun j _ ↦ (contDiff_grad hθ j).pow 2))

/-- The iterated transposes of an amplitude depend jointly smoothly on the parameter and the
point. -/
private theorem contDiff_iterate_op (hθ : ContDiff ℝ ∞ θ) (hδ : 0 < δ) {φ : E → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    ContDiff ℝ ∞ fun z : V × E ↦ (op θ b δ z.1)^[k] φ z.2 := by
  induction k with
  | zero => exact hφ.comp contDiff_snd
  | succ k ih =>
    simp only [Function.iterate_succ_apply', op]
    refine ContDiff.sum fun i _ ↦ ?_
    refine ContDiff.fderiv_apply (f := fun (z : V × E) (y : E) ↦
      (op θ b δ z.1)^[k] φ y * (field θ b δ i z.1 y : ℂ)) (g := Prod.snd) (k := fun _ ↦ b i)
      ?_ contDiff_snd contDiff_const le_rfl
    exact (ih.comp (contDiff_fst.fst.prodMk contDiff_snd)).mul (ofRealCLM.contDiff.comp
      ((contDiff_field hθ hδ i).comp (contDiff_fst.fst.prodMk contDiff_snd)))

/-- The iterated transposes of a smooth amplitude are smooth. -/
private theorem contDiff_iterate_op_apply (hθ : ContDiff ℝ ∞ θ) (hδ : 0 < δ) {φ : E → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (p : V) (k : ℕ) : ContDiff ℝ ∞ ((op θ b δ p)^[k] φ) := by
  induction k with
  | zero => exact hφ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ContDiff.sum fun i _ ↦ ?_
    have hw : ContDiff ℝ ∞ fun y ↦ (field θ b δ i p y : ℂ) :=
      ofRealCLM.contDiff.comp ((contDiff_field hθ hδ i).comp (contDiff_const.prodMk contDiff_id))
    exact ((ih.mul hw).fderiv_right le_rfl).clm_apply contDiff_const

/-- The iterated transposes of an amplitude are supported in the support of the amplitude. -/
private theorem support_iterate_op_subset (φ : E → ℂ) (p : V) (k : ℕ) :
    Function.support ((op θ b δ p)^[k] φ) ⊆ tsupport φ := by
  induction k with
  | zero => exact subset_tsupport φ
  | succ k ih =>
    intro x hx
    by_contra hxs
    refine hx ?_
    -- Near `x` the previous amplitude vanishes, so each summand has zero derivative at `x`.
    have h0 : ((op θ b δ p)^[k] φ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
      exact Function.notMem_support.1 fun h ↦ hy (ih h)
    rw [Function.iterate_succ_apply', op]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have h1 : (fun y ↦ (op θ b δ p)^[k] φ y * (field θ b δ i p y : ℂ)) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [h0] with y hy
      simp [hy]
    rw [h1.fderiv_eq]
    simp

omit [Fintype ι] in
/-- The directional derivatives of the oscillating factor `𝐞 (-θ x (t • p))`. -/
private theorem fderiv_fourierChar_apply (hθ : ContDiff ℝ ∞ θ) (t : ℝ) (p : V) (x : E) (i : ι) :
    fderiv ℝ (fun y ↦ (𝐞 (-θ y (t • p)) : ℂ)) x (b i) =
      -(2 * π * I * t) * grad θ b i p x * 𝐞 (-θ x (t • p)) := by
  have hd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have h1 : HasFDerivAt (fun y ↦ θ y (t • p)) ((fderiv ℝ θ x).flip (t • p)) x := by
    convert (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const (t • p) x) using 1
    ext v
    simp
  have h : HasFDerivAt (fun y ↦ (𝐞 (-θ y (t • p)) : ℂ))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (2 * π * I * 𝐞 (-θ x (t • p)))).comp
        (-(fderiv ℝ θ x).flip (t • p))) x :=
    (Real.hasDerivAt_fourierChar _).hasFDerivAt.comp x h1.neg
  rw [h.fderiv]
  simp [grad]
  ring

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

omit [Fintype ι] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The oscillating factor `𝐞 (-θ y p)` is smooth in `y`. -/
private theorem contDiff_fourierChar_neg_apply (hθ : ContDiff ℝ ∞ θ) (p : V) :
    ContDiff ℝ ∞ fun y ↦ (𝐞 (-θ y p) : ℂ) := by
  have h : (fun y ↦ (𝐞 (-θ y p) : ℂ)) = fun y ↦ cexp (((2 * π * -θ y p : ℝ) : ℂ) * I) := by
    ext y
    simp [Real.fourierChar_apply]
  rw [h]
  exact Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp (contDiff_const.mul
    (hθ.clm_apply contDiff_const).neg)).mul contDiff_const)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Where `sq θ b p ≥ δ`, the derivative of `𝐞 (-θ · (t p))` along the field `∑ w_i b_i` is
`-2πi t` times the factor itself, so `𝐞 (-θ x (t p)) f x` is `(-2πi t)⁻¹ ∑ f w_i D_{b_i} 𝐞`. -/
private theorem fourierChar_mul_eq_sum (hθ : ContDiff ℝ ∞ θ) (hδ : 0 < δ) {f : E → ℂ} {p : V}
    {x : E} (hq : f x ≠ 0 → δ ≤ sq θ b p x) {t : ℝ} (ht : t ≠ 0) :
    (𝐞 (-θ x (t • p)) : ℂ) * f x = (-(2 * π * I * t))⁻¹ * ∑ i, f x * (field θ b δ i p x : ℂ) *
      fderiv ℝ (fun y ↦ (𝐞 (-θ y (t • p)) : ℂ)) x (b i) := by
  by_cases hx : f x = 0
  · simp [hx]
  have hc : (2 * π * I * t : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero, ht]
  have hsum : ∑ i, (field θ b δ i p x : ℂ) * grad θ b i p x = 1 := by
    have h : ∑ i, field θ b δ i p x * grad θ b i p x = sq θ b p x * recip δ (sq θ b p x) := by
      rw [Finset.sum_congr rfl (g := fun i ↦ grad θ b i p x ^ 2 * recip δ (sq θ b p x))
        fun i _ ↦ by rw [field]; ring, ← Finset.sum_mul, sq]
    exact_mod_cast h.trans (mul_recip hδ (hq hx))
  have h : ∑ i, f x * (field θ b δ i p x : ℂ) *
      (-(2 * π * I * t) * grad θ b i p x * 𝐞 (-θ x (t • p))) =
        -(2 * π * I * t) * (𝐞 (-θ x (t • p)) * f x) *
          ∑ i, (field θ b δ i p x : ℂ) * grad θ b i p x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp only [fderiv_fourierChar_apply hθ]
  rw [h, hsum, mul_one, inv_mul_cancel_left₀ (neg_ne_zero.2 hc)]

/-- **One integration by parts.** If `f` is smooth and supported where `sq θ b p ≥ δ`, then
`∫ 𝐞 (-θ x (t p)) f x = (2πi t)⁻¹ ∫ 𝐞 (-θ x (t p)) (op p f) x`. -/
private theorem integral_eq_mul_integral_op (hθ : ContDiff ℝ ∞ θ) (hδ : 0 < δ) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {p : V}
    (hq : ∀ x ∈ Function.support f, δ ≤ sq θ b p x) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, 𝐞 (-θ x (t • p)) • f x ∂μ =
      (2 * π * I * t)⁻¹ * ∫ x, 𝐞 (-θ x (t • p)) • op θ b δ p f x ∂μ := by
  set e : E → ℂ := fun y ↦ (𝐞 (-θ y (t • p)) : ℂ)
  have he : ContDiff ℝ ∞ e := contDiff_fourierChar_neg_apply hθ (t • p)
  -- The amplitudes `f w_i`.
  set u : ι → E → ℂ := fun i y ↦ f y * (field θ b δ i p y : ℂ)
  have hu (i : ι) : ContDiff ℝ ∞ (u i) :=
    hf.mul (ofRealCLM.contDiff.comp ((contDiff_field hθ hδ i).comp
      (contDiff_const.prodMk contDiff_id)))
  have hint (i : ι) : Integrable (fun x ↦ u i x * fderiv ℝ e x (b i)) μ :=
    ((hu i).continuous.mul ((he.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport hfc.mul_right.mul_right
  have hint' (i : ι) : Integrable (fun x ↦ fderiv ℝ (u i) x (b i) * e x) μ :=
    (((hu i).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
      he.continuous).integrable_of_hasCompactSupport
        (hfc.mul_right.fderiv_apply (𝕜 := ℝ) (b i)).mul_right
  have hop : ∫ x, 𝐞 (-θ x (t • p)) • op θ b δ p f x ∂μ =
      ∫ x, ∑ i, fderiv ℝ (u i) x (b i) * e x ∂μ := by
    simp [e, Circle.smul_def, op, u, Finset.sum_mul, mul_comm]
  -- Pointwise `𝐞 f = (-2πi t)⁻¹ ∑ (f w_i) D_{b_i} 𝐞`; integrate and move each derivative onto
  -- the amplitude.
  calc ∫ x, 𝐞 (-θ x (t • p)) • f x ∂μ
      = (-(2 * π * I * t))⁻¹ * ∑ i, ∫ x, u i x * fderiv ℝ e x (b i) ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint i, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [Circle.smul_def, smul_eq_mul]
        exact fourierChar_mul_eq_sum hθ hδ (fun hx ↦ hq x hx) ht
    _ = (2 * π * I * t)⁻¹ * ∫ x, 𝐞 (-θ x (t • p)) • op θ b δ p f x ∂μ := by
        rw [Finset.sum_congr rfl fun i _ ↦
          integral_mul_fderiv_eq_neg_fderiv_mul_of_hasCompactSupport
            ((hu i).of_le (by simp)) hfc.mul_right (he.of_le (by simp)) (b i),
          Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ ↦ hint' i, hop, inv_neg,
          neg_mul_neg]
/-- **Iterated integration by parts.** If `sq θ b p ≥ δ` on the support of `φ`, then
`∫ 𝐞 (-θ x (t p)) φ x = (2πi t)⁻ᵏ ∫ 𝐞 (-θ x (t p)) (op p)ᵏ φ x`. -/
private theorem integral_eq_pow_mul_integral_iterate_op (hθ : ContDiff ℝ ∞ θ) (hδ : 0 < δ)
    {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {p : V}
    (hq : ∀ x ∈ tsupport φ, δ ≤ sq θ b p x) {t : ℝ} (ht : t ≠ 0) (k : ℕ) :
    ∫ x, 𝐞 (-θ x (t • p)) • φ x ∂μ =
      ((2 * π * I * t)⁻¹) ^ k * ∫ x, 𝐞 (-θ x (t • p)) • (op θ b δ p)^[k] φ x ∂μ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := integral_eq_mul_integral_op (μ := μ) (b := b) (p := p)
      (f := (op θ b δ p)^[k] φ) hθ hδ (contDiff_iterate_op_apply hθ hδ hφ p k)
      (hφc.mono' (support_iterate_op_subset φ p k))
      (fun x hx ↦ hq x (support_iterate_op_subset φ p k hx)) ht
    rw [ih, h, Function.iterate_succ_apply', pow_succ]
    ring

/-- **The estimate for large parameters.** If `sq θ b p ≥ δ` on the support of `φ` and the `N`-th
transposed amplitude at `p` is bounded by `M` there, then for `t ≥ 1`,
`(1 + t) ^ N ‖∫ 𝐞 (-θ x (t p)) φ x‖ ≤ max M 0 μ(supp φ)`. -/
private theorem one_add_pow_mul_norm_integral_le (hθ : ContDiff ℝ ∞ θ) (hδ : 0 < δ) {φ : E → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {p : V}
    (hq : ∀ x ∈ tsupport φ, δ ≤ sq θ b p x) {N : ℕ} {M : ℝ}
    (hM : ∀ x ∈ tsupport φ, ‖(op θ b δ p)^[N] φ x‖ ≤ M) {t : ℝ} (ht : 1 ≤ t) :
    (1 + t) ^ N * ‖∫ x, 𝐞 (-θ x (t • p)) • φ x ∂μ‖ ≤ max M 0 * μ.real (tsupport φ) := by
  have ht0 : 0 < t := one_pos.trans_le ht
  set B := max M 0 * μ.real (tsupport φ)
  have hbound : ‖∫ x, 𝐞 (-θ x (t • p)) • (op θ b δ p)^[N] φ x ∂μ‖ ≤ B := by
    have hzero : ∀ x ∉ tsupport φ, 𝐞 (-θ x (t • p)) • (op θ b δ p)^[N] φ x = 0 := fun x hx ↦ by
      rw [Function.notMem_support.1 fun h ↦ hx (support_iterate_op_subset φ p N h), smul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    refine norm_setIntegral_le_of_norm_le_const hφc.measure_lt_top fun x hx ↦ ?_
    rw [Circle.norm_smul]
    exact (hM x hx).trans (le_max_left _ _)
  rw [integral_eq_pow_mul_integral_iterate_op hθ hδ hφ hφc hq ht0.ne' N, norm_mul, norm_pow,
    norm_inv]
  have hc' : ‖(2 * π * I * t : ℂ)‖ = 2 * π * t := by
    simp [abs_of_pos Real.pi_pos, abs_of_pos ht0]
  rw [hc']
  calc (1 + t) ^ N * ((2 * π * t)⁻¹ ^ N * ‖∫ x, 𝐞 (-θ x (t • p)) • (op θ b δ p)^[N] φ x ∂μ‖)
      ≤ (2 * t) ^ N * ((2 * π * t)⁻¹ ^ N * B) := by
        gcongr
        linarith
    _ = π⁻¹ ^ N * B := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        field_simp
    _ ≤ 1 ^ N * B := by
        gcongr
        exact inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
    _ = B := by simp

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- On a compact set of parameters `P` at which the phase is non-stationary on a compact set `K`,
the squared gradient `sq θ b` has a positive lower bound. -/
private theorem exists_pos_forall_le_sq (hθ : ContDiff ℝ ∞ θ) (B : Module.Basis ι ℝ E)
    {P : Set V} (hP : IsCompact P) {K : Set E} (hK : IsCompact K)
    (hPK : ∀ p ∈ P, ∀ x ∈ K, (fderiv ℝ θ x).flip p ≠ 0) :
    ∃ δ > 0, ∀ p ∈ P, ∀ x ∈ K, δ ≤ sq θ B p x := by
  have hsqpos : ∀ z ∈ P ×ˢ K, 0 < sq θ B z.1 z.2 := by
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) fun h0 ↦ hPK p hp x hx ?_
    refine ContinuousLinearMap.coe_injective (B.ext fun i ↦ ?_)
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg (grad θ B i p x)).1
      h0.symm i (Finset.mem_univ i)
    simpa [grad] using pow_eq_zero_iff (two_ne_zero) |>.1 h
  have hsqc : Continuous fun z : V × E ↦ sq θ B z.1 z.2 :=
    (ContDiff.sum fun i _ ↦ (contDiff_grad (b := ⇑B) hθ i).pow 2).continuous
  rcases (P ×ˢ K).eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun p hp x hx ↦ ?_⟩
    have hpx : (p, x) ∈ P ×ˢ K := Set.mk_mem_prod hp hx
    rw [h] at hpx
    exact absurd hpx (Set.notMem_empty _)
  obtain ⟨z₀, hz₀, hmin⟩ := (hP.prod hK).exists_isMinOn h hsqc.continuousOn
  exact ⟨_, hsqpos z₀ hz₀, fun p hp x hx ↦ isMinOn_iff.1 hmin (p, x) (Set.mk_mem_prod hp hx)⟩

end NonstationaryPhase

open NonstationaryPhase

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]

/-- **Non-stationary phase, uniformly in a parameter.** Let `φ` be smooth with compact support
and `θ x : V →L[ℝ] ℝ` depend smoothly on `x`. If for `p ∈ S` the phase `x ↦ θ x p` satisfies
`c ‖p‖ ≤ ‖D_x (θ x p)‖` on the support of `φ`, then `∫ 𝐞 (-θ x p) φ x dx` decays faster than
every power of `‖p‖` on `S`: for every `N` there is `C` with

`(1 + ‖p‖) ^ N ‖∫ 𝐞 (-θ x p) φ x dx‖ ≤ C` for all `p ∈ S`. -/
theorem exists_one_add_norm_pow_mul_norm_integral_le {θ : E → V →L[ℝ] ℝ}
    (hθ : ContDiff ℝ ∞ θ) {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set V} {c : ℝ} (hc : 0 < c)
    (hS : ∀ p ∈ S, ∀ x ∈ tsupport φ, c * ‖p‖ ≤ ‖fderiv ℝ (fun y ↦ θ y p) x‖) (N : ℕ) :
    ∃ C, ∀ p ∈ S, (1 + ‖p‖) ^ N * ‖∫ x, 𝐞 (-θ x p) • φ x ∂μ‖ ≤ C := by
  have hd : Differentiable ℝ θ := hθ.differentiable (by simp)
  set K := tsupport φ
  have hK : IsCompact K := hφc
  let b := Module.finBasis ℝ E
  -- The compact set `P` of unit parameters at which the phase is non-stationary on `K`.
  set P : Set V := {p | ‖p‖ = 1} ∩ ⋂ x ∈ K, {p | c ≤ ‖(fderiv ℝ θ x).flip p‖}
  have hP : IsCompact P := by
    refine (isCompact_sphere (0 : V) 1).of_isClosed_subset ?_ fun p hp ↦ by simpa using hp.1
    exact (isClosed_eq continuous_norm continuous_const).inter (isClosed_biInter fun x _ ↦
      isClosed_le continuous_const (continuous_norm.comp (fderiv ℝ θ x).flip.continuous))
  -- On `P × K` the squared gradient `sq θ b` has a positive lower bound `δ`.
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_forall_le_sq hθ b hP hK fun p hp x hx h0 ↦ by
    have := mem_iInter₂.1 hp.2 x hx
    rw [mem_ofPred_eq, h0, norm_zero] at this
    linarith
  -- The `N`-th transposed amplitude is bounded on `P × K`.
  obtain ⟨M, hM⟩ := (hP.prod hK).exists_bound_of_continuousOn
    (contDiff_iterate_op (b := ⇑b) hθ hδ hφ N).continuous.continuousOn
  refine ⟨max (2 ^ N * ∫ x, ‖φ x‖ ∂μ) (max M 0 * μ.real K), fun p hp ↦ ?_⟩
  have hnorm : ‖∫ x, 𝐞 (-θ x p) • φ x ∂μ‖ ≤ ∫ x, ‖φ x‖ ∂μ :=
    (norm_integral_le_integral_norm _).trans_eq (by simp)
  rcases lt_or_ge ‖p‖ 1 with hp1 | hp1
  · -- Small parameters: the trivial bound.
    refine le_max_of_le_left (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) N)
      hnorm (norm_nonneg _) (by positivity))
  refine le_max_of_le_right ?_
  -- Large parameters: write `p = t • p₁` with `t = ‖p‖` and `p₁ ∈ P`, and integrate by parts.
  have hp0 : ‖p‖ ≠ 0 := (one_pos.trans_le hp1).ne'
  obtain ⟨t, p₁, ht1, hn, rfl⟩ : ∃ t : ℝ, ∃ p₁ : V, 1 ≤ t ∧ ‖p₁‖ = 1 ∧ p = t • p₁ :=
    ⟨‖p‖, ‖p‖⁻¹ • p, hp1, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp0],
      by rw [smul_smul, mul_inv_cancel₀ hp0, one_smul]⟩
  have ht : 0 < t := one_pos.trans_le ht1
  have htn : ‖t • p₁‖ = t := by rw [norm_smul, hn, mul_one, Real.norm_of_nonneg ht.le]
  rw [htn]
  have hp₁ : p₁ ∈ P := by
    refine ⟨hn, mem_iInter₂.2 fun x hx ↦ ?_⟩
    have h := hS _ hp x hx
    rw [htn, fderiv_apply_eq_flip hd, map_smul, norm_smul, Real.norm_of_nonneg ht.le] at h
    exact (mul_le_mul_iff_of_pos_left ht).1 (by linarith)
  exact one_add_pow_mul_norm_integral_le hθ hδ hφ hφc (fun x hx ↦ hδle p₁ hp₁ x hx)
    (fun x hx ↦ hM (p₁, x) ⟨hp₁, hx⟩) ht1

end TauCeti
