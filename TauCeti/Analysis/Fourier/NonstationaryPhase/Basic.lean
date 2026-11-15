/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Non-stationary phase

Let `a` be a smooth compactly supported function on a finite-dimensional real inner product space
`E`, and `Φ : E → F` a smooth map into a finite-dimensional real normed space. For a covector
`Λ : F →L[ℝ] ℝ` consider the oscillatory integral

`∫ 𝐞 (-Λ (Φ x)) a x dx`,

whose phase `x ↦ Λ (Φ x)` has differential `Λ ∘ DΦ(x)`. If this differential is bounded below by a
fixed multiple of `‖Λ‖` on the support of `a`, that is, if the phase has no stationary point there
uniformly in the direction of `Λ`, then the integral decays faster than every power of `‖Λ‖`:

`(1 + ‖Λ‖) ^ N ‖∫ 𝐞 (-Λ (Φ x)) a x dx‖ ≤ C_N` whenever `c ‖Λ‖ ≤ ‖Λ ∘ DΦ(x)‖` on `supp a`

(`TauCeti.exists_one_add_norm_pow_mul_norm_integral_fourierChar_le`). For linear `Φ` the integral
is a Fourier transform of `a`; for `Φ x = (x, f x)` and `Λ (z, w) = ⟪z, ζ⟫ + ⟪w, η⟫` it is the
oscillatory integral `∫ 𝐞 (-(⟪x, ζ⟫ + ⟪f x, η⟫)) a x dx` that controls the localized Fourier
transforms of a pushforward along a smooth map `f`.

## Proof

Write `Λ = ‖Λ‖ θ` with `‖θ‖ = 1`. The vector field `v = ∇ψ / ‖∇ψ‖²`, for the phase
`ψ x = θ (Φ x)`, satisfies `Dψ(x) (v x) = 1`, so `𝐞 (-Λ (Φ x))` is `(-2πi‖Λ‖)⁻¹` times its
derivative along `v`. Integrating by parts along `v` gives

`∫ 𝐞 (-Λ (Φ x)) a x dx = (2πi‖Λ‖)⁻¹ ∫ 𝐞 (-Λ (Φ x)) (L_θ a) x dx`,

with `L_θ a = div (a v)`, and `N` integrations by parts gain `‖Λ‖ ^ (-N)`. The amplitudes
`L_θ^N a` depend smoothly on `θ` and `x` jointly, so they are bounded uniformly for `θ` in the
compact set of unit covectors with `c ≤ ‖θ ∘ DΦ(x)‖` on `supp a`. To keep everything smooth on
all of `E`, the factor `‖∇ψ‖⁻²` is replaced by a smooth function that agrees with it where
`‖∇ψ‖ ≥ c`.

## Main results

* `TauCeti.exists_one_add_norm_pow_mul_norm_integral_fourierChar_le`: decay of order `N` of the
  oscillatory integral with phase `Λ ∘ Φ`, uniformly over the covectors `Λ` whose phase is
  uniformly non-stationary on the support of the amplitude.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §2, Proposition 4.
-/

public section

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff FourierTransform RealInnerProductSpace

namespace TauCeti

namespace NonstationaryPhaseAux

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth function equal to `t` for `t ≥ 2 δ` and bounded below by `δ`. -/
private def floorFn (δ t : ℝ) : ℝ :=
  δ + (t - δ) * Real.smoothTransition ((t - δ) / δ)

private theorem contDiff_floorFn (δ : ℝ) : ContDiff ℝ ∞ (floorFn δ) := by
  unfold floorFn
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)))

private theorem le_floorFn {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : δ ≤ floorFn δ t := by
  unfold floorFn
  rcases le_or_gt t δ with ht | ht
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      hδ.le)]
    simp
  · have := Real.smoothTransition.nonneg ((t - δ) / δ)
    nlinarith

private theorem floorFn_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) : floorFn δ t = t := by
  unfold floorFn
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith))]
  ring

/-- The differential `θ ∘ DΦ(x)` of the phase `x ↦ θ (Φ x)`, as a function of `p = (θ, x)`. -/
private def dphase (Φ : E → F) (p : (F →L[ℝ] ℝ) × E) : E →L[ℝ] ℝ :=
  p.1.comp (fderiv ℝ Φ p.2)

/-- The oscillating factor `𝐞 (-Λ (Φ y))`. -/
private def osc (Φ : E → F) (Λ : F →L[ℝ] ℝ) (y : E) : ℂ :=
  𝐞 (-Λ (Φ y))

private theorem hasFDerivAt_osc {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) (Λ : F →L[ℝ] ℝ) (y : E) :
    HasFDerivAt (osc Φ Λ)
      ((-2 * Real.pi * I * osc Φ Λ y) • (ofRealCLM ∘L (Λ ∘L fderiv ℝ Φ y))) y := by
  have hΦy : HasFDerivAt Φ (fderiv ℝ Φ y) y :=
    (hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have ha : HasFDerivAt (fun y ↦ Λ (Φ y)) (Λ ∘L fderiv ℝ Φ y) y :=
    Λ.hasFDerivAt.comp y hΦy
  convert! (Real.hasDerivAt_fourierChar (-Λ (Φ y))).hasFDerivAt.comp y ha.neg using 1
  ext u
  simp [osc]
  ring

private theorem continuous_osc {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) (Λ : F →L[ℝ] ℝ) :
    Continuous (osc Φ Λ) :=
  continuous_iff_continuousAt.2 fun y ↦ (hasFDerivAt_osc hΦ Λ y).continuousAt

private theorem contDiff_dphase {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (dphase Φ) :=
  contDiff_fst.clm_comp ((hΦ.fderiv_right (m := ∞) (by simp)).comp contDiff_snd)

variable [FiniteDimensional ℝ E]

/-- The gradient of the phase `x ↦ θ (Φ x)`, as a function of `p = (θ, x)`. -/
private def grad (Φ : E → F) (p : (F →L[ℝ] ℝ) × E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (dphase Φ p)

/-- The vector field `∇ψ / ‖∇ψ‖²` along which the phase `ψ` has derivative one, with `‖∇ψ‖²`
replaced by a smooth function bounded below by `δ` and equal to it where `‖∇ψ‖² ≥ 2 δ`. -/
private def field (Φ : E → F) (δ : ℝ) (p : (F →L[ℝ] ℝ) × E) : E :=
  (floorFn δ (‖grad Φ p‖ ^ 2))⁻¹ • grad Φ p

private theorem norm_grad (Φ : E → F) (p : (F →L[ℝ] ℝ) × E) : ‖grad Φ p‖ = ‖dphase Φ p‖ := by
  simp [grad]

private theorem contDiff_grad {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (grad Φ) :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp (contDiff_dphase hΦ)

private theorem contDiff_field {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (field Φ δ) := by
  have hg := contDiff_grad hΦ
  refine ContDiff.smul ?_ hg
  exact ((contDiff_floorFn δ).comp (hg.norm_sq ℝ)).inv fun p ↦
    (hδ.trans_le (le_floorFn hδ _)).ne'

/-- Where `‖∇ψ‖² ≥ 2 δ`, the phase has derivative one along the vector field. -/
private theorem dphase_field {Φ : E → F} {δ : ℝ} (hδ : 0 < δ) {p : (F →L[ℝ] ℝ) × E}
    (hp : 2 * δ ≤ ‖dphase Φ p‖ ^ 2) : dphase Φ p (field Φ δ p) = 1 := by
  have hpos : 0 < ‖dphase Φ p‖ ^ 2 := by linarith
  rw [field, norm_grad, floorFn_of_le hδ hp, map_smul, smul_eq_mul, grad,
    ← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq, ← grad, norm_grad]
  exact inv_mul_cancel₀ hpos.ne'

/-- The orthonormal basis of `E` used to write the divergence. -/
private abbrev obasis (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] := stdOrthonormalBasis ℝ E

/-- The transpose `A ↦ div (A v)` of the derivative along the vector field `v`, acting on
amplitudes `A (θ, x)` in the variable `x`. -/
private def lop (Φ : E → F) (δ : ℝ) (A : (F →L[ℝ] ℝ) × E → ℂ) (p : (F →L[ℝ] ℝ) × E) : ℂ :=
  ∑ i, fderiv ℝ (fun y ↦ ((⟪obasis E i, field Φ δ (p.1, y)⟫ : ℝ) : ℂ) * A (p.1, y)) p.2
    (obasis E i)

private theorem contDiff_lop {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) {δ : ℝ} (hδ : 0 < δ)
    {A : (F →L[ℝ] ℝ) × E → ℂ} (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (lop Φ δ A) := by
  unfold lop
  refine ContDiff.sum fun i _ ↦ ContDiff.fderiv_apply (m := ∞) ?_ contDiff_snd contDiff_const
    (by simp)
  have h1 : ContDiff ℝ ∞ fun q : ((F →L[ℝ] ℝ) × E) × E ↦ (q.1.1, q.2) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  exact (ofRealCLM.contDiff.comp (contDiff_const.inner ℝ ((contDiff_field hΦ hδ).comp h1))).mul
    (hA.comp h1)

/-- `lop` does not enlarge the support in the variable `x`. -/
private theorem lop_eq_zero {Φ : E → F} {δ : ℝ} {A : (F →L[ℝ] ℝ) × E → ℂ} {K : Set E}
    (hK : IsClosed K) (hA : ∀ p : (F →L[ℝ] ℝ) × E, p.2 ∉ K → A p = 0) {p : (F →L[ℝ] ℝ) × E}
    (hp : p.2 ∉ K) : lop Φ δ A p = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h : (fun y ↦ ((⟪obasis E i, field Φ δ (p.1, y)⟫ : ℝ) : ℂ) * A (p.1, y)) =ᶠ[𝓝 p.2]
      fun _ ↦ 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hp] with y hy
    simp [hA (p.1, y) hy]
  simp [h.fderiv_eq]

private theorem contDiff_iterate_lop {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) {δ : ℝ} (hδ : 0 < δ)
    {A : (F →L[ℝ] ℝ) × E → ℂ} (hA : ContDiff ℝ ∞ A) (k : ℕ) :
    ContDiff ℝ ∞ ((lop Φ δ)^[k] A) := by
  induction k with
  | zero => exact hA
  | succ k ih => rw [Function.iterate_succ_apply']; exact contDiff_lop hΦ hδ ih

private theorem iterate_lop_eq_zero {Φ : E → F} {δ : ℝ} {A : (F →L[ℝ] ℝ) × E → ℂ} {K : Set E}
    (hK : IsClosed K) (hA : ∀ p : (F →L[ℝ] ℝ) × E, p.2 ∉ K → A p = 0) (k : ℕ)
    {p : (F →L[ℝ] ℝ) × E} (hp : p.2 ∉ K) : (lop Φ δ)^[k] A p = 0 := by
  induction k generalizing p with
  | zero => exact hA p hp
  | succ k ih => rw [Function.iterate_succ_apply']; exact lop_eq_zero hK (fun q hq ↦ ih hq) hp

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the oscillating factor, in terms of the differential of the phase
`θ ∘ Φ` for `θ = Λ / ‖Λ‖`. -/
private theorem fderiv_osc_apply {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) {Λ : F →L[ℝ] ℝ} (hΛ : Λ ≠ 0)
    (y u : E) : fderiv ℝ (osc Φ Λ) y u =
      -2 * Real.pi * I * ‖Λ‖ * dphase Φ (‖Λ‖⁻¹ • Λ, y) u * osc Φ Λ y := by
  have h : ((‖Λ‖ : ℝ) : ℂ) * ((dphase Φ (‖Λ‖⁻¹ • Λ, y) u : ℝ) : ℂ) =
      ((Λ (fderiv ℝ Φ y u) : ℝ) : ℂ) := by
    rw [← ofReal_mul]
    congr 1
    simp [dphase, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hΛ)]
  rw [(hasFDerivAt_osc hΦ Λ y).fderiv, mul_assoc (-2 * (Real.pi : ℂ) * I), h]
  simp
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_fderiv_osc_apply {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) (Λ : F →L[ℝ] ℝ)
    (u : E) : Continuous fun y ↦ fderiv ℝ (osc Φ Λ) y u := by
  simp_rw [(hasFDerivAt_osc hΦ Λ _).fderiv]
  exact ((continuous_const.mul (continuous_osc hΦ Λ)).smul (continuous_const.clm_comp
    (continuous_const.clm_comp (hΦ.continuous_fderiv (by simp))))).clm_apply continuous_const

omit [MeasurableSpace E] [BorelSpace E] in
/-- The coefficients of the vector field in the orthonormal basis, paired with the differential of
the phase, sum to one where the phase has derivative one along the field. -/
private theorem sum_inner_mul_dphase {Φ : E → F} {δ : ℝ} {p : (F →L[ℝ] ℝ) × E}
    (hp : dphase Φ p (field Φ δ p) = 1) :
    ∑ i, ((⟪obasis E i, field Φ δ p⟫ : ℝ) : ℂ) * (dphase Φ p (obasis E i) : ℂ) = 1 := by
  have h : ∑ i, (⟪obasis E i, field Φ δ p⟫ : ℝ) * dphase Φ p (obasis E i) = 1 := by
    rw [← hp]
    conv_rhs => rw [← (obasis E).sum_repr' (field Φ δ p)]
    simp [map_sum, map_smul]
  exact_mod_cast h

/-- Integration by parts against the oscillating factor, for a smooth amplitude vanishing outside
a compact set, with the integrability of both sides. -/
private theorem integral_mul_fderiv_osc {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) (Λ : F →L[ℝ] ℝ)
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K) (hfK : ∀ y ∉ K, f y = 0)
    (u : E) :
    Integrable (fun y ↦ f y * fderiv ℝ (osc Φ Λ) y u) μ ∧
      Integrable (fun y ↦ osc Φ Λ y * fderiv ℝ f y u) μ ∧
      ∫ y, f y * fderiv ℝ (osc Φ Λ) y u ∂μ = -∫ y, osc Φ Λ y * fderiv ℝ f y u ∂μ := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro hK hfK
  have hcf : Continuous fun y ↦ fderiv ℝ f y u :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun y ↦ f y * fderiv ℝ (osc Φ Λ) y u) μ :=
    (hf.continuous.mul (continuous_fderiv_osc_apply hΦ Λ u)).integrable_of_hasCompactSupport
      hfc.mul_right
  refine ⟨h1, ((continuous_osc hΦ Λ).mul hcf).integrable_of_hasCompactSupport
    (hfc.fderiv_apply (𝕜 := ℝ) u).mul_left, ?_⟩
  simp_rw [mul_comm (osc Φ Λ _)]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hcf.mul (continuous_osc hΦ Λ)).integrable_of_hasCompactSupport
      (hfc.fderiv_apply (𝕜 := ℝ) u).mul_right) h1
    ((hf.continuous.mul (continuous_osc hΦ Λ)).integrable_of_hasCompactSupport hfc.mul_right)
    (fun y _ ↦ hf.differentiable (by simp) y)
    (fun y _ ↦ (hasFDerivAt_osc hΦ Λ y).differentiableAt)

/-- **One integration by parts.** If the phase `θ ∘ Φ`, `θ = Λ / ‖Λ‖`, satisfies
`2 δ ≤ ‖∇(θ ∘ Φ)‖²` on a compact set `K` outside which the amplitude vanishes, then integrating by
parts along the vector field gains a factor `(2πi‖Λ‖)⁻¹`. -/
private theorem integral_osc_mul_eq {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) {δ : ℝ} (hδ : 0 < δ)
    {A : (F →L[ℝ] ℝ) × E → ℂ} (hA : ContDiff ℝ ∞ A) {K : Set E} (hK : IsCompact K)
    (hAK : ∀ p : (F →L[ℝ] ℝ) × E, p.2 ∉ K → A p = 0) {Λ : F →L[ℝ] ℝ} (hΛ : Λ ≠ 0)
    (hKΛ : ∀ y ∈ K, 2 * δ ≤ ‖dphase Φ (‖Λ‖⁻¹ • Λ, y)‖ ^ 2) :
    ∫ y, osc Φ Λ y * A (‖Λ‖⁻¹ • Λ, y) ∂μ =
      (2 * Real.pi * I * ‖Λ‖)⁻¹ * ∫ y, osc Φ Λ y * lop Φ δ A (‖Λ‖⁻¹ • Λ, y) ∂μ := by
  set θ := ‖Λ‖⁻¹ • Λ
  set b := obasis E
  have hc : (-2 * Real.pi * I * ‖Λ‖ : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero, norm_ne_zero_iff.2 hΛ]
  -- The pieces `f i y = ⟪b i, v (θ, y)⟫ A (θ, y)` of the amplitude times the vector field.
  set f : _ → E → ℂ := fun i y ↦ ((⟪b i, field Φ δ (θ, y)⟫ : ℝ) : ℂ) * A (θ, y)
  have hθy : ContDiff ℝ ∞ fun y : E ↦ (θ, y) := contDiff_const.prodMk contDiff_id
  have hf (i) : ContDiff ℝ ∞ (f i) :=
    (ofRealCLM.contDiff.comp ((contDiff_const.inner ℝ ((contDiff_field hΦ hδ).comp hθy)))).mul
      (hA.comp hθy)
  have hibp (i) := integral_mul_fderiv_osc (μ := μ) hΦ Λ (hf i) hK
    (fun y hy ↦ by simp [f, hAK (θ, y) hy]) (b i)
  -- Pointwise, `osc · A = (-2πi‖Λ‖)⁻¹ ∑ᵢ fᵢ ∂_{bᵢ} osc`, since `∑ᵢ ⟪bᵢ, v⟫ Dψ(bᵢ) = Dψ(v) = 1`.
  have hpt (y : E) : osc Φ Λ y * A (θ, y) =
      (-2 * Real.pi * I * ‖Λ‖)⁻¹ * ∑ i, f i y * fderiv ℝ (osc Φ Λ) y (b i) := by
    by_cases hy : y ∈ K
    · have h := sum_inner_mul_dphase (dphase_field hδ (hKΛ y hy))
      simp only [f, fderiv_osc_apply hΦ hΛ]
      rw [eq_inv_mul_iff_mul_eq₀ hc, ← mul_one (_ * (osc Φ Λ y * A (θ, y))), ← h,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    · simp [hAK (θ, y) hy, f]
  have hlop (y : E) : lop Φ δ A (θ, y) = ∑ i, fderiv ℝ (f i) y (b i) := rfl
  calc ∫ y, osc Φ Λ y * A (θ, y) ∂μ
      = (-2 * Real.pi * I * ‖Λ‖)⁻¹ * ∑ i, ∫ y, f i y * fderiv ℝ (osc Φ Λ) y (b i) ∂μ := by
        simp_rw [hpt]
        rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ (hibp i).1]
    _ = (2 * Real.pi * I * ‖Λ‖)⁻¹ * ∑ i, ∫ y, osc Φ Λ y * fderiv ℝ (f i) y (b i) ∂μ := by
        simp_rw [fun i ↦ (hibp i).2.2, Finset.sum_neg_distrib, mul_neg, ← neg_mul, ← inv_neg]
        ring_nf
    _ = _ := by
        congr 1
        simp_rw [hlop, Finset.mul_sum]
        rw [integral_finsetSum _ fun i _ ↦ (hibp i).2.1]

/-- **Iterated integration by parts**: `k` integrations by parts gain `(2πi‖Λ‖)⁻ᵏ`. -/
private theorem integral_osc_mul_eq_iterate {Φ : E → F} (hΦ : ContDiff ℝ ∞ Φ) {δ : ℝ}
    (hδ : 0 < δ) {A : (F →L[ℝ] ℝ) × E → ℂ} (hA : ContDiff ℝ ∞ A) {K : Set E} (hK : IsCompact K)
    (hAK : ∀ p : (F →L[ℝ] ℝ) × E, p.2 ∉ K → A p = 0) {Λ : F →L[ℝ] ℝ} (hΛ : Λ ≠ 0)
    (hKΛ : ∀ y ∈ K, 2 * δ ≤ ‖dphase Φ (‖Λ‖⁻¹ • Λ, y)‖ ^ 2) (k : ℕ) :
    ∫ y, osc Φ Λ y * A (‖Λ‖⁻¹ • Λ, y) ∂μ = (2 * Real.pi * I * ‖Λ‖)⁻¹ ^ k *
      ∫ y, osc Φ Λ y * (lop Φ δ)^[k] A (‖Λ‖⁻¹ • Λ, y) ∂μ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, integral_osc_mul_eq hΦ hδ (contDiff_iterate_lop hΦ hδ hA k) hK
      (fun p hp ↦ iterate_lop_eq_zero hK.isClosed hAK k hp) hΛ hKΛ, ← mul_assoc, ← pow_succ,
      Function.iterate_succ_apply']

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- After the integrations by parts, the integral is bounded by the size of the amplitude times
the measure of the compact set outside which it vanishes. -/
private theorem norm_integral_osc_mul_le {Φ : E → F} {Λ θ : F →L[ℝ] ℝ}
    {B : (F →L[ℝ] ℝ) × E → ℂ} {K : Set E} (hK : IsCompact K) (hBK : ∀ y ∉ K, B (θ, y) = 0)
    {M : ℝ} (hM : ∀ y ∈ K, ‖B (θ, y)‖ ≤ M) :
    ‖∫ y, osc Φ Λ y * B (θ, y) ∂μ‖ ≤ M * μ.real K := by
  have h := norm_integral_le_of_norm_le (μ := μ) (f := fun y ↦ osc Φ Λ y * B (θ, y))
    (g := K.indicator fun _ ↦ M)
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.isClosed.measurableSet)
    (Eventually.of_forall fun y ↦ ?_)
  · rwa [integral_indicator_const _ hK.isClosed.measurableSet, smul_eq_mul, mul_comm] at h
  · by_cases hy : y ∈ K
    · rw [indicator_of_mem hy, norm_mul, osc, Circle.norm_coe, one_mul]
      exact hM y hy
    · simp [indicator_of_notMem hy, hBK y hy]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The factor gained by `N` integrations by parts beats `(1 + t) ^ N` for `t ≥ 1`. -/
private theorem one_add_pow_mul_norm_inv_le {t X Y : ℝ} (ht : 1 ≤ t) (hX : 0 ≤ X) (hXY : X ≤ Y)
    (N : ℕ) : (1 + t) ^ N * (‖(2 * Real.pi * I * t : ℂ)⁻¹‖ ^ N * X) ≤ Real.pi⁻¹ ^ N * Y := by
  have hnorm : ‖(2 * Real.pi * I * t : ℂ)⁻¹‖ = (2 * Real.pi * t)⁻¹ := by
    simp [abs_of_pos Real.pi_pos, abs_of_pos (zero_lt_one.trans_le ht)]
  have h2 : (1 + t) / (2 * t) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hratio : (1 + t) * (2 * Real.pi * t)⁻¹ ≤ Real.pi⁻¹ := by
    calc (1 + t) * (2 * Real.pi * t)⁻¹ = (1 + t) / (2 * t) * Real.pi⁻¹ := by field_simp
      _ ≤ 1 * Real.pi⁻¹ := by gcongr
      _ = Real.pi⁻¹ := one_mul _
  rw [hnorm, ← mul_assoc, ← mul_pow]
  gcongr

end NonstationaryPhaseAux

open NonstationaryPhaseAux

/-- **Non-stationary phase.** Let `a` be a smooth compactly supported function on `E` and
`Φ : E → F` a smooth map. For every `c > 0` and every `N`, the oscillatory integral
`∫ 𝐞 (-Λ (Φ x)) a x dx` is `O(‖Λ‖ ^ (-N))` uniformly over the covectors `Λ` whose phase
`x ↦ Λ (Φ x)` is uniformly non-stationary on the support of `a`, in the sense that
`c ‖Λ‖ ≤ ‖Λ ∘ DΦ(x)‖` for every `x ∈ supp a`. -/
theorem exists_one_add_norm_pow_mul_norm_integral_fourierChar_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (ha' : HasCompactSupport a) {Φ : E → F}
    (hΦ : ContDiff ℝ ∞ Φ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ Λ : F →L[ℝ] ℝ, (∀ x ∈ tsupport a, c * ‖Λ‖ ≤ ‖Λ ∘L fderiv ℝ Φ x‖) →
      (1 + ‖Λ‖) ^ N * ‖∫ x, 𝐞 (-Λ (Φ x)) • a x ∂μ‖ ≤ C := by
  set K := tsupport a
  have hK : IsCompact K := ha'
  set δ := c ^ 2 / 2
  have hδ : 0 < δ := by positivity
  -- The amplitude, as a function of `(θ, x)`, and its `N`-th transform.
  set A : (F →L[ℝ] ℝ) × E → ℂ := fun p ↦ a p.2
  have hA : ContDiff ℝ ∞ A := ha.comp contDiff_snd
  have hAK : ∀ p : (F →L[ℝ] ℝ) × E, p.2 ∉ K → A p = 0 := fun p hp ↦
    image_eq_zero_of_notMem_tsupport (f := a) hp
  set B := (lop Φ δ)^[N] A
  have hB : ContDiff ℝ ∞ B := contDiff_iterate_lop hΦ hδ hA N
  -- The compact set `S` of unit covectors whose phase is non-stationary on `K`.
  set S : Set (F →L[ℝ] ℝ) := Metric.sphere 0 1 ∩ ⋂ x ∈ K, {θ | c ≤ ‖θ ∘L fderiv ℝ Φ x‖}
  have hS : IsCompact S := (isCompact_sphere 0 1).inter_right <| isClosed_biInter fun x _ ↦
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.clm_comp continuous_const))
  obtain ⟨M₀, hM₀⟩ := (hS.prod hK).exists_bound_of_continuousOn hB.continuous.continuousOn
  set M := max M₀ 0
  refine ⟨max (2 ^ N * ∫ x, ‖a x‖ ∂μ) ((Real.pi⁻¹) ^ N * (M * μ.real K)), fun Λ hΛ ↦ ?_⟩
  rcases le_or_gt ‖Λ‖ 1 with h1 | h1
  · -- Small covectors: the trivial bound.
    refine le_max_of_le_left (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) N)
      ((norm_integral_le_integral_norm _).trans_eq (by simp)) (norm_nonneg _)
      (by positivity))
  -- Large covectors: `N` integrations by parts along the direction `θ = Λ / ‖Λ‖`.
  refine le_max_of_le_right ?_
  have hΛ0 : Λ ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans h1)
  have hn : 0 < ‖Λ‖ := zero_lt_one.trans h1
  set θ := ‖Λ‖⁻¹ • Λ
  have hθ (x : E) (hx : x ∈ K) : c ≤ ‖θ ∘L fderiv ℝ Φ x‖ := by
    rw [ContinuousLinearMap.smul_comp, norm_smul, norm_inv, norm_norm, le_inv_mul_iff₀ hn,
      mul_comm]
    exact hΛ x hx
  have hθS : θ ∈ S := by
    refine ⟨by simp [θ, norm_smul, hn.ne'], mem_iInter₂.2 fun x hx ↦ hθ x hx⟩
  have hKΛ (y : E) (hy : y ∈ K) : 2 * δ ≤ ‖dphase Φ (θ, y)‖ ^ 2 := by
    have h : c ^ 2 ≤ ‖dphase Φ (θ, y)‖ ^ 2 := pow_le_pow_left₀ hc.le (hθ y hy) 2
    simp only [δ]; linarith
  have hosc : (fun x ↦ 𝐞 (-Λ (Φ x)) • a x) = fun x ↦ osc Φ Λ x * A (θ, x) := by
    ext x
    simp [osc, A, Circle.smul_def]
  -- The integral after `N` integrations by parts is bounded by `M μ(K)`.
  have hbound : ‖∫ y, osc Φ Λ y * B (θ, y) ∂μ‖ ≤ M * μ.real K :=
    norm_integral_osc_mul_le hK (fun y hy ↦ iterate_lop_eq_zero hK.isClosed hAK N (p := (θ, y)) hy)
      fun y hy ↦ (hM₀ (θ, y) ⟨hθS, hy⟩).trans (le_max_left _ _)
  rw [hosc, integral_osc_mul_eq_iterate hΦ hδ hA hK hAK hΛ0 hKΛ N, norm_mul, norm_pow]
  exact one_add_pow_mul_norm_inv_le h1.le (norm_nonneg _) hbound N

end TauCeti
