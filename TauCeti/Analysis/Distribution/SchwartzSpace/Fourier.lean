/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Calculus.Taylor.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Derivatives of Schwartz functions on the Fourier side

The Fourier transform turns the directional derivative `∂_v` on Schwartz space into
multiplication by `2πi ⟪ξ, v⟫` (Mathlib's `SchwartzMap.fourier_lineDerivOp_eq`). This file
records the pointwise consequences for second-order operators: with Mathlib's normalization of the
Fourier transform,

* `𝓕 (∂_v ∂_w u) ξ = -(2π)² ⟪ξ, v⟫ ⟪ξ, w⟫ 𝓕 u ξ`, and
* `𝓕 (Δ u) ξ = -(2π)² ‖ξ‖² 𝓕 u ξ`.

Since `∑ᵢ ∑ⱼ ⟪ξ, bᵢ⟫² ⟪ξ, bⱼ⟫² = ‖ξ‖⁴` for an orthonormal basis `b`, Plancherel's theorem turns
these into the identity

`∑ᵢ ∑ⱼ ‖∂_{bᵢ} ∂_{bⱼ} u‖²_{L²} = ‖Δ u‖²_{L²}`,

so the Laplacian controls the whole Hessian of `u` in `L²`. This is the `p = 2` case of the
Calderón–Zygmund estimate `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`, and the `L²` input to elliptic regularity
for the Laplacian on `ℝⁿ`.

Fourier multipliers are additive in their symbol and commute with the Laplacian.

For the inverse Fourier transform, iterating Mathlib's `SchwartzMap.fourierInv_lineDerivOp_eq`
gives `𝓕⁻ (∂_m^N σ) x = (-2πi ⟪x, m⟫) ^ N 𝓕⁻ σ x`, the inverse Fourier transform commutes with
postcomposition by a continuous linear map, and Mathlib's `norm_fourier_toL2_eq` gives
Plancherel's theorem `‖𝓕⁻ f‖_{L²} = ‖f‖_{L²}`.

For a Schwartz function `φ` and a nonzero `ε`, the *cut-off exponential*
`y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v` is a Schwartz function whose Fourier transform
`|ε|⁻ⁿ 𝓕 φ (ε⁻¹ (ζ - ξ / 2π)) v` concentrates at the frequency `ξ / 2π` as `ε → 0`.

If a Schwartz function `χ` equals `1` near `0`, the moments of positive order of its Fourier
transform vanish, since they are the derivatives at `0` of `𝓕 (𝓕 χ) = χ (-·)`. Convolving with
`𝓕 χ` therefore reproduces Taylor polynomials, which is how a cutoff of a kernel near the diagonal
changes a symbol only by a smoothing remainder.

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `SchwartzMap.fourierMultiplierCLM_laplacian`: Fourier multipliers commute with the Laplacian.

* `SchwartzMap.fourier_lineDerivOp_apply`: the Fourier transform of a directional derivative.
* `SchwartzMap.support_fourier_lineDerivOp_subset`,
  `SchwartzMap.support_fourier_iteratedLineDerivOp_subset`: differentiation does not enlarge the
  support of the Fourier transform.
* `SchwartzMap.fourier_lineDerivOp_lineDerivOp_apply`: the Fourier transform of a second
  directional derivative.
* `SchwartzMap.fourier_laplacian_apply`: the Fourier transform of the Laplacian.
* `SchwartzMap.fourierInv_iterate_lineDerivOp_apply`: the inverse Fourier transform of an
  iterated directional derivative, `𝓕⁻ (∂_m^N σ) x = (-2πi ⟪x, m⟫) ^ N 𝓕⁻ σ x`.
* `SchwartzMap.norm_fourierInv_iterate_lineDerivOp_sq`: its consequence for squared norms,
  `‖𝓕⁻ (∂_m^N σ) x‖² = (2π) ^ (2N) ⟪x, m⟫ ^ (2N) ‖𝓕⁻ σ x‖²`.
* `SchwartzMap.fourierInv_postcompCLM_apply`: the inverse Fourier transform commutes with
  postcomposition by a continuous linear map.
* `SchwartzMap.norm_fourierInv_toL2_eq`: Plancherel's theorem for the inverse Fourier transform.
* `SchwartzMap.norm_toLp_fourierMultiplierCLM_eq`: Plancherel's theorem for Fourier multipliers,
  `‖𝓕⁻ (w • 𝓕 f)‖_{L²} = ‖w • 𝓕 f‖_{L²}`.
* `SchwartzMap.sum_sum_norm_toLp_lineDerivOp_lineDerivOp_sq`: the squared `L²` norms of the
  second derivatives along an orthonormal basis sum to the squared `L²` norm of the Laplacian.
* `SchwartzMap.cutoffExponential`: the cut-off exponential `y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v`.
* `SchwartzMap.fourier_cutoffExponential`: its Fourier transform.
* `SchwartzMap.integral_fourier_eq_apply_zero`, `SchwartzMap.fourier_fourier_apply`: the integral
  of `𝓕 f` is `f 0`, and `𝓕 (𝓕 f) = f (-·)`.
* `SchwartzMap.integral_fourier_smul_apply_eq_zero`: if `χ = 1` near `0`, every moment of positive
  order of `𝓕 χ` vanishes, `∫ 𝓕 χ (v) M (v, …, v) dv = 0`.
* `SchwartzMap.integral_fourier_smul_sum_iteratedFDeriv_eq`,
  `SchwartzMap.norm_integral_fourier_smul_sub_smul_sub_le`: if `χ = 1` near `0`, averaging against
  `𝓕 χ` reproduces Taylor polynomials, so averaging the translates `η ↦ h (ξ - c • η)` changes
  `h ξ` only by a Taylor remainder of order `N + 1`.
* `SchwartzMap.integral_fourierChar_mul_fourier`: Fourier inversion with the Fourier character.
* `SchwartzMap.fourier_smulLeftCLM_sub_apply`: the Fourier transform of `y ↦ χ(x - y) u(y)` is a
  twisted convolution of `𝓕 χ` with `𝓕 u`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.4.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace Real Laplacian LineDeriv
open FourierTransform MeasureTheory
open scoped Topology

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

section FourierMultiplier

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
  [SMulCommClass ℂ 𝕜 F]

/-- Fourier multipliers are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg₁ hg₂]

variable [CompleteSpace F]

/-- Fourier multipliers commute with the Laplacian. -/
theorem fourierMultiplierCLM_laplacian {g : E → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (Δ f) = Δ (fourierMultiplierCLM F g f) := by
  have hn : (fun ξ : E ↦ ‖ξ‖ ^ 2).HasTemperateGrowth := by fun_prop
  -- Commute the two symbols before transporting the identity through the Laplacian formula.
  have hcomm : fourierMultiplierCLM F g
      (fourierMultiplierCLM F (fun ξ : E ↦ ‖ξ‖ ^ 2) f) =
      fourierMultiplierCLM F (fun ξ : E ↦ ‖ξ‖ ^ 2) (fourierMultiplierCLM F g f) := by
    have hn𝕜 : (fun ξ : E ↦ RCLike.ofReal (K := 𝕜) (‖ξ‖ ^ 2)).HasTemperateGrowth := by
      fun_prop
    simp only [← fourierMultiplierCLM_ofReal 𝕜 hn]
    simp only [fourierMultiplierCLM_fourierMultiplierCLM_apply hg hn𝕜,
      fourierMultiplierCLM_fourierMultiplierCLM_apply hn𝕜 hg, mul_comm g]
  simpa only [laplacian_eq_fourierMultiplierCLM, ContinuousLinearMap.map_smul_of_tower]
    using congrArg (fun q ↦ -((2 * π) ^ 2) • q) hcomm

end FourierMultiplier

section normed

variable [NormedSpace ℂ F]

/-- The Fourier transform of the directional derivative `∂_v u` of a Schwartz function is `𝓕 u`
multiplied by `2πi ⟪ξ, v⟫`. -/
theorem fourier_lineDerivOp_apply (u : 𝓢(E, F)) (v ξ : E) :
    𝓕 (∂_{v} u) ξ = ((2 * π * Complex.I) * ⟪ξ, v⟫) • 𝓕 u ξ := by
  have hv : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply hv, ← Complex.coe_smul,
    smul_smul]

/-- The Fourier transform of an iterated directional derivative is multiplication by the
product of the corresponding linear Fourier symbols. -/
theorem fourier_iteratedLineDerivOp_apply (u : 𝓢(E, F)) {k : ℕ} (v : Fin k → E) (ξ : E) :
    𝓕 (∂^{v} u) ξ = (∏ j, ((2 * π * Complex.I) * ⟪ξ, v j⟫)) • 𝓕 u ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, fourier_lineDerivOp_apply, ih,
      smul_smul, Fin.prod_univ_succ]
    simp only [Fin.tail_def]

/-- The frequencies of a directional derivative of a Schwartz function are among those of the
function. -/
theorem support_fourier_lineDerivOp_subset (u : 𝓢(E, F)) (v : E) :
    Function.support ⇑(𝓕 (∂_{v} u) : 𝓢(E, F)) ⊆ Function.support ⇑(𝓕 u : 𝓢(E, F)) := by
  intro ξ hξ h0
  rw [Function.mem_support, fourier_lineDerivOp_apply, h0, smul_zero] at hξ
  exact hξ rfl

/-- The frequencies of an iterated directional derivative of a Schwartz function are among those
of the function. -/
theorem support_fourier_iteratedLineDerivOp_subset (u : 𝓢(E, F)) {n : ℕ} (m : Fin n → E) :
    Function.support ⇑(𝓕 (∂^{m} u) : 𝓢(E, F)) ⊆ Function.support ⇑(𝓕 u : 𝓢(E, F)) := by
  induction n with
  | zero => rw [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    exact (support_fourier_lineDerivOp_subset _ _).trans (ih _)

/-- The Fourier transform of the second directional derivative `∂_v ∂_w u` of a Schwartz function
is `𝓕 u` multiplied by `-(2π)² ⟪ξ, v⟫ ⟪ξ, w⟫`. -/
theorem fourier_lineDerivOp_lineDerivOp_apply (u : 𝓢(E, F)) (v w ξ : E) :
    𝓕 (∂_{v} (∂_{w} u)) ξ = (-(2 * π) ^ 2 * (⟪ξ, v⟫ * ⟪ξ, w⟫)) • 𝓕 u ξ := by
  have hv : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  have hw : (inner ℝ · w : E → ℝ).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply hv, fourier_lineDerivOp_eq,
    smul_apply, smulLeftCLM_apply_apply hw]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  linear_combination (2 * π : ℂ) ^ 2 * (⟪ξ, v⟫ : ℂ) * ⟪ξ, w⟫ * Complex.I_sq

/-- The Fourier transform of the Laplacian of a Schwartz function is `𝓕 u` multiplied by
`-(2π)² ‖ξ‖²`. -/
theorem fourier_laplacian_apply (u : 𝓢(E, F)) (ξ : E) :
    𝓕 (Δ u) ξ = (-(2 * π) ^ 2 * ‖ξ‖ ^ 2) • 𝓕 u ξ := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_sum b, FourierTransform.fourier_sum, sum_apply]
  simp only [fourier_lineDerivOp_lineDerivOp_apply, ← Finset.sum_smul, ← Finset.mul_sum, ← sq,
    b.sum_sq_inner_left]

/-- Differentiating `N` times along `m` multiplies the inverse Fourier transform by
`(-2πi ⟪x, m⟫) ^ N`. -/
theorem fourierInv_iterate_lineDerivOp_apply (σ : 𝓢(E, F)) (m : E) (N : ℕ) (x : E) :
    𝓕⁻ ((∂_{m})^[N] σ) x = (-(2 * π * Complex.I) * ⟪x, m⟫) ^ N • 𝓕⁻ σ x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hm : (inner ℝ · m : E → ℝ).HasTemperateGrowth := by fun_prop
    rw [Function.iterate_succ_apply', fourierInv_lineDerivOp_eq, smul_apply,
      smulLeftCLM_apply_apply hm, ih, pow_succ, ← Complex.coe_smul, smul_smul, smul_smul]
    congr 1
    ring

/-- Differentiating `N` times along `m` multiplies the squared norm of the inverse Fourier
transform by `(2π) ^ (2N) ⟪x, m⟫ ^ (2N)`. -/
theorem norm_fourierInv_iterate_lineDerivOp_sq (σ : 𝓢(E, F)) (m : E) (N : ℕ) (x : E) :
    ‖𝓕⁻ ((∂_{m})^[N] σ) x‖ ^ 2 = (2 * π) ^ (2 * N) * (⟪x, m⟫ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2) := by
  rw [fourierInv_iterate_lineDerivOp_apply, norm_smul, mul_pow, norm_pow, norm_mul, norm_neg,
    Complex.norm_real, Complex.norm_mul, Complex.norm_I, Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    ← (even_two_mul N).pow_abs ⟪x, m⟫]
  ring

/-- The inverse Fourier transform of a Schwartz function commutes with postcomposition by a
continuous complex-linear map: `𝓕⁻ (L ∘ f) = L ∘ 𝓕⁻ f`. -/
@[simp]
theorem fourierInv_postcompCLM_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace F] [CompleteSpace G] (L : F →L[ℂ] G) (f : 𝓢(E, F)) (x : E) :
    𝓕⁻ (postcompCLM L f) x = L (𝓕⁻ f x) := by
  rw [fourierInv_coe, fourierInv_coe, Real.fourierInv_eq, Real.fourierInv_eq,
    ← L.integral_comp_comm]
  · simp [Circle.smul_def]
  · refine f.integrable.norm.mono' ?_ (.of_forall fun v ↦ ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        f.continuous).aestronglyMeasurable
    · simp [Circle.norm_smul]

end normed

section CutoffExponential

variable [NormedSpace ℂ F]

/-- The *cut-off exponential* `y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v` of the angular frequency `ξ`, a
Schwartz function for `ε ≠ 0`. As `ε → 0` it tends to the exponential `exp(i ⟪y, ξ⟫) φ(0) v`
locally uniformly, while its Fourier transform concentrates at `ξ / 2π`. For `ε = 0` it is `0`
by convention (`SchwartzMap.cutoffExponential_zero`). -/
noncomputable def cutoffExponential (φ : 𝓢(E, ℂ)) (ε : ℝ) (ξ : E) (v : F) : 𝓢(E, F) :=
  if hε : ε = 0 then 0 else
    postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ v)
      (smulLeftCLM ℂ (fun y : E ↦ Complex.exp (⟪y, ξ⟫ * Complex.I))
        (compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.smulLeft (Units.mk0 ε hε) : E ≃L[ℝ] E) φ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cut-off exponential at scale `ε = 0` is `0` by convention. -/
@[simp]
theorem cutoffExponential_zero (φ : 𝓢(E, ℂ)) (ξ : E) (v : F) : φ.cutoffExponential 0 ξ v = 0 := by
  simp [cutoffExponential]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The values of a cut-off exponential: `y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v` for `ε ≠ 0`. -/
@[simp]
theorem cutoffExponential_apply (φ : 𝓢(E, ℂ)) {ε : ℝ} (hε : ε ≠ 0) (ξ : E) (v : F) (y : E) :
    φ.cutoffExponential ε ξ v y = (Complex.exp (⟪y, ξ⟫ * Complex.I) * φ (ε • y)) • v := by
  have hg : (fun y : E ↦ Complex.exp (⟪y, ξ⟫ * Complex.I)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp
      (by fun_prop : (inner ℝ · ξ : E → ℝ).HasTemperateGrowth)
  simp [cutoffExponential, hε, smulLeftCLM_apply_apply hg]

/-- **The Fourier transform of a cut-off exponential** is the rescaled Fourier transform of the
cutoff, translated to the frequency `ξ / 2π`:
`𝓕 (cutoffExponential φ ε ξ v) ζ = |ε|⁻ⁿ 𝓕 φ (ε⁻¹ (ζ - ξ / 2π)) v`. -/
theorem fourier_cutoffExponential [CompleteSpace F] (φ : 𝓢(E, ℂ)) {ε : ℝ} (hε : ε ≠ 0) (ξ : E)
    (v : F) (ζ : E) :
    𝓕 (φ.cutoffExponential ε ξ v) ζ =
      |ε ^ Module.finrank ℝ E|⁻¹ • (𝓕 φ (ε⁻¹ • (ζ - (2 * π)⁻¹ • ξ)) • v) := by
  -- The factor `exp(i ⟪y, ξ⟫)` is the character `𝐞 ⟪y, ξ / 2π⟫`, a modulation.
  have hmod : ⇑(φ.cutoffExponential ε ξ v) =
      fun y ↦ 𝐞 ⟪y, (2 * π)⁻¹ • ξ⟫ • (φ (ε • y) • v) := by
    ext y
    rw [cutoffExponential_apply φ hε, TauCeti.exp_inner_mul_I_eq_fourierChar, Circle.smul_def,
      smul_smul]
  rw [fourier_coe, hmod, TauCeti.fourier_fourierChar_smul,
    TauCeti.fourier_comp_smul (fun z ↦ φ z • v), TauCeti.fourier_smul_const, fourier_coe]

end CutoffExponential

section Moment

/-! ### Moments of the Fourier transform -/

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- The integral of the Fourier transform of a Schwartz function is its value at `0`. -/
@[simp]
theorem integral_fourier_eq_apply_zero (f : 𝓢(E, F)) : ∫ v, 𝓕 f v = f 0 := by
  have h : (𝓕⁻ (𝓕 f : 𝓢(E, F)) : 𝓢(E, F)) 0 = f 0 := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rw [fourierInv_coe, fourier_coe, Real.fourierInv_eq] at h
  rw [fourier_coe]
  simpa using h

/-- The Fourier transform of the Fourier transform of a Schwartz function is its reflection. -/
@[simp]
theorem fourier_fourier_apply (f : 𝓢(E, F)) (w : E) : 𝓕 (𝓕 f) w = f (-w) := by
  have h := Real.fourierInv_eq_fourier_neg (𝓕 (f : E → F)) (-w)
  rw [neg_neg] at h
  rw [fourier_coe, fourier_coe, ← h]
  have h' : (𝓕⁻ (𝓕 f : 𝓢(E, F)) : 𝓢(E, F)) (-w) = f (-w) := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rwa [fourierInv_coe, fourier_coe] at h'

/-- **Vanishing moments**, in coordinates. If a Schwartz function `χ` equals `1` near `0`, then
`∫ ⟪v, m₁⟫ ⋯ ⟪v, mₖ⟫ 𝓕 χ (v) dv = 0` for every `k ≠ 0`: the `k`-th derivative at `0` of
`𝓕 (𝓕 χ) = χ (-·)` vanishes. -/
theorem integral_prod_inner_smul_fourier_eq_zero (χ : 𝓢(E, ℂ))
    (hχ : (χ : E → ℂ) =ᶠ[𝓝 0] 1) {k : ℕ} (hk : k ≠ 0) (m : Fin k → E) :
    ∫ v, (∏ i, ⟪v, m i⟫) • 𝓕 χ v = 0 := by
  rw [fourier_coe]
  have hD := Real.iteratedFDeriv_fourier (f := 𝓕 (χ : E → ℂ)) (N := k)
    (fun n _ ↦ (𝓕 χ).integrable_pow_mul volume n) (𝓕 χ).continuous.aestronglyMeasurable
    (n := k) le_rfl
  have hev : 𝓕 (𝓕 (χ : E → ℂ)) =ᶠ[𝓝 0] fun _ ↦ (1 : ℂ) := by
    have ht : Filter.Tendsto (fun w : E ↦ -w) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : E))
    filter_upwards [ht.eventually hχ] with w hw
    rw [← fourier_coe, ← fourier_coe, fourier_fourier_apply]
    simpa using hw
  have hzero : iteratedFDeriv ℝ k (𝓕 (𝓕 (χ : E → ℂ))) 0 m = 0 := by
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_const_of_ne hk]
    rfl
  have hint : Integrable fun v ↦
      VectorFourier.fourierPowSMulRight (innerSL ℝ) (𝓕 (χ : E → ℂ)) v k :=
    VectorFourier.integrable_fourierPowSMulRight _ ((𝓕 χ).integrable_pow_mul volume k)
      (𝓕 χ).continuous.aestronglyMeasurable
  rw [hD, Real.fourier_eq] at hzero
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul] at hzero
  rw [ContinuousMultilinearMap.integral_apply hint] at hzero
  simp only [VectorFourier.fourierPowSMulRight_apply] at hzero
  rw [integral_smul] at hzero
  exact (smul_eq_zero.1 hzero).resolve_left (pow_ne_zero _ (by simp [Real.pi_ne_zero]))

/-- **Vanishing moments.** If a Schwartz function `χ` equals `1` near `0`, then every moment of
positive order of its Fourier transform vanishes: `∫ 𝓕 χ (v) M (v, …, v) dv = 0` for every
continuous multilinear map `M` of positive arity. -/
theorem integral_fourier_smul_apply_eq_zero (χ : 𝓢(E, ℂ)) (hχ : (χ : E → ℂ) =ᶠ[𝓝 0] 1)
    {k : ℕ} (hk : k ≠ 0) (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F) :
    ∫ v, 𝓕 χ v • M (fun _ ↦ v) = 0 := by
  classical
  rw [fourier_coe]
  set b := stdOrthonormalBasis ℝ E
  -- Expand `M (v, …, v)` in the coordinates of `v` in an orthonormal basis.
  have hM (v : E) : M (fun _ ↦ v) = ∑ r : Fin k → Fin (Module.finrank ℝ E),
      (∏ i, ⟪v, b (r i)⟫) • M (fun i ↦ b (r i)) := by
    have hv : (fun _ : Fin k ↦ v) = fun _ ↦ ∑ j, ⟪b j, v⟫ • b j :=
      funext fun _ ↦ (b.sum_repr' v).symm
    rw [hv, M.map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [M.map_smul_univ]
    simp [real_inner_comm]
  have hterm (r : Fin k → Fin (Module.finrank ℝ E)) : Integrable fun v ↦
      ((∏ i, ⟪v, b (r i)⟫) • 𝓕 (χ : E → ℂ) v) • M (fun i ↦ b (r i)) := by
    refine Integrable.smul_const ?_ _
    have hc : Continuous (𝓕 (χ : E → ℂ)) := (𝓕 χ).continuous
    refine ((𝓕 χ).integrable_pow_mul volume k).mono'
      (by fun_prop : Continuous fun v ↦ (∏ i, ⟪v, b (r i)⟫) • 𝓕 (χ : E → ℂ) v).aestronglyMeasurable
      (.of_forall fun v ↦ ?_)
    rw [norm_smul, norm_prod]
    gcongr
    · calc ∏ i, ‖⟪v, b (r i)⟫‖ ≤ ∏ _i : Fin k, ‖v‖ := by
            gcongr with i
            simpa [b.orthonormal.1 (r i)] using abs_real_inner_le_norm v (b (r i))
        _ = ‖v‖ ^ k := by simp
    · rfl
  calc ∫ v, 𝓕 (χ : E → ℂ) v • M (fun _ ↦ v)
      = ∫ v, ∑ r : Fin k → Fin (Module.finrank ℝ E),
          ((∏ i, ⟪v, b (r i)⟫) • 𝓕 (χ : E → ℂ) v) • M (fun i ↦ b (r i)) := by
        congr 1 with v
        rw [hM, Finset.smul_sum]
        exact Finset.sum_congr rfl fun r _ ↦ by rw [smul_assoc, smul_comm]
    _ = ∑ r : Fin k → Fin (Module.finrank ℝ E),
          (∫ v, (∏ i, ⟪v, b (r i)⟫) • 𝓕 (χ : E → ℂ) v) • M (fun i ↦ b (r i)) := by
        rw [integral_finsetSum _ fun r _ ↦ hterm r]
        exact Finset.sum_congr rfl fun r _ ↦ integral_smul_const _ _
    _ = 0 := Finset.sum_eq_zero fun r _ ↦ by
        rw [← fourier_coe, integral_prod_inner_smul_fourier_eq_zero χ hχ hk, zero_smul]

open scoped Nat in
/-- **Averaging reproduces Taylor polynomials.** If a Schwartz function `χ` equals `1` near `0`,
averaging a Taylor polynomial `η ↦ ∑_{k ≤ N} D^k h(ξ) (c • η, …, c • η) / k!` against `𝓕 χ` gives
back its constant term `h ξ`: the moments of positive order of `𝓕 χ` vanish and its integral is
`χ 0 = 1`. -/
theorem integral_fourier_smul_sum_iteratedFDeriv_eq (χ : 𝓢(E, ℂ)) (hχ : (χ : E → ℂ) =ᶠ[𝓝 0] 1)
    (h : E → F) (ξ : E) (c : ℝ) (N : ℕ) :
    ∫ η, 𝓕 χ η • ∑ k ∈ Finset.range (N + 1),
        (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k h ξ (fun _ ↦ c • η) = h ξ := by
  have hterm (k : ℕ) : Integrable fun η ↦
      (k ! : ℝ)⁻¹ • (𝓕 χ η • iteratedFDeriv ℝ k h ξ (fun _ ↦ c • η)) :=
    ((𝓕 χ).integrable_smul_continuousMultilinearMap_apply_smul _ _).smul _
  simp_rw [Finset.smul_sum, smul_comm (𝓕 χ _) ((_ : ℕ) ! : ℝ)⁻¹]
  rw [integral_finsetSum _ fun k _ ↦ hterm k, Finset.sum_range_succ']
  -- The terms of positive order vanish, by the vanishing moments of `𝓕 χ`.
  have hzero (k : ℕ) : ∫ η, (((k + 1) ! : ℕ) : ℝ)⁻¹ •
      (𝓕 χ η • iteratedFDeriv ℝ (k + 1) h ξ (fun _ ↦ c • η)) = 0 := by
    have hM := integral_fourier_smul_apply_eq_zero χ hχ k.succ_ne_zero
      ((iteratedFDeriv ℝ (k + 1) h ξ).compContinuousLinearMap
        fun _ ↦ c • ContinuousLinearMap.id ℝ E)
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply] at hM
    rw [integral_smul, hM, smul_zero]
  simp only [hzero, Finset.sum_const_zero, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_smul, iteratedFDeriv_zero_apply]
  rw [integral_smul_const, integral_fourier_eq_apply_zero, hχ.self_of_nhds,
    Pi.one_apply, one_smul]

open scoped Nat in
/-- **Taylor remainder of an average of translates.** If a Schwartz function `χ` equals `1` near
`0`, averaging the translates `η ↦ h (ξ - c • η)` of a function `h` of polynomial growth against
`𝓕 χ` changes `h ξ` by at most the size of the `(N + 1)`-st derivative of `h`: if
`‖D^{N+1} h ζ‖ ≤ C ⟨ζ⟩ ^ t`, then `‖∫ 𝓕 χ(η) h(ξ - c • η) dη - h(ξ)‖ ≤ C' ⟨ξ⟩ ^ t`, with `C'`
independent of `ξ`. -/
theorem norm_integral_fourier_smul_sub_smul_sub_le (χ : 𝓢(E, ℂ))
    (hχ : (χ : E → ℂ) =ᶠ[𝓝 0] 1) {h : E → F} {N : ℕ} (hh : ContDiff ℝ (N + 1) h) {C₀ s₀ : ℝ}
    (h₀ : ∀ ζ, ‖h ζ‖ ≤ C₀ * (1 + ‖ζ‖ ^ 2) ^ (s₀ / 2)) {C t : ℝ}
    (hN : ∀ ζ, ‖iteratedFDeriv ℝ (N + 1) h ζ‖ ≤ C * (1 + ‖ζ‖ ^ 2) ^ (t / 2)) (c : ℝ) (ξ : E) :
    ‖(∫ η, 𝓕 χ η • h (ξ - c • η)) - h ξ‖ ≤
      C * 2 ^ (|t| / 2) / N ! *
        (∫ η, (1 + ‖c • η‖ ^ 2) ^ ((|t| + (N + 1)) / 2) * ‖𝓕 χ η‖) *
          (1 + ‖ξ‖ ^ 2) ^ (t / 2) := by
  set T : E → F := fun η ↦ ∑ k ∈ Finset.range (N + 1),
    (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k h ξ (fun _ ↦ (-c) • η)
  have hTi : Integrable fun η ↦ 𝓕 χ η • T η := by
    simp_rw [T, Finset.smul_sum, smul_comm (𝓕 χ _) ((_ : ℕ) ! : ℝ)⁻¹]
    exact integrable_finsetSum _ fun k _ ↦
      ((𝓕 χ).integrable_smul_continuousMultilinearMap_apply_smul _ _).smul _
  have hhi := (𝓕 χ).integrable_smul_apply_sub_smul (μ := volume) hh.continuous h₀ c ξ
  rw [← integral_fourier_smul_sum_iteratedFDeriv_eq χ hχ h ξ (-c) N, ← integral_sub hhi hTi]
  simp_rw [← smul_sub]
  refine (norm_integral_le_of_norm_le (((𝓕 χ).integrable_one_add_norm_smul_sq_rpow_mul_norm
    c (|t| + (N + 1))).const_mul (C * 2 ^ (|t| / 2) / N ! * (1 + ‖ξ‖ ^ 2) ^ (t / 2)))
    (.of_forall fun η ↦ ?_)).trans (le_of_eq ?_)
  · have hT := TauCeti.norm_sub_sum_iteratedFDeriv_le_one_add_norm_sq_rpow hh hN ξ ((-c) • η)
    have he : ξ + (-c) • η = ξ - c • η := by rw [neg_smul, ← sub_eq_add_neg]
    have hn : ‖(-c) • η‖ = ‖c • η‖ := by rw [neg_smul, norm_neg]
    rw [he, hn] at hT
    rw [norm_smul]
    calc ‖𝓕 χ η‖ * ‖h (ξ - c • η) - T η‖
        ≤ ‖𝓕 χ η‖ * (C * 2 ^ (|t| / 2) / N ! * (1 + ‖ξ‖ ^ 2) ^ (t / 2) *
            (1 + ‖c • η‖ ^ 2) ^ ((|t| + (N + 1)) / 2)) := by gcongr
      _ = _ := by ring
  · rw [integral_const_mul]
    ring

end Moment

section Cutoff

/-! ### Cutting off by a translate -/

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- **Fourier inversion** for a Schwartz function, written with the Fourier character:
`∫ exp(2πi ⟪η, w⟫) 𝓕 χ(η) dη = χ w`. -/
@[simp]
theorem integral_fourierChar_mul_fourier (χ : 𝓢(E, ℂ)) (w : E) :
    ∫ η, (𝐞 ⟪η, w⟫ : ℂ) * 𝓕 χ η = χ w := by
  have h : (𝓕⁻ (𝓕 χ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) w = χ w := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rw [← h, fourierInv_coe, Real.fourierInv_eq]
  simp only [Circle.smul_def, smul_eq_mul]

/-- **The Fourier transform of a cut-off function.** The Fourier transform of the product
`y ↦ χ(x - y) u(y)` is a twisted convolution of the Fourier transforms:
`∫ 𝓕 χ(η) exp(2πi ⟪η, x⟫) 𝓕 u(ζ + η) dη`. -/
theorem fourier_smulLeftCLM_sub_apply (χ : 𝓢(E, ℂ)) (u : 𝓢(E, F)) (x ζ : E) :
    𝓕 (smulLeftCLM F (fun y ↦ χ (x - y)) u) ζ =
      ∫ η, 𝓕 χ η • (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 u (ζ + η) := by
  have hχx : (fun y : E ↦ χ (x - y)).HasTemperateGrowth := χ.hasTemperateGrowth.comp (by fun_prop)
  set K : E × E → F := fun p ↦ (𝓕 χ p.2 * 𝐞 ⟪p.2, x⟫ * 𝐞 (-⟪p.1, ζ + p.2⟫)) • u p.1
  have hK : Integrable K (volume.prod volume) := by
    have hc : Continuous fun p : E × E ↦ 𝓕 χ p.2 * (𝐞 ⟪p.2, x⟫ : ℂ) * 𝐞 (-⟪p.1, ζ + p.2⟫) := by
      have h₁ : Continuous ⇑(𝓕 χ : 𝓢(E, ℂ)) := (𝓕 χ).continuous
      have h₂ : Continuous fun t : ℝ ↦ (𝐞 t : ℂ) :=
        continuous_subtype_val.comp Real.continuous_fourierChar
      fun_prop
    refine (u.integrable.norm.mul_prod (𝓕 χ).integrable.norm).mono'
      (hc.smul (u.continuous.comp continuous_fst)).aestronglyMeasurable (.of_forall fun p ↦ ?_)
    simp only [K, norm_smul, norm_mul, Circle.norm_coe, mul_one]
    exact (mul_comm _ _).le
  -- The Fourier transform of the cut-off input, with `χ(x - y)` written by Fourier inversion.
  have hL : 𝓕 (smulLeftCLM F (fun y ↦ χ (x - y)) u) ζ = ∫ y, ∫ η, K (y, η) := by
    rw [fourier_coe, Real.fourier_eq]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [smulLeftCLM_apply_apply hχx, K, ← integral_fourierChar_mul_fourier χ (x - y),
      Circle.smul_def, ← integral_smul_const, ← integral_smul]
    refine integral_congr_ae (.of_forall fun η ↦ ?_)
    simp only [smul_smul]
    congr 1
    have e : (𝐞 (-⟪y, ζ⟫) : ℂ) * 𝐞 ⟪η, x - y⟫ = 𝐞 ⟪η, x⟫ * 𝐞 (-⟪y, ζ + η⟫) := by
      rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [inner_sub_right, inner_add_right, real_inner_comm y η]
      ring
    calc (𝐞 (-⟪y, ζ⟫) : ℂ) * ((𝐞 ⟪η, x - y⟫ : ℂ) * 𝓕 χ η)
        = (𝐞 (-⟪y, ζ⟫) : ℂ) * 𝐞 ⟪η, x - y⟫ * 𝓕 χ η := by ring
      _ = _ := by rw [e]; ring
  rw [hL, integral_integral_swap hK]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [K, mul_smul, integral_smul]
  congr 2

end Cutoff

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Plancherel's theorem** for the inverse Fourier transform of Schwartz functions. -/
@[simp]
theorem norm_fourierInv_toL2_eq (f : 𝓢(E, F)) : ‖(𝓕⁻ f).toLp 2‖ = ‖f.toLp 2‖ := by
  rw [← norm_fourier_toL2_eq (𝓕⁻ f), FourierTransform.fourier_fourierInv_eq]

/-- **Plancherel for Fourier multipliers.** For a symbol `w` of temperate growth, the `L²` norm
of the Fourier multiplier `𝓕⁻ (w • 𝓕 f)` of a Schwartz function is the `L²` norm of `w • 𝓕 f`. -/
theorem norm_toLp_fourierMultiplierCLM_eq {w : E → ℂ} (hw : w.HasTemperateGrowth)
    (f : 𝓢(E, F)) :
    ‖(fourierMultiplierCLM F w f).toLp 2‖ = (eLpNorm (fun ξ ↦ w ξ • 𝓕 f ξ) 2 volume).toReal := by
  rw [← norm_fourier_toL2_eq, fourierMultiplierCLM_apply, fourier_fourierInv_eq, norm_toLp]
  congr 2
  ext ξ
  rw [smulLeftCLM_apply_apply hw]

/-- The Laplacian controls the Hessian in `L²`: for a Schwartz function `u` and an orthonormal
basis `b`, `∑ᵢ ∑ⱼ ‖∂_{bᵢ} ∂_{bⱼ} u‖²_{L²} = ‖Δ u‖²_{L²}`. -/
theorem sum_sum_norm_toLp_lineDerivOp_lineDerivOp_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) :
    ∑ i, ∑ j, ‖(∂_{b i} (∂_{b j} u)).toLp 2‖ ^ 2 = ‖(Δ u).toLp 2‖ ^ 2 := by
  -- By Plancherel, each squared `L²` norm is the integral of `‖𝓕 g‖²`; the pointwise identity
  -- `∑ᵢ ∑ⱼ ⟪ξ, bᵢ⟫² ⟪ξ, bⱼ⟫² = ‖ξ‖⁴` then matches the integrands.
  have hF (g : 𝓢(E, F)) : ‖g.toLp 2‖ ^ 2 = ∫ ξ, ‖𝓕 g ξ‖ ^ 2 := by
    rw [← Lp.norm_fourier_eq, toLp_fourier_eq, norm_toLp' two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, ← Real.rpow_two,
      ← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity)]
    norm_num
  have hint (g : 𝓢(E, F)) : Integrable (fun ξ ↦ ‖𝓕 g ξ‖ ^ 2) :=
    ((𝓕 g).memLp 2).integrable_norm_pow two_ne_zero
  simp only [hF]
  simp_rw [← integral_finsetSum _ fun i _ ↦ hint _]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  have hsum : ∑ i, ∑ j, (⟪ξ, b i⟫ * ⟪ξ, b j⟫) ^ 2 = (‖ξ‖ ^ 2) ^ 2 := by
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, b.sum_sq_inner_left, sq]
  simp only [fourier_lineDerivOp_lineDerivOp_apply, fourier_laplacian_apply, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, ← hsum, Finset.mul_sum, Finset.sum_mul]

end SchwartzMap
