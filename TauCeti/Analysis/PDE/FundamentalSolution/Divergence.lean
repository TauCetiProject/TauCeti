/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.CompactSupport
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Integral.RieszPotential.Basic

/-!
# Scalar data as minus divergences of vector fields

Let `E` be a nontrivial finite-dimensional real inner product space of dimension `d`, with an
additive Haar measure `μ`, and let `1 < q` and `1 / p = 1 / q - 1 / d`. Every compactly supported
`h ∈ L^q(E)` is minus the divergence of a vector field `H ∈ Lᵖ(E; E)`, in the sense that

`∫ ⟪H, ∇φ⟫ = ∫ h φ` for every `C¹` function `φ` with compact support,

that is `-div H = h` weakly, with `‖H‖_p ≤ C ‖h‖_q` for a constant `C` depending only on `E`, `μ`,
`p` and `q` (`TauCeti.exists_eLpNorm_le_and_integral_inner_gradient_eq`). The field is the
gradient of the Newtonian potential of `h`,

`H = K ⋆ h`, `K(x) = -(d μ(B(0, 1)))⁻¹ ‖x‖⁻ᵈ x`,

whose kernel satisfies `-div K = δ₀` in every dimension, including the plane, where the Newtonian
kernel itself is logarithmic. The gain of integrability from `q` to `p` is the
Hardy–Littlewood–Sobolev inequality, since `‖K(x)‖` is a multiple of `‖x‖^(1 - d)`, the kernel
of the Riesz potential of order one.

This is how a scalar right-hand side enters an estimate for divergence-form equations that only
accepts data in divergence form: localizing a weak solution of `-div(a ∇u) = -div G` with a cutoff
`ζ` produces the scalar term `⟪G - a ∇u, ∇ζ⟫`, and replacing it by its field `H` costs only its
`L^q` norm, a lower order of integrability of `∇u` than the `Lᵖ` norm being estimated.

## The argument

Pairing the convolution with `∂ᵢφ` and exchanging the integrals
(`TauCeti.integral_mul_convolution_eq_integral_mul_integral_left_comp_sub`) moves the derivative
onto the kernel with pole `t`. Summed over an orthonormal basis, the kernel terms give
`-(d μ(B(0, 1)))⁻¹ ∫ ‖x - t‖⁻ᵈ φ'(x)(x - t) dx`, which is `φ(t)` by the radial fundamental theorem
of calculus (`TauCeti.integral_norm_rpow_neg_finrank_mul_fderiv_apply_self`). The norm of the
field is pointwise at most a multiple of the Riesz potential `I₁ |h|`
(`TauCeti.rieszPotential`), which the Hardy–Littlewood–Sobolev inequality
(`TauCeti.exists_eLpNorm_rieszPotential_le`) bounds in `Lᵖ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.1 (the gradient of the Newtonian potential) and Lemma 7.12 (potential estimates).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §1.2 (the Hardy–Littlewood–Sobolev inequality).
-/

public section

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal InnerProductSpace Gradient Convolution

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- The component in the direction `v` of the kernel `-(d μ(B(0, 1)))⁻¹ ‖x‖⁻ᵈ x`, the gradient of
the Newtonian kernel normalized by `μ`. -/
private noncomputable def divKernel (μ : Measure E) (v x : E) : ℝ :=
  -(((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * (‖x‖ ^ (-(finrank ℝ E : ℝ)) * ⟪x, v⟫_ℝ))

private theorem measurable_divKernel [BorelSpace E] (μ : Measure E) (v : E) :
    Measurable (divKernel μ v) := by
  unfold divKernel
  exact (((continuous_norm.measurable.pow_const _).mul
    (continuous_id.inner continuous_const).measurable).const_mul _).neg

private theorem divKernel_neg (μ : Measure E) (v x : E) :
    divKernel μ v (-x) = -divKernel μ v x := by
  simp only [divKernel, norm_neg, inner_neg_left, mul_neg, neg_neg]

/-- The kernel component is bounded by a multiple of `‖x‖ ^ (1 - d)`. -/
private theorem abs_divKernel_le (μ : Measure E) (v x : E) :
    |divKernel μ v x| ≤
      ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖ * ‖x‖ ^ (1 - (finrank ℝ E : ℝ)) := by
  have hc : 0 ≤ ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ := by positivity
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [divKernel, inner_zero_left, mul_zero, neg_zero, abs_zero]
    positivity
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [divKernel, abs_neg, abs_mul, abs_of_nonneg hc, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  calc ‖x‖ ^ (-(finrank ℝ E : ℝ)) * |⟪x, v⟫_ℝ| ≤ ‖x‖ ^ (-(finrank ℝ E : ℝ)) * (‖x‖ * ‖v‖) := by
        gcongr
        exact abs_real_inner_le_norm x v
    _ = ‖v‖ * ‖x‖ ^ (1 - (finrank ℝ E : ℝ)) := by
        rw [show 1 - (finrank ℝ E : ℝ) = -(finrank ℝ E : ℝ) + 1 by ring,
          Real.rpow_add_one hx'.ne']
        ring

private theorem locallyIntegrable_divKernel [FiniteDimensional ℝ E] [BorelSpace E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) : LocallyIntegrable (divKernel μ v) μ := by
  refine locallyIntegrable_of_norm_le_rpow (μ := μ) finrank_pos
    (C := ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖)
    (α := (finrank ℝ E : ℝ) - 1) (by linarith) (ae_of_all _ fun x ↦ ?_)
    (measurable_divKernel μ v).aestronglyMeasurable
  rw [Real.norm_eq_abs, neg_sub]
  exact abs_divKernel_le μ v x

/-- Summed over an orthonormal basis, the kernel components pair with the derivative of `φ` to the
radial integrand `-(d μ(B(0, 1)))⁻¹ ‖x‖⁻ᵈ φ'(y)(x)`. -/
private theorem sum_fderiv_mul_divKernel {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (μ : Measure E) (L : E →L[ℝ] ℝ) (x : E) :
    ∑ i, L (b i) * divKernel μ (b i) x =
      -((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * (‖x‖ ^ (-(finrank ℝ E : ℝ)) * L x) := by
  have hx : L x = ∑ i, ⟪x, b i⟫_ℝ * L (b i) := by
    conv_lhs => rw [← b.sum_repr' x]
    simp [map_sum, real_inner_comm]
  simp_rw [divKernel, hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The pairing of the kernel with pole `t` against the derivatives of `φ` along an orthonormal
basis gives back `φ(t)`: `-div K = δ` in the sense of distributions. -/
private theorem sum_integral_fderiv_mul_divKernel_sub [FiniteDimensional ℝ E] [BorelSpace E]
    [Nontrivial E] [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (t : E) :
    ∑ i, ∫ x, fderiv ℝ φ x (b i) * divKernel μ (b i) (x - t) ∂μ = φ t := by
  have hφ' : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hint : ∀ i, Integrable (fun x ↦ fderiv ℝ φ x (b i) * divKernel μ (b i) (x - t)) μ := by
    intro i
    have hcont : Continuous fun y ↦ fderiv ℝ φ (y + t) (b i) :=
      (hφ'.comp (continuous_id.add continuous_const)).clm_apply continuous_const
    have hcpt : HasCompactSupport fun y ↦ fderiv ℝ φ (y + t) (b i) :=
      (hφc.fderiv_apply (𝕜 := ℝ) (b i)).comp_homeomorph (Homeomorph.addRight t)
    have hy : Integrable (fun y ↦ fderiv ℝ φ (y + t) (b i) * divKernel μ (b i) y) μ := by
      simpa only [smul_eq_mul] using
        (locallyIntegrable_divKernel μ (b i)).integrable_smul_left_of_hasCompactSupport hcont hcpt
    simpa only [sub_add_cancel] using hy.comp_sub_right t
  rw [← integral_finsetSum _ fun i _ ↦ hint i]
  simp_rw [sum_fderiv_mul_divKernel b μ]
  rw [integral_const_mul]
  -- The radial fundamental theorem of calculus, with the pole moved to `t`.
  have hrad := integral_norm_rpow_neg_finrank_mul_fderiv_apply_self (μ := μ)
    (f := fun y ↦ φ (y + t)) (hφ.comp (contDiff_id.add contDiff_const))
    (hφc.comp_homeomorph (Homeomorph.addRight t))
  simp only [fderiv_comp_add_right, zero_add] at hrad
  have hshift := integral_add_right_eq_self (μ := μ)
    (fun x ↦ ‖x - t‖ ^ (-(finrank ℝ E : ℝ)) * fderiv ℝ φ x (x - t)) t
  simp only [add_sub_cancel_right] at hshift
  rw [← hshift, hrad]
  have hvol : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have hd : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
  field_simp

/-- The gradient of the Newtonian potential of `h`, assembled from its components along an
orthonormal basis. -/
private noncomputable def divField [FiniteDimensional ℝ E] (μ : Measure E) (h : E → ℝ) (x : E) :
    E :=
  ∑ i, (divKernel μ (stdOrthonormalBasis ℝ E i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x •
    stdOrthonormalBasis ℝ E i

private theorem divField_apply [FiniteDimensional ℝ E] (μ : Measure E) (h : E → ℝ) (x : E) :
    divField μ h x = ∑ i, (divKernel μ (stdOrthonormalBasis ℝ E i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      μ] h) x • stdOrthonormalBasis ℝ E i := rfl

/-- Each component of the field is bounded by `(d μ(B(0, 1)))⁻¹` times the Riesz potential of order
one of `h`. -/
private theorem enorm_convolution_divKernel_le [BorelSpace E] [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] {v : E} (hv : ‖v‖ = 1) (h : E → ℝ) (x : E) :
    ‖(divKernel μ v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x‖ₑ ≤
      (((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹.toNNReal : ℝ≥0∞) *
        rieszPotential μ 1 h x := by
  have hc : 0 ≤ ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ := by positivity
  rw [convolution_lsmul]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  rw [rieszPotential_def, ← lintegral_sub_left_eq_self _ x,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun y ↦ ?_
  simp only [sub_sub_cancel, smul_eq_mul, eNorm_mul, ← mul_assoc]
  gcongr
  rcases eq_or_ne (x - y) 0 with hy | hy
  · simp [divKernel, hy]
  have hy' : 0 < ‖x - y‖ := norm_pos_iff.mpr hy
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos hy',
    ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ((abs_divKernel_le μ v (x - y)).trans_eq ?_)
  rw [hv, mul_one]

/-- The field is pointwise at most `d (d μ(B(0, 1)))⁻¹` times the Riesz potential of order one of
`h`. -/
private theorem enorm_divField_le [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (h : E → ℝ) (x : E) :
    ‖divField μ h x‖ₑ ≤ (((finrank ℝ E : ℝ≥0) *
      ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) *
        ‖rieszPotential μ 1 h x‖ₑ := by
  set b := stdOrthonormalBasis ℝ E
  calc ‖divField μ h x‖ₑ
      ≤ ∑ i, ‖(divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x • b i‖ₑ := by
        rw [divField_apply]
        exact eNorm_sum_le _ _
    _ = ∑ i, ‖(divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x‖ₑ := by
        simp only [eNorm_smul, ← ofReal_norm (b _), b.orthonormal.1, ENNReal.ofReal_one, mul_one]
    _ ≤ ∑ _i : Fin (finrank ℝ E), (((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹.toNNReal :
          ℝ≥0∞) * rieszPotential μ 1 h x :=
        Finset.sum_le_sum fun i _ ↦ enorm_convolution_divKernel_le (b.orthonormal.1 i) h x
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, eNorm_eq_self]
        push_cast
        ring

/-- Pairing the kernel with pole `t` against a continuous compactly supported `ψ` is continuous in
the pole: up to sign it is the convolution of the kernel with `ψ`. -/
private theorem continuous_integral_mul_divKernel_sub [FiniteDimensional ℝ E] [BorelSpace E]
    [Nontrivial E] [μ.IsAddHaarMeasure] (v : E) {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) : Continuous fun t ↦ ∫ x, ψ x * divKernel μ v (x - t) ∂μ := by
  have hcont := hψc.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_divKernel μ v) hψ
  refine (hcont.neg).congr fun t ↦ ?_
  rw [Pi.neg_apply, convolution_lsmul, ← integral_neg, ← integral_sub_left_eq_self _ μ t]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [sub_sub_cancel, smul_eq_mul, show t - x = -(x - t) by abel, divKernel_neg]
  ring

/-- **The field is a weak solution of `-div H = h`.** -/
private theorem integral_inner_divField_gradient [FiniteDimensional ℝ E] [BorelSpace E]
    [Nontrivial E] [μ.IsAddHaarMeasure] {h : E → ℝ} (hhi : Integrable h μ)
    (hhc : HasCompactSupport h) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ x, ⟪divField μ h x, ∇ φ x⟫_ℝ ∂μ = ∫ x, h x * φ x ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  have hconv : ∀ i, LocallyIntegrable
      (divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) μ :=
    fun i ↦ hhc.locallyIntegrable_convolution_right _ (locallyIntegrable_divKernel μ (b i)) hhi
  have hψ : ∀ i, Continuous fun x ↦ fderiv ℝ φ x (b i) :=
    fun i ↦ (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψc : ∀ i, HasCompactSupport fun x ↦ fderiv ℝ φ x (b i) :=
    fun i ↦ hφc.fderiv_apply (𝕜 := ℝ) (b i)
  -- Each component pairs with the corresponding derivative of `φ`.
  have hinner : ∀ x, ⟪divField μ h x, ∇ φ x⟫_ℝ =
      ∑ i, fderiv ℝ φ x (b i) * (divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x := by
    intro x
    rw [divField_apply, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, inner_gradient_right, conj_trivial, mul_comm]
  -- The pairing of each component is integrated against the compactly supported `h`.
  have hhI : ∀ i, Integrable
      (fun t ↦ h t * ∫ x, fderiv ℝ φ x (b i) * divKernel μ (b i) (x - t) ∂μ) μ := by
    intro i
    rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport h)
      (fun t ht ↦ subset_tsupport h (left_ne_zero_of_mul ht))]
    exact hhi.integrableOn.mul_continuousOn
      (continuous_integral_mul_divKernel_sub (b i) (hψ i) (hψc i)).continuousOn hhc.isCompact
  calc ∫ x, ⟪divField μ h x, ∇ φ x⟫_ℝ ∂μ
      = ∑ i, ∫ x, fderiv ℝ φ x (b i) *
          (divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x ∂μ := by
        simp_rw [hinner]
        refine integral_finsetSum _ fun i _ ↦ ?_
        simpa only [smul_eq_mul] using
          (hconv i).integrable_smul_right_of_hasCompactSupport (hψ i) (hψc i) |>.congr
            (ae_of_all _ fun x ↦ mul_comm _ _)
    _ = ∑ i, ∫ t, h t * ∫ x, fderiv ℝ φ x (b i) * divKernel μ (b i) (x - t) ∂μ ∂μ :=
        Finset.sum_congr rfl fun i _ ↦
          integral_mul_convolution_eq_integral_mul_integral_left_comp_sub (hψ i) (hψc i)
            (locallyIntegrable_divKernel μ (b i)) hhi hhc
    _ = ∫ t, h t * ∑ i, ∫ x, fderiv ℝ φ x (b i) * divKernel μ (b i) (x - t) ∂μ ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hhI i]
        simp_rw [Finset.mul_sum]
    _ = ∫ t, h t * φ t ∂μ := by
        simp_rw [sum_integral_fderiv_mul_divKernel_sub b hφ hφc]

/-- **Compactly supported `L^q` data are minus divergences of `Lᵖ` fields.** Let `E` be a nontrivial
finite-dimensional real inner product space of dimension `d` with an additive Haar measure `μ`,
and let `1 < q` and `1 / p = 1 / q - 1 / d`. There is a constant `C` such that every compactly
supported `h ∈ L^q(E)` is minus the divergence of a field `H` with `‖H‖_p ≤ C ‖h‖_q`:
`∫ ⟪H, ∇φ⟫ = ∫ h φ` for every `C¹` function `φ` with compact support, so that `-div H = h`
weakly. One may take for `H` the gradient of the Newtonian potential of `h`. -/
theorem exists_eLpNorm_le_and_integral_inner_gradient_eq [FiniteDimensional ℝ E] [BorelSpace E]
    [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure] {p q : ℝ≥0} (hq : 1 < q)
    (hpq : (p : ℝ)⁻¹ = (q : ℝ)⁻¹ - 1 / finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ h : E → ℝ, MemLp h q μ → HasCompactSupport h →
      ∃ H : E → E, AEStronglyMeasurable H μ ∧ eLpNorm H p μ ≤ C * eLpNorm h q μ ∧
        ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          ∫ x, ⟪H x, ∇ φ x⟫_ℝ ∂μ = ∫ x, h x * φ x ∂μ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_rieszPotential_le (F := ℝ) μ one_pos hq hpq
  refine ⟨((finrank ℝ E : ℝ≥0) * ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹.toNNReal) * C,
    fun h hh hhc ↦ ?_⟩
  have hhi : Integrable h μ :=
    ((hh.locallyIntegrable (by exact_mod_cast hq.le)).integrableOn_isCompact
      hhc.isCompact).integrable_of_forall_notMem_eq_zero
        fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hmeas : AEStronglyMeasurable (divField μ h) μ := by
    simp only [funext (divField_apply μ h)]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
      (hhc.locallyIntegrable_convolution_right _ (locallyIntegrable_divKernel μ _)
        hhi).aestronglyMeasurable.smul_const _
  refine ⟨divField μ h, hmeas, ?_, fun φ hφ hφc ↦ integral_inner_divField_gradient hhi hhc hφ hφc⟩
  calc eLpNorm (divField μ h) p μ
      ≤ (((finrank ℝ E : ℝ≥0) * ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹.toNNReal :
          ℝ≥0) : ℝ≥0∞) * eLpNorm (rieszPotential μ 1 h) p μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hmeas (ae_of_all _ (enorm_divField_le h)) _
    _ ≤ _ * (C * eLpNorm h q μ) := by gcongr; exact hC h
    _ = _ := by push_cast; ring

end TauCeti
