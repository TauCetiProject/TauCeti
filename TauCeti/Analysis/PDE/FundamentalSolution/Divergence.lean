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
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.MeasureTheory.Function.Morrey
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.CompactSupport
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Integral.DistRpow
import TauCeti.MeasureTheory.Integral.RieszPotential.Basic
import TauCeti.MeasureTheory.Integral.RieszPotential.Bounded
import TauCeti.Topology.MetricSpace.Holder

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

## Data supported in a bounded set

When `h` is integrable and vanishes off a bounded set `Ω`, the same field is controlled on `Ω`
in every `Lᵖ`, `1 ≤ p ≤ ∞`, without a change of exponent:

`‖H‖_{Lᵖ(Ω)} ≤ d diam(Ω) ‖h‖_{Lᵖ(Ω)}`

(`TauCeti.exists_eLpNorm_restrict_le_and_integral_inner_gradient_eq`). This holds in every
dimension, including `d = 1`, because on `Ω` the Riesz potential of order one only integrates
`‖x - y‖^(1 - d)` over a ball of radius `diam Ω` (`TauCeti.eLpNorm_rieszPotential_restrict_le`).
The factor `diam Ω` is the scaling of one derivative, which is how a scalar datum enters a
divergence-form estimate on a ball of radius `R` with the weight `R`. On a ball `B = B(x₀, r)`, an
`f` integrable on `B` is minus the divergence in `B` of a field with
`‖H‖_{Lᵖ(B)} ≤ 2 d r ‖f‖_{Lᵖ(B)}`
(`TauCeti.exists_eLpNorm_restrict_ball_le_and_setIntegral_inner_gradient_eq`).

## Data in a Morrey space

For a Schauder estimate the field must be Hölder continuous rather than integrable. Let
`0 < α < 1` and let `h` be measurable, compactly supported, and in the Morrey space
`L^{1, d - 1 + α}(E)`: its mass on closed balls is `∫_{B(x, r)} |h| ≤ M r^(d - 1 + α)`. Then the
same field `H` is `α`-Hölder, with Hölder constant `C M` for a constant `C` depending only on `E`,
`μ` and `α`
(`TauCeti.exists_holderWith_and_integral_inner_gradient_eq_of_morreyNormPow_le`). The space
contains compactly supported `L^q` data for `q = d / (1 - α)`
(`TauCeti.MeasureTheory.morreyNormPow_le_eLpNorm_rpow_mul`). The proof is the potential estimate
behind Morrey's lemma (Gilbarg–Trudinger, Section 7.9), applied to the kernel of `H`, which is
homogeneous of degree `1 - d`. This is how zero-order terms with Morrey coefficients enter Morrey's
`C^{1,α}` estimates for divergence-form equations.

## The argument

Pairing the convolution with `∂ᵢφ` and exchanging the integrals
(`TauCeti.integral_mul_convolution_eq_integral_mul_integral_left_comp_sub`) moves the derivative
onto the kernel with pole `t`. Summed over an orthonormal basis, the kernel terms give
`-(d μ(B(0, 1)))⁻¹ ∫ ‖x - t‖⁻ᵈ φ'(x)(x - t) dx`, which is `φ(t)` by the radial fundamental theorem
of calculus (`TauCeti.integral_norm_rpow_neg_finrank_mul_fderiv_apply_self`). The norm of the
field is pointwise at most a multiple of the Riesz potential `I₁ |h|`
(`TauCeti.rieszPotential`), which the Hardy–Littlewood–Sobolev inequality
(`TauCeti.exists_eLpNorm_rieszPotential_le`) bounds in `Lᵖ`.

For the Hölder estimate at two points `x`, `x'` at distance `δ`, split the integral defining
`H(x) - H(x')` at the ball `B(x, 2δ)`. Inside, each kernel is at most a multiple of `‖·‖^(1 - d)`,
whose integral against `|h|` over a ball of radius `ρ` about its pole is at most a multiple of
`M ρ^α` (`TauCeti.setLIntegral_ball_ofReal_dist_rpow_neg_mul_le`). Outside, the smoothness of the
radial field `z ↦ ‖z‖⁻ᵈ z` (`TauCeti.norm_norm_rpow_smul_sub_le`) bounds the difference of the
kernels by a multiple of `δ ‖x - y‖⁻ᵈ`, whose integral against `|h|` off the ball is at most a
multiple of `M δ^(α - 1)` (`TauCeti.setLIntegral_ofReal_dist_rpow_neg_mul_le`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.1 (the gradient of the Newtonian potential), Lemma 7.12 (potential estimates) and
  Section 7.9 (Morrey's estimate).
* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Springer, 1966, §3.5 and §5.5.
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

/-! ### Data in a Morrey space

If the mass of `|h|` on balls of radius `r` is at most `M r^(d - 1 + α)`, `0 < α < 1`, then the
field `H` is `α`-Hölder, with constant a multiple of `M`. Near the two points compared, the kernel
is integrated against `|h|` on dyadic annuli; away from them, the difference of the kernels decays
like `‖x - y‖⁻ᵈ`. -/

section Morrey

/-- The kernel components inherit the smoothness estimate `norm_norm_rpow_smul_sub_le` of the
radial field `z ↦ ‖z‖⁻ᵈ z`. -/
private theorem abs_divKernel_sub_le (μ : Measure E) (v : E) {z w : E}
    (hzw : 2 * ‖z - w‖ ≤ ‖z‖) :
    |divKernel μ v z - divKernel μ v w| ≤
      ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖ *
        ((1 + finrank ℝ E) * (2 : ℝ) ^ (finrank ℝ E : ℝ) * ‖z - w‖ *
          ‖z‖ ^ (-(finrank ℝ E : ℝ))) := by
  have hc : 0 ≤ ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ := by positivity
  have heq : divKernel μ v z - divKernel μ v w =
      -(((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ *
        ⟪‖z‖ ^ (-(finrank ℝ E : ℝ)) • z - ‖w‖ ^ (-(finrank ℝ E : ℝ)) • w, v⟫_ℝ) := by
    simp only [divKernel, inner_sub_left, real_inner_smul_left]
    ring
  rw [heq, abs_neg, abs_mul, abs_of_nonneg hc, mul_assoc]
  gcongr
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mul_comm]
  gcongr
  have h := norm_norm_rpow_smul_sub_le (p := -(finrank ℝ E : ℝ)) (a := w) (b := z)
    (neg_nonpos.2 (Nat.cast_nonneg _)) (by rwa [norm_sub_rev])
  rw [norm_sub_rev, norm_sub_rev w z, abs_neg, Nat.abs_cast, neg_neg] at h
  exact h

/-- The constant of the Hölder estimate for one component of the field of data in a Morrey space
with exponent `d - 1 + α`. -/
private noncomputable def divHolderConst (μ : Measure E) (α : ℝ) : ℝ :=
  ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ *
    (2 ^ ((finrank ℝ E : ℝ) - 1) / (1 - 2 ^ (-α)) * 2 ^ α +
      2 ^ ((finrank ℝ E : ℝ) - 1) / (1 - 2 ^ (-α)) * 3 ^ α +
      (1 + finrank ℝ E) * (2 : ℝ) ^ (finrank ℝ E : ℝ) *
        (2 ^ ((finrank ℝ E : ℝ) - 1 + α) / (1 - 2 ^ (α - 1))) * 2 ^ (α - 1))

private theorem divHolderConst_nonneg (μ : Measure E) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) : 0 ≤ divHolderConst μ α := by
  have h₁ : 0 ≤ 1 - (2 : ℝ) ^ (-α) :=
    sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith))
  have h₂ : 0 ≤ 1 - (2 : ℝ) ^ (α - 1) :=
    sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith))
  unfold divHolderConst
  positivity

variable [FiniteDimensional ℝ E] [BorelSpace E] [Nontrivial E] {h : E → ℝ} {M : ℝ≥0∞} {α : ℝ}

/-- Near its pole, the kernel integrated against a function whose mass on balls of radius `r` is at
most `M r^(d - 1 + α)` is at most a multiple of `M ρ^α` on the ball of radius `ρ`. -/
private theorem setLIntegral_ball_enorm_divKernel_sub_mul_le (v x : E) {ρ : ℝ} (hρ : 0 < ρ)
    (hα : 0 < α)
    (hM : ∀ x r, 0 < r → ∫⁻ y in closedBall x r, ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - 1 + α))) :
    ∫⁻ y in ball x ρ, ‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖ *
        (2 ^ ((finrank ℝ E : ℝ) - 1) / (1 - 2 ^ (-α)) * ρ ^ α)) := by
  set c := ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖
  have hc : 0 ≤ c := by positivity
  have hd : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos
  have hpt (y : E) : ‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ ≤
      ENNReal.ofReal c * (ENNReal.ofReal (dist y x ^ (-((finrank ℝ E : ℝ) - 1))) * ‖h y‖ₑ) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
    gcongr
    rw [← ofReal_norm, Real.norm_eq_abs, neg_sub, dist_eq_norm, norm_sub_rev]
    exact ENNReal.ofReal_le_ofReal (abs_divKernel_le μ v (x - y))
  have hA := setLIntegral_ball_ofReal_dist_rpow_neg_mul_le (μ := μ) (y := x)
    (g := fun y => ‖h y‖ₑ) (s := (finrank ℝ E : ℝ) - 1) (lam := (finrank ℝ E : ℝ) - 1 + α)
    (fun r hr _ => hM x r hr) (by linarith) (by linarith) hρ
  rw [show (finrank ℝ E : ℝ) - 1 - ((finrank ℝ E : ℝ) - 1 + α) = -α by ring,
    show (finrank ℝ E : ℝ) - 1 + α - ((finrank ℝ E : ℝ) - 1) = α by ring] at hA
  calc ∫⁻ y in ball x ρ, ‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ ∂μ
      ≤ ∫⁻ y in ball x ρ, ENNReal.ofReal c *
          (ENNReal.ofReal (dist y x ^ (-((finrank ℝ E : ℝ) - 1))) * ‖h y‖ₑ) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal c * ∫⁻ y in ball x ρ,
          ENNReal.ofReal (dist y x ^ (-((finrank ℝ E : ℝ) - 1))) * ‖h y‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * (M * ENNReal.ofReal
          (2 ^ ((finrank ℝ E : ℝ) - 1) / (1 - 2 ^ (-α)) * ρ ^ α)) := by gcongr
    _ = _ := by rw [mul_left_comm, ← ENNReal.ofReal_mul hc]

/-- Away from the two points `x` and `x'`, at distance at least `2 dist x x'` from `x`, the
difference of the kernels with poles `x` and `x'`, integrated against a function whose mass on
balls of radius `r` is at most `M r^(d - 1 + α)`, is at most a multiple of `M dist x x' ^ α`. -/
private theorem setLIntegral_enorm_divKernel_sub_sub_mul_le (v : E) {x x' : E}
    (hxx' : 0 < dist x x') (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ x r, 0 < r → ∫⁻ y in closedBall x r, ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - 1 + α))) :
    ∫⁻ y in {y | 2 * dist x x' ≤ dist y x},
        ‖divKernel μ v (x - y) - divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖ *
        ((1 + finrank ℝ E) * (2 : ℝ) ^ (finrank ℝ E : ℝ) * dist x x' *
          (2 ^ ((finrank ℝ E : ℝ) - 1 + α) / (1 - 2 ^ (α - 1)) *
            (2 * dist x x') ^ (α - 1)))) := by
  set δ := dist x x'
  set c := ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖ *
    ((1 + finrank ℝ E) * (2 : ℝ) ^ (finrank ℝ E : ℝ) * δ)
  have hc : 0 ≤ c := by positivity
  have hd : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos
  have hmeas : MeasurableSet {y | 2 * δ ≤ dist y x} :=
    measurableSet_le measurable_const (continuous_id.dist continuous_const).measurable
  have hpt (y : E) (hy : y ∈ {y | 2 * δ ≤ dist y x}) :
      ‖divKernel μ v (x - y) - divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ ≤
        ENNReal.ofReal c * (ENNReal.ofReal (dist y x ^ (-(finrank ℝ E : ℝ))) * ‖h y‖ₑ) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
    gcongr
    have hzw : x - y - (x' - y) = x - x' := by abel
    have hy' : dist y x = ‖x - y‖ := by rw [dist_eq_norm, norm_sub_rev]
    rw [← ofReal_norm, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ((abs_divKernel_sub_le μ v ?_).trans_eq ?_)
    · rw [hzw, ← dist_eq_norm, ← hy']
      exact hy
    · rw [hzw, ← dist_eq_norm, ← hy']
      ring
  have hB := setLIntegral_ofReal_dist_rpow_neg_mul_le (μ := μ) (y := x)
    (g := fun y => ‖h y‖ₑ) (R := 2 * δ) (s := finrank ℝ E) (lam := (finrank ℝ E : ℝ) - 1 + α)
    (fun r hr => (lintegral_mono_set ball_subset_closedBall).trans
      (hM x r (by linarith)))
    (by linarith) (by linarith) (by positivity)
  rw [show (finrank ℝ E : ℝ) - 1 + α - finrank ℝ E = α - 1 by ring] at hB
  calc ∫⁻ y in {y | 2 * δ ≤ dist y x},
        ‖divKernel μ v (x - y) - divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ ∂μ
      ≤ ∫⁻ y in {y | 2 * δ ≤ dist y x}, ENNReal.ofReal c *
          (ENNReal.ofReal (dist y x ^ (-(finrank ℝ E : ℝ))) * ‖h y‖ₑ) ∂μ :=
        setLIntegral_mono' hmeas hpt
    _ = ENNReal.ofReal c * ∫⁻ y in {y | 2 * δ ≤ dist y x},
          ENNReal.ofReal (dist y x ^ (-(finrank ℝ E : ℝ))) * ‖h y‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * (M * ENNReal.ofReal (2 ^ ((finrank ℝ E : ℝ) - 1 + α) /
          (1 - 2 ^ (α - 1)) * (2 * δ) ^ (α - 1))) := by gcongr
    _ = _ := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul hc]
        simp only [c, mul_assoc]

/-- Against a function whose mass on balls grows like `r^(d - 1 + α)`, the kernel with any pole is
integrable. -/
private theorem integrable_divKernel_sub_mul (v x : E) (hh : Integrable h μ) (hMt : M ≠ ∞)
    (hα : 0 < α)
    (hM : ∀ x r, 0 < r → ∫⁻ y in closedBall x r, ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - 1 + α))) :
    Integrable (fun y => divKernel μ v (x - y) * h y) μ := by
  set c := ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖
  have hc : 0 ≤ c := by positivity
  have hd : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast finrank_pos
  refine ⟨((measurable_divKernel μ v).comp
    (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hh.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, eNorm_mul]
  -- Off the unit ball about the pole the kernel is bounded by `c`.
  have hfar : ∫⁻ y in (ball x 1)ᶜ, ‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ ∂μ ≤
      ENNReal.ofReal c * ∫⁻ y, ‖h y‖ₑ ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_mono' measurableSet_ball.compl fun y hy => ?_).trans
      (setLIntegral_le_lintegral _ _)
    gcongr
    have hy : 1 ≤ ‖x - y‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact not_lt.1 hy
    rw [← ofReal_norm, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ((abs_divKernel_le μ v (x - y)).trans ?_)
    exact mul_le_of_le_one_right hc (Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith))
  rw [← lintegral_add_compl _ (measurableSet_ball (x := x) (ε := 1))]
  exact ENNReal.add_lt_top.2
    ⟨(setLIntegral_ball_enorm_divKernel_sub_mul_le v x one_pos hα hM).trans_lt
      (ENNReal.mul_lt_top hMt.lt_top ENNReal.ofReal_lt_top),
    hfar.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.2)⟩

/-- Near the two points `x` and `x'`, within distance `2 dist x x'` of `x`, the kernels with
poles `x` and `x'` are integrated separately against `|h|`. -/
private theorem setLIntegral_ball_enorm_divKernel_sub_sub_mul_le (v : E) (hh : Integrable h μ)
    (hα : 0 < α)
    (hM : ∀ x r, 0 < r → ∫⁻ y in closedBall x r, ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - 1 + α))) {x x' : E} (hxx' : 0 < dist x x') :
    ∫⁻ y in ball x (2 * dist x x'),
        ‖divKernel μ v (x - y) - divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖ *
          ((2 : ℝ) ^ ((finrank ℝ E : ℝ) - 1) / (1 - 2 ^ (-α)) * (2 * dist x x') ^ α)) +
        M * ENNReal.ofReal (((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹ * ‖v‖ *
          ((2 : ℝ) ^ ((finrank ℝ E : ℝ) - 1) / (1 - 2 ^ (-α)) * (3 * dist x x') ^ α)) := by
  set δ := dist x x'
  have hmeas : AEMeasurable (fun y => ‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ) μ :=
    ((measurable_divKernel μ v).comp (measurable_const.sub measurable_id)).eNorm.aemeasurable.mul
      hh.aestronglyMeasurable.eNorm
  calc ∫⁻ y in ball x (2 * δ), ‖divKernel μ v (x - y) - divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ ∂μ
      ≤ ∫⁻ y in ball x (2 * δ), (‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ +
          ‖divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ) ∂μ :=
        lintegral_mono fun y => by rw [← add_mul]; gcongr; exact eNorm_sub_le
    _ = ∫⁻ y in ball x (2 * δ), ‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ ∂μ +
          ∫⁻ y in ball x (2 * δ), ‖divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ ∂μ :=
        lintegral_add_left' hmeas.restrict _
    _ ≤ ∫⁻ y in ball x (2 * δ), ‖divKernel μ v (x - y)‖ₑ * ‖h y‖ₑ ∂μ +
          ∫⁻ y in ball x' (3 * δ), ‖divKernel μ v (x' - y)‖ₑ * ‖h y‖ₑ ∂μ := by
        gcongr
        intro y hy
        rw [mem_ball] at hy ⊢
        linarith [dist_triangle y x x']
    _ ≤ _ := add_le_add (setLIntegral_ball_enorm_divKernel_sub_mul_le v x (by positivity) hα hM)
        (setLIntegral_ball_enorm_divKernel_sub_mul_le v x' (by positivity) hα hM)

variable [μ.IsAddHaarMeasure]

/-- **The components of the field are `α`-Hölder.** If the mass of `|h|` on balls of radius `r` is
at most `M r^(d - 1 + α)`, `0 < α < 1`, the components of the field along a unit vector differ at
two points by at most a multiple of `M dist x x' ^ α`. -/
private theorem enorm_convolution_divKernel_sub_le {v : E} (hv : ‖v‖ = 1) (hh : Integrable h μ)
    (hMt : M ≠ ∞) (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ x r, 0 < r → ∫⁻ y in closedBall x r, ‖h y‖ₑ ∂μ ≤
      M * ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - 1 + α))) {x x' : E} (hxx' : 0 < dist x x') :
    ‖(divKernel μ v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x -
        (divKernel μ v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x'‖ₑ ≤
      M * ENNReal.ofReal (divHolderConst μ α * dist x x' ^ α) := by
  set δ := dist x x'
  set c := ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹
  set A := (2 : ℝ) ^ ((finrank ℝ E : ℝ) - 1) / (1 - 2 ^ (-α))
  set B := (2 : ℝ) ^ ((finrank ℝ E : ℝ) - 1 + α) / (1 - 2 ^ (α - 1))
  set K := (1 + (finrank ℝ E : ℝ)) * (2 : ℝ) ^ (finrank ℝ E : ℝ)
  have hA : 0 ≤ A := div_nonneg (by positivity)
    (sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)))
  have hB : 0 ≤ B := div_nonneg (by positivity)
    (sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)))
  simp only [convolution_lsmul_swap, smul_eq_mul]
  rw [← integral_sub (integrable_divKernel_sub_mul v x hh hMt hα hM)
      (integrable_divKernel_sub_mul v x' hh hMt hα hM)]
  simp_rw [← sub_mul]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  simp_rw [eNorm_mul]
  -- Near `x` each kernel is integrated separately; away from `x` their difference decays.
  have hnear := setLIntegral_ball_enorm_divKernel_sub_sub_mul_le v hh hα hM (x := x) (x' := x')
    hxx'
  have hfar := setLIntegral_enorm_divKernel_sub_sub_mul_le v hxx' hα hα1 hM
  have hcompl : (ball x (2 * δ))ᶜ = {y | 2 * δ ≤ dist y x} := by
    ext y
    simp [mem_ball]
  rw [← lintegral_add_compl _ measurableSet_ball, hcompl]
  refine (add_le_add hnear hfar).trans_eq ?_
  rw [← mul_add, ← mul_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 2
  have hδ : δ * (2 * δ) ^ (α - 1) = 2 ^ (α - 1) * δ ^ α := by
    rw [Real.mul_rpow zero_le_two hxx'.le, Real.rpow_sub_one hxx'.ne']
    field_simp
  rw [Real.mul_rpow zero_le_two hxx'.le, Real.mul_rpow zero_le_three hxx'.le, divHolderConst, hv]
  linear_combination c * K * B * hδ


/-- **The field is `α`-Hölder.** Summing the estimates `enorm_convolution_divKernel_sub_le` of its
components along an orthonormal basis, the field of a function whose mass on balls of radius `r` is
at most `N r^(d - 1 + α)` moves by at most `d K N dist x x' ^ α`. -/
private theorem dist_divField_le (hh : Integrable h μ) {N : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hM : ∀ x r, 0 < r → ∫⁻ y in closedBall x r, ‖h y‖ₑ ∂μ ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - 1 + α))) (x x' : E) :
    dist (divField μ h x) (divField μ h x') ≤
      (finrank ℝ E : ℝ) * divHolderConst μ α * N * dist x x' ^ α := by
  have hK : 0 ≤ divHolderConst μ α := divHolderConst_nonneg μ hα hα1
  set b := stdOrthonormalBasis ℝ E
  -- Each component of the field is `α`-Hölder with constant `K N`, `K = divHolderConst μ α`.
  have hcomp (i : Fin (finrank ℝ E)) {x x' : E} (hxx' : 0 < dist x x') :
      ‖(divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x -
          (divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x'‖ ≤
        divHolderConst μ α * N * dist x x' ^ α := by
    have h1 := enorm_convolution_divKernel_sub_le (b.orthonormal.1 i) hh ENNReal.coe_ne_top hα
      hα1 hM hxx'
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul N.coe_nonneg,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    linarith
  rcases (dist_nonneg (x := x) (y := x')).eq_or_lt with h0 | hxx'
  · rw [(dist_eq_zero.1 h0.symm), dist_self]
    positivity
  calc dist (divField μ h x) (divField μ h x')
      = ‖∑ i, ((divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x -
          (divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x') • b i‖ := by
        rw [dist_eq_norm, divField_apply, divField_apply, ← Finset.sum_sub_distrib]
        simp only [b, sub_smul]
    _ ≤ ∑ i, ‖((divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x -
          (divKernel μ (b i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x') • b i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℝ E), divHolderConst μ α * N * dist x x' ^ α := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, b.orthonormal.1 i, mul_one]
        exact hcomp i hxx'
    _ = (finrank ℝ E : ℝ) * divHolderConst μ α * N * dist x x' ^ α := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Morrey

/-- **Data in a Morrey space are minus divergences of Hölder fields.** Let `E` be a nontrivial
finite-dimensional real inner product space of dimension `d` with an additive Haar measure `μ`, and
let `0 < α < 1`. There is a constant `C` such that every measurable, compactly supported `h` in the
Morrey space `L^{1, d - 1 + α}(E)` with `‖h‖_{L^{1, d - 1 + α}(E)} ≤ M`, that is with
`∫_{B(x, r)} |h| ≤ M r^(d - 1 + α)` on every closed ball, is minus the divergence of an `α`-Hölder
field `H` with Hölder constant `C M`: `∫ ⟪H, ∇φ⟫ = ∫ h φ` for every `C¹` function `φ` with compact
support, so that `-div H = h` weakly. One may take for `H` the gradient of the Newtonian potential
of `h`.

By Hölder's inequality, `L^q(E) ⊆ L^{1, d - 1 + α}(E)` for `q = d / (1 - α)`
(`TauCeti.MeasureTheory.morreyNormPow_le_eLpNorm_rpow_mul`), so this covers compactly supported
`L^q` data, `q > d`, with `α = 1 - d / q`. -/
theorem exists_holderWith_and_integral_inner_gradient_eq_of_morreyNormPow_le
    [FiniteDimensional ℝ E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ (h : E → ℝ) (M : ℝ≥0), AEStronglyMeasurable h μ → HasCompactSupport h →
      MeasureTheory.morreyNormPow μ univ 1 ((finrank ℝ E : ℝ) - 1 + α) h ≤ M →
      ∃ H : E → E, HolderWith (C * M) α H ∧
        ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          ∫ x, ⟪H x, ∇ φ x⟫_ℝ ∂μ = ∫ x, h x * φ x ∂μ := by
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  set K := divHolderConst μ α
  have hK : 0 ≤ K := divHolderConst_nonneg μ hα' hα1'
  refine ⟨((finrank ℝ E : ℝ) * K).toNNReal, fun h M hhm hhc hM => ?_⟩
  set lam : ℝ := (finrank ℝ E : ℝ) - 1 + α
  -- The Morrey bound bounds the mass of `|h|` on every closed ball.
  have hgrowth (x : E) (r : ℝ) (hr : 0 < r) :
      ∫⁻ y in closedBall x r, ‖h y‖ₑ ∂μ ≤ (M : ℝ≥0∞) * ENNReal.ofReal (r ^ lam) := by
    have h1 := MeasureTheory.setLIntegral_closedBall_le_morreyNormPow_of_mem (μ := μ) (p := 1)
      (f := h) (lam := lam) (mem_univ x) hr
    simp only [ENNReal.rpow_one, Measure.restrict_univ] at h1
    exact h1.trans (by rw [mul_comm]; gcongr)
  have hhi : Integrable h μ :=
    MeasureTheory.integrable_of_hasCompactSupport_of_morreyNormPow_ne_top hhm hhc
      (hM.trans_lt ENNReal.coe_lt_top).ne
  refine ⟨divField μ h, ?_, fun φ hφ hφc => integral_inner_divField_gradient hhi hhc hφ hφc⟩
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le fun x _ x' _ => ?_)
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
  exact dist_divField_le hhi hα' hα1' hgrowth x x'


/-- The field of an integrable, compactly supported datum is almost everywhere strongly
measurable. -/
private theorem aestronglyMeasurable_divField [FiniteDimensional ℝ E] [BorelSpace E]
    [Nontrivial E] [μ.IsAddHaarMeasure] {h : E → ℝ} (hhi : Integrable h μ)
    (hhc : HasCompactSupport h) : AEStronglyMeasurable (divField μ h) μ := by
  simp only [funext (divField_apply μ h)]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
    (hhc.locallyIntegrable_convolution_right _ (locallyIntegrable_divKernel μ _)
      hhi).aestronglyMeasurable.smul_const _

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
  have hmeas : AEStronglyMeasurable (divField μ h) μ := aestronglyMeasurable_divField hhi hhc
  refine ⟨divField μ h, hmeas, ?_, fun φ hφ hφc ↦ integral_inner_divField_gradient hhi hhc hφ hφc⟩
  calc eLpNorm (divField μ h) p μ
      ≤ (((finrank ℝ E : ℝ≥0) * ((finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1))⁻¹.toNNReal :
          ℝ≥0) : ℝ≥0∞) * eLpNorm (rieszPotential μ 1 h) p μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hmeas (ae_of_all _ (enorm_divField_le h)) _
    _ ≤ _ * (C * eLpNorm h q μ) := by gcongr; exact hC h
    _ = _ := by push_cast; ring

/-- **Compactly supported integrable data are minus divergences of fields controlled on bounded
sets.** Let `E` be a nontrivial finite-dimensional real inner product space of dimension `d` with
an additive Haar measure `μ`. Every integrable `h` with compact support is minus the divergence of
a field `H`: `∫ ⟪H, ∇φ⟫ = ∫ h φ` for every `C¹` function `φ` with compact support. On every bounded
set `Ω` off which `h` vanishes, `H` is controlled in every `Lᵖ`, `1 ≤ p ≤ ∞`, by

`‖H‖_{Lᵖ(Ω)} ≤ d diam(Ω) ‖h‖_{Lᵖ(Ω)}`.

Unlike `TauCeti.exists_eLpNorm_le_and_integral_inner_gradient_eq`, the exponent is not raised,
and the estimate holds in every dimension, including `d = 1`, and at `p = 1` and `p = ∞`; the
price is the factor `diam Ω`, which is the scaling of one derivative. The field is the gradient of
the Newtonian potential of `h`, pointwise at most `(μ(B(0, 1)))⁻¹` times the Riesz potential of
order one of `h`, and on `Ω` that potential is bounded in `Lᵖ(Ω)` by `d μ(B(0, 1)) diam(Ω)` times
`‖h‖_{Lᵖ(Ω)}` (`TauCeti.eLpNorm_rieszPotential_restrict_le`). -/
theorem exists_eLpNorm_restrict_le_and_integral_inner_gradient_eq [FiniteDimensional ℝ E]
    [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure] {h : E → ℝ}
    (hhi : Integrable h μ) (hhc : HasCompactSupport h) :
    ∃ H : E → E, AEStronglyMeasurable H μ ∧
      (∀ {Ω : Set E}, Bornology.IsBounded Ω → (∀ x ∉ Ω, h x = 0) →
        ∀ {p : ℝ≥0∞}, 1 ≤ p →
          eLpNorm H p (μ.restrict Ω) ≤
            ENNReal.ofReal (finrank ℝ E * diam Ω) * eLpNorm h p (μ.restrict Ω)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        ∫ x, ⟪H x, ∇ φ x⟫_ℝ ∂μ = ∫ x, h x * φ x ∂μ := by
  have hmeas : AEStronglyMeasurable (divField μ h) μ := aestronglyMeasurable_divField hhi hhc
  refine ⟨divField μ h, hmeas, fun {Ω} hb hh0 {p} hp ↦ ?_,
    fun φ hφ hφc ↦ integral_inner_divField_gradient hhi hhc hφ hφc⟩
  set d : ℝ := (finrank ℝ E : ℝ)
  set ω : ℝ := μ.real (ball (0 : E) 1)
  have hd : 0 < d := Nat.cast_pos.2 Module.finrank_pos
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  -- Off `Ω` the datum vanishes, so its Riesz potential only integrates over `Ω`.
  have hriesz : rieszPotential μ 1 h = rieszPotential (μ.restrict Ω) 1 h := by
    ext x
    rw [rieszPotential_def, rieszPotential_def, setLIntegral_eq_of_support_subset]
    intro y hy
    by_contra hyΩ
    simp [hh0 y hyΩ] at hy
  calc eLpNorm (divField μ h) p (μ.restrict Ω)
      ≤ (((finrank ℝ E : ℝ≥0) * ((finrank ℝ E : ℝ) * ω)⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) *
          eLpNorm (rieszPotential μ 1 h) p (μ.restrict Ω) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hmeas.restrict (ae_of_all _ (enorm_divField_le h)) _
    _ ≤ (((finrank ℝ E : ℝ≥0) * ((finrank ℝ E : ℝ) * ω)⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) *
          (ENNReal.ofReal (d * ω / 1 * diam Ω ^ (1 : ℝ)) * eLpNorm h p (μ.restrict Ω)) := by
        rw [hriesz]
        gcongr
        exact eLpNorm_rieszPotential_restrict_le hb one_pos hp h
    _ = ENNReal.ofReal (d * diam Ω) * eLpNorm h p (μ.restrict Ω) := by
        rw [← mul_assoc, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        push_cast
        rw [Real.coe_toNNReal _ (by positivity), Real.rpow_one, div_one]
        have hd' : (finrank ℝ E : ℝ) ≠ 0 := hd.ne'
        field_simp

/-- **Integrable data on a ball are minus divergences of fields controlled on the ball.** Let `E`
be a nontrivial finite-dimensional real inner product space of dimension `d` with an additive Haar
measure `μ`, and let `f` be integrable on the ball `B = B(x₀, r)`. There is a field `H` with
`∫_B ⟪H, ∇φ⟫ = ∫_B f φ` for every `C¹` function `φ` with compact support in `B`, so that
`-div H = f` weakly in `B`, controlled in every `Lᵖ(B)`, `1 ≤ p ≤ ∞`, by

`‖H‖_{Lᵖ(B)} ≤ 2 d r ‖f‖_{Lᵖ(B)}`.

This is `TauCeti.exists_eLpNorm_restrict_le_and_integral_inner_gradient_eq` applied to `f` cut off
outside `B`. -/
theorem exists_eLpNorm_restrict_ball_le_and_setIntegral_inner_gradient_eq [FiniteDimensional ℝ E]
    [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure] {x₀ : E} {r : ℝ}
    (hr : 0 ≤ r) {f : E → ℝ} (hf : IntegrableOn f (ball x₀ r) μ) :
    ∃ H : E → E, AEStronglyMeasurable H μ ∧
      (∀ {p : ℝ≥0∞}, 1 ≤ p → eLpNorm H p (μ.restrict (ball x₀ r)) ≤
        ENNReal.ofReal (finrank ℝ E * (2 * r)) * eLpNorm f p (μ.restrict (ball x₀ r))) ∧
      ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball x₀ r →
        ∫ x in ball x₀ r, ⟪H x, ∇ φ x⟫_ℝ ∂μ = ∫ x in ball x₀ r, f x * φ x ∂μ := by
  -- The datum cut off outside the ball is integrable with compact support.
  have hhi : Integrable ((ball x₀ r).indicator f) μ :=
    (integrable_indicator_iff measurableSet_ball).2 hf
  have hhc : HasCompactSupport ((ball x₀ r).indicator f) :=
    HasCompactSupport.intro (isCompact_closedBall x₀ r) fun x hx =>
      indicator_of_notMem (fun hxB => hx (ball_subset_closedBall hxB)) f
  obtain ⟨H, hHm, hHle, hHeq⟩ := exists_eLpNorm_restrict_le_and_integral_inner_gradient_eq μ hhi hhc
  refine ⟨H, hHm, fun {p} hp => ?_, fun φ hφ1 hφc hφs => ?_⟩
  · refine (hHle isBounded_ball (fun x hx => indicator_of_notMem hx f) hp).trans ?_
    rw [eLpNorm_congr_ae (indicator_ae_eq_restrict measurableSet_ball.nullMeasurableSet)]
    gcongr
    exact diam_ball hr
  calc ∫ x in ball x₀ r, ⟪H x, ∇ φ x⟫_ℝ ∂μ
      = ∫ x, ⟪H x, ∇ φ x⟫_ℝ ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [gradient, fderiv_of_notMem_tsupport ℝ fun h => hx (hφs h), map_zero,
            inner_zero_right]
    _ = ∫ x, (ball x₀ r).indicator f x * φ x ∂μ := hHeq φ hφ1 hφc
    _ = ∫ x in ball x₀ r, f x * φ x ∂μ := by
        rw [← integral_indicator measurableSet_ball]
        exact integral_congr_ae (ae_of_all _ fun x => (indicator_mul_left _ _ _).symm)

end TauCeti
