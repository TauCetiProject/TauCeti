/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The adjoint of a quantization with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) with compact spatial support,
with values in operators between complex Hilbert spaces `V` and `W`. Its left quantization
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` (`TauCeti.quantizeSchwartzValue`) has a
formal adjoint, which is again a left quantization: for the adjoint symbol

`a*(y, ξ) = (∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2πθ) dθ)†`,

where `â(θ, ξ)` is the Fourier transform of the position slice `x ↦ a(x, ξ)` and `†` is the Hilbert
space adjoint, `∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(a*) v⟫` for all Schwartz functions `u` and `v`. In angular
frequency the formula reads `a*(y, ξ) = (2π)⁻ⁿ ∫ exp(-i ⟪y, η⟫) â(η / 2π, ξ - η)† dη`. The adjoint
symbol has order `m`, with estimates uniform in the position, but in general not compact spatial
support.

## Main declarations

* `TauCeti.Symbol.adjoint a ha`: the adjoint symbol `a*`, a symbol of order `m`, with its formula
  `TauCeti.Symbol.coefficient_adjoint`.
* `TauCeti.Symbol.isUniform_adjoint`: `a*` satisfies the symbol estimates uniformly in the
  position.
* `TauCeti.Symbol.spatialDeriv_adjoint`, `TauCeti.Symbol.frequencyDeriv_adjoint`: derivatives
  commute with taking adjoint symbols, `∂ (a*) = (∂ a)*`.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`: the quantization of `a*` is the
  formal adjoint of the quantization of `a`.

## The estimates

Since `a` has compact spatial support, `â(θ, ξ)` decays rapidly in `θ`, with
`(1 + ‖θ‖) ^ N ‖â(θ, ξ)‖ ≤ C_N ⟨ξ⟩ ^ m`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`). Peetre's
inequality `⟨ξ - 2πθ⟩ ^ m ≤ C ⟨θ⟩ ^ |m| ⟨ξ⟩ ^ m` then bounds the integrand by
`C ⟨ξ⟩ ^ m (1 + ‖θ‖) ^ (-(n + 1))`, which is integrable in `θ`. A position derivative of the
integrand multiplies `â` by `2πi θ_j`, giving the Fourier transform of `∂_{x_j} a`, and a frequency
derivative falls on `â`, giving the Fourier transform of `∂_{ξ_j} a`. So the derivatives of `a*`
are the adjoint symbols of the derivatives of `a`, and the estimates of every order follow from
the growth bound.

The adjoint identity is proved on the Fourier side. Plancherel's theorem and the formula
`𝓕 (Op(a) u) η = ∫ â(η - ζ, 2πζ) û(ζ) dζ`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`) give
`∫ ⟪Op(a) u, v⟫ = ∫∫ ⟪â(η - ζ, 2πζ) û(ζ), v̂(η)⟫ dζ dη`. Expanding `⟪u, Op(a*) v⟫` produces an
absolutely convergent triple integral over `y`, `η` and `θ`, and integrating out `y` first turns it
into the same double integral, after the substitution `ζ = η - θ`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped SchwartzMap RealInnerProductSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Fourier transforms of the position slices -/

section Slice

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-- The Fourier transform `â(g t, h t)` of a position slice of a symbol with compact spatial
support is continuous along continuous maps `g`, `h` into the dual position variable and the
frequency. -/
private theorem HasCompactSpatialSupport.continuous_fourier_slice
    (ha : a.HasCompactSpatialSupport) {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {g h : X → CoordinateSpace n} (hg : Continuous g) (hh : Continuous h) :
    Continuous fun t ↦ 𝓕 (fun x ↦ a.coefficient (x, h t)) (g t) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (h t₀) 1)).exists_bound_of_continuousOn
    a.contDiff_coefficient.continuous.continuousOn
  simp only [Real.fourier_eq]
  refine continuousAt_of_dominated (bound := K.indicator fun _ ↦ C) ?_ ?_ ?_ ?_
  · exact .of_forall fun t ↦ ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (a.contDiff_coefficient_slice _).continuous).aestronglyMeasurable
  · filter_upwards [(hh.tendsto t₀).eventually
      (Metric.closedBall_mem_nhds (h t₀) one_pos)] with t ht
    refine .of_forall fun x ↦ ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Circle.norm_smul]
      exact hC (x, h t) ⟨hx, ht⟩
    · simp [Set.indicator_of_notMem hx, hKa x hx]
  · exact (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  · refine .of_forall fun x ↦ ?_
    exact ((Real.continuous_fourierChar.comp (continuous_const.inner hg).neg).smul
      (a.contDiff_coefficient.continuous.comp (continuous_const.prodMk hh))).continuousAt

/-- **Differentiation of a Fourier transform in a parameter.** If `f(x, ξ)` is `C¹` and vanishes
for `x` outside a compact set, the Fourier transform of `x ↦ f(x, ξ)` at `θ` is differentiable in
`ξ`, with derivative the Fourier transform of the partial derivative in `ξ`. -/
private theorem hasFDerivAt_fourier_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : CoordinateSpace n × CoordinateSpace n → E} (hf : ContDiff ℝ 1 f)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hfK : ∀ x ∉ K, ∀ ξ, f (x, ξ) = 0)
    (θ ξ₀ : CoordinateSpace n) :
    HasFDerivAt (fun ξ ↦ 𝓕 (fun x ↦ f (x, ξ)) θ)
      (𝓕 (fun x ↦ (fderiv ℝ f (x, ξ₀)).comp (ContinuousLinearMap.inr ℝ _ _)) θ) ξ₀ := by
  have hcont : Continuous fun q ↦ fderiv ℝ f q := hf.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall ξ₀ 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  -- Outside `K` the partial derivatives vanish as well.
  have hfK' : ∀ x ∉ K, ∀ ξ, fderiv ℝ f (x, ξ) = 0 := fun x hx ξ ↦ by
    have hzero : f =ᶠ[nhds (x, ξ)] fun _ ↦ 0 :=
      Filter.eventually_of_mem ((hK.isClosed.isOpen_compl.prod isOpen_univ).mem_nhds
        ⟨hx, Set.mem_univ _⟩) fun q hq ↦ hfK q.1 hq.1 q.2
    rw [hzero.fderiv_eq, fderiv_const_apply]
  simp only [Real.fourier_eq, Circle.smul_def]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Metric.ball ξ₀ 1)
    (F := fun ξ x ↦ (𝐞 (-⟪x, θ⟫) : ℂ) • f (x, ξ))
    (F' := fun ξ x ↦ (𝐞 (-⟪x, θ⟫) : ℂ) • (fderiv ℝ f (x, ξ)).comp (ContinuousLinearMap.inr ℝ _ _))
    (bound := K.indicator fun _ ↦ C) (Metric.ball_mem_nhds ξ₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact .of_forall fun ξ ↦ ((Real.continuous_fourierChar.comp (by fun_prop)).subtype_val.smul
      (hf.continuous.comp (by fun_prop))).aestronglyMeasurable
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).subtype_val.smul
      (hf.continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun x hx ↦ by simp [hfK x hx])
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).subtype_val.smul
      ((hcont.comp (by fun_prop)).clm_comp continuous_const)).aestronglyMeasurable
  · refine .of_forall fun x ξ hξ ↦ ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, norm_smul, Circle.norm_coe, one_mul]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine (mul_le_of_le_one_right (norm_nonneg _)
        (ContinuousLinearMap.norm_inr_le_one _ _ _)).trans ?_
      exact hC (x, ξ) ⟨hx, Metric.ball_subset_closedBall hξ⟩
    · simp [Set.indicator_of_notMem hx, hfK' x hx]
  · exact (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  · refine .of_forall fun x ξ _ ↦ ?_
    exact ((hf.differentiable one_ne_zero (x, ξ)).hasFDerivAt.comp ξ
      (hasFDerivAt_prodMk_right x ξ)).const_smul _

/-- `hasFDerivAt_fourier_slice` with the derivative written in coordinates: its value on the
coordinate vector `e_j` is the Fourier transform of `x ↦ ∂_{ξ_j} f(x, ξ₀)`. -/
private theorem hasFDerivAt_fourier_slice_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : CoordinateSpace n × CoordinateSpace n → E} (hf : ContDiff ℝ 1 f)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hfK : ∀ x ∉ K, ∀ ξ, f (x, ξ) = 0)
    (θ ξ₀ : CoordinateSpace n) :
    HasFDerivAt (fun ξ ↦ 𝓕 (fun x ↦ f (x, ξ)) θ)
      (∑ j, (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j).smulRight
        (𝓕 (fun x ↦ fderiv ℝ f (x, ξ₀) (0, EuclideanSpace.single j 1)) θ)) ξ₀ := by
  refine (hasFDerivAt_fourier_slice hf hK hfK θ ξ₀).congr_fderiv
    (ContinuousLinearMap.ext fun h ↦ ?_)
  have hcont : Continuous fun q ↦ fderiv ℝ f q := hf.continuous_fderiv one_ne_zero
  have hzero : ∀ x ∉ K, fderiv ℝ f (x, ξ₀) = 0 := fun x hx ↦ by
    have hz : f =ᶠ[nhds (x, ξ₀)] fun _ ↦ 0 :=
      Filter.eventually_of_mem ((hK.isClosed.isOpen_compl.prod isOpen_univ).mem_nhds
        ⟨hx, Set.mem_univ _⟩) fun q hq ↦ hfK q.1 hq.1 q.2
    rw [hz.fderiv_eq, fderiv_const_apply]
  have hint : Integrable fun x ↦ (fderiv ℝ f (x, ξ₀)).comp (ContinuousLinearMap.inr ℝ _ _) :=
    ((hcont.comp (by fun_prop)).clm_comp continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun x hx ↦ by simp [hzero x hx])
  have hpt : ∀ x, fderiv ℝ f (x, ξ₀) (0, h) =
      ∑ j, h j • fderiv ℝ f (x, ξ₀) (0, EuclideanSpace.single j 1) := fun x ↦ by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
    have hsum : ((0 : CoordinateSpace n), ∑ i, h i • EuclideanSpace.single i (1 : ℝ)) =
        ∑ i, h i • ((0 : CoordinateSpace n), EuclideanSpace.single i (1 : ℝ)) :=
      Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
    rw [hsum, map_sum]
    simp only [map_smul]
  have hj : ∀ j, Integrable fun x ↦ (𝐞 (-⟪x, θ⟫) : ℂ) •
      (h j • fderiv ℝ f (x, ξ₀) (0, EuclideanSpace.single j 1)) := fun j ↦
    ((Real.continuous_fourierChar.comp (by fun_prop)).subtype_val.smul
      (((hcont.comp (by fun_prop)).clm_apply continuous_const).const_smul
        _)).integrable_of_hasCompactSupport
          (HasCompactSupport.intro hK fun x hx ↦ by simp [hzero x hx])
  rw [Real.fourier_continuousLinearMap_apply hint]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hpt,
    sum_apply, ContinuousLinearMap.smulRight_apply, Real.fourier_eq,
    Circle.smul_def, Finset.smul_sum]
  rw [integral_finsetSum _ fun j _ ↦ hj j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← integral_smul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  exact smul_comm _ _ _

/-- The Fourier transform of a position slice of `∂_{x_j} a` is `2πi θ_j` times that of `a`. -/
private theorem HasCompactSpatialSupport.fourier_spatialDeriv_slice
    (ha : a.HasCompactSpatialSupport) (j : Fin n) (θ ξ : CoordinateSpace n) :
    𝓕 (fun x ↦ (Symbol.spatialDeriv j a).coefficient (x, ξ)) θ =
      ((2 * π * Complex.I * θ j : ℂ)) • 𝓕 (fun x ↦ a.coefficient (x, ξ)) θ := by
  have hslice : (fun x ↦ (Symbol.spatialDeriv j a).coefficient (x, ξ)) =
      fun x ↦ fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x (EuclideanSpace.single j 1) := by
    funext x
    rw [← fderiv_coefficient_single]
  rw [hslice, fourier_fderiv_apply ((a.contDiff_coefficient_slice ξ).of_le (by simp))
    (ha.hasCompactSupport_slice ξ), EuclideanSpace.inner_single_right, one_mul, conj_trivial]

/-- The decay of `â(θ, ξ - 2πθ)`: for a symbol of order `m` with compact spatial support,
`‖â(θ, ξ - 2πθ)‖ ≤ C (1 + ‖θ‖) ^ (-(n + 1)) ⟨ξ⟩ ^ m`, which is integrable in `θ`. The decay of `â`
in its first variable absorbs the growth of Peetre's inequality in the shift `2πθ`. -/
private theorem HasCompactSpatialSupport.exists_norm_fourier_slice_sub_le
    (ha : a.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ θ ξ : CoordinateSpace n,
      ‖𝓕 (fun x ↦ a.coefficient (x, ξ - (2 * π) • θ)) θ‖ ≤
        C * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
  set k := ⌈|m|⌉₊
  obtain ⟨C₀, hC₀, hdecay⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le (n + 1 + k)
  refine ⟨C₀ * 2 ^ (|m| / 2) * (2 * π) ^ |m|, by positivity, fun θ ξ ↦ ?_⟩
  set t := 1 + ‖θ‖
  have ht : 0 < t := by positivity
  have h1 : 1 ≤ t := le_add_of_nonneg_right (norm_nonneg θ)
  -- Peetre's inequality for the shift by `2πθ`.
  have hpeetre := one_add_norm_sq_rpow_le_mul_sub m (ξ - (2 * π) • θ) ξ
  have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul (c := 2 * π)
    (by linarith [Real.two_le_pi]) |m| (x := ξ - (2 * π) • θ - ξ) (y := θ)
    (by rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
  rw [abs_abs] at hscale
  -- The bracket `⟨θ⟩ ^ |m|` is at most `(1 + ‖θ‖) ^ k`.
  have hbr : (1 + ‖θ‖ ^ 2) ^ (|m| / 2) ≤ t ^ k := by
    calc (1 + ‖θ‖ ^ 2) ^ (|m| / 2) ≤ (t ^ 2) ^ (|m| / 2) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg θ]) (by positivity)
      _ = t ^ |m| := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
          ring_nf
      _ ≤ t ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
      _ = t ^ k := Real.rpow_natCast t k
  have hF := hdecay θ (ξ - (2 * π) • θ)
  have hpow : t ^ (-((n : ℝ) + 1)) * t ^ (n + 1 + k) = t ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht, ← Real.rpow_natCast]
    push_cast
    ring_nf
  have hkey : t ^ (n + 1 + k) * ‖𝓕 (fun x ↦ a.coefficient (x, ξ - (2 * π) • θ)) θ‖ ≤
      t ^ (n + 1 + k) * (C₀ * 2 ^ (|m| / 2) * (2 * π) ^ |m| *
        (t ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) := by
    refine hF.trans ?_
    calc C₀ * (1 + ‖ξ - (2 * π) • θ‖ ^ 2) ^ (m / 2)
        ≤ C₀ * (2 ^ (|m| / 2) * ((2 * π) ^ |m| * t ^ k) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          gcongr
          refine hpeetre.trans ?_
          gcongr
          exact hscale.trans (by gcongr)
      _ = C₀ * 2 ^ (|m| / 2) * (2 * π) ^ |m| *
            ((t ^ (-((n : ℝ) + 1)) * t ^ (n + 1 + k)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          rw [hpow]
          ring
      _ = _ := by ring
  exact le_of_mul_le_mul_left hkey (by positivity)

end Slice

/-! ### Differentiating the shifted Fourier integral -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The real-linear map `w ↦ ∑ⱼ w.1 j • A j + ∑ⱼ w.2 j • B j` on `ℝⁿ × ℝⁿ`, with values on the
coordinate vectors given by `A` and `B`. -/
private def coordCLM (A B : Fin n → E) : CoordinateSpace n × CoordinateSpace n →L[ℝ] E :=
  ∑ j, ((EuclideanSpace.proj j).comp (ContinuousLinearMap.fst ℝ _ _)).smulRight (A j) +
    ∑ j, ((EuclideanSpace.proj j).comp (ContinuousLinearMap.snd ℝ _ _)).smulRight (B j)

private theorem coordCLM_apply (A B : Fin n → E) (w : CoordinateSpace n × CoordinateSpace n) :
    coordCLM A B w = ∑ j, w.1 j • A j + ∑ j, w.2 j • B j := by
  simp [coordCLM]

private theorem norm_coordCLM_le (A B : Fin n → E) :
    ‖coordCLM A B‖ ≤ ∑ j, ‖A j‖ + ∑ j, ‖B j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  rw [coordCLM_apply, add_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_) <;>
    rw [norm_smul, mul_comm] <;> gcongr
  · exact (PiLp.norm_apply_le w.1 j).trans (norm_fst_le w)
  · exact (PiLp.norm_apply_le w.2 j).trans (norm_snd_le w)

/-- The derivative of `p ↦ exp(2πi ⟪θ, p.1⟫) S(θ, p.2 - 2πθ)` for a function `S(θ, ζ)` that is
differentiable in `ζ`, with partial derivatives `B j θ ζ`, and whose products with `2πi θ_j` are
`A j θ ζ`. -/
private theorem hasFDerivAt_fourierChar_smul_shift {S : CoordinateSpace n → CoordinateSpace n → E}
    {A B : Fin n → CoordinateSpace n → CoordinateSpace n → E}
    (hA : ∀ j θ ζ, A j θ ζ = ((2 * π * Complex.I * θ j : ℂ)) • S θ ζ)
    (hB : ∀ θ ζ, HasFDerivAt (S θ)
      (∑ j, (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j).smulRight (B j θ ζ)) ζ)
    (θ : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
        (𝐞 ⟪θ, p.1⟫ : ℂ) • S θ (p.2 - (2 * π) • θ))
      (coordCLM (fun j ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) • A j θ (p.2 - (2 * π) • θ))
        (fun j ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) • B j θ (p.2 - (2 * π) • θ))) p := by
  have hc := (Real.hasDerivAt_fourierChar ⟪θ, p.1⟫).hasFDerivAt.comp p
    ((innerSL ℝ θ).hasFDerivAt.comp p hasFDerivAt_fst)
  have hS : HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦ S θ (p.2 - (2 * π) • θ))
      ((∑ j, (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j).smulRight
        (B j θ (p.2 - (2 * π) • θ))).comp
        (ContinuousLinearMap.snd ℝ _ _)) p :=
    (hB θ _).comp p (hasFDerivAt_snd.sub_const _)
  refine (hc.smul hS).congr_fderiv (ContinuousLinearMap.ext fun w ↦ ?_)
  simp only [coordCLM_apply, hA, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    innerSL_apply_apply, Function.comp_apply]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.proj, Finset.smul_sum]
  rw [add_comm]
  congr 1
  · simp only [← Complex.coe_smul, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [real_inner_comm, PiLp.inner_apply]
    rw [smul_eq_mul, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  · exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _

private theorem continuous_coordCLM {X : Type*} [TopologicalSpace X] {A B : Fin n → X → E}
    (hA : ∀ j, Continuous (A j)) (hB : ∀ j, Continuous (B j)) :
    Continuous fun t ↦ coordCLM (fun j ↦ A j t) (fun j ↦ B j t) := by
  unfold coordCLM
  refine (continuous_finsetSum _ fun j _ ↦ ?_).add (continuous_finsetSum _ fun j _ ↦ ?_)
  · exact (ContinuousLinearMap.smulRightL ℝ _ E _).continuous.comp (hA j)
  · exact (ContinuousLinearMap.smulRightL ℝ _ E _).continuous.comp (hB j)

/-- **Differentiation under the integral sign** for `p ↦ ∫ exp(2πi ⟪θ, p.1⟫) S(θ, p.2 - 2πθ) dθ`:
if the functions `A j` and `B j` of `hasFDerivAt_fourierChar_smul_shift` are dominated by one
integrable function of `θ` for `p.2` near `p₀.2`, the integral is differentiable at `p₀`, and its
derivative on the coordinate vectors is the integral of `A j` and `B j`. -/
private theorem hasFDerivAt_integral_fourierChar_smul_shift
    {S : CoordinateSpace n → CoordinateSpace n → E}
    {A B : Fin n → CoordinateSpace n → CoordinateSpace n → E}
    (hA : ∀ j θ ζ, A j θ ζ = ((2 * π * Complex.I * θ j : ℂ)) • S θ ζ)
    (hB : ∀ θ ζ, HasFDerivAt (S θ)
      (∑ j, (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j).smulRight (B j θ ζ)) ζ)
    (hSc : ∀ ξ, Continuous fun θ ↦ S θ (ξ - (2 * π) • θ))
    (hAc : ∀ j ξ, Continuous fun θ ↦ A j θ (ξ - (2 * π) • θ))
    (hBc : ∀ j ξ, Continuous fun θ ↦ B j θ (ξ - (2 * π) • θ))
    (hSi : ∀ ξ, Integrable fun θ ↦ S θ (ξ - (2 * π) • θ))
    {g : CoordinateSpace n → ℝ} (hg : Integrable g) (p₀ : CoordinateSpace n × CoordinateSpace n)
    (hbound : ∀ θ, ∀ ξ ∈ Metric.ball p₀.2 1, ∀ j,
      ‖A j θ (ξ - (2 * π) • θ)‖ ≤ g θ ∧ ‖B j θ (ξ - (2 * π) • θ)‖ ≤ g θ) :
    HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
        ∫ θ, (𝐞 ⟪θ, p.1⟫ : ℂ) • S θ (p.2 - (2 * π) • θ))
      (coordCLM (fun j ↦ ∫ θ, (𝐞 ⟪θ, p₀.1⟫ : ℂ) • A j θ (p₀.2 - (2 * π) • θ))
        (fun j ↦ ∫ θ, (𝐞 ⟪θ, p₀.1⟫ : ℂ) • B j θ (p₀.2 - (2 * π) • θ))) p₀ := by
  have he : ∀ y : CoordinateSpace n, Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, y⟫ : ℂ) :=
    fun y ↦ (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).subtype_val
  have hAi : ∀ j, Integrable fun θ ↦ (𝐞 ⟪θ, p₀.1⟫ : ℂ) • A j θ (p₀.2 - (2 * π) • θ) := fun j ↦
    hg.mono' ((he _).smul (hAc j _)).aestronglyMeasurable (.of_forall fun θ ↦ by
      rw [norm_smul, Circle.norm_coe, one_mul]
      exact (hbound θ p₀.2 (Metric.mem_ball_self one_pos) j).1)
  have hBi : ∀ j, Integrable fun θ ↦ (𝐞 ⟪θ, p₀.1⟫ : ℂ) • B j θ (p₀.2 - (2 * π) • θ) := fun j ↦
    hg.mono' ((he _).smul (hBc j _)).aestronglyMeasurable (.of_forall fun θ ↦ by
      rw [norm_smul, Circle.norm_coe, one_mul]
      exact (hbound θ p₀.2 (Metric.mem_ball_self one_pos) j).2)
  -- The derivative of the integrand is dominated by `2n g(θ)` for `p` near `p₀`.
  have hb : ∀ θ, ∀ p ∈ Metric.ball p₀ 1,
      ‖coordCLM (fun j ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) • A j θ (p.2 - (2 * π) • θ))
        (fun j ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) • B j θ (p.2 - (2 * π) • θ))‖ ≤ (2 * n) * g θ := by
    intro θ p hp
    have hp2 : p.2 ∈ Metric.ball p₀.2 1 :=
      lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) (Metric.mem_ball.1 hp)
    refine (norm_coordCLM_le _ _).trans ?_
    simp only [norm_smul, Circle.norm_coe, one_mul]
    calc ∑ j, ‖A j θ (p.2 - (2 * π) • θ)‖ + ∑ j, ‖B j θ (p.2 - (2 * π) • θ)‖
        ≤ ∑ _j : Fin n, g θ + ∑ _j : Fin n, g θ :=
          add_le_add (Finset.sum_le_sum fun j _ ↦ (hbound θ p.2 hp2 j).1)
            (Finset.sum_le_sum fun j _ ↦ (hbound θ p.2 hp2 j).2)
      _ = (2 * n) * g θ := by simp; ring
  -- Differentiate under the integral sign, then compute the integrated derivative coordinatewise.
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (s := Metric.ball p₀ 1)
    (F := fun p θ ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) • S θ (p.2 - (2 * π) • θ))
    (F' := fun p θ ↦ coordCLM (fun j ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) • A j θ (p.2 - (2 * π) • θ))
      (fun j ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) • B j θ (p.2 - (2 * π) • θ)))
    (bound := fun θ ↦ (2 * n) * g θ) (Metric.ball_mem_nhds p₀ one_pos)
    (.of_forall fun p ↦ ((he _).smul (hSc _)).aestronglyMeasurable)
    ((hSi p₀.2).norm.mono' ((he _).smul (hSc _)).aestronglyMeasurable
      (.of_forall fun θ ↦ by rw [norm_smul, Circle.norm_coe, one_mul]))
    (continuous_coordCLM (fun j ↦ (he _).smul (hAc j _))
      (fun j ↦ (he _).smul (hBc j _))).aestronglyMeasurable
    (.of_forall hb) (hg.const_mul _)
    (.of_forall fun θ p _ ↦ hasFDerivAt_fourierChar_smul_shift hA hB θ p)
  refine key.congr_fderiv (ContinuousLinearMap.ext fun w ↦ ?_)
  have hint : Integrable fun θ ↦ coordCLM (fun j ↦ (𝐞 ⟪θ, p₀.1⟫ : ℂ) • A j θ (p₀.2 - (2 * π) • θ))
      (fun j ↦ (𝐞 ⟪θ, p₀.1⟫ : ℂ) • B j θ (p₀.2 - (2 * π) • θ)) :=
    (hg.const_mul (2 * n)).mono' (continuous_coordCLM (fun j ↦ (he _).smul (hAc j _))
      (fun j ↦ (he _).smul (hBc j _))).aestronglyMeasurable
      (.of_forall fun θ ↦ hb θ p₀ (Metric.mem_ball_self one_pos))
  rw [ContinuousLinearMap.integral_apply hint]
  simp only [coordCLM_apply]
  have hA' : ∀ j, Integrable fun θ ↦
      w.1 j • ((𝐞 ⟪θ, p₀.1⟫ : ℂ) • A j θ (p₀.2 - (2 * π) • θ)) := fun j ↦ (hAi j).smul _
  have hB' : ∀ j, Integrable fun θ ↦
      w.2 j • ((𝐞 ⟪θ, p₀.1⟫ : ℂ) • B j θ (p₀.2 - (2 * π) • θ)) := fun j ↦ (hBi j).smul _
  rw [integral_add (integrable_finsetSum _ fun j _ ↦ hA' j)
    (integrable_finsetSum _ fun j _ ↦ hB' j), integral_finsetSum _ fun j _ ↦ hA' j,
    integral_finsetSum _ fun j _ ↦ hB' j]
  simp only [integral_smul]

/-- A function on `ℝⁿ × ℝⁿ` whose derivative has `C^k` values `A j`, `B j` on the coordinate
vectors is `C^(k + 1)`. -/
private theorem contDiff_succ_of_hasFDerivAt_coordCLM
    {f : CoordinateSpace n × CoordinateSpace n → E} {k : ℕ}
    {A B : Fin n → CoordinateSpace n × CoordinateSpace n → E}
    (hf : ∀ p, HasFDerivAt f (coordCLM (fun j ↦ A j p) (fun j ↦ B j p)) p)
    (hA : ∀ j, ContDiff ℝ k (A j)) (hB : ∀ j, ContDiff ℝ k (B j)) :
    ContDiff ℝ (k + 1) f := by
  rw [contDiff_succ_iff_fderiv]
  refine ⟨fun p ↦ (hf p).differentiableAt, by simp, ?_⟩
  rw [funext fun p ↦ (hf p).fderiv]
  refine contDiff_clm_apply_iff.2 fun w ↦ ?_
  simp only [coordCLM_apply]
  exact (ContDiff.sum fun j _ ↦ (hA j).const_smul _).add
    (ContDiff.sum fun j _ ↦ (hB j).const_smul _)

end Abstract

/-! ### The left symbol of the adjoint -/

section LeftCoeff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- The coefficient `A(y, ξ) = ∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2πθ) dθ`, where `â(θ, ξ)` is the Fourier
transform of the position slice `x ↦ a(x, ξ)`. For a symbol with compact spatial support the
adjoint symbol is `A(y, ξ)†`. -/
private def leftCoeff (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    V →L[ℂ] W :=
  ∫ θ, (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, p.2 - (2 * π) • θ)) θ

variable {a : Symbol n V W m}

private theorem HasCompactSpatialSupport.continuous_leftCoeff_integrand
    (ha : a.HasCompactSpatialSupport) (p : CoordinateSpace n × CoordinateSpace n) :
    Continuous fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, p.2 - (2 * π) • θ)) θ := by
  have h₁ : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).subtype_val
  have h₂ : Continuous fun θ : CoordinateSpace n ↦
      𝓕 (fun x ↦ a.coefficient (x, p.2 - (2 * π) • θ)) θ := by
    exact ha.continuous_fourier_slice continuous_id (by fun_prop)
  exact h₁.smul h₂

private theorem integrable_one_add_norm_rpow_neg :
    Integrable fun θ : CoordinateSpace n ↦ (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) :=
  integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)

private theorem HasCompactSpatialSupport.integrable_fourier_slice_sub
    (ha : a.HasCompactSpatialSupport) (ξ : CoordinateSpace n) :
    Integrable fun θ : CoordinateSpace n ↦ 𝓕 (fun x ↦ a.coefficient (x, ξ - (2 * π) • θ)) θ := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_fourier_slice_sub_le
  exact ((integrable_one_add_norm_rpow_neg.mul_const ((1 + ‖ξ‖ ^ 2) ^ (m / 2))).const_mul
    C).mono' (ha.continuous_fourier_slice continuous_id (by fun_prop)).aestronglyMeasurable
      (.of_forall fun θ ↦ hC θ ξ)

private theorem HasCompactSpatialSupport.integrable_leftCoeff_integrand
    (ha : a.HasCompactSpatialSupport) (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, p.2 - (2 * π) • θ)) θ :=
  (ha.integrable_fourier_slice_sub p.2).norm.mono'
    (ha.continuous_leftCoeff_integrand p).aestronglyMeasurable
    (.of_forall fun θ ↦ by rw [norm_smul, Circle.norm_coe, one_mul])

/-- On the ball of radius one around `ξ₀`, the weight `⟨ξ⟩ ^ s` is at most `2 ^ |s| ⟨ξ₀⟩ ^ s`. -/
private theorem one_add_norm_sq_rpow_le_of_mem_ball {ξ ξ₀ : CoordinateSpace n}
    (hξ : ξ ∈ Metric.ball ξ₀ 1) (s : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ (s / 2) ≤ 2 ^ |s| * (1 + ‖ξ₀‖ ^ 2) ^ (s / 2) := by
  have hd : ‖ξ - ξ₀‖ < 1 := by rwa [← dist_eq_norm]
  have hb : (1 + ‖ξ - ξ₀‖ ^ 2) ^ (|s| / 2) ≤ 2 ^ (|s| / 2) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg (ξ - ξ₀)]) (by positivity)
  calc (1 + ‖ξ‖ ^ 2) ^ (s / 2)
      ≤ 2 ^ (|s| / 2) * (1 + ‖ξ - ξ₀‖ ^ 2) ^ (|s| / 2) * (1 + ‖ξ₀‖ ^ 2) ^ (s / 2) :=
        one_add_norm_sq_rpow_le_mul_sub s ξ ξ₀
    _ ≤ 2 ^ (|s| / 2) * 2 ^ (|s| / 2) * (1 + ‖ξ₀‖ ^ 2) ^ (s / 2) := by gcongr
    _ = 2 ^ |s| * (1 + ‖ξ₀‖ ^ 2) ^ (s / 2) := by
        rw [← Real.rpow_add two_pos]
        ring_nf

/-- **The derivative of `A`.** The coefficient `A(y, ξ)` of a symbol with compact spatial support
is differentiable, with partial derivatives the coefficients of `∂_{x_j} a` and `∂_{ξ_j} a`. -/
private theorem HasCompactSpatialSupport.hasFDerivAt_leftCoeff
    (ha : a.HasCompactSpatialSupport) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (leftCoeff a) (coordCLM (fun j ↦ leftCoeff (Symbol.spatialDeriv j a) p₀)
      (fun j ↦ leftCoeff (Symbol.frequencyDeriv j a) p₀)) p₀ := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  -- A common integrable bound `D (1 + ‖θ‖) ^ (-(n + 1))` for the shifted Fourier slices of all
  -- first derivatives of `a`, at frequencies within distance one of `p₀.2`.
  choose Cx hCx0 hCx using fun j ↦ (ha.spatialDeriv j).exists_norm_fourier_slice_sub_le
  choose Cξ hCξ0 hCξ using fun j ↦ (ha.frequencyDeriv j).exists_norm_fourier_slice_sub_le
  set D := ∑ j, (Cx j * (2 ^ |m| * (1 + ‖p₀.2‖ ^ 2) ^ (m / 2)) +
    Cξ j * (2 ^ |m - 1| * (1 + ‖p₀.2‖ ^ 2) ^ ((m - 1) / 2)))
  have hterm : ∀ j, Cx j * (2 ^ |m| * (1 + ‖p₀.2‖ ^ 2) ^ (m / 2)) ≤ D ∧
      Cξ j * (2 ^ |m - 1| * (1 + ‖p₀.2‖ ^ 2) ^ ((m - 1) / 2)) ≤ D := fun j ↦ by
    have hnn : ∀ i, 0 ≤ Cx i * (2 ^ |m| * (1 + ‖p₀.2‖ ^ 2) ^ (m / 2)) +
        Cξ i * (2 ^ |m - 1| * (1 + ‖p₀.2‖ ^ 2) ^ ((m - 1) / 2)) := fun i ↦ by
      have := hCx0 i
      have := hCξ0 i
      positivity
    have hle := Finset.single_le_sum (fun i _ ↦ hnn i) (Finset.mem_univ j)
    constructor <;> refine le_trans ?_ hle
    · have := hCξ0 j
      exact le_add_of_nonneg_right (by positivity)
    · have := hCx0 j
      exact le_add_of_nonneg_left (by positivity)
  -- Apply the abstract differentiation lemma to `â` and the Fourier slices of the derivatives.
  refine hasFDerivAt_integral_fourierChar_smul_shift
    (S := fun θ ζ ↦ 𝓕 (fun x ↦ a.coefficient (x, ζ)) θ)
    (A := fun j θ ζ ↦ 𝓕 (fun x ↦ (Symbol.spatialDeriv j a).coefficient (x, ζ)) θ)
    (B := fun j θ ζ ↦ 𝓕 (fun x ↦ (Symbol.frequencyDeriv j a).coefficient (x, ζ)) θ)
    (fun j θ ζ ↦ ha.fourier_spatialDeriv_slice j θ ζ) (fun θ ζ ↦ ?_)
    (fun ξ ↦ ha.continuous_fourier_slice continuous_id (by fun_prop))
    (fun j ξ ↦ (ha.spatialDeriv j).continuous_fourier_slice continuous_id (by fun_prop))
    (fun j ξ ↦ (ha.frequencyDeriv j).continuous_fourier_slice continuous_id (by fun_prop))
    (fun ξ ↦ ha.integrable_fourier_slice_sub ξ)
    (integrable_one_add_norm_rpow_neg.const_mul D) p₀ (fun θ ξ hξ j ↦ ⟨?_, ?_⟩)
  · have h := hasFDerivAt_fourier_slice_sum ((a.contDiff_coefficient).of_le (by simp)) hK hKa θ ζ
    convert h using 4 with j
    funext x
    have hx : HasFDerivAt (fun η ↦ a.coefficient (x, η))
        ((fderiv ℝ a.coefficient (x, ζ)).comp (.inr ℝ _ _)) ζ :=
      (a.contDiff_coefficient.differentiable (by simp) (x, ζ)).hasFDerivAt.comp ζ
        (hasFDerivAt_prodMk_right x ζ)
    rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil, hx.fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  · have h0 := hCx0 j
    calc _ ≤ Cx j * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := hCx j θ ξ
      _ ≤ Cx j * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) *
            (2 ^ |m| * (1 + ‖p₀.2‖ ^ 2) ^ (m / 2))) := by
          gcongr
          exact one_add_norm_sq_rpow_le_of_mem_ball hξ _
      _ = (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * (Cx j * (2 ^ |m| * (1 + ‖p₀.2‖ ^ 2) ^ (m / 2))) := by
          ring
      _ ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * D := by
          gcongr
          exact (hterm j).1
      _ = D * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := mul_comm _ _
  · have h0 := hCξ0 j
    calc _ ≤ Cξ j * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2)) := hCξ j θ ξ
      _ ≤ Cξ j * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) *
            (2 ^ |(m - 1)| * (1 + ‖p₀.2‖ ^ 2) ^ ((m - 1) / 2))) := by
          gcongr
          exact one_add_norm_sq_rpow_le_of_mem_ball hξ _
      _ = (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) *
            (Cξ j * (2 ^ |(m - 1)| * (1 + ‖p₀.2‖ ^ 2) ^ ((m - 1) / 2))) := by
          ring
      _ ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * D := by
          gcongr
          exact (hterm j).2
      _ = D * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := mul_comm _ _

/-- The coefficient `A(y, ξ)` of a symbol with compact spatial support is smooth. -/
private theorem HasCompactSpatialSupport.contDiff_leftCoeff :
    ∀ (k : ℕ) {m : ℝ} {a : Symbol n V W m}, a.HasCompactSpatialSupport →
      ContDiff ℝ k (leftCoeff a)
  | 0, _, _, ha => contDiff_zero.2 <| continuous_iff_continuousAt.2 fun p ↦
      (ha.hasFDerivAt_leftCoeff p).continuousAt
  | k + 1, _, _, ha => contDiff_succ_of_hasFDerivAt_coordCLM ha.hasFDerivAt_leftCoeff
      (fun j ↦ (ha.spatialDeriv j).contDiff_leftCoeff k)
      (fun j ↦ (ha.frequencyDeriv j).contDiff_leftCoeff k)

private theorem HasCompactSpatialSupport.contDiff_leftCoeff_infty
    (ha : a.HasCompactSpatialSupport) : ContDiff ℝ ∞ (leftCoeff a) :=
  contDiff_infty.2 fun k ↦ HasCompactSpatialSupport.contDiff_leftCoeff k ha

/-- The coordinate derivative `∂_{y_j} A` is the coefficient of `∂_{x_j} a`. -/
private theorem HasCompactSpatialSupport.coordinateDeriv_leftCoeff_fst
    (ha : a.HasCompactSpatialSupport) (j : Fin n) (y ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ leftCoeff a (y, ξ)) y =
      leftCoeff (Symbol.spatialDeriv j a) (y, ξ) := by
  have h := (ha.hasFDerivAt_leftCoeff (y, ξ)).comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y ξ)
  simp only [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp [coordCLM_apply]

/-- The coordinate derivative `∂_{ξ_j} A` is the coefficient of `∂_{ξ_j} a`. -/
private theorem HasCompactSpatialSupport.coordinateDeriv_leftCoeff_snd
    (ha : a.HasCompactSpatialSupport) (j : Fin n) (y ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ leftCoeff a (y, η)) ξ =
      leftCoeff (Symbol.frequencyDeriv j a) (y, ξ) := by
  have h := (ha.hasFDerivAt_leftCoeff (y, ξ)).comp ξ (hasFDerivAt_prodMk_right (𝕜 := ℝ) y ξ)
  simp only [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp [coordCLM_apply]

/-- The coefficient `A(y, ξ)` grows at most like `⟨ξ⟩ ^ m`, uniformly in `y`. -/
private theorem HasCompactSpatialSupport.exists_norm_leftCoeff_le
    (ha : a.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ p : CoordinateSpace n × CoordinateSpace n,
      ‖leftCoeff a p‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_sub_le
  set I := ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1))
  have hI : 0 ≤ I := integral_nonneg fun θ ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun p ↦ ?_⟩
  refine (norm_integral_le_of_norm_le ((integrable_one_add_norm_rpow_neg.mul_const
    ((1 + ‖p.2‖ ^ 2) ^ (m / 2))).const_mul C) (.of_forall fun θ ↦ ?_)).trans_eq ?_
  · rw [norm_smul, Circle.norm_coe, one_mul]
    exact hC θ p.2
  · rw [integral_const_mul, integral_mul_const]
    ring

private theorem leftCoeff_inclusion {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    leftCoeff (inclusion h a) = leftCoeff a := by
  funext p
  simp only [leftCoeff, coefficient_inclusion]

/-- Frequency derivatives of `A` along a word `β` are the coefficient `A` of a symbol of order
`m - |β|` with compact spatial support. -/
private theorem HasCompactSpatialSupport.exists_coordinateDeriv_leftCoeff_snd :
    ∀ (β : List (Fin n)) {m : ℝ} {a : Symbol n V W m}, a.HasCompactSpatialSupport →
      ∃ b : Symbol n V W (m - β.length), b.HasCompactSpatialSupport ∧ ∀ y,
        coordinateDeriv β (fun η ↦ leftCoeff a (y, η)) = fun ξ ↦ leftCoeff b (y, ξ)
  | [], m, a, ha => ⟨Symbol.inclusion (by simp) a, ha.inclusion _, fun y ↦ by
      rw [coordinateDeriv_nil, leftCoeff_inclusion]⟩
  | j :: js, m, a, ha => by
    obtain ⟨b, hb, hab⟩ := ha.exists_coordinateDeriv_leftCoeff_snd js
    refine ⟨Symbol.inclusion (by simp; linarith) (Symbol.frequencyDeriv j b),
      (hb.frequencyDeriv j).inclusion _, fun y ↦ ?_⟩
    rw [leftCoeff_inclusion, ← List.singleton_append, coordinateDeriv_append, hab y]
    funext ξ
    exact hb.coordinateDeriv_leftCoeff_snd j y ξ

/-- Position derivatives of `A` along a word `α` are the coefficient `A` of a symbol of order `m`
with compact spatial support. -/
private theorem HasCompactSpatialSupport.exists_coordinateDeriv_leftCoeff_fst :
    ∀ (α : List (Fin n)) {a : Symbol n V W m}, a.HasCompactSpatialSupport →
      ∃ b : Symbol n V W m, b.HasCompactSpatialSupport ∧ ∀ ξ,
        coordinateDeriv α (fun y ↦ leftCoeff a (y, ξ)) = fun y ↦ leftCoeff b (y, ξ)
  | [], a, ha => ⟨a, ha, fun ξ ↦ coordinateDeriv_nil _⟩
  | j :: js, a, ha => by
    obtain ⟨b, hb, hab⟩ := ha.exists_coordinateDeriv_leftCoeff_fst js
    refine ⟨Symbol.spatialDeriv j b, hb.spatialDeriv j, fun ξ ↦ ?_⟩
    rw [← List.singleton_append, coordinateDeriv_append, hab ξ]
    funext y
    exact hb.coordinateDeriv_leftCoeff_fst j y ξ

/-- The symbol estimates for `A`, uniformly in the position. -/
private theorem HasCompactSpatialSupport.exists_norm_mixedDeriv_leftCoeff_le
    (ha : a.HasCompactSpatialSupport) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ y ξ, ‖mixedDeriv α β (leftCoeff a) y ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨b, hb, hab⟩ := ha.exists_coordinateDeriv_leftCoeff_snd β
  obtain ⟨c, hc, hbc⟩ := hb.exists_coordinateDeriv_leftCoeff_fst α
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_leftCoeff_le
  refine ⟨C, hC0, fun y ξ ↦ ?_⟩
  have h : mixedDeriv α β (leftCoeff a) y ξ = leftCoeff c (y, ξ) := by
    rw [mixedDeriv_def]
    simp_rw [hab]
    rw [hbc ξ]
  rw [h]
  exact hC (y, ξ)


/-- The coefficient `A(y, ξ)` as a symbol of order `m`. -/
private def leftSymbol (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) :
    Symbol n V W m where
  coefficient := leftCoeff a
  contDiff_coefficient := ha.contDiff_leftCoeff_infty
  exists_bound _ _ α β := (ha.exists_norm_mixedDeriv_leftCoeff_le α β).imp
    fun _ hC ↦ ⟨hC.1, fun y _ ξ ↦ hC.2 y ξ⟩

end LeftCoeff

/-! ### The adjoint symbol -/

section Adjoint

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The Hilbert space adjoint `T ↦ T†`, as a real-linear map. -/
private def adjointCLM : (V →L[ℂ] W) →L[ℝ] (W →L[ℂ] V) :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ ContinuousLinearMap.adjoint T
      map_add' := map_add _
      map_smul' := fun r T ↦ by
        rw [← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal,
          Complex.coe_smul, RingHom.id_apply] }
    1 fun T ↦ by simp

private theorem adjointCLM_apply (T : V →L[ℂ] W) :
    adjointCLM T = ContinuousLinearMap.adjoint T := by
  simp [adjointCLM]

/-- **The adjoint symbol.** For a symbol `a` of order `m` with compact spatial support, the symbol
`a*(y, ξ) = (∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2πθ) dθ)†` of order `m`, where `â(θ, ξ)` is the Fourier
transform of the position slice `x ↦ a(x, ξ)` at `θ`. Its quantization is the formal adjoint of
the quantization of `a` (`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`). -/
def adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) : Symbol n W V m :=
  (leftSymbol a ha).map adjointCLM

theorem coefficient_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
    (y ξ : CoordinateSpace n) :
    (adjoint a ha).coefficient (y, ξ) = ContinuousLinearMap.adjoint
      (∫ θ, (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, ξ - (2 * π) • θ)) θ) := by
  rw [adjoint, coefficient_map, adjointCLM_apply]
  rfl

variable {a : Symbol n V W m}

private theorem HasCompactSpatialSupport.coefficient_adjoint_eq
    (ha : a.HasCompactSpatialSupport) :
    (adjoint a ha).coefficient = adjointCLM ∘ leftCoeff a :=
  funext fun p ↦ coefficient_map _ _ p

/-- The adjoint symbol satisfies its estimates uniformly in the position, although it need not
have compact spatial support. -/
theorem isUniform_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) :
    (adjoint a ha).IsUniform := by
  refine isUniform_iff.2 fun α β ↦ ?_
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_mixedDeriv_leftCoeff_le α β
  refine ⟨‖(adjointCLM : (V →L[ℂ] W) →L[ℝ] (W →L[ℂ] V))‖ * C, by positivity, fun y ξ ↦ ?_⟩
  rw [ha.coefficient_adjoint_eq,
    adjointCLM.mixedDeriv_comp_left ha.contDiff_leftCoeff_infty, mul_assoc]
  exact adjointCLM.le_opNorm_of_le (hC y ξ)

/-- A position derivative of the adjoint symbol is the adjoint symbol of the position
derivative: `∂_{y_j} a* = (∂_{x_j} a)*`. -/
theorem spatialDeriv_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
    (j : Fin n) :
    spatialDeriv j (adjoint a ha) = adjoint (spatialDeriv j a) (ha.spatialDeriv j) := by
  ext1
  funext ⟨y, ξ⟩
  rw [coefficient_spatialDeriv, ha.coefficient_adjoint_eq,
    (ha.spatialDeriv j).coefficient_adjoint_eq]
  have hf : ContDiff ℝ ([j] : List (Fin n)).length fun y ↦ leftCoeff a (y, ξ) :=
    (ha.contDiff_leftCoeff_infty.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  exact (adjointCLM.coordinateDeriv_comp_left [j] hf y).trans
    (congrArg adjointCLM (ha.coordinateDeriv_leftCoeff_fst j y ξ))

/-- A frequency derivative of the adjoint symbol is the adjoint symbol of the frequency
derivative: `∂_{ξ_j} a* = (∂_{ξ_j} a)*`. -/
theorem frequencyDeriv_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
    (j : Fin n) :
    frequencyDeriv j (adjoint a ha) = adjoint (frequencyDeriv j a) (ha.frequencyDeriv j) := by
  ext1
  funext ⟨y, ξ⟩
  rw [coefficient_frequencyDeriv, ha.coefficient_adjoint_eq,
    (ha.frequencyDeriv j).coefficient_adjoint_eq]
  have hf : ContDiff ℝ ([j] : List (Fin n)).length fun η ↦ leftCoeff a (y, η) :=
    (ha.contDiff_leftCoeff_infty.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  exact (adjointCLM.coordinateDeriv_comp_left [j] hf ξ).trans
    (congrArg adjointCLM (ha.coordinateDeriv_leftCoeff_snd j y ξ))

/-! ### The adjoint identity -/


/-- The integrand `exp(2πi ⟪η - θ, y⟫) ⟪â(θ, 2π(η - θ)) u(y), v̂(η)⟫` of the triple integral
giving `∫ ⟪u, Op(a*) v⟫`. -/
private def adjointIntegrand (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) (y η θ : CoordinateSpace n) : ℂ :=
  (𝐞 ⟪η - θ, y⟫ : ℂ) *
    inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ (u y)) (𝓕 v η)

/-- The pairing `⟪u(y), Op(a*) v (y)⟫` as an iterated integral. -/
private theorem HasCompactSpatialSupport.inner_quantizeSchwartzValue_adjoint
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) (y : CoordinateSpace n) :
    inner ℂ (u y) (quantizeSchwartzValue (adjoint a ha).coefficient v y) =
      ∫ η, ∫ θ, adjointIntegrand a u v y η θ := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_leftCoeff_le
  have hbound : ∀ ξ, ‖(adjoint a ha).coefficient (y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
    fun ξ ↦ by
      rw [ha.coefficient_adjoint_eq, Function.comp_apply, adjointCLM_apply,
        LinearIsometryEquiv.norm_map]
      exact hC (y, ξ)
  rw [quantizeSchwartzValue_def, ← integral_inner (integrable_quantizeSchwartzValue_integrand
    ((adjoint a ha).continuous_coefficient_slice y).aestronglyMeasurable hbound (𝓕 v))]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  have hint := ha.integrable_leftCoeff_integrand (y, (2 * π) • η)
  dsimp only at hint ⊢
  rw [Circle.smul_def, inner_smul_right, coefficient_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.integral_apply hint]
  have key := (innerSLFlip ℂ (𝓕 v η)).integral_comp_commSL (by simp)
    (hint.apply_continuousLinearMap (u y))
  simp only [innerSLFlip_apply_apply] at key
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun θ ↦ ?_)
  simp only [smul_apply, inner_smul_left, adjointIntegrand, ← mul_assoc,
    ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul,
    ← sub_eq_add_neg, ← inner_sub_left, smul_sub]

omit [CompleteSpace V] [CompleteSpace W] in
/-- The triple integrand is integrable: `â(θ, 2π(η - θ))` decays in `θ` and grows like `⟨η⟩ ^ m`,
which `u` and `v̂` absorb. -/
private theorem HasCompactSpatialSupport.integrable_adjointIntegrand
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    Integrable (fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
      adjointIntegrand a u v q.1 q.2.1 q.2.2) (volume.prod (volume.prod volume)) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_sub_le
  have hg : Integrable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      (1 + ‖z.1‖ ^ 2) ^ (m / 2) * ‖𝓕 v z.1‖ * (1 + ‖z.2‖) ^ (-((n : ℝ) + 1)))
      (volume.prod volume) :=
    ((𝓕 v).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).mul_prod
      integrable_one_add_norm_rpow_neg
  have hcont : Continuous fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
      adjointIntegrand a u v q.1 q.2.1 q.2.2 := by
    have h₁ : Continuous fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
        (𝐞 ⟪q.2.1 - q.2.2, q.1⟫ : ℂ) :=
      (Real.continuous_fourierChar.comp (by fun_prop)).subtype_val
    have h₂ : Continuous fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
        𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (q.2.1 - q.2.2))) q.2.2 :=
      ha.continuous_fourier_slice (by fun_prop) (by fun_prop)
    exact h₁.mul ((h₂.clm_apply (u.continuous.comp continuous_fst)).inner
      ((𝓕 v).continuous.comp (by fun_prop)))
  refine ((u.integrable.norm.mul_prod hg).const_mul (C * (2 * π) ^ |m|)).mono'
    hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  obtain ⟨y, η, θ⟩ := q
  have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul (c := 2 * π)
    (by linarith [Real.two_le_pi]) m (x := (2 * π) • η) (y := η)
    (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
  have hF : ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ‖ ≤
      C * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * ((2 * π) ^ |m| * (1 + ‖η‖ ^ 2) ^ (m / 2))) := by
    rw [smul_sub]
    refine (hC θ _).trans ?_
    gcongr
  simp only [adjointIntegrand, norm_mul, Circle.norm_coe, one_mul]
  calc ‖inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ (u y)) (𝓕 v η)‖
      ≤ ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ‖ * ‖u y‖ * ‖𝓕 v η‖ :=
        (norm_inner_le_norm _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ ≤ C * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * ((2 * π) ^ |m| * (1 + ‖η‖ ^ 2) ^ (m / 2))) *
          ‖u y‖ * ‖𝓕 v η‖ := by gcongr
    _ = C * (2 * π) ^ |m| * (‖u y‖ * ((1 + ‖η‖ ^ 2) ^ (m / 2) * ‖𝓕 v η‖ *
          (1 + ‖θ‖) ^ (-((n : ℝ) + 1)))) := by ring

/-- Integrating out the position: `∫ exp(2πi ⟪η - θ, y⟫) ⟪B u(y), w⟫ dy = ⟪B û(η - θ), w⟫`. -/
private theorem integral_adjointIntegrand (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) (η θ : CoordinateSpace n) :
    ∫ y, adjointIntegrand a u v y η θ =
      inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ (𝓕 u (η - θ))) (𝓕 v η) := by
  set B := 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ
  have hu : Integrable fun y : CoordinateSpace n ↦ (𝐞 (-⟪y, η - θ⟫) : ℂ) • u y :=
    u.integrable.norm.mono' ((Real.continuous_fourierChar.comp (by fun_prop)).subtype_val.smul
      u.continuous).aestronglyMeasurable
      (.of_forall fun y ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  have hfu : 𝓕 u (η - θ) = ∫ y, (𝐞 (-⟪y, η - θ⟫) : ℂ) • u y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp only [Circle.smul_def]
  have key := (innerSLFlip ℂ (𝓕 v η)).integral_comp_commSL (by simp) (B.integrable_comp hu)
  simp only [innerSLFlip_apply_apply] at key
  rw [hfu, ← ContinuousLinearMap.integral_comp_comm B hu, ← key]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [adjointIntegrand]
  rw [map_smul, inner_smul_left, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg,
    real_inner_comm]

omit [CompleteSpace V] in
/-- The pairing `∫ ⟪Op(a) u, v⟫` on the Fourier side, by Plancherel's theorem and the formula
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) û(ζ) dζ`. -/
private theorem HasCompactSpatialSupport.integral_inner_quantizeSchwartzValue_eq
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (v x) =
      ∫ η, ∫ ζ, inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ))
        (𝓕 v η) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le 0
  set U : 𝓢(CoordinateSpace n, W) := (ha.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (a.contDiff_quantizeSchwartzValue u)
  have hU : ⇑U = quantizeSchwartzValue a.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [← hU, ← SchwartzMap.integral_inner_fourier_fourier]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  have hint : Integrable fun ζ : CoordinateSpace n ↦
      𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ) := by
    refine (((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul
      (C * (2 * π) ^ |m|)).mono' ?_ (.of_forall fun ζ ↦ ?_)
    · exact ((ha.continuous_fourier_slice (by fun_prop) (by fun_prop)).clm_apply
        (𝓕 u).continuous).aestronglyMeasurable
    · have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul (c := 2 * π)
        (by linarith [Real.two_le_pi]) m (x := (2 * π) • ζ) (y := ζ)
        (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
      have h := hC (η - ζ) ((2 * π) • ζ)
      rw [pow_zero, one_mul] at h
      calc ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ)‖
          ≤ ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ)‖ * ‖𝓕 u ζ‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * ‖𝓕 u ζ‖ := by
            gcongr
            exact h.trans (by gcongr)
        _ = C * (2 * π) ^ |m| * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) := by ring
  dsimp only
  have key := (innerSLFlip ℂ (𝓕 v η)).integral_comp_commSL (by simp) hint
  simp only [innerSLFlip_apply_apply] at key
  rw [SchwartzMap.fourier_coe, hU, ha.fourier_quantizeSchwartzValue u η, ← key]

/-- **The adjoint of a quantization.** For a symbol `a` of order `m` with compact spatial support,
with values in operators between complex Hilbert spaces, the quantization of the adjoint symbol
`a*` is the formal adjoint of the quantization of `a`:
`∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(a*) v⟫` for all Schwartz functions `u` and `v`. -/
theorem integral_inner_quantizeSchwartzValue_adjoint (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (v x) =
      ∫ x, inner ℂ (u x) (quantizeSchwartzValue (adjoint a ha).coefficient v x) := by
  have hG := ha.integrable_adjointIntegrand u v
  simp_rw [ha.inner_quantizeSchwartzValue_adjoint u v, ha.integral_inner_quantizeSchwartzValue_eq]
  calc ∫ η, ∫ ζ, inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ)) (𝓕 v η)
      = ∫ η, ∫ θ, ∫ y, adjointIntegrand a u v y η θ := by
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        simp only [integral_adjointIntegrand]
        exact (integral_sub_left_eq_self (fun ζ ↦ inner ℂ
          (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ)) (𝓕 v η)) volume η).symm.trans
            (by simp only [sub_sub_cancel])
    _ = ∫ q : CoordinateSpace n × CoordinateSpace n, ∫ y, adjointIntegrand a u v y q.1 q.2 :=
        (integral_prod _ hG.integral_prod_right).symm
    _ = ∫ y, ∫ q : CoordinateSpace n × CoordinateSpace n, adjointIntegrand a u v y q.1 q.2 :=
        (integral_integral_swap (f := fun y (q : CoordinateSpace n × CoordinateSpace n) ↦
          adjointIntegrand a u v y q.1 q.2) hG).symm
    _ = ∫ y, ∫ η, ∫ θ, adjointIntegrand a u v y η θ :=
        integral_congr_ae (hG.prod_right_ae.mono fun y hy ↦ integral_prod _ hy)

end Adjoint

end Symbol

end TauCeti
