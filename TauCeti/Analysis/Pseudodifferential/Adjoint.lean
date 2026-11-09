/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Quantization
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Affine.MazurUlam
import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The adjoint symbol

Let `V` and `W` be complex Hilbert spaces and `a` a symbol of order `m` with values in `V →L[ℂ] W`
that vanishes for positions outside a compact set. Its **adjoint symbol** is

`a*(x, ξ) = (∫ exp(2πi ⟪η, x⟫) â(η, ξ - 2πη) dη)†`,

where `â(η, ξ)` is the Fourier transform (with Mathlib's phase `exp(-2πi ⟪y, η⟫)`) of the position
slice `y ↦ a(y, ξ)` and `†` is the Hilbert space adjoint `W →L[ℂ] V`. This file shows that `a*` is
a symbol of order `m`, with estimates uniform in the position, and that its quantization is the
formal adjoint of the quantization of `a`:

`∫ ⟪Op(a) u (x), v(x)⟫ dx = ∫ ⟪u(x), Op(a*) v (x)⟫ dx`

for Schwartz functions `u` and `v`. The adjoint symbol is the starting point of the symbol calculus
of adjoints: Taylor expanding `â(η, ξ - 2πη)` in its second variable leads to the asymptotic
expansion `a* ∼ ∑_α (1 / α!) ∂_ξ^α D_x^α a†`, whose leading term is the pointwise adjoint of `a`;
that expansion is not proved here.

## Main results

* `TauCeti.Symbol.adjoint`: the adjoint symbol `a*`, a symbol of order `m`, with its defining
  formula `TauCeti.Symbol.coefficient_adjoint`.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`: **`Op(a*)` is the formal adjoint
  of `Op(a)`** on Schwartz functions.
* `TauCeti.Symbol.isUniform_adjoint`: the estimates of `a*` are uniform in the position, so
  `Op(a*)` maps Schwartz space to itself (`TauCeti.Symbol.quantizeUniformCLM`).
* `TauCeti.Symbol.spatialDeriv_adjoint`, `TauCeti.Symbol.frequencyDeriv_adjoint`: taking the
  adjoint symbol commutes with spatial and frequency derivatives.
* `TauCeti.Symbol.adjoint_add`, `TauCeti.Symbol.adjoint_smul`: the adjoint symbol is
  conjugate-linear, and it is compatible with the inclusions of symbol classes
  (`TauCeti.Symbol.adjoint_inclusion`) and preserves smoothing symbols
  (`TauCeti.Symbol.IsSmoothing.adjoint`).

## Proof outline

By the rapid decay of `â` in its first variable and Peetre's inequality
`⟨ξ - 2πη⟩ ^ m ≤ C ⟨ξ⟩ ^ m ⟨η⟩ ^ |m|`, the integrand is bounded by `C ⟨ξ⟩ ^ m ⟨η⟩ ^ (-(n + 1))`
uniformly in the position, which gives the order-`m` bound. The derivative of the phase in a
position direction turns `â` into the Fourier transform of `∂_x a`, and a frequency derivative
falls on `â`, so differentiating under the integral sign gives `∂(a*) = (∂a)*`, from which the
symbol estimates follow by induction on the number of derivatives.

For the adjoint identity, Plancherel's theorem and the formula
`𝓕 (Op(a) u) ζ' = ∫ â(ζ' - ζ, 2πζ) (𝓕 u ζ) dζ` turn the left side into
`∫∫ ⟪𝓕 u ζ, â(ζ' - ζ, 2πζ)† (𝓕 v ζ')⟫ dζ' dζ`, while the change of variables `η = ζ' - ζ` in the
definition of `a*` shows that `Op(a*) v` is the inverse Fourier transform of
`w(ζ) = ∫ â(ζ' - ζ, 2πζ)† (𝓕 v ζ') dζ'`. The two sides then agree because the Fourier transform is
self-adjoint for the sesquilinear pairing of integrable functions.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The integrand of the adjoint symbol -/

section Integrand

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] (a : Symbol n V W m)

/-- The integrand `exp(2πi ⟪η, x⟫) â(η, ξ - 2πη)` of the adjoint symbol, before taking the Hilbert
space adjoint, where `â(η, ξ)` is the Fourier transform of the position slice `y ↦ a(y, ξ)`. -/
private def adjIntegrand (p : CoordinateSpace n × CoordinateSpace n) (η : CoordinateSpace n) :
    V →L[ℂ] W :=
  (𝐞 ⟪η, p.1⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (y, p.2 - (2 * π) • η)) η

variable {a}

/-- The integrand decays in `η` faster than every power, with the weight `⟨ξ⟩ ^ m` in the
frequency, uniformly in the position. -/
private theorem exists_norm_adjIntegrand_le (ha : a.HasCompactSpatialSupport) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ η, ‖adjIntegrand a (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨Cb, hCb0, hCb⟩ := ha.exists_norm_fourier_slice_le (r + |m|)
  refine ⟨Cb * 2 ^ (|m| / 2) * (2 * π) ^ |m|, by positivity, fun x ξ η ↦ ?_⟩
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m ξ (-((2 * π) • η))
  have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul h2π |m| (x := -((2 * π) • η)) (y := η)
    (by rw [norm_neg, norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
  rw [abs_abs] at hscale
  rw [← sub_eq_add_neg] at hpeetre
  have hη : (1 + ‖η‖ ^ 2) ^ (|m| / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m|) / 2) =
      (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  calc ‖adjIntegrand a (x, ξ) η‖
      = ‖𝓕 (fun y ↦ a.coefficient (y, ξ - (2 * π) • η)) η‖ := by
        rw [adjIntegrand, norm_smul, Circle.norm_coe, one_mul]
    _ ≤ Cb * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((2 * π) ^ |m| * (1 + ‖η‖ ^ 2) ^ (|m| / 2))) * (1 + ‖η‖ ^ 2) ^ (-(r + |m|) / 2) := by
        refine (hCb η _).trans ?_
        gcongr
        exact hpeetre.trans (by gcongr)
    _ = Cb * 2 ^ (|m| / 2) * (2 * π) ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((1 + ‖η‖ ^ 2) ^ (|m| / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m|) / 2)) := by ring
    _ = _ := by rw [hη]

private theorem continuous_adjIntegrand (ha : a.HasCompactSpatialSupport) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      adjIntegrand a q.1 q.2 := by
  have he : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      (𝐞 ⟪q.2, q.1.1⟫ : ℂ) := by
    fun_prop
  have hB : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (y, q.1.2 - (2 * π) • q.2)) q.2 := by
    have h := ha.continuous_fourier_slice.comp (by fun_prop :
      Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
        (q.2, q.1.2 - (2 * π) • q.2))
    simpa only [Function.comp_def] using h
  exact he.smul hB

/-- The weight `⟨η⟩ ^ (-(n + 1))` is integrable on `ℝⁿ`. -/
private theorem integrable_weight :
    Integrable fun η : CoordinateSpace n ↦ (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
  integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; linarith)

/-- The integrand is dominated, for frequencies in a neighbourhood of `ξ₀` and all positions, by a
multiple of the integrable weight `⟨η⟩ ^ (-(n + 1))`. -/
private theorem exists_norm_adjIntegrand_le_weight (ha : a.HasCompactSpatialSupport)
    (ξ₀ : CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ p : CoordinateSpace n × CoordinateSpace n,
      p.2 ∈ Metric.closedBall ξ₀ 1 → ∀ η,
        ‖adjIntegrand a p η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_adjIntegrand_le ha ((n : ℝ) + 1)
  have hw : Continuous fun ξ : CoordinateSpace n ↦ (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  obtain ⟨M, hM⟩ := (isCompact_closedBall ξ₀ 1).exists_bound_of_continuousOn hw.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ξ₀ (Metric.mem_closedBall_self zero_le_one))
  refine ⟨C * M, mul_nonneg hC0 hM0, fun p hp η ↦ (hC p.1 p.2 η).trans ?_⟩
  have hMp := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM p.2 hp))
  gcongr

private theorem integrable_adjIntegrand (ha : a.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) : Integrable (adjIntegrand a p) := by
  obtain ⟨C, -, hC⟩ := exists_norm_adjIntegrand_le_weight ha p.2
  exact (integrable_weight.const_mul _).mono'
    ((continuous_adjIntegrand ha).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall fun η ↦ hC p (Metric.mem_closedBall_self zero_le_one) η)

variable (a) in
/-- The coefficient `∫ exp(2πi ⟪η, x⟫) â(η, ξ - 2πη) dη`, whose pointwise adjoint is the adjoint
symbol. -/
private def adjCoeff (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ∫ η, adjIntegrand a p η

private theorem continuous_adjCoeff (ha : a.HasCompactSpatialSupport) :
    Continuous (adjCoeff a) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  obtain ⟨C, -, hC⟩ := exists_norm_adjIntegrand_le_weight ha p₀.2
  refine continuousAt_of_dominated
    (bound := fun η ↦ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2))
    (.of_forall fun p ↦ (integrable_adjIntegrand ha p).aestronglyMeasurable) ?_
    (integrable_weight.const_mul _)
    (.of_forall fun η ↦ ((continuous_adjIntegrand ha).comp
      (continuous_id.prodMk continuous_const)).continuousAt)
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (Metric.closedBall_mem_nhds p₀.2 one_pos)] with p hp
  exact .of_forall (hC p hp)

/-- **Growth of the coefficient.** `‖c(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` uniformly in the position. -/
private theorem exists_norm_adjCoeff_le (ha : a.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ, ‖adjCoeff a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_adjIntegrand_le ha ((n : ℝ) + 1)
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun η ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun x ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le (integrable_weight.const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) (.of_forall fun η ↦ hC x ξ η)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- The derivative of the integrand in the `j`-th position direction. The derivative of the phase
gives the Fourier transform of `∂_{x_j} a`, by `fourier_spatialDeriv_slice`. -/
private theorem coordinateDeriv_fst_adjIntegrand (ha : a.HasCompactSpatialSupport) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ adjIntegrand a (x, ξ) η) x =
      adjIntegrand (Symbol.spatialDeriv j a) (x, ξ) η := by
  set B := 𝓕 (fun y ↦ a.coefficient (y, ξ - (2 * π) • η)) η
  have he := (Real.hasDerivAt_fourierChar ⟪η, x⟫).hasFDerivAt.comp x
    ((innerSL ℝ η).hasFDerivAt (x := x))
  have h : HasFDerivAt (fun x ↦ adjIntegrand a (x, ξ) η) _ x := he.smul_const B
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp only [adjIntegrand, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ha.fourier_spatialDeriv_slice, smul_smul, B]
  congr 1
  rw [ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul]
  ring

/-- The derivative of the integrand in the `j`-th frequency direction. -/
private theorem coordinateDeriv_snd_adjIntegrand (ha : a.HasCompactSpatialSupport) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ adjIntegrand a (x, ξ) η) ξ =
      adjIntegrand (Symbol.frequencyDeriv j a) (x, ξ) η := by
  set c := (2 * π) • η
  have hD := ha.hasFDerivAt_fourier_slice η (ξ - c)
  have hB : HasFDerivAt (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ - c)) η)
      ((∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ a.coefficient (y, ξ)) (ξ - c)).comp
        (ContinuousLinearMap.id ℝ _)) ξ :=
    HasFDerivAt.comp (g := fun ζ ↦ 𝓕 (fun y ↦ a.coefficient (y, ζ)) η)
      (f := fun ξ ↦ ξ - c) ξ hD ((hasFDerivAt_id ξ).sub_const c)
  have h : HasFDerivAt (fun ξ ↦ adjIntegrand a (x, ξ) η) _ ξ := hB.const_smul (𝐞 ⟪η, x⟫ : ℂ)
  have hj := ha.coordinateDeriv_fourier_slice j η (ξ - c)
  rw [coordinateDeriv_cons, coordinateDeriv_nil, hD.fderiv] at hj
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, hj, adjIntegrand, c]

private theorem differentiableAt_adjIntegrand (ha : a.HasCompactSpatialSupport)
    (η : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ adjIntegrand a p η) p := by
  have he : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪η, p.1⟫ : ℂ)) p :=
    DifferentiableAt.comp (g := fun t : ℝ ↦ (𝐞 t : ℂ))
      (f := fun p : CoordinateSpace n × CoordinateSpace n ↦ ⟪η, p.1⟫) p
      (Real.differentiable_fourierChar _)
      (((innerSL ℝ η).differentiableAt).comp p differentiableAt_fst)
  have hB : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (y, p.2 - (2 * π) • η)) η) p :=
    DifferentiableAt.comp (g := fun ζ ↦ 𝓕 (fun y ↦ a.coefficient (y, ζ)) η)
      (f := fun p : CoordinateSpace n × CoordinateSpace n ↦ p.2 - (2 * π) • η) p
      (ha.hasFDerivAt_fourier_slice η _).differentiableAt (differentiableAt_snd.sub_const _)
  exact he.smul hB

private theorem fderiv_adjIntegrand_apply (ha : a.HasCompactSpatialSupport)
    (η : CoordinateSpace n) (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p ↦ adjIntegrand a p η) p v =
      ∑ j, v.1 j • adjIntegrand (Symbol.spatialDeriv j a) p η +
      ∑ j, v.2 j • adjIntegrand (Symbol.frequencyDeriv j a) p η := by
  rw [fderiv_apply_eq_sum_coordinateDeriv (differentiableAt_adjIntegrand ha η p)]
  simp only [coordinateDeriv_fst_adjIntegrand ha, coordinateDeriv_snd_adjIntegrand ha,
    Prod.mk.eta]

private theorem continuous_fderiv_adjIntegrand_apply (ha : a.HasCompactSpatialSupport)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    Continuous fun η ↦ fderiv ℝ (fun p ↦ adjIntegrand a p η) p v := by
  have hc {m' : ℝ} {a' : Symbol n V W m'} (ha' : a'.HasCompactSpatialSupport) :
      Continuous fun η ↦ adjIntegrand a' p η :=
    Continuous.comp (g := fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      adjIntegrand a' q.1 q.2) (f := fun η ↦ (p, η)) (continuous_adjIntegrand ha')
      (continuous_const.prodMk continuous_id)
  have hf : (fun η ↦ fderiv ℝ (fun p ↦ adjIntegrand a p η) p v) = fun η ↦
      ∑ j, v.1 j • adjIntegrand (Symbol.spatialDeriv j a) p η +
        ∑ j, v.2 j • adjIntegrand (Symbol.frequencyDeriv j a) p η :=
    funext fun η ↦ fderiv_adjIntegrand_apply ha η p v
  rw [hf]
  refine (continuous_finsetSum _ fun j _ ↦ ?_).add (continuous_finsetSum _ fun j _ ↦ ?_)
  · exact (hc (ha.spatialDeriv j)).const_smul (v.1 j)
  · exact (hc (ha.frequencyDeriv j)).const_smul (v.2 j)

/-- The derivative of the integrand is dominated, for frequencies near `ξ₀` and all positions, by
a multiple of the integrable weight `⟨η⟩ ^ (-(n + 1))`. -/
private theorem exists_norm_fderiv_adjIntegrand_le (ha : a.HasCompactSpatialSupport)
    (ξ₀ : CoordinateSpace n) :
    ∃ D, ∀ p : CoordinateSpace n × CoordinateSpace n, p.2 ∈ Metric.closedBall ξ₀ 1 → ∀ η,
      ‖fderiv ℝ (fun p ↦ adjIntegrand a p η) p‖ ≤
        D * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  choose C₁ hC₁0 hC₁ using fun j ↦ exists_norm_adjIntegrand_le_weight (ha.spatialDeriv j) ξ₀
  choose C₂ hC₂0 hC₂ using fun j ↦ exists_norm_adjIntegrand_le_weight (ha.frequencyDeriv j) ξ₀
  refine ⟨∑ j, C₁ j + ∑ j, C₂ j, fun p hp η ↦ ?_⟩
  refine ((fderiv ℝ (fun p ↦ adjIntegrand a p η) p).opNorm_le_of_apply_eq_sum _ _
    (fderiv_adjIntegrand_apply ha η p)).trans ?_
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  gcongr with j
  · exact hC₁ j p hp η
  · exact hC₂ j p hp η

/-- Differentiation under the integral sign: the coefficient is differentiable, and its derivative
in a direction `v` is the integral of the derivative of the integrand. -/
private theorem hasFDerivAt_adjCoeff (ha : a.HasCompactSpatialSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (adjCoeff a) p₀ ∧ ∀ v, fderiv ℝ (adjCoeff a) p₀ v =
      ∫ η, fderiv ℝ (fun p ↦ adjIntegrand a p η) p₀ v := by
  obtain ⟨D, hD⟩ := exists_norm_fderiv_adjIntegrand_le ha p₀.2
  have hmeas : AEStronglyMeasurable (fun η ↦ fderiv ℝ (fun p ↦ adjIntegrand a p η) p₀) :=
    (continuous_clm_apply.2 (continuous_fderiv_adjIntegrand_apply ha p₀)).aestronglyMeasurable
  have hball {p : CoordinateSpace n × CoordinateSpace n} (hp : p ∈ Metric.ball p₀ 1) :
      p.2 ∈ Metric.closedBall p₀.2 1 :=
    Metric.mem_closedBall.2 (((le_max_right _ _).trans (Prod.dist_eq).ge).trans
      (Metric.mem_ball.1 hp).le)
  have h : HasFDerivAt (adjCoeff a) _ p₀ := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun p η ↦ fderiv ℝ (fun p ↦ adjIntegrand a p η) p) (Metric.ball_mem_nhds p₀ one_pos)
    (.of_forall fun p ↦ (integrable_adjIntegrand ha p).aestronglyMeasurable)
    (integrable_adjIntegrand ha p₀) hmeas
    (.of_forall fun η p hp ↦ hD p (hball hp) η) (integrable_weight.const_mul D)
    (.of_forall fun η p _ ↦ (differentiableAt_adjIntegrand ha η p).hasFDerivAt)
  -- Instance search does not find `ContinuousENorm` on this space of operator-valued continuous
  -- linear maps by itself, so we provide its normed group structure.
  let : NormedAddCommGroup (CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] W) :=
    inferInstance
  have hint : Integrable fun η ↦ fderiv ℝ (fun p ↦ adjIntegrand a p η) p₀ :=
    (integrable_weight.const_mul D).mono' hmeas
      (.of_forall (hD p₀ (Metric.mem_closedBall_self zero_le_one)))
  refine ⟨h.differentiableAt, fun v ↦ ?_⟩
  rw [h.fderiv, ContinuousLinearMap.integral_apply hint]

/-- The derivative of the coefficient in a direction `v`, in terms of the coefficients of the
derivatives of the symbol. -/
private theorem fderiv_adjCoeff_apply (ha : a.HasCompactSpatialSupport)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (adjCoeff a) p v =
      ∑ j, v.1 j • adjCoeff (Symbol.spatialDeriv j a) p +
      ∑ j, v.2 j • adjCoeff (Symbol.frequencyDeriv j a) p := by
  have hj₁ (j : Fin n) : Integrable fun η ↦ v.1 j • adjIntegrand (Symbol.spatialDeriv j a) p η :=
    (integrable_adjIntegrand (ha.spatialDeriv j) p).smul (v.1 j)
  have hj₂ (j : Fin n) : Integrable fun η ↦ v.2 j • adjIntegrand (Symbol.frequencyDeriv j a) p η :=
    (integrable_adjIntegrand (ha.frequencyDeriv j) p).smul (v.2 j)
  rw [(hasFDerivAt_adjCoeff ha p).2 v]
  simp only [fderiv_adjIntegrand_apply ha]
  rw [integral_add (integrable_finsetSum _ fun j _ ↦ hj₁ j)
      (integrable_finsetSum _ fun j _ ↦ hj₂ j),
    integral_finsetSum _ fun j _ ↦ hj₁ j, integral_finsetSum _ fun j _ ↦ hj₂ j]
  simp only [integral_smul, adjCoeff]

/-- The position derivatives of the coefficient are the coefficients of the position derivatives
of the symbol. -/
private theorem coordinateDeriv_fst_adjCoeff (ha : a.HasCompactSpatialSupport) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ adjCoeff a (x, ξ)) x =
      adjCoeff (Symbol.spatialDeriv j a) (x, ξ) := by
  rw [coordinateDeriv_fst_eq_fderiv (p := (x, ξ)) (hasFDerivAt_adjCoeff ha (x, ξ)).1,
    fderiv_adjCoeff_apply ha]
  simp

/-- The frequency derivatives of the coefficient are the coefficients of the frequency derivatives
of the symbol. -/
private theorem coordinateDeriv_snd_adjCoeff (ha : a.HasCompactSpatialSupport) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ adjCoeff a (x, ξ)) ξ =
      adjCoeff (Symbol.frequencyDeriv j a) (x, ξ) := by
  rw [coordinateDeriv_snd_eq_fderiv (p := (x, ξ)) (hasFDerivAt_adjCoeff ha (x, ξ)).1,
    fderiv_adjCoeff_apply ha]
  simp

/-- The coefficient is smooth. -/
private theorem contDiff_adjCoeff (ha : a.HasCompactSpatialSupport) :
    ContDiff ℝ ∞ (adjCoeff a) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing m with
  | zero => exact contDiff_zero.2 (continuous_adjCoeff ha)
  | succ k ih =>
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv_apply.2
      ⟨fun p ↦ (hasFDerivAt_adjCoeff ha p).1, by simp, fun v ↦ ?_⟩
    simp only [fderiv_adjCoeff_apply ha]
    exact (ContDiff.sum fun j _ ↦ (ih (ha.spatialDeriv j)).const_smul _).add
      (ContDiff.sum fun j _ ↦ (ih (ha.frequencyDeriv j)).const_smul _)

/-- The symbol estimates of order `m` for the coefficient, uniformly in the position, by induction
on the number of derivatives: each derivative falls on the symbol, and a frequency derivative
lowers its order by one. -/
private theorem exists_bound_adjCoeff (N : ℕ) :
    ∀ {m : ℝ} (a : Symbol n V W m), a.HasCompactSpatialSupport →
      ∀ α β : List (Fin n), α.length + β.length = N → ∃ C, 0 ≤ C ∧ ∀ x ξ,
        ‖mixedDeriv α β (adjCoeff a) x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  induction N with
  | zero =>
    intro m a ha α β hN
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hN
    obtain ⟨C, hC0, hC⟩ := exists_norm_adjCoeff_le ha
    exact ⟨C, hC0, fun x ξ ↦ by simpa using hC x ξ⟩
  | succ N ih =>
    intro m a ha α β hN
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hN
      · have hlen : α'.length + ([] : List (Fin n)).length = N := by
          simp only [List.length_append, List.length_singleton, List.length_nil] at hN ⊢
          omega
        obtain ⟨C, hC0, hC⟩ := ih (Symbol.spatialDeriv j a) (ha.spatialDeriv j) α' [] hlen
        refine ⟨C, hC0, fun x ξ ↦ ?_⟩
        have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
            coordinateDeriv [j] (fun y ↦ adjCoeff a (y, q.2)) q.1) =
              adjCoeff (Symbol.spatialDeriv j a) :=
          funext fun q ↦ coordinateDeriv_fst_adjCoeff ha j q.1 q.2
        rw [← mixedDeriv_coordinateDeriv_fst (contDiff_adjCoeff ha), hfun]
        exact hC x ξ
    · have hlen : α.length + β'.length = N := by
        simp only [List.length_append, List.length_singleton] at hN
        omega
      obtain ⟨C, hC0, hC⟩ := ih (Symbol.frequencyDeriv j a) (ha.frequencyDeriv j) α β' hlen
      refine ⟨C, hC0, fun x ξ ↦ ?_⟩
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun η ↦ adjCoeff a (q.1, η)) q.2) =
            adjCoeff (Symbol.frequencyDeriv j a) :=
        funext fun q ↦ coordinateDeriv_snd_adjCoeff ha j q.1 q.2
      rw [← mixedDeriv_coordinateDeriv_snd, hfun, ← order_sub_one_sub_length]
      exact hC x ξ

/-- The symbol of order `m` with coefficient `∫ exp(2πi ⟪η, x⟫) â(η, ξ - 2πη) dη`; the adjoint
symbol is its pointwise Hilbert space adjoint. -/
private def adjointAux (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) : Symbol n V W m where
  coefficient := adjCoeff a
  contDiff_coefficient := contDiff_adjCoeff ha
  exists_bound K _ α β := by
    obtain ⟨C, hC0, hC⟩ := exists_bound_adjCoeff _ a ha α β rfl
    exact ⟨C, hC0, fun x _ ξ ↦ hC x ξ⟩

private theorem coefficient_adjointAux (ha : a.HasCompactSpatialSupport) :
    (adjointAux a ha).coefficient = adjCoeff a :=
  (rfl)

private theorem isUniform_adjointAux (ha : a.HasCompactSpatialSupport) :
    (adjointAux a ha).IsUniform :=
  isUniform_iff.2 fun α β ↦ exists_bound_adjCoeff _ a ha α β rfl

/-- The coefficient depends only on the coefficient of the symbol. -/
private theorem adjCoeff_congr {m₁ m₂ : ℝ} {a₁ : Symbol n V W m₁} {a₂ : Symbol n V W m₂}
    (h : a₁.coefficient = a₂.coefficient) : adjCoeff a₁ = adjCoeff a₂ := by
  funext p
  simp only [adjCoeff, adjIntegrand, h]

private theorem adjCoeff_add {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) : adjCoeff (a + b) = adjCoeff a + adjCoeff b := by
  funext p
  rw [Pi.add_apply, adjCoeff, adjCoeff, adjCoeff,
    ← integral_add (integrable_adjIntegrand ha p) (integrable_adjIntegrand hb p)]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [adjIntegrand, ha.fourier_slice_add hb, smul_add]

private theorem adjCoeff_smul (ha : a.HasCompactSpatialSupport) (c : ℂ) :
    adjCoeff (c • a) = c • adjCoeff a := by
  funext p
  rw [Pi.smul_apply, adjCoeff, adjCoeff, ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [adjIntegrand, ha.fourier_slice_smul, smul_comm c]

/-- The integrand `â(ζ' - ζ, 2πζ) (𝓕 u ζ)` of `𝓕 (Op(a) u) ζ'` is integrable in both frequencies:
it is dominated by a convolution-type product of integrable functions. -/
private theorem integrable_fourier_slice_apply_prod (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (y, (2 * π) • q.2)) (q.1 - q.2) (𝓕 u q.2))
      (volume.prod volume) := by
  obtain ⟨Cb, -, hCb⟩ := ha.exists_norm_fourier_slice_le ((n : ℝ) + 1)
  have hh : Integrable fun ζ : CoordinateSpace n ↦
      (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ :=
    (𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m
  have hB : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (y, (2 * π) • q.2)) (q.1 - q.2) := by
    have h := ha.continuous_fourier_slice.comp (by fun_prop :
      Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ (q.1 - q.2, (2 * π) • q.2))
    simpa only [Function.comp_def] using h
  refine ((hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) integrable_weight).const_mul
    Cb).mono' (hB.clm_apply ((𝓕 u).continuous.comp continuous_snd)).aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  rw [ContinuousLinearMap.mul_apply']
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  calc _ ≤ Cb * (1 + ‖(2 * π) • q.2‖ ^ 2) ^ (m / 2) *
        (1 + ‖q.1 - q.2‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * ‖𝓕 u q.2‖ := by
        gcongr
        exact hCb _ _
    _ = _ := by ring

end Integrand

/-! ### The adjoint symbol -/

section Adjoint

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The **adjoint symbol** `a*` of a symbol `a` of order `m` with compact spatial support, a symbol
of order `m`:

`a*(x, ξ) = (∫ exp(2πi ⟪η, x⟫) â(η, ξ - 2πη) dη)†`,

where `â(η, ξ)` is the Fourier transform of the position slice `y ↦ a(y, ξ)` and `†` is the Hilbert
space adjoint. Its quantization is the formal adjoint of the quantization of `a`
(`integral_inner_quantizeSchwartzValue_adjoint`). It differs in general from the pointwise
adjoint `(x, ξ) ↦ a(x, ξ)†`. -/
def adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) : Symbol n W V m :=
  (adjointAux a ha).map ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).toIsometryEquiv
    |>.toRealLinearIsometryEquivOfMapZero (by simp)).toContinuousLinearEquiv

variable {a : Symbol n V W m}

/-- The coefficient of `a*` is the adjoint of the auxiliary coefficient. -/
private theorem coefficient_adjoint_eq_adjCoeff (ha : a.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.adjoint ha).coefficient p = ContinuousLinearMap.adjoint (adjCoeff a p) := by
  rw [adjoint, coefficient_map, coefficient_adjointAux]
  simp

@[simp]
theorem coefficient_adjoint (ha : a.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    (a.adjoint ha).coefficient (x, ξ) = ContinuousLinearMap.adjoint
      (∫ η, (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (y, ξ - (2 * π) • η)) η) := by
  simp only [coefficient_adjoint_eq_adjCoeff, adjCoeff, adjIntegrand]

/-- The adjoint symbol as an integral of adjoints:
`a*(x, ξ) = ∫ exp(-2πi ⟪η, x⟫) â(η, ξ - 2πη)† dη`. -/
theorem coefficient_adjoint_eq_integral (ha : a.HasCompactSpatialSupport)
    (x ξ : CoordinateSpace n) :
    (a.adjoint ha).coefficient (x, ξ) = ∫ η, (𝐞 (-⟪η, x⟫) : ℂ) •
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, ξ - (2 * π) • η)) η) := by
  have h := ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul
    ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).toContinuousLinearEquiv
      |>.toContinuousLinearMap) (integrable_adjIntegrand ha (x, ξ))
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    adjIntegrand, map_smulₛₗ, Circle.starRingEnd_addChar] at h
  rw [coefficient_adjoint_eq_adjCoeff, adjCoeff]
  simp only [adjIntegrand]
  exact h.symm

/-- The estimates of the adjoint symbol are uniform in the position, so its quantization maps
Schwartz space to itself (`quantizeUniformCLM`). -/
theorem isUniform_adjoint (ha : a.HasCompactSpatialSupport) : (a.adjoint ha).IsUniform :=
  (isUniform_adjointAux ha).map _

/-- Taking the adjoint symbol commutes with spatial derivatives. -/
theorem spatialDeriv_adjoint (ha : a.HasCompactSpatialSupport) (j : Fin n) :
    Symbol.spatialDeriv j (a.adjoint ha) =
      (Symbol.spatialDeriv j a).adjoint (ha.spatialDeriv j) := by
  rw [adjoint, adjoint, spatialDeriv_map]
  congr 1
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_spatialDeriv]
  exact coordinateDeriv_fst_adjCoeff ha j x ξ

/-- Taking the adjoint symbol commutes with frequency derivatives. -/
theorem frequencyDeriv_adjoint (ha : a.HasCompactSpatialSupport) (j : Fin n) :
    Symbol.frequencyDeriv j (a.adjoint ha) =
      (Symbol.frequencyDeriv j a).adjoint (ha.frequencyDeriv j) := by
  rw [adjoint, adjoint, frequencyDeriv_map]
  congr 1
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_frequencyDeriv]
  exact coordinateDeriv_snd_adjCoeff ha j x ξ

/-! ### Conjugate-linearity, inclusions and smoothing symbols -/

theorem adjoint_add {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) :
    (a + b).adjoint (ha.add hb) = a.adjoint ha + b.adjoint hb := by
  ext1
  funext p
  rw [coefficient_add, Pi.add_apply, coefficient_adjoint_eq_adjCoeff,
    coefficient_adjoint_eq_adjCoeff, coefficient_adjoint_eq_adjCoeff, adjCoeff_add ha hb,
    Pi.add_apply, map_add]

@[simp]
theorem adjoint_smul (ha : a.HasCompactSpatialSupport) (c : ℂ) :
    (c • a).adjoint (ha.smul c) = (starRingEnd ℂ c) • a.adjoint ha := by
  ext1
  funext p
  rw [coefficient_smul, Pi.smul_apply, coefficient_adjoint_eq_adjCoeff,
    coefficient_adjoint_eq_adjCoeff, adjCoeff_smul ha, Pi.smul_apply, map_smulₛₗ]

@[simp]
theorem adjoint_zero :
    (0 : Symbol n V W m).adjoint hasCompactSpatialSupport_zero = 0 := by
  simpa using adjoint_smul (hasCompactSpatialSupport_zero (m := m) (V := V) (W := W)) 0

@[simp]
theorem adjoint_neg (ha : a.HasCompactSpatialSupport) : (-a).adjoint ha.neg = -a.adjoint ha := by
  simpa using adjoint_smul ha (-1)

theorem adjoint_sub {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) :
    (a - b).adjoint (ha.sub hb) = a.adjoint ha - b.adjoint hb := by
  calc (a - b).adjoint (ha.sub hb) = (a + -b).adjoint (ha.add hb.neg) := by
        simp only [sub_eq_add_neg]
    _ = a.adjoint ha - b.adjoint hb := by
        rw [adjoint_add ha hb.neg, adjoint_neg, ← sub_eq_add_neg]

theorem adjoint_inclusion {m' : ℝ} (h : m ≤ m') (ha : a.HasCompactSpatialSupport) :
    (inclusion h a).adjoint (ha.inclusion h) = inclusion h (a.adjoint ha) := by
  ext1
  funext p
  rw [coefficient_inclusion, coefficient_adjoint_eq_adjCoeff, coefficient_adjoint_eq_adjCoeff,
    adjCoeff_congr (coefficient_inclusion h a)]

/-- The adjoint symbol of a smoothing symbol is smoothing. -/
theorem IsSmoothing.adjoint (hs : a.IsSmoothing) (ha : a.HasCompactSpatialSupport) :
    (a.adjoint ha).IsSmoothing := isSmoothing_iff.2 fun m' ↦ by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 hs m'
  refine ⟨b.adjoint (ha.of_coefficient_eq hb), ?_⟩
  funext p
  rw [coefficient_adjoint_eq_adjCoeff, coefficient_adjoint_eq_adjCoeff, adjCoeff_congr hb]

end Adjoint

/-! ### The formal adjoint of the quantization -/

section Operator

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

open scoped InnerProductSpace

/-- The integrand `η ↦ exp(-2πi ⟪η, x⟫) â(η, ξ - 2πη)†` of `a*(x, ξ)` is integrable. -/
private theorem integrable_adjoint_adjIntegrand (ha : a.HasCompactSpatialSupport)
    (x ξ : CoordinateSpace n) :
    Integrable fun η ↦ (𝐞 (-⟪η, x⟫) : ℂ) •
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, ξ - (2 * π) • η)) η) := by
  refine ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).toContinuousLinearEquiv
    |>.toContinuousLinearMap.integrable_comp (integrable_adjIntegrand ha (x, ξ))).congr
    (.of_forall fun η ↦ ?_)
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    adjIntegrand, map_smulₛₗ, Circle.starRingEnd_addChar]

/-- The integrand `â(θ - ζ, 2πζ)† (𝓕 v θ)` of the Fourier transform of `Op(a*) v` is integrable in
both frequencies `(ζ, θ)`: by Peetre's inequality it is dominated by a convolution-type product of
integrable functions. -/
private theorem integrable_adjoint_fourier_slice_apply (ha : a.HasCompactSpatialSupport)
    (v : 𝓢(CoordinateSpace n, W)) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • q.1)) (q.2 - q.1))
        (𝓕 v q.2)) (volume.prod volume) := by
  obtain ⟨Cb, hCb0, hCb⟩ := ha.exists_norm_fourier_slice_le ((n : ℝ) + 1 + |m|)
  have hh : Integrable fun θ : CoordinateSpace n ↦
      (1 + ‖(2 * π) • θ‖ ^ 2) ^ (m / 2) * ‖𝓕 v θ‖ :=
    (𝓕 v).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m
  have hB : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • q.1)) (q.2 - q.1)) := by
    have h := ha.continuous_fourier_slice.comp (by fun_prop :
      Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ (q.2 - q.1, (2 * π) • q.1))
    exact (LinearIsometryEquiv.continuous _).comp (by simpa only [Function.comp_def] using h)
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  refine ((hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) integrable_weight).const_mul
    (Cb * 2 ^ (|m| / 2) * (2 * π) ^ |m|)).mono'
    (hB.clm_apply ((𝓕 v).continuous.comp continuous_snd)).aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  -- Peetre's inequality moves the weight from the frequency `2πζ` to `2πθ`.
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m ((2 * π) • q.2) ((2 * π) • (q.1 - q.2))
  rw [← smul_add, add_sub_cancel] at hpeetre
  have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul h2π |m| (x := (2 * π) • (q.1 - q.2))
    (y := q.1 - q.2) (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])
  rw [abs_abs] at hscale
  have hw : (1 + ‖q.1 - q.2‖ ^ 2) ^ (|m| / 2) *
      (1 + ‖q.2 - q.1‖ ^ 2) ^ (-((n : ℝ) + 1 + |m|) / 2) =
        (1 + ‖q.1 - q.2‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [norm_sub_rev q.2 q.1, ← Real.rpow_add (by positivity)]
    ring_nf
  rw [ContinuousLinearMap.mul_apply']
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  calc ‖𝓕 (fun y ↦ a.coefficient (y, (2 * π) • q.1)) (q.2 - q.1)‖ * ‖𝓕 v q.2‖
      ≤ Cb * (2 ^ (|m| / 2) * (1 + ‖(2 * π) • q.2‖ ^ 2) ^ (m / 2) *
          ((2 * π) ^ |m| * (1 + ‖q.1 - q.2‖ ^ 2) ^ (|m| / 2))) *
          (1 + ‖q.2 - q.1‖ ^ 2) ^ (-((n : ℝ) + 1 + |m|) / 2) * ‖𝓕 v q.2‖ := by
        gcongr
        refine (hCb _ _).trans ?_
        gcongr
        exact hpeetre.trans (by gcongr)
    _ = Cb * 2 ^ (|m| / 2) * (2 * π) ^ |m| *
          ((1 + ‖(2 * π) • q.2‖ ^ 2) ^ (m / 2) * ‖𝓕 v q.2‖) *
          ((1 + ‖q.1 - q.2‖ ^ 2) ^ (|m| / 2) *
            (1 + ‖q.2 - q.1‖ ^ 2) ^ (-((n : ℝ) + 1 + |m|) / 2)) := by ring
    _ = _ := by rw [hw]; ring

/-- **`Op(a*) v` as an inverse Fourier transform.** The change of variables `η = θ - ζ` in the
definition of `a*` gives `Op(a*) v (x) = ∫ exp(2πi ⟪ζ, x⟫) w(ζ) dζ` with
`w(ζ) = ∫ â(θ - ζ, 2πζ)† (𝓕 v θ) dθ`. -/
private theorem quantizeSchwartzValue_adjoint_eq (ha : a.HasCompactSpatialSupport)
    (v : 𝓢(CoordinateSpace n, W)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.adjoint ha).coefficient v x = ∫ ζ, 𝐞 ⟪ζ, x⟫ • ∫ θ,
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (θ - ζ))
        (𝓕 v θ) := by
  set H : CoordinateSpace n → CoordinateSpace n → V := fun ζ θ ↦
    ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (θ - ζ)) (𝓕 v θ)
    with hHdef
  have hH : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ H q.1 q.2)
      (volume.prod volume) := integrable_adjoint_fourier_slice_apply ha v
  have hH' : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.2, x⟫ : ℂ) • H q.2 q.1) (volume.prod volume) := by
    refine hH.swap.norm.mono'
      ((Continuous.aestronglyMeasurable (by fun_prop)).smul hH.swap.aestronglyMeasurable)
      (.of_forall fun q ↦ ?_)
    rw [norm_smul, Circle.norm_coe, one_mul]
    rfl
  calc quantizeSchwartzValue (a.adjoint ha).coefficient v x
      = ∫ θ, ∫ ζ, (𝐞 ⟪ζ, x⟫ : ℂ) • H ζ θ := by
        rw [quantizeSchwartzValue_def]
        refine integral_congr_ae (.of_forall fun θ ↦ ?_)
        dsimp only
        rw [coefficient_adjoint_eq_integral,
          ContinuousLinearMap.integral_apply (integrable_adjoint_adjIntegrand ha x _),
          Circle.smul_def, ← integral_smul]
        refine (integral_sub_left_eq_self _ volume θ).symm.trans
          (integral_congr_ae (.of_forall fun ζ ↦ ?_))
        have h₁ : (2 * π) • θ - (2 * π) • (θ - ζ) = (2 * π) • ζ := by
          rw [smul_sub, sub_sub_cancel]
        have h₂ : (𝐞 ⟪θ, x⟫ : ℂ) * 𝐞 (-⟪θ - ζ, x⟫) = 𝐞 ⟪ζ, x⟫ := by
          rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_sub_left]
          ring_nf
        simp only [hHdef, smul_apply, smul_smul, h₁, h₂]
    _ = ∫ ζ, ∫ θ, (𝐞 ⟪ζ, x⟫ : ℂ) • H ζ θ := integral_integral_swap hH'
    _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        dsimp only
        rw [integral_smul, Circle.smul_def]

/-- The Fourier side `w(ζ) = ∫ â(θ - ζ, 2πζ)† (𝓕 v θ) dθ` of `Op(a*) v`, which is integrable. -/
private theorem integrable_integral_adjoint_fourier_slice_apply (ha : a.HasCompactSpatialSupport)
    (v : 𝓢(CoordinateSpace n, W)) :
    Integrable fun ζ ↦ ∫ θ,
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (θ - ζ))
        (𝓕 v θ) :=
  (integrable_adjoint_fourier_slice_apply ha v).integral_prod_left

/-- **The left side of the adjoint identity.** By Plancherel's theorem and the Fourier transform of
`Op(a) u`, `∫ ⟪Op(a) u (x), v(x)⟫ dx = ∫ ⟪𝓕 u ζ, w(ζ)⟫ dζ` with
`w(ζ) = ∫ â(θ - ζ, 2πζ)† (𝓕 v θ) dθ`. -/
private theorem integral_inner_quantizeSchwartzValue_eq (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, ⟪quantizeSchwartzValue a.coefficient u x, v x⟫_ℂ = ∫ ζ, ⟪𝓕 u ζ, ∫ θ,
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (θ - ζ))
        (𝓕 v θ)⟫_ℂ := by
  set A : CoordinateSpace n → CoordinateSpace n → V →L[ℂ] W := fun ζ' ζ ↦
    𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (ζ' - ζ) with hAdef
  have hAu : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ A q.1 q.2 (𝓕 u q.2))
      (volume.prod volume) := integrable_fourier_slice_apply_prod ha u
  have hH : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      ContinuousLinearMap.adjoint (A q.2 q.1) (𝓕 v q.2)) (volume.prod volume) :=
    integrable_adjoint_fourier_slice_apply ha v
  set M := SchwartzMap.seminorm ℂ 0 0 (𝓕 v)
  have hM (ζ : CoordinateSpace n) : ‖𝓕 v ζ‖ ≤ M := SchwartzMap.norm_le_seminorm ℂ (𝓕 v) ζ
  have hswap : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      ⟪A q.1 q.2 (𝓕 u q.2), 𝓕 v q.1⟫_ℂ) (volume.prod volume) :=
    (hAu.norm.const_mul M).mono'
      (hAu.aestronglyMeasurable.inner
        ((𝓕 v).continuous.comp continuous_fst).aestronglyMeasurable)
      (.of_forall fun q ↦ (norm_inner_le_norm _ _).trans (by
        rw [mul_comm]
        gcongr
        exact hM q.1))
  -- Taking the inner product with a fixed vector on the right commutes with the integral.
  have hinner {f : CoordinateSpace n → W} (hf : Integrable f) (c : W) :
      ⟪∫ ζ, f ζ, c⟫_ℂ = ∫ ζ, ⟪f ζ, c⟫_ℂ := by
    rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
    simp only [inner_conj_symm]
  calc ∫ x, ⟪quantizeSchwartzValue a.coefficient u x, v x⟫_ℂ
      = ∫ ζ', ⟪𝓕 (quantizeSchwartzValue a.coefficient u) ζ', 𝓕 v ζ'⟫_ℂ := by
        have h := SchwartzMap.integral_inner_fourier_fourier
          (quantizeUniformCLM a ha.isUniform u) v
        rw [SchwartzMap.fourier_coe (quantizeUniformCLM a ha.isUniform u),
          coe_quantizeUniformCLM] at h
        exact h.symm
    _ = ∫ ζ', ∫ ζ, ⟪A ζ' ζ (𝓕 u ζ), 𝓕 v ζ'⟫_ℂ := by
        refine integral_congr_ae ?_
        filter_upwards [hAu.prod_right_ae] with ζ' hζ'
        rw [ha.fourier_quantizeSchwartzValue u ζ', hinner hζ']
    _ = ∫ ζ, ∫ ζ', ⟪A ζ' ζ (𝓕 u ζ), 𝓕 v ζ'⟫_ℂ := integral_integral_swap hswap
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hH.prod_right_ae] with ζ hζ
        rw [← integral_inner hζ]
        exact integral_congr_ae (.of_forall fun ζ' ↦
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm)

/-- **The right side of the adjoint identity.** Since `Op(a*) v` is the inverse Fourier transform of
`w(ζ) = ∫ â(θ - ζ, 2πζ)† (𝓕 v θ) dθ` and the Fourier transform is self-adjoint for the
sesquilinear pairing of integrable functions, `∫ ⟪u(x), Op(a*) v (x)⟫ dx = ∫ ⟪𝓕 u ζ, w(ζ)⟫ dζ`. -/
private theorem integral_inner_quantizeSchwartzValue_adjoint_eq (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, ⟪u x, quantizeSchwartzValue (a.adjoint ha).coefficient v x⟫_ℂ = ∫ ζ, ⟪𝓕 u ζ, ∫ θ,
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (θ - ζ))
        (𝓕 v θ)⟫_ℂ := by
  have hq : quantizeSchwartzValue (a.adjoint ha).coefficient v = 𝓕⁻ fun ζ ↦ ∫ θ,
      ContinuousLinearMap.adjoint (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) (θ - ζ))
        (𝓕 v θ) :=
    funext fun x ↦ by rw [quantizeSchwartzValue_adjoint_eq, Real.fourierInv_eq]
  have hsesq := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L := innerₗ (CoordinateSpace n)) Real.continuous_fourierChar continuous_inner
    (u.integrable (μ := volume)) (integrable_integral_adjoint_fourier_slice_apply ha v)
  rw [hq]
  -- `𝓕` and `𝓕⁻` are the Fourier integrals for the pairings `innerₗ` and `-(innerₗ).flip`.
  simpa using! hsesq.symm

/-- **The quantization of `a*` is the formal adjoint of the quantization of `a`.** For a symbol `a`
with compact spatial support and Schwartz functions `u` and `v`,
`∫ ⟪Op(a) u (x), v(x)⟫ dx = ∫ ⟪u(x), Op(a*) v (x)⟫ dx`. -/
theorem integral_inner_quantizeSchwartzValue_adjoint (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, ⟪quantizeSchwartzValue a.coefficient u x, v x⟫_ℂ =
      ∫ x, ⟪u x, quantizeSchwartzValue (a.adjoint ha).coefficient v x⟫_ℂ := by
  rw [integral_inner_quantizeSchwartzValue_eq ha, integral_inner_quantizeSchwartzValue_adjoint_eq]

end Operator

end Symbol

end TauCeti
