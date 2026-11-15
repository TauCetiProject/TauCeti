/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.WeightedSlice
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import TauCeti.Analysis.Calculus.CoordinateDeriv.ParametricIntegral
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Pseudodifferential.OutputSupport
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Composition of symbols with a uniform right factor

`TauCeti.Analysis.Pseudodifferential.Composition.Basic` constructs `a # b` when `b` has compact
spatial support, excluding constant symbols, Bessel multipliers `⟨ξ / 2π⟩ ^ s`, and general uniform
symbols (`TauCeti.Symbol.IsUniform`). This file constructs `a.uniformSharp b hb : Symbol n V U
(m' + m)` for every symbol `a` of order `m'` and uniform symbol `b` of order `m` by integrating by
parts `2(n + 1)` times in frequency via `TauCeti.Symbol.oneSubFrequencyLaplacian` and
`TauCeti.Symbol.weightedSlice`:

`(a # b)(x, ξ) = ∫ ((1 - Δ_ξ) ^ (n + 1) a)(x, ξ + 2πη) ∘ 𝓕 (weightedSlice b x ξ) η dη`.

## Main results

* `TauCeti.Symbol.uniformSharp`, `TauCeti.Symbol.IsUniform.uniformSharp`,
  `TauCeti.Symbol.spatialDeriv_uniformSharp`, `TauCeti.Symbol.frequencyDeriv_uniformSharp`: the
  composition symbol, preservation of `IsUniform`, and position/frequency Leibniz rules.
* `TauCeti.Symbol.quantizeSchwartzValue_uniformSharp`,
  `TauCeti.Symbol.quantizeUniformCLM_uniformSharp`, `TauCeti.Symbol.uniformSharp_eq_sharp`:
  `Op(a # b) = Op(a) ∘ Op(b)` on Schwartz space and agreement with `sharp` for compactly supported
  right factors.
* `TauCeti.Symbol.const_id_uniformSharp`, `TauCeti.Symbol.uniformSharp_const_id`,
  `TauCeti.Symbol.uniformSharp_assoc`, `TauCeti.Symbol.uniformSharp_ofFrequency`,
  `TauCeti.Symbol.uniformSharp_besselPotential`,
  `TauCeti.Symbol.quantizeUniformCLM_besselPotential_uniformSharp`: unit laws, associativity, and
  composition with frequency multipliers and Bessel potentials.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* H. Kumano-go, *Pseudo-Differential Operators*, MIT Press, 1981, Chapter 2, §1–§2.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §2.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The uniform composition integrand and coefficient -/

section Integrand

variable (a : Symbol n W U m') (b : Symbol n V W m)

private def uniformCompIntegrand (p : CoordinateSpace n × CoordinateSpace n)
    (η : CoordinateSpace n) : V →L[ℂ] U :=
  (((oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (p.1, p.2 + (2 * π) • η)).comp
    (𝓕 (weightedSlice b p.1 p.2) η)

private def uniformCompCoeff (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] U :=
  ∫ η, uniformCompIntegrand a b p η

variable {a b}

private theorem IsUniform.exists_norm_uniformCompIntegrand_le (hb : b.IsUniform)
    {K : Set (CoordinateSpace n)}
    (ha : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η, ‖uniformCompIntegrand a b (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨Ca, hCa0, hCa⟩ := ha
  obtain ⟨Cb, hCb0, hCb⟩ := hb.exists_norm_fourier_weightedSlice_le (r + |m'|)
  have h2pi : 1 ≤ 2 * π := by linarith [Real.two_le_pi]
  refine ⟨Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * Cb, by positivity, fun x hx ξ η ↦ ?_⟩
  have hshift : (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m'| / 2) ≤
      (2 * π) ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2) := by
    simpa only [abs_abs] using one_add_norm_smul_sq_rpow_le h2pi |m'| η
  have hpeetre : (1 + ‖ξ + (2 * π) • η‖ ^ 2) ^ (m' / 2) ≤
      2 ^ (|m'| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * ((2 * π) ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2)) :=
    (one_add_norm_add_sq_rpow_le_mul m' ξ ((2 * π) • η)).trans (by gcongr)
  have hξ : (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
  have hη : (1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m'|) / 2) =
      (1 + ‖η‖ ^ 2) ^ (-r / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
  calc ‖uniformCompIntegrand a b (x, ξ) η‖
      ≤ ‖((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, ξ + (2 * π) • η)‖ *
          ‖𝓕 (weightedSlice b x ξ) η‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Ca * (2 ^ (|m'| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) *
          ((2 * π) ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2)))) *
          (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m'|) / 2)) :=
        mul_le_mul ((hCa x hx _).trans (by gcongr)) (hCb x ξ η) (norm_nonneg _) (by positivity)
    _ = Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * Cb *
          ((1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) *
          ((1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m'|) / 2)) := by ring
    _ = _ := by rw [hξ, hη]

private theorem IsUniform.continuous_uniformCompIntegrand (hb : b.IsUniform) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      uniformCompIntegrand a b q.1 q.2 := by
  dsimp only [uniformCompIntegrand]
  have hca := ((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).contDiff_coefficient
  exact (hca.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).add
      ((continuous_const_smul (2 * π)).comp continuous_snd)))).clm_comp
    hb.continuous_fourier_weightedSlice

private theorem IsUniform.integrable_uniformCompIntegrand (hb : b.IsUniform)
    (p : CoordinateSpace n × CoordinateSpace n) : Integrable (uniformCompIntegrand a b p) := by
  obtain ⟨C, -, hC⟩ := hb.exists_norm_uniformCompIntegrand_le
    (((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).exists_bound_coefficient {p.1}
      isCompact_singleton) ((n : ℝ) + 1)
  exact (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _).mono'
    (hb.continuous_uniformCompIntegrand.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall fun η ↦ hC p.1 rfl p.2 η)

private theorem IsUniform.exists_norm_uniformCompIntegrand_le_weight (hb : b.IsUniform)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ p : CoordinateSpace n × CoordinateSpace n, p.1 ∈ Metric.closedBall p₀.1 1 →
      p.2 ∈ Metric.closedBall p₀.2 1 → ∀ η,
        ‖uniformCompIntegrand a b p η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_uniformCompIntegrand_le
    (((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).exists_bound_coefficient
      (Metric.closedBall p₀.1 1) (isCompact_closedBall p₀.1 1)) ((n : ℝ) + 1)
  have hw : Continuous fun ξ : CoordinateSpace n ↦ (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  obtain ⟨M, hM⟩ := (isCompact_closedBall p₀.2 1).exists_bound_of_continuousOn hw.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p₀.2 (Metric.mem_closedBall_self zero_le_one))
  refine ⟨C * M, mul_nonneg hC0 hM0, fun p hp₁ hp₂ η ↦ (hC p.1 hp₁ p.2 η).trans ?_⟩
  have hMp : (1 + ‖p.2‖ ^ 2) ^ ((m' + m) / 2) ≤ M :=
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM p.2 hp₂))
  gcongr

private theorem IsUniform.continuous_uniformCompCoeff (hb : b.IsUniform) :
    Continuous (uniformCompCoeff a b) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  obtain ⟨C, -, hC⟩ := hb.exists_norm_uniformCompIntegrand_le_weight (a := a) p₀
  refine continuousAt_of_dominated
    (bound := fun η ↦ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2))
    (.of_forall fun p ↦ (hb.integrable_uniformCompIntegrand p).aestronglyMeasurable) ?_
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _)
    (.of_forall fun η ↦ (hb.continuous_uniformCompIntegrand.comp
      (continuous_id.prodMk continuous_const)).continuousAt)
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds p₀.1 one_pos),
    continuous_snd.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds p₀.2 one_pos)]
    with p hp₁ hp₂
  exact .of_forall (hC p hp₁ hp₂)

private theorem IsUniform.exists_norm_uniformCompCoeff_le (hb : b.IsUniform)
    {K : Set (CoordinateSpace n)}
    (ha : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖uniformCompCoeff a b (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_uniformCompIntegrand_le ha ((n : ℝ) + 1)
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  refine ⟨C * I, mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity), fun x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2))) (.of_forall fun η ↦ hC x hx ξ η)).trans_eq ?_
  rw [integral_const_mul]; ring

private lemma coordinateDeriv_fst_uniformCompIntegrand (hb : b.IsUniform) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun x' ↦ uniformCompIntegrand a b (x', ξ) η) x =
      uniformCompIntegrand (spatialDeriv j a) b (x, ξ) η +
        uniformCompIntegrand a (spatialDeriv j b) (x, ξ) η := by
  set aN := (oneSubFrequencyLaplacian (m := m'))^[n + 1] a
  set ζ := ξ + (2 * π) • η
  set Φ := (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  have hA := ((aN.contDiff_coefficient_slice ζ).differentiable (by simp) x).hasFDerivAt
  have hBfull := hb.differentiableAt_fourier_weightedSlice_and_fderiv η (x, ξ)
  have hB : HasFDerivAt (fun x' ↦ 𝓕 (weightedSlice b x' ξ) η)
      ((fderiv ℝ (fun p ↦ 𝓕 (weightedSlice b p.1 p.2) η) (x, ξ)).comp
        (.inl ℝ (CoordinateSpace n) (CoordinateSpace n))) x := by
    simpa only [Function.comp_def] using
      HasFDerivAt.comp x hBfull.1.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) x ξ)
  have hBj : fderiv ℝ (fun p ↦ 𝓕 (weightedSlice b p.1 p.2) η) (x, ξ)
      (EuclideanSpace.single j 1, 0) = 𝓕 (weightedSlice (spatialDeriv j b) x ξ) η := by
    rw [hBfull.2]; simp
  have hAj : fderiv ℝ (fun x' ↦ aN.coefficient (x', ζ)) x (EuclideanSpace.single j 1) =
      ((oneSubFrequencyLaplacian (m := m'))^[n + 1] (spatialDeriv j a)).coefficient (x, ζ) := by
    rw [fderiv_coefficient_single, ← spatialDeriv_iterate_oneSubFrequencyLaplacian]
  rw [coordinateDeriv_cons, coordinateDeriv_nil,
    show (fun x' ↦ uniformCompIntegrand a b (x', ξ) η) =
      fun x' ↦ Φ (aN.coefficient (x', ζ)) (𝓕 (weightedSlice b x' ξ) η) from rfl,
    (Φ.hasFDerivAt_of_bilinear hA hB).fderiv]
  simp only [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hAj, hBj, Φ,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply, ContinuousLinearMap.compL_apply,
    uniformCompIntegrand, ζ, aN, add_comm]

private lemma coordinateDeriv_snd_uniformCompIntegrand (hb : b.IsUniform) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ' ↦ uniformCompIntegrand a b (x, ξ') η) ξ =
      uniformCompIntegrand (frequencyDeriv j a) b (x, ξ) η +
        uniformCompIntegrand a (frequencyDeriv j b) (x, ξ) η := by
  set aN := (oneSubFrequencyLaplacian (m := m'))^[n + 1] a
  set c := (2 * π) • η
  set Φ := (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  have hA : HasFDerivAt (fun ξ' ↦ aN.coefficient (x, ξ' + c))
      (fderiv ℝ (fun ζ ↦ aN.coefficient (x, ζ)) (ξ + c)) ξ :=
    (hasFDerivAt_comp_add_right c).2 (((aN.contDiff_coefficient.comp
      (contDiff_prodMk_right x)).differentiable (by simp) (ξ + c)).hasFDerivAt)
  have hBfull := hb.differentiableAt_fourier_weightedSlice_and_fderiv η (x, ξ)
  have hB : HasFDerivAt (fun ξ' ↦ 𝓕 (weightedSlice b x ξ') η)
      ((fderiv ℝ (fun p ↦ 𝓕 (weightedSlice b p.1 p.2) η) (x, ξ)).comp
        (.inr ℝ (CoordinateSpace n) (CoordinateSpace n))) ξ :=
    hBfull.1.hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right (𝕜 := ℝ) x ξ)
  have hBj : fderiv ℝ (fun p ↦ 𝓕 (weightedSlice b p.1 p.2) η) (x, ξ)
      (0, EuclideanSpace.single j 1) = 𝓕 (weightedSlice (frequencyDeriv j b) x ξ) η := by
    rw [hBfull.2]; simp
  have hAj : fderiv ℝ (fun ζ ↦ aN.coefficient (x, ζ)) (ξ + c) (EuclideanSpace.single j 1) =
      ((oneSubFrequencyLaplacian (m := m' - 1))^[n + 1] (frequencyDeriv j a)).coefficient
        (x, ξ + c) := by
    rw [fderiv_coefficient_slice_single, ← frequencyDeriv_iterate_oneSubFrequencyLaplacian]
  rw [coordinateDeriv_cons, coordinateDeriv_nil,
    show (fun ξ' ↦ uniformCompIntegrand a b (x, ξ') η) =
      fun ξ' ↦ Φ (aN.coefficient (x, ξ' + c)) (𝓕 (weightedSlice b x ξ') η) from rfl,
    (Φ.hasFDerivAt_of_bilinear hA hB).fderiv]
  simp only [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hAj, hBj, Φ,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply, ContinuousLinearMap.compL_apply,
    uniformCompIntegrand, c, aN, add_comm]

private lemma differentiableAt_uniformCompIntegrand (hb : b.IsUniform) (η : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ uniformCompIntegrand a b p η) p := by
  set aN := (oneSubFrequencyLaplacian (m := m'))^[n + 1] a
  set Φ := (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  have hA : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      aN.coefficient (p.1, p.2 + (2 * π) • η)) p :=
    (aN.contDiff_coefficient.differentiable (by simp) _).comp p
      (differentiableAt_fst.prodMk (differentiableAt_snd.add_const _))
  exact (Φ.differentiableAt.comp p hA).clm_apply
    (hb.differentiableAt_fourier_weightedSlice_and_fderiv η p).1

private lemma fderiv_uniformCompIntegrand (hb : b.IsUniform) (η : CoordinateSpace n)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p ↦ uniformCompIntegrand a b p η) p v =
      ∑ j, v.1 j • (uniformCompIntegrand (spatialDeriv j a) b p η +
        uniformCompIntegrand a (spatialDeriv j b) p η) +
      ∑ j, v.2 j • (uniformCompIntegrand (frequencyDeriv j a) b p η +
        uniformCompIntegrand a (frequencyDeriv j b) p η) := by
  rw [fderiv_apply_eq_sum_coordinateDeriv (differentiableAt_uniformCompIntegrand hb η p)]
  simp only [coordinateDeriv_fst_uniformCompIntegrand hb,
    coordinateDeriv_snd_uniformCompIntegrand hb, Prod.mk.eta]

private theorem IsUniform.differentiableAt_uniformCompCoeff_and_fderiv (hb : b.IsUniform)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (uniformCompCoeff a b) p₀ ∧
      ∀ v, fderiv ℝ (uniformCompCoeff a b) p₀ v =
        ∑ j, v.1 j • (uniformCompCoeff (Symbol.spatialDeriv j a) b p₀ +
          uniformCompCoeff a (Symbol.spatialDeriv j b) p₀) +
        ∑ j, v.2 j • (uniformCompCoeff (Symbol.frequencyDeriv j a) b p₀ +
          uniformCompCoeff a (Symbol.frequencyDeriv j b) p₀) := by
  choose C₁ _ hC₁ using fun j ↦
    hb.exists_norm_uniformCompIntegrand_le_weight (a := Symbol.spatialDeriv j a) p₀
  choose C₂ _ hC₂ using fun j ↦
    (hb.spatialDeriv j).exists_norm_uniformCompIntegrand_le_weight (a := a) p₀
  choose C₃ _ hC₃ using fun j ↦
    hb.exists_norm_uniformCompIntegrand_le_weight (a := Symbol.frequencyDeriv j a) p₀
  choose C₄ _ hC₄ using fun j ↦
    (hb.frequencyDeriv j).exists_norm_uniformCompIntegrand_le_weight (a := a) p₀
  set D := ∑ j, (C₁ j + C₂ j) + ∑ j, (C₃ j + C₄ j)
  have hc {m₁ m₂ : ℝ} (a' : Symbol n W U m₁) {b' : Symbol n V W m₂} (hb' : b'.IsUniform)
      (p : CoordinateSpace n × CoordinateSpace n) : Continuous (uniformCompIntegrand a' b' p) :=
    hb'.continuous_uniformCompIntegrand.comp (continuous_const.prodMk continuous_id)
  have key := differentiableAt_integral_and_fderiv_apply_eq_sum
    (differentiableAt_uniformCompIntegrand hb) (fderiv_uniformCompIntegrand hb)
    hb.integrable_uniformCompIntegrand
    (fun j p ↦ (hc (Symbol.spatialDeriv j a) hb p).add (hc a (hb.spatialDeriv j) p))
    (fun j p ↦ (hc (Symbol.frequencyDeriv j a) hb p).add (hc a (hb.frequencyDeriv j) p))
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul D) p₀ fun η p hp ↦ by
      have hp₁ : p.1 ∈ Metric.closedBall p₀.1 1 := Metric.mem_closedBall.2
        (((le_max_left _ _).trans Prod.dist_eq.ge).trans (Metric.mem_ball.1 hp).le)
      have hp₂ : p.2 ∈ Metric.closedBall p₀.2 1 := Metric.mem_closedBall.2
        (((le_max_right _ _).trans Prod.dist_eq.ge).trans (Metric.mem_ball.1 hp).le)
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      gcongr with j _ j _
      · exact (norm_add_le _ _).trans
          ((add_le_add (hC₁ j p hp₁ hp₂ η) (hC₂ j p hp₁ hp₂ η)).trans_eq (by ring))
      · exact (norm_add_le _ _).trans
          ((add_le_add (hC₃ j p hp₁ hp₂ η) (hC₄ j p hp₁ hp₂ η)).trans_eq (by ring))
  refine ⟨key.1, fun v ↦ (key.2 v).trans ?_⟩
  congr 1 <;> refine Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_
  · exact integral_add (hb.integrable_uniformCompIntegrand p₀)
      ((hb.spatialDeriv j).integrable_uniformCompIntegrand p₀)
  · exact integral_add (hb.integrable_uniformCompIntegrand p₀)
      ((hb.frequencyDeriv j).integrable_uniformCompIntegrand p₀)

private theorem coordinateDeriv_fst_uniformCompCoeff (hb : b.IsUniform) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x' ↦ uniformCompCoeff a b (x', ξ)) x =
      uniformCompCoeff (spatialDeriv j a) b (x, ξ) +
        uniformCompCoeff a (spatialDeriv j b) (x, ξ) := by
  rw [coordinateDeriv_fst_eq_fderiv (p := (x, ξ))
    (hb.differentiableAt_uniformCompCoeff_and_fderiv (x, ξ)).1,
    (hb.differentiableAt_uniformCompCoeff_and_fderiv (x, ξ)).2]
  simp [Finset.sum_add_distrib]

private theorem coordinateDeriv_snd_uniformCompCoeff (hb : b.IsUniform) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ' ↦ uniformCompCoeff a b (x, ξ')) ξ =
      uniformCompCoeff (frequencyDeriv j a) b (x, ξ) +
        uniformCompCoeff a (frequencyDeriv j b) (x, ξ) := by
  rw [coordinateDeriv_snd_eq_fderiv (p := (x, ξ))
    (hb.differentiableAt_uniformCompCoeff_and_fderiv (x, ξ)).1,
    (hb.differentiableAt_uniformCompCoeff_and_fderiv (x, ξ)).2]
  simp [Finset.sum_add_distrib]

private theorem contDiff_uniformCompCoeff (hb : b.IsUniform) :
    ContDiff ℝ ∞ (uniformCompCoeff a b) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing m m' with
  | zero => exact contDiff_zero.2 hb.continuous_uniformCompCoeff
  | succ k ih =>
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv_apply.2
      ⟨fun p ↦ (hb.differentiableAt_uniformCompCoeff_and_fderiv p).1, by simp, fun v ↦ ?_⟩
    rw [funext fun p ↦ (hb.differentiableAt_uniformCompCoeff_and_fderiv p).2 v]
    exact (ContDiff.sum fun j _ ↦ ((ih (a := spatialDeriv j a) hb).add
        (ih (a := a) (hb.spatialDeriv j))).const_smul _).add
      (ContDiff.sum fun j _ ↦ ((ih (a := frequencyDeriv j a) hb).add
        (ih (a := a) (hb.frequencyDeriv j))).const_smul _)

private theorem exists_bound_uniformCompCoeff (P : ∀ {m' : ℝ}, Symbol n W U m' → Prop)
    (hPspatial : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∀ j, P (spatialDeriv j a))
    (hPfrequency : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∀ j, P (frequencyDeriv j a))
    {K : Set (CoordinateSpace n)}
    (hP : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖((oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (ha : P a) (hb : b.IsUniform) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (uniformCompCoeff a b) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing m m' α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, hC0, hC⟩ := hb.exists_norm_uniformCompCoeff_le (hP ha)
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa using hC x hx ξ⟩
  | succ D ih =>
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C₁, hC₁0, hC₁⟩ := ih (a := spatialDeriv j a) (hPspatial ha j) hb α' []
          (by simpa using hD)
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih (a := a) ha (hb.spatialDeriv j) α' [] (by simpa using hD)
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
        have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
            coordinateDeriv [j] (fun y ↦ uniformCompCoeff a b (y, q.2)) q.1) =
              uniformCompCoeff (spatialDeriv j a) b + uniformCompCoeff a (spatialDeriv j b) :=
          funext fun q ↦ coordinateDeriv_fst_uniformCompCoeff hb j q.1 q.2
        rw [← mixedDeriv_coordinateDeriv_fst (contDiff_uniformCompCoeff hb), hfun]
        exact norm_mixedDeriv_add_le (contDiff_uniformCompCoeff hb)
          (contDiff_uniformCompCoeff (hb.spatialDeriv j)) (hC₁ x hx ξ) (hC₂ x hx ξ)
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD; omega
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih (a := frequencyDeriv j a) (hPfrequency ha j) hb α β' hlen
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih (a := a) ha (hb.frequencyDeriv j) α β' hlen
      refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
      have h₁ : ‖mixedDeriv α β' (uniformCompCoeff (frequencyDeriv j a) b) x ξ‖ ≤
          C₁ * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - (β' ++ [j]).length) / 2) := by
        convert hC₁ x hx ξ using 3; simp [List.length_append]; ring
      have h₂ : ‖mixedDeriv α β' (uniformCompCoeff a (frequencyDeriv j b)) x ξ‖ ≤
          C₂ * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - (β' ++ [j]).length) / 2) := by
        convert hC₂ x hx ξ using 3; simp [List.length_append]; ring
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun η ↦ uniformCompCoeff a b (q.1, η)) q.2) =
            uniformCompCoeff (frequencyDeriv j a) b + uniformCompCoeff a (frequencyDeriv j b) :=
        funext fun q ↦ coordinateDeriv_snd_uniformCompCoeff hb j q.1 q.2
      rw [← mixedDeriv_coordinateDeriv_snd, hfun]
      exact norm_mixedDeriv_add_le (contDiff_uniformCompCoeff hb)
        (contDiff_uniformCompCoeff (hb.frequencyDeriv j)) h₁ h₂

end Integrand

/-! ### The composition symbol `uniformSharp` -/

section UniformSharp

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- **The composition symbol with a uniform right factor.** For `a : Symbol n W U m'` and uniform
`b : Symbol n V W m`, `a.uniformSharp b hb` is a symbol of order `m' + m` quantizing on Schwartz
functions to `Op(a) ∘ Op(b)`. -/
def uniformSharp (hb : b.IsUniform) : Symbol n V U (m' + m) where
  coefficient := uniformCompCoeff a b
  contDiff_coefficient := contDiff_uniformCompCoeff hb
  exists_bound K hK α β := exists_bound_uniformCompCoeff (fun _ ↦ True) (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun {_} a' _ ↦ ((oneSubFrequencyLaplacian)^[n + 1] a').exists_bound_coefficient K hK)
    trivial hb α β

theorem coefficient_uniformSharp (hb : b.IsUniform) (x ξ : CoordinateSpace n) :
    (a.uniformSharp b hb).coefficient (x, ξ) =
      ∫ η, (((oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, ξ + (2 * π) • η)).comp
        (𝓕 (weightedSlice b x ξ) η) :=
  (rfl)

private lemma coefficient_uniformSharp_eq_uniformCompCoeff (hb : b.IsUniform) :
    (a.uniformSharp b hb).coefficient = uniformCompCoeff a b := (rfl)

private lemma uniformCompCoeff_congr {m₁ m₂ k₁ k₂ : ℝ} {a₁ : Symbol n W U m₁}
    {a₂ : Symbol n W U m₂} {b₁ : Symbol n V W k₁} {b₂ : Symbol n V W k₂}
    (ha : a₁.coefficient = a₂.coefficient) (hb : b₁.coefficient = b₂.coefficient) :
    uniformCompCoeff a₁ b₁ = uniformCompCoeff a₂ b₂ := by
  funext p; have ha' := iterate_oneSubFrequencyLaplacian_congr ha (n + 1)
  simp only [uniformCompCoeff, uniformCompIntegrand, ha', weightedSlice_congr hb]

/-- **Leibniz rule in the position** for `uniformSharp`. -/
theorem spatialDeriv_uniformSharp (hb : b.IsUniform) (j : Fin n) :
    spatialDeriv j (a.uniformSharp b hb) =
      (spatialDeriv j a).uniformSharp b hb +
        a.uniformSharp (spatialDeriv j b) (hb.spatialDeriv j) := by
  ext1; funext ⟨x, ξ⟩; rw [coefficient_spatialDeriv, coefficient_add, Pi.add_apply]
  exact coordinateDeriv_fst_uniformCompCoeff hb j x ξ

/-- **Leibniz rule in the frequency** for `uniformSharp`, on coefficients. -/
theorem coefficient_frequencyDeriv_uniformSharp (hb : b.IsUniform) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    (frequencyDeriv j (a.uniformSharp b hb)).coefficient (x, ξ) =
      ((frequencyDeriv j a).uniformSharp b hb).coefficient (x, ξ) +
        (a.uniformSharp (frequencyDeriv j b) (hb.frequencyDeriv j)).coefficient (x, ξ) := by
  rw [coefficient_frequencyDeriv]; exact coordinateDeriv_snd_uniformCompCoeff hb j x ξ

/-- **Leibniz rule in the frequency** for `uniformSharp`, as an equality of symbols. -/
theorem frequencyDeriv_uniformSharp (hb : b.IsUniform) (j : Fin n) :
    frequencyDeriv j (a.uniformSharp b hb) =
      inclusion (by linarith) ((frequencyDeriv j a).uniformSharp b hb) +
        inclusion (by linarith) (a.uniformSharp (frequencyDeriv j b) (hb.frequencyDeriv j)) := by
  ext1; funext ⟨x, ξ⟩
  rw [coefficient_add, Pi.add_apply, coefficient_inclusion, coefficient_inclusion,
    coefficient_frequencyDeriv_uniformSharp]

/-- **Composition preserves uniform symbol estimates.** -/
theorem IsUniform.uniformSharp (ha : a.IsUniform) (hb : b.IsUniform) :
    (a.uniformSharp b hb).IsUniform := isUniform_iff.2 fun α β ↦ by
  obtain ⟨C, hC0, hC⟩ := exists_bound_uniformCompCoeff IsUniform (fun ha' j ↦ ha'.spatialDeriv j)
    (fun ha' j ↦ ha'.frequencyDeriv j) (K := Set.univ)
    (fun ha' ↦ (ha'.iterate_oneSubFrequencyLaplacian (n + 1)).exists_bound_coefficient.imp
      fun _ hC ↦ ⟨hC.1, fun x _ ξ ↦ hC.2 x ξ⟩) ha hb α β
  exact ⟨C, hC0, fun x ξ ↦ hC x (Set.mem_univ x) ξ⟩

theorem HasCompactSpatialSupport.uniformSharp (ha : a.HasCompactSpatialSupport) (hb : b.IsUniform) :
    (a.uniformSharp b hb).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp
    (ha.iterate_oneSubFrequencyLaplacian (n + 1))
  refine hasCompactSpatialSupport_iff.mpr ⟨K, hK, fun x hx ξ ↦ ?_⟩
  rw [coefficient_uniformSharp]
  exact integral_eq_zero_of_ae (.of_forall fun η ↦ by
    dsimp only; rw [hKa x hx, ContinuousLinearMap.zero_comp]; rfl)

theorem add_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ + a₂).uniformSharp b hb = a₁.uniformSharp b hb + a₂.uniformSharp b hb := by
  ext1; funext p
  simp only [coefficient_add, Pi.add_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_add (hb.integrable_uniformCompIntegrand p)
      (hb.integrable_uniformCompIntegrand p)]
  have hlin (k : ℕ) : (oneSubFrequencyLaplacian (m := m'))^[k] (a₁ + a₂) =
      (oneSubFrequencyLaplacian (m := m'))^[k] a₁ +
        (oneSubFrequencyLaplacian (m := m'))^[k] a₂ := by
    induction k with | zero => rfl | succ k ih => simp [Function.iterate_succ_apply', ih]
  exact integral_congr_ae (.of_forall fun η ↦ by
    simp only [uniformCompIntegrand, hlin, coefficient_add, Pi.add_apply,
      ContinuousLinearMap.add_comp])

theorem uniformSharp_add (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) :
    a.uniformSharp (b₁ + b₂) (hb₁.add hb₂) = a.uniformSharp b₁ hb₁ + a.uniformSharp b₂ hb₂ := by
  ext1; funext p
  simp only [coefficient_add, Pi.add_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_add (hb₁.integrable_uniformCompIntegrand p)
      (hb₂.integrable_uniformCompIntegrand p)]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  have hF : 𝓕 (weightedSlice (b₁ + b₂) p.1 p.2) η =
      𝓕 (weightedSlice b₁ p.1 p.2) η + 𝓕 (weightedSlice b₂ p.1 p.2) η := by
    rw [weightedSlice_add, Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
    simp_rw [Pi.add_apply, Circle.smul_def, smul_add, ← Circle.smul_def]
    exact integral_add
      ((Real.fourierIntegral_convergent_iff η).2 (hb₁.integrable_weightedSlice p.1 p.2))
      ((Real.fourierIntegral_convergent_iff η).2 (hb₂.integrable_weightedSlice p.1 p.2))
  simp only [uniformCompIntegrand, hF, ContinuousLinearMap.comp_add]

@[simp]
theorem smul_uniformSharp (c : ℂ) (a : Symbol n W U m') (hb : b.IsUniform) :
    (c • a).uniformSharp b hb = c • a.uniformSharp b hb := by
  ext1; funext p
  simp only [coefficient_smul, Pi.smul_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_smul]
  have hlin (k : ℕ) : (oneSubFrequencyLaplacian (m := m'))^[k] (c • a) =
      c • (oneSubFrequencyLaplacian (m := m'))^[k] a := by
    induction k with | zero => rfl | succ k ih => simp [Function.iterate_succ_apply', ih]
  exact integral_congr_ae (.of_forall fun η ↦ by
    simp only [uniformCompIntegrand, hlin, coefficient_smul, Pi.smul_apply,
      ContinuousLinearMap.smul_comp])

@[simp]
theorem uniformSharp_smul (a : Symbol n W U m') (hb : b.IsUniform) (c : ℂ) :
    a.uniformSharp (c • b) (hb.smul c) = c • a.uniformSharp b hb := by
  ext1; funext p
  simp only [coefficient_smul, Pi.smul_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  have hF : 𝓕 (weightedSlice (c • b) p.1 p.2) η = c • 𝓕 (weightedSlice b p.1 p.2) η := by
    rw [weightedSlice_smul, Real.fourier_eq, Real.fourier_eq]
    simp_rw [Pi.smul_apply, Circle.smul_def, smul_comm _ c, integral_smul]
  simp only [uniformCompIntegrand, hF, ContinuousLinearMap.comp_smul]

@[simp]
theorem zero_uniformSharp (hb : b.IsUniform) : (0 : Symbol n W U m').uniformSharp b hb = 0 := by
  simpa using smul_uniformSharp (0 : ℂ) (0 : Symbol n W U m') hb

@[simp]
theorem uniformSharp_zero (a : Symbol n W U m') :
    a.uniformSharp (0 : Symbol n V W m) isUniform_zero = 0 := by
  simpa using uniformSharp_smul a (isUniform_zero (m := m) (V := V) (W := W)) 0

@[simp]
theorem neg_uniformSharp (a : Symbol n W U m') (hb : b.IsUniform) :
    (-a).uniformSharp b hb = -a.uniformSharp b hb := by
  simpa using smul_uniformSharp (-1 : ℂ) a hb

@[simp]
theorem uniformSharp_neg (a : Symbol n W U m') (hb : b.IsUniform) :
    a.uniformSharp (-b) hb.neg = -a.uniformSharp b hb := by
  simpa using uniformSharp_smul a hb (-1)

theorem sub_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ - a₂).uniformSharp b hb = a₁.uniformSharp b hb - a₂.uniformSharp b hb := by
  rw [sub_eq_add_neg, add_uniformSharp, neg_uniformSharp, ← sub_eq_add_neg]

theorem uniformSharp_sub (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) :
    a.uniformSharp (b₁ - b₂) (hb₁.sub hb₂) = a.uniformSharp b₁ hb₁ - a.uniformSharp b₂ hb₂ := by
  calc a.uniformSharp (b₁ - b₂) (hb₁.sub hb₂)
      = a.uniformSharp (b₁ + -b₂) (hb₁.add hb₂.neg) := by simp only [sub_eq_add_neg]
    _ = a.uniformSharp b₁ hb₁ - a.uniformSharp b₂ hb₂ := by
        rw [uniformSharp_add a hb₁ hb₂.neg, uniformSharp_neg, ← sub_eq_add_neg]

theorem inclusion_uniformSharp {m'' : ℝ} (h : m' ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    (inclusion h a).uniformSharp b hb = inclusion (by linarith) (a.uniformSharp b hb) := by
  ext1; simp only [coefficient_inclusion, coefficient_uniformSharp_eq_uniformCompCoeff]
  exact uniformCompCoeff_congr (coefficient_inclusion h a) rfl

theorem uniformSharp_inclusion {m'' : ℝ} (h : m ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    a.uniformSharp (inclusion h b) (hb.inclusion h) =
      inclusion (by linarith) (a.uniformSharp b hb) := by
  ext1; simp only [coefficient_inclusion, coefficient_uniformSharp_eq_uniformCompCoeff]
  exact uniformCompCoeff_congr rfl (coefficient_inclusion h b)

/-- Composing a smoothing symbol on the right with any uniform symbol yields a smoothing symbol. -/
theorem IsSmoothing.uniformSharp_right (ha : a.IsSmoothing) (b : Symbol n V W m)
    (hb : b.IsUniform) : (a.uniformSharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦ by
  obtain ⟨a', ha'⟩ := isSmoothing_iff.1 ha (m'' - m)
  refine ⟨Symbol.inclusion (by linarith) (a'.uniformSharp b hb), ?_⟩
  simp only [coefficient_inclusion, coefficient_uniformSharp_eq_uniformCompCoeff]
  exact uniformCompCoeff_congr ha' rfl

/-- Composing any symbol on the right with a symbol admitting uniform bounds of every real order
yields a smoothing symbol. -/
theorem isSmoothing_uniformSharp_of_forall_exists_isUniform {b : Symbol n V W m} (hb : b.IsUniform)
    (hbs : ∀ k : ℝ, ∃ b' : Symbol n V W k, b'.IsUniform ∧ b'.coefficient = b.coefficient)
    (a : Symbol n W U m') : (a.uniformSharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦ by
  obtain ⟨b', hb'u, hb'⟩ := hbs (m'' - m')
  refine ⟨Symbol.inclusion (by linarith) (a.uniformSharp b' hb'u), ?_⟩
  simp only [coefficient_inclusion, coefficient_uniformSharp_eq_uniformCompCoeff]
  exact uniformCompCoeff_congr rfl hb'

end UniformSharp

/-! ### Composition of quantizations on Schwartz space -/

section Operator

variable {a : Symbol n W U m'} {b : Symbol n V W m}

private lemma hasTemperateGrowth_sub_sq_rpow (x : CoordinateSpace n) (r : ℝ) :
    (fun y : CoordinateSpace n ↦ (1 + ‖x - y‖ ^ 2) ^ r).HasTemperateGrowth :=
  (Function.hasTemperateGrowth_one_add_norm_sq_rpow (CoordinateSpace n) r).comp
    (by fun_prop : (x - ·).HasTemperateGrowth)

private lemma IsUniform.integrable_fourier_smulLeftCLM_prod (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x ζ' : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪q.1, ζ' - q.2⟫) •
        (((1 + ‖x - q.1‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))) •
          b.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2)))
      (volume.prod volume) := by
  obtain ⟨Cb, _, hCb⟩ := hb.exists_bound_coefficient
  have hw_int : Integrable fun y : CoordinateSpace n ↦
      (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)) := by
    have hle (y : CoordinateSpace n) :
        (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)) ≤
          (1 + ‖x - y‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖x - y‖]) ?_
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hint_sub : Integrable fun y : CoordinateSpace n ↦
        (1 + ‖x - y‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
      simpa using integrable_one_add_norm_sq_rpow_neg_succ_div_two.comp_sub_left x
    exact hint_sub.mono'
      (hasTemperateGrowth_sub_sq_rpow x _).1.continuous.aestronglyMeasurable
      (.of_forall fun y ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact hle y)
  have hgu := (𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (μ := volume) (2 * π) m
  have hGcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪q.1, ζ' - q.2⟫) •
        (((1 + ‖x - q.1‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))) •
          b.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2)) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      (((hasTemperateGrowth_sub_sq_rpow x _).1.continuous.comp continuous_fst).smul
        ((b.contDiff_coefficient.continuous.comp (by fun_prop)).clm_apply
          ((𝓕 u).continuous.comp continuous_snd)))
  refine (hw_int.mul_prod (hgu.const_mul Cb)).mono' hGcont.aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  rw [Circle.norm_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc (1 + ‖x - q.1‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)) * ‖b.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2)‖
      ≤ (1 + ‖x - q.1‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)) *
          (Cb * (1 + ‖(2 * π) • q.2‖ ^ 2) ^ (m / 2) * ‖𝓕 u q.2‖) := by
        gcongr
        exact ((b.coefficient _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hCb q.1 _) (norm_nonneg _))
    _ = _ := by ring

private theorem IsUniform.fourier_smulLeftCLM_quantizeUniformCLM (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x ζ' : CoordinateSpace n) :
    𝓕 (SchwartzMap.smulLeftCLM W (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)))
        (quantizeUniformCLM b hb u)) ζ' =
      ∫ ζ, 𝐞 (-⟪x, ζ' - ζ⟫) • 𝓕 (weightedSlice b x ((2 * π) • ζ)) (ζ' - ζ) (𝓕 u ζ) := by
  set G : CoordinateSpace n × CoordinateSpace n → W := fun q ↦
    𝐞 (-⟪q.1, ζ' - q.2⟫) •
      (((1 + ‖x - q.1‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))) • b.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2))
  calc 𝓕 (SchwartzMap.smulLeftCLM W (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)))
          (quantizeUniformCLM b hb u)) ζ'
      = ∫ y, ∫ ζ, G (y, ζ) := by
        rw [SchwartzMap.fourier_coe, Real.fourier_eq]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        dsimp only
        rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_sub_sq_rpow x _),
          quantizeUniformCLM_apply, quantizeSchwartzValue_def, ← integral_smul, Circle.smul_def,
          ← integral_smul]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        dsimp only [G]
        rw [Circle.smul_def, Circle.smul_def,
          smul_comm ((1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))),
          smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
        congr 3; rw [inner_sub_right, real_inner_comm ζ y]; ring
    _ = ∫ ζ, ∫ y, G (y, ζ) :=
        integral_integral_swap (hb.integrable_fourier_smulLeftCLM_prod u x ζ')
    _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        dsimp only
        rw [← integral_add_left_eq_self (fun y ↦ G (y, ζ)) x]
        have hint : Integrable fun z ↦
            𝐞 (-⟪z, ζ' - ζ⟫) • weightedSlice b x ((2 * π) • ζ) z :=
          (Real.fourierIntegral_convergent_iff (ζ' - ζ)).2
            (hb.integrable_weightedSlice x ((2 * π) • ζ))
        rw [Real.fourier_eq, ContinuousLinearMap.integral_apply hint, Circle.smul_def,
          ← integral_smul]
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        have hnorm : ‖x - (x + z)‖ = ‖z‖ := by simp
        dsimp only [G]
        simp only [weightedSlice_apply, hnorm, inner_add_left, neg_add, AddChar.map_add_eq_mul,
          Circle.smul_def, Circle.coe_mul, smul_apply, smul_smul]

private theorem IsUniform.integrable_uniformComposeIntegrand (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪q.2, x⟫ •
      ((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, (2 * π) • q.1)
        (𝓕 (weightedSlice b x ((2 * π) • q.2)) (q.1 - q.2) (𝓕 u q.2)))
      (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := hb.exists_norm_uniformCompIntegrand_le
    (((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).exists_bound_coefficient {x}
      isCompact_singleton) ((n : ℝ) + 1)
  have hh := (𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (μ := volume) (2 * π) (m' + m)
  have hB : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (weightedSlice b x ((2 * π) • q.2)) (q.1 - q.2) := by
    simpa only [Function.comp_def] using hb.continuous_fourier_weightedSlice.comp (by fun_prop :
      Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ ((x, (2 * π) • q.2), q.1 - q.2))
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪q.2, x⟫ •
      ((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, (2 * π) • q.1)
        (𝓕 (weightedSlice b x ((2 * π) • q.2)) (q.1 - q.2) (𝓕 u q.2)) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      ((((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).contDiff_coefficient.continuous.comp
        (by fun_prop)).clm_apply (hB.clm_apply ((𝓕 u).continuous.comp continuous_snd)))
  refine ((hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    integrable_one_add_norm_sq_rpow_neg_succ_div_two).const_mul C).mono'
    hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  have hξ : (2 * π) • q.2 + (2 * π) • (q.1 - q.2) = (2 * π) • q.1 := by
    rw [← smul_add, add_sub_cancel]
  have h := hC x rfl ((2 * π) • q.2) (q.1 - q.2)
  rw [uniformCompIntegrand, hξ] at h
  rw [Circle.norm_smul, ContinuousLinearMap.mul_apply', ← ContinuousLinearMap.comp_apply]
  exact ((ContinuousLinearMap.le_opNorm _ (𝓕 u q.2)).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg _))).trans_eq (by ring)

private theorem IsUniform.integrable_fourier_weightedSlice_apply (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x ζ' : CoordinateSpace n) :
    Integrable fun ζ ↦ 𝐞 (-⟪x, ζ' - ζ⟫) •
      𝓕 (weightedSlice b x ((2 * π) • ζ)) (ζ' - ζ) (𝓕 u ζ) := by
  obtain ⟨Cb, _, hCb⟩ := hb.exists_norm_fourier_weightedSlice_le 0
  have hB : Continuous fun ζ : CoordinateSpace n ↦
      𝓕 (weightedSlice b x ((2 * π) • ζ)) (ζ' - ζ) := by
    simpa only [Function.comp_def] using hb.continuous_fourier_weightedSlice.comp (by fun_prop :
      Continuous fun ζ : CoordinateSpace n ↦ ((x, (2 * π) • ζ), ζ' - ζ))
  refine (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (μ := volume) (2 * π) m).const_mul
      Cb).mono'
    ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (hB.clm_apply (𝓕 u).continuous)).aestronglyMeasurable (.of_forall fun ζ ↦ ?_)
  rw [Circle.norm_smul]
  have h := hCb x ((2 * π) • ζ) (ζ' - ζ)
  simp only [neg_zero, zero_div, Real.rpow_zero, mul_one] at h
  exact ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg _))).trans_eq (by ring)

/-- **Composition of quantizations.** For any symbol `a` of order `m'` and any uniform symbol `b`
of order `m`, `Op(a # b) u = Op(a) (Op(b) u)` on Schwartz functions. -/
theorem quantizeSchwartzValue_uniformSharp [CompleteSpace W] [CompleteSpace U] (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.uniformSharp b hb).coefficient u x =
      quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x := by
  rw [quantizeSchwartzValue_eq_iterate_oneSubFrequencyLaplacian (n + 1) a
    (quantizeUniformCLM b hb u) x]
  set aN := (oneSubFrequencyLaplacian (m := m'))^[n + 1] a
  set F : CoordinateSpace n → CoordinateSpace n → U := fun ζ' ζ ↦ 𝐞 ⟪ζ, x⟫ •
    aN.coefficient (x, (2 * π) • ζ') (𝓕 (weightedSlice b x ((2 * π) • ζ)) (ζ' - ζ) (𝓕 u ζ))
  have hF : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ F q.1 q.2)
      (volume.prod volume) := hb.integrable_uniformComposeIntegrand u x
  have hR : quantizeSchwartzValue aN.coefficient
      (SchwartzMap.smulLeftCLM W (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)))
        (quantizeUniformCLM b hb u)) x = ∫ ζ', ∫ ζ, F ζ' ζ := by
    rw [quantizeSchwartzValue_def]
    refine integral_congr_ae (.of_forall fun ζ' ↦ ?_)
    dsimp only
    rw [hb.fourier_smulLeftCLM_quantizeUniformCLM u x ζ',
      ← (aN.coefficient (x, (2 * π) • ζ')).integral_comp_comm
        (hb.integrable_fourier_weightedSlice_apply u x ζ'), Circle.smul_def, ← integral_smul]
    refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
    dsimp only [F]
    rw [Circle.smul_def, Circle.smul_def, map_smul, smul_smul, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul]
    congr 3; rw [real_inner_comm (ζ' - ζ) x, inner_sub_left]; ring
  rw [hR, integral_integral_swap hF, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  dsimp only
  rw [← integral_add_right_eq_self (fun ζ' ↦ F ζ' ζ) ζ,
    coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff,
    ContinuousLinearMap.integral_apply (hb.integrable_uniformCompIntegrand _), Circle.smul_def,
    ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  dsimp only [F, uniformCompIntegrand, aN]
  rw [add_sub_cancel_right, smul_add, add_comm ((2 * π) • η), Circle.smul_def,
    ContinuousLinearMap.comp_apply]

/-- **Composition of uniform quantizations on Schwartz space**: `Op(a # b) = Op(a) ∘ Op(b)`. -/
theorem quantizeUniformCLM_uniformSharp [CompleteSpace W] [CompleteSpace U]
    (ha : a.IsUniform) (hb : b.IsUniform) :
    quantizeUniformCLM (a.uniformSharp b hb) (ha.uniformSharp hb) =
      (quantizeUniformCLM a ha).comp (quantizeUniformCLM b hb) := by
  ext u x; simp only [quantizeUniformCLM_apply, ContinuousLinearMap.comp_apply]
  exact quantizeSchwartzValue_uniformSharp hb u x

/-- **Uniqueness of the uniform composition symbol.** Any symbol whose quantization on compactly
supported Schwartz functions agrees with `Op(a) ∘ Op(b)` has the coefficient of `a # b`. -/
theorem coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq [CompleteSpace V]
    [CompleteSpace W] [CompleteSpace U] (hb : b.IsUniform) {m'' : ℝ} {c : Symbol n V U m''}
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u → ∀ x,
      quantizeSchwartzValue c.coefficient u x =
        quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x) :
    c.coefficient = (a.uniformSharp b hb).coefficient :=
  coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u hu ↦ funext fun x ↦
    (h u hu x).trans (quantizeSchwartzValue_uniformSharp hb u x).symm

/-- **Agreement with `Symbol.sharp`** when `b` has compact spatial support. -/
theorem uniformSharp_eq_sharp [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) :
    a.uniformSharp b hb.isUniform = a.sharp b hb := by
  ext1; refine coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq hb fun u _ x ↦ ?_
  rw [quantizeSchwartzValue_uniformSharp]
  congr 1; ext y; simp [HasCompactSupport.toSchwartzMap_toFun]

/-- The constant identity symbol `1` is a left identity for `uniformSharp`. -/
@[simp]
theorem const_id_uniformSharp [CompleteSpace V] [CompleteSpace W] (hb : b.IsUniform) :
    (const (ContinuousLinearMap.id ℂ W)).uniformSharp b hb = inclusion (by simp) b := by
  ext1; symm; rw [coefficient_inclusion]
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq hb fun u _ x ↦ ?_
  rw [← quantizeUniformCLM_apply (const (ContinuousLinearMap.id ℂ W))
    (isUniform_const (ContinuousLinearMap.id ℂ W)) (quantizeUniformCLM b hb u) x,
    quantizeUniformCLM_const]; simp

/-- The constant identity symbol `1` is a right identity for `uniformSharp`. -/
@[simp]
theorem uniformSharp_const_id [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m) :
    a.uniformSharp (const (ContinuousLinearMap.id ℂ V)) (isUniform_const _) =
      inclusion (by simp) a := by
  ext1; symm; rw [coefficient_inclusion]
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq
    (isUniform_const (ContinuousLinearMap.id ℂ V)) fun u _ x ↦ ?_
  have hid : SchwartzMap.postcompCLM (ContinuousLinearMap.id ℂ V) u = u := by ext y; simp
  rw [quantizeUniformCLM_const, hid]

/-- **Associativity of `uniformSharp`**: `(a # b) # c = a # (b # c)` up to order associativity. -/
theorem uniformSharp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U']
    [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] [CompleteSpace U'] {m'' : ℝ}
    (a : Symbol n U U' m'') {b : Symbol n W U m'} {c : Symbol n V W m}
    (hb : b.IsUniform) (hc : c.IsUniform) :
    (a.uniformSharp b hb).uniformSharp c hc =
      inclusion (add_assoc m'' m' m).ge
        (a.uniformSharp (b.uniformSharp c hc) (hb.uniformSharp hc)) := by
  ext1; rw [coefficient_inclusion]
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq (hb.uniformSharp hc)
    fun u _ x ↦ ?_
  rw [quantizeSchwartzValue_uniformSharp hc, quantizeSchwartzValue_uniformSharp hb,
    quantizeUniformCLM_uniformSharp hb hc, ContinuousLinearMap.comp_apply]

/-! ### Frequency multipliers and Bessel potentials in the uniform calculus -/

/-- **Right composition with a frequency-only symbol is exact**: `a # c(ξ) = a ∘ c(ξ)`. -/
theorem uniformSharp_ofFrequency [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {c : CoordinateSpace n → V →L[ℂ] W} (hc : ContDiff ℝ ∞ c)
    (hcbound : ∀ k : ℕ, ∃ C, ∀ ξ,
      ‖iteratedFDeriv ℝ k c ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2)) :
    a.uniformSharp (ofFrequency c hc hcbound) (isUniform_ofFrequency hc hcbound) =
      a.comp (ofFrequency c hc hcbound) := by
  have hctemp : c.HasTemperateGrowth :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hc hcbound
  ext1; symm
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq
    (isUniform_ofFrequency hc hcbound) fun u _ x ↦ ?_
  have hq : quantizeUniformCLM (ofFrequency c hc hcbound) (isUniform_ofFrequency hc hcbound) u =
      quantizeFrequencyCLM c u := by
    ext y; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_ofFrequency hc hcbound u y
  rw [hq, quantizeSchwartzValue_quantizeFrequencyCLM hctemp]
  exact quantizeSchwartzValue_congr_left (fun ξ ↦ by simp) u

/-- **Right composition with the Bessel potential symbol is exact**:
`a # ⟨ξ / 2π⟩ ^ s = a ∘ ⟨ξ / 2π⟩ ^ s`. -/
@[simp]
theorem uniformSharp_besselPotential [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (s : ℝ) :
    a.uniformSharp (besselPotential s) (isUniform_besselPotential s) =
      a.comp (besselPotential s) := by
  have hg : Function.HasTemperateGrowth
      (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow (CoordinateSpace n) (s / 2))
  ext1; symm
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq
    (isUniform_besselPotential s) fun u _ x ↦ ?_
  have hq : quantizeUniformCLM (besselPotential s) (isUniform_besselPotential s) u =
      SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u := by
    ext y; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_besselPotential s u y
  rw [hq, quantizeSchwartzValue_fourierMultiplierCLM hg]
  exact quantizeSchwartzValue_congr_left
    (fun ξ ↦ by simp only [coefficient_comp, coefficient_besselPotential,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]) u

/-- **Left composition with a frequency-only symbol on Schwartz space**: `c(D) ∘ Op(b) = Op(c # b)`.
-/
theorem quantizeUniformCLM_ofFrequency_uniformSharp [CompleteSpace W] [CompleteSpace U]
    {c : CoordinateSpace n → W →L[ℂ] U} (hc : ContDiff ℝ ∞ c)
    (hcbound : ∀ k : ℕ, ∃ C, ∀ ξ,
      ‖iteratedFDeriv ℝ k c ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2)) (hb : b.IsUniform) :
    quantizeUniformCLM ((ofFrequency c hc hcbound).uniformSharp b hb)
        ((isUniform_ofFrequency hc hcbound).uniformSharp hb) =
      (quantizeFrequencyCLM c).comp (quantizeUniformCLM b hb) := by
  rw [quantizeUniformCLM_uniformSharp (isUniform_ofFrequency hc hcbound) hb]
  congr 1; ext u x; rw [quantizeUniformCLM_apply]
  exact quantizeSchwartzValue_ofFrequency hc hcbound u x

/-- **Left composition with the Bessel multiplier**: `J^s ∘ Op(b) = Op(⟨ξ / 2π⟩ ^ s # b)`. -/
theorem quantizeUniformCLM_besselPotential_uniformSharp [CompleteSpace W]
    (hb : b.IsUniform) (s : ℝ) :
    quantizeUniformCLM ((besselPotential s : Symbol n W W s).uniformSharp b hb)
        ((isUniform_besselPotential s).uniformSharp hb) =
      (SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))).comp
        (quantizeUniformCLM b hb) := by
  rw [quantizeUniformCLM_uniformSharp (isUniform_besselPotential s) hb]
  congr 1; ext u x; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_besselPotential s u x

end Operator

end Symbol

end TauCeti
