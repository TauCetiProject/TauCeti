/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.UniformlySmoothing
public import TauCeti.Analysis.Pseudodifferential.Symbol.WeightedSlice
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import TauCeti.Algebra.Module.LinearMap.Iterate
import TauCeti.Analysis.Calculus.CoordinateDeriv.ParametricIntegral
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.GroupTheory.GroupAction.Hom

/-!
# Explicit composition symbol with a uniform right factor

Constructs `a.uniformSharp b hb : Symbol n V U (m' + m)` for every symbol `a` of order `m'` and
uniform symbol `b` (`IsUniform`) of order `m`, dropping the compact spatial support hypothesis of
`Composition.Basic`. Integrating by parts `2(n + 1)` times in frequency via
`oneSubFrequencyLaplacian` and `weightedSlice` yields
`(a # b)(x, ξ) = ∫ ((1 - Δ_ξ) ^ (n + 1) a)(x, ξ + 2πη) ∘ 𝓕 (weightedSlice b x ξ) η dη`.

## Main results

* `uniformSharp`, `IsUniform.uniformSharp`, `coefficient_uniformSharp_congr`,
  `spatialDeriv_uniformSharp`, `frequencyDeriv_uniformSharp`: composition symbol, preservation of
  `IsUniform`, order independence, and Leibniz rules.
* `IsUniformlySmoothing.uniformSharp_right`, `IsUniformlySmoothing.uniformSharp_left`,
  `IsUniformlySmoothing.isSmoothing_uniformSharp_left`: ideal closure under `uniformSharp`.
* `quantizeSchwartzValue_uniformSharp`, `quantizeUniformCLM_uniformSharp`, `uniformSharp_eq_sharp`:
  `Op(a # b) = Op(a) ∘ Op(b)` on Schwartz space and agreement with `sharp`.
* `const_uniformSharp`, `const_id_uniformSharp`, `uniformSharp_eq_comp_of_coefficient_eq`,
  `uniformSharp_const`, `uniformSharp_const_id`, `uniformSharp_assoc`, `uniformSharp_ofFrequency`,
  `uniformSharp_besselPotential`, `quantizeUniformCLM_besselPotential_uniformSharp`: unit laws,
  associativity, and composition with frequency multipliers and Bessel potentials.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* H. Kumano-go, *Pseudo-Differential Operators*, MIT Press, 1981, Chapter 2, §1–§2.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §2.
-/

public section
noncomputable section

open MeasureTheory Real FourierTransform
open ContinuousLinearMap (compL bilinearRestrictScalars_apply_apply compL_apply comp_apply
  opNorm_comp_le le_opNorm integral_apply)
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
  refine ⟨Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * Cb, by positivity, fun x hx ξ η ↦ ?_⟩
  have hshift := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) |m'| η
  rw [abs_abs] at hshift
  have hpeetre := (one_add_norm_add_sq_rpow_le_mul m' ξ ((2 * π) • η)).trans
    (mul_le_mul_of_nonneg_left hshift (by positivity))
  have hξ : (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
  have hη : (1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m'|) / 2) =
      (1 + ‖η‖ ^ 2) ^ (-r / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
  exact (opNorm_comp_le _ _).trans ((mul_le_mul ((hCa x hx _).trans
    (mul_le_mul_of_nonneg_left hpeetre hCa0)) (hCb x ξ η) (norm_nonneg _)
    (by positivity)).trans_eq (by rw [← hξ, ← hη]; ring))

private theorem IsUniform.continuous_uniformCompIntegrand (hb : b.IsUniform) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      uniformCompIntegrand a b q.1 q.2 :=
  (((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).contDiff_coefficient.continuous.comp
    ((continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).add
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
  set M := (2 : ℝ) ^ |m' + m| * (1 + ‖p₀.2‖ ^ 2) ^ ((m' + m) / 2)
  refine ⟨C * M, by positivity, fun p hp₁ hp₂ η ↦ (hC p.1 hp₁ p.2 η).trans ?_⟩
  have hMp := one_add_norm_sq_rpow_le_of_norm_sub_le_one
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp₂) (m' + m); gcongr

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
    with p hp₁ hp₂ using .of_forall (hC p hp₁ hp₂)

private theorem IsUniform.exists_norm_uniformCompCoeff_le (hb : b.IsUniform)
    {K : Set (CoordinateSpace n)}
    (ha : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖uniformCompCoeff a b (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_uniformCompIntegrand_le ha ((n : ℝ) + 1)
  exact ⟨C * ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2),
    mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity), fun x hx ξ ↦
    (norm_integral_le_of_norm_le (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
      (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2))) (.of_forall fun η ↦ hC x hx ξ η)).trans_eq
      (by rw [integral_const_mul]; ring)⟩

private theorem uniformCompIntegrand_eq_bilinear (a : Symbol n W U m') (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) (η : CoordinateSpace n) :
    uniformCompIntegrand a b p η = (compL ℂ V W U).bilinearRestrictScalars ℝ
      (((oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (p.1, p.2 + (2 * π) • η))
      (𝓕 (weightedSlice b p.1 p.2) η) := by
  simp only [uniformCompIntegrand, bilinearRestrictScalars_apply_apply, compL_apply]

private lemma coordinateDeriv_fst_uniformCompIntegrand (hb : b.IsUniform) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun x' ↦ uniformCompIntegrand a b (x', ξ) η) x =
      uniformCompIntegrand (spatialDeriv j a) b (x, ξ) η +
        uniformCompIntegrand a (spatialDeriv j b) (x, ξ) η := by
  set aN := (oneSubFrequencyLaplacian (m := m'))^[n + 1] a; set ζ := ξ + (2 * π) • η
  have hf : ContDiff ℝ 1 fun x' ↦ aN.coefficient (x', ζ) :=
    (aN.contDiff_coefficient_slice ζ).of_le (by simp)
  have hg : ContDiff ℝ 1 fun x' ↦ 𝓕 (weightedSlice b x' ξ) η :=
    ((hb.contDiff_fourier_weightedSlice η).comp (contDiff_prodMk_left ξ)).of_le (by simp)
  have hBfull := hb.differentiableAt_fourier_weightedSlice_and_fderiv η (x, ξ)
  dsimp only [uniformCompIntegrand]
  rw [coordinateDeriv_singleton_clm_comp hf hg j x, ← coefficient_spatialDeriv,
    ← spatialDeriv_iterate_oneSubFrequencyLaplacian,
    coordinateDeriv_fst_eq_fderiv (p := (x, ξ)) hBfull.1, hBfull.2]
  simp [aN, ζ]

private lemma coordinateDeriv_snd_uniformCompIntegrand (hb : b.IsUniform) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ' ↦ uniformCompIntegrand a b (x, ξ') η) ξ =
      uniformCompIntegrand (frequencyDeriv j a) b (x, ξ) η +
        uniformCompIntegrand a (frequencyDeriv j b) (x, ξ) η := by
  set aN := (oneSubFrequencyLaplacian (m := m'))^[n + 1] a; set c := (2 * π) • η
  have hf : ContDiff ℝ 1 fun ξ' ↦ aN.coefficient (x, ξ' + c) :=
    ((aN.contDiff_coefficient.comp (contDiff_prodMk_right x)).comp
      (contDiff_id.add contDiff_const)).of_le (by simp)
  have hg : ContDiff ℝ 1 fun ξ' ↦ 𝓕 (weightedSlice b x ξ') η :=
    ((hb.contDiff_fourier_weightedSlice η).comp (contDiff_prodMk_right x)).of_le (by simp)
  have hA : coordinateDeriv [j] (fun ξ' ↦ aN.coefficient (x, ξ' + c)) ξ =
      (frequencyDeriv j aN).coefficient (x, ξ + c) := by
    rw [coordinateDeriv_cons, coordinateDeriv_nil,
      fderiv_comp_add_right (f := fun ζ ↦ aN.coefficient (x, ζ)), fderiv_coefficient_slice_single]
  have hBfull := hb.differentiableAt_fourier_weightedSlice_and_fderiv η (x, ξ)
  dsimp only [uniformCompIntegrand]
  rw [coordinateDeriv_singleton_clm_comp hf hg j ξ, hA,
    ← frequencyDeriv_iterate_oneSubFrequencyLaplacian,
    coordinateDeriv_snd_eq_fderiv (p := (x, ξ)) hBfull.1, hBfull.2]
  simp [aN, c]

private lemma differentiableAt_uniformCompIntegrand (hb : b.IsUniform) (η : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ uniformCompIntegrand a b p η) p := by
  set aN := (oneSubFrequencyLaplacian (m := m'))^[n + 1] a
  simp_rw [uniformCompIntegrand_eq_bilinear a b]
  exact (((compL ℂ V W U).bilinearRestrictScalars ℝ).differentiableAt.comp p
    ((aN.contDiff_coefficient.differentiable (by simp) _).comp p
      (differentiableAt_fst.prodMk (differentiableAt_snd.add_const _)))).clm_apply
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
  let w {m₁ m₂ : ℝ} (a' : Symbol n W U m₁) {b' : Symbol n V W m₂} (hb' : b'.IsUniform) :=
    hb'.exists_norm_uniformCompIntegrand_le_weight (a := a') p₀
  choose C₁ _ hC₁ using fun j ↦ w (Symbol.spatialDeriv j a) hb
  choose C₂ _ hC₂ using fun j ↦ w a (hb.spatialDeriv j)
  choose C₃ _ hC₃ using fun j ↦ w (Symbol.frequencyDeriv j a) hb
  choose C₄ _ hC₄ using fun j ↦ w a (hb.frequencyDeriv j)
  have hc {m₁ m₂ : ℝ} (a' : Symbol n W U m₁) {b' : Symbol n V W m₂} (hb' : b'.IsUniform)
      (p : CoordinateSpace n × CoordinateSpace n) : Continuous (uniformCompIntegrand a' b' p) :=
    hb'.continuous_uniformCompIntegrand.comp (continuous_const.prodMk continuous_id)
  have key := differentiableAt_integral_and_fderiv_apply_eq_sum
    (differentiableAt_uniformCompIntegrand hb) (fderiv_uniformCompIntegrand hb)
    hb.integrable_uniformCompIntegrand
    (fun j p ↦ (hc (Symbol.spatialDeriv j a) hb p).add (hc a (hb.spatialDeriv j) p))
    (fun j p ↦ (hc (Symbol.frequencyDeriv j a) hb p).add (hc a (hb.frequencyDeriv j) p))
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
      (∑ j, (C₁ j + C₂ j) + ∑ j, (C₃ j + C₄ j))) p₀ fun η p hp ↦ by
      have h1 : p.1 ∈ Metric.closedBall p₀.1 1 := Metric.mem_closedBall.2
        (((le_max_left _ _).trans Prod.dist_eq.ge).trans (Metric.mem_ball.1 hp).le)
      have h2 : p.2 ∈ Metric.closedBall p₀.2 1 := Metric.mem_closedBall.2
        (((le_max_right _ _).trans Prod.dist_eq.ge).trans (Metric.mem_ball.1 hp).le)
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]; gcongr with j _ j _
      · rw [add_mul]; exact (norm_add_le _ _).trans (add_le_add (hC₁ _ _ h1 h2 _) (hC₂ _ _ h1 h2 _))
      · rw [add_mul]; exact (norm_add_le _ _).trans (add_le_add (hC₃ _ _ h1 h2 _) (hC₄ _ _ h1 h2 _))
  refine ⟨key.1, fun v ↦ (key.2 v).trans ?_⟩
  congr 1 <;> refine Finset.sum_congr rfl fun j _ ↦ congrArg _ (integral_add
    (hb.integrable_uniformCompIntegrand p₀) ?_)
  · exact (hb.spatialDeriv j).integrable_uniformCompIntegrand p₀
  · exact (hb.frequencyDeriv j).integrable_uniformCompIntegrand p₀

private theorem coordinateDeriv_fst_uniformCompCoeff (hb : b.IsUniform) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x' ↦ uniformCompCoeff a b (x', ξ)) x =
      uniformCompCoeff (spatialDeriv j a) b (x, ξ) +
        uniformCompCoeff a (spatialDeriv j b) (x, ξ) := by
  have hd := hb.differentiableAt_uniformCompCoeff_and_fderiv (a := a) (x, ξ)
  rw [coordinateDeriv_fst_eq_fderiv (p := (x, ξ)) hd.1, hd.2]; simp [Finset.sum_add_distrib]

private theorem coordinateDeriv_snd_uniformCompCoeff (hb : b.IsUniform) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ' ↦ uniformCompCoeff a b (x, ξ')) ξ =
      uniformCompCoeff (frequencyDeriv j a) b (x, ξ) +
        uniformCompCoeff a (frequencyDeriv j b) (x, ξ) := by
  have hd := hb.differentiableAt_uniformCompCoeff_and_fderiv (a := a) (x, ξ)
  rw [coordinateDeriv_snd_eq_fderiv (p := (x, ξ)) hd.1, hd.2]; simp [Finset.sum_add_distrib]

private theorem contDiff_uniformCompCoeff (hb : b.IsUniform) :
    ContDiff ℝ ∞ (uniformCompCoeff a b) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing m m' with
  | zero => exact contDiff_zero.2 hb.continuous_uniformCompCoeff
  | succ k ih =>
    rw [Nat.cast_succ]; refine contDiff_succ_iff_fderiv_apply.2
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
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β (uniformCompCoeff a b) x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_le_of_leibniz (ι := Unit) 0 P hPspatial hPfrequency
    (fun b ↦ (b ()).IsUniform) (fun hb j ↦ hb.spatialDeriv j) (fun hb j ↦ hb.frequencyDeriv j)
    (fun a b _ _ ↦ uniformCompCoeff a (b ()))
    (fun _ _ hb _ ↦ contDiff_uniformCompCoeff hb)
    (fun _ _ hb j _ ↦ coordinateDeriv_fst_uniformCompCoeff hb j)
    (fun _ _ hb j _ ↦ coordinateDeriv_snd_uniformCompCoeff hb j)
    (fun _ ha _ hb ↦ by
      obtain ⟨C, hC0, hC⟩ := hb.exists_norm_uniformCompCoeff_le (hP ha)
      exact ⟨C, hC0, fun _ x hx ξ ↦ by simpa only [sub_zero] using hC x hx ξ⟩)
    a ha (b := fun _ ↦ b) hb α β
  exact ⟨C, hC0, fun x hx ξ ↦ by simpa only [sub_zero] using hC () x hx ξ⟩

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
  exists_bound K hK := exists_bound_uniformCompCoeff (fun _ ↦ True) (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun {_} a' _ ↦ (oneSubFrequencyLaplacian^[n + 1] a').exists_bound_coefficient K hK) trivial hb

theorem coefficient_uniformSharp (hb : b.IsUniform) (x ξ : CoordinateSpace n) :
    (a.uniformSharp b hb).coefficient (x, ξ) =
      ∫ η, (((oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, ξ + (2 * π) • η)).comp
        (𝓕 (weightedSlice b x ξ) η) := (rfl)

private lemma coefficient_uniformSharp_eq_uniformCompCoeff (hb : b.IsUniform) :
    (a.uniformSharp b hb).coefficient = uniformCompCoeff a b := (rfl)

/-- The coefficient of `a.uniformSharp b hb` depends only on the coefficients of `a` and `b`, not on
their symbol orders. -/
theorem coefficient_uniformSharp_congr {m₁ m₂ k₁ k₂ : ℝ} {a₁ : Symbol n W U m₁}
    {a₂ : Symbol n W U m₂} {b₁ : Symbol n V W k₁} {b₂ : Symbol n V W k₂}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform)
    (ha : a₁.coefficient = a₂.coefficient) (hb : b₁.coefficient = b₂.coefficient) :
    (a₁.uniformSharp b₁ hb₁).coefficient = (a₂.uniformSharp b₂ hb₂).coefficient := by
  funext p; have ha' := coefficient_iterate_oneSubFrequencyLaplacian_congr ha (n + 1)
  simp only [coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff, uniformCompIntegrand,
    ha', weightedSlice_congr hb]

/-- **Leibniz rule in the position** for `uniformSharp`. -/
theorem spatialDeriv_uniformSharp (hb : b.IsUniform) (j : Fin n) :
    spatialDeriv j (a.uniformSharp b hb) =
      (spatialDeriv j a).uniformSharp b hb +
        a.uniformSharp (spatialDeriv j b) (hb.spatialDeriv j) := by
  ext ⟨x, ξ⟩ : 2
  rw [coefficient_spatialDeriv, coefficient_add, Pi.add_apply]
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
  ext ⟨x, ξ⟩ : 2
  rw [coefficient_add, Pi.add_apply, coefficient_inclusion,
    coefficient_inclusion, coefficient_frequencyDeriv_uniformSharp]

/-- **Composition preserves uniform symbol estimates.** -/
theorem IsUniform.uniformSharp (ha : a.IsUniform) (hb : b.IsUniform) :
    (a.uniformSharp b hb).IsUniform := isUniform_iff.2 fun α β ↦ by
  obtain ⟨C, hC0, hC⟩ := exists_bound_uniformCompCoeff IsUniform (fun ha' j ↦ ha'.spatialDeriv j)
    (fun ha' j ↦ ha'.frequencyDeriv j) (K := Set.univ)
    (fun ha' ↦ (ha'.iterate_oneSubFrequencyLaplacian (n + 1)).exists_bound_coefficient.imp
      fun _ hC ↦ ⟨hC.1, fun x _ ξ ↦ hC.2 x ξ⟩) ha hb α β
  exact ⟨C, hC0, fun x ξ ↦ hC x (Set.mem_univ x) ξ⟩

theorem HasCompactSpatialSupport.uniformSharp (ha : a.HasCompactSpatialSupport) (hb : b.IsUniform) :
    (a.uniformSharp b hb).HasCompactSpatialSupport :=
  let ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp (ha.iterate_oneSubFrequencyLaplacian (n + 1))
  hasCompactSpatialSupport_iff.mpr ⟨K, hK, fun x hx ξ ↦ by
    rw [coefficient_uniformSharp]
    exact integral_eq_zero_of_ae (.of_forall fun _ ↦ by
      dsimp only; rw [hKa x hx _, ContinuousLinearMap.zero_comp, Pi.zero_apply])⟩

theorem add_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ + a₂).uniformSharp b hb = a₁.uniformSharp b hb + a₂.uniformSharp b hb := by
  ext p : 2; simp only [coefficient_add, Pi.add_apply,
    coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff,
    ← integral_add (hb.integrable_uniformCompIntegrand p) (hb.integrable_uniformCompIntegrand p)]
  exact integral_congr_ae (.of_forall fun _ ↦ by
    simp only [uniformCompIntegrand, iterate_map_add, coefficient_add, Pi.add_apply,
      ContinuousLinearMap.add_comp])

theorem uniformSharp_add (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) :
    a.uniformSharp (b₁ + b₂) (hb₁.add hb₂) = a.uniformSharp b₁ hb₁ + a.uniformSharp b₂ hb₂ := by
  ext p : 2; simp only [coefficient_add, Pi.add_apply,
    coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff,
    ← integral_add (hb₁.integrable_uniformCompIntegrand p) (hb₂.integrable_uniformCompIntegrand p)]
  exact integral_congr_ae (.of_forall fun _ ↦ by
    simp only [uniformCompIntegrand, weightedSlice_add,
      (hb₁.integrable_weightedSlice p.1 p.2).fourier_add (hb₂.integrable_weightedSlice p.1 p.2),
      Pi.add_apply, ContinuousLinearMap.comp_add])

@[simp] theorem smul_uniformSharp (c : ℂ) (a : Symbol n W U m') (hb : b.IsUniform) :
    (c • a).uniformSharp b hb = c • a.uniformSharp b hb := by
  ext p : 2; simp only [coefficient_smul, Pi.smul_apply,
    coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff, ← integral_smul]
  exact integral_congr_ae (.of_forall fun _ ↦ by
    simp only [uniformCompIntegrand, TauCeti.iterate_map_smul, coefficient_smul, Pi.smul_apply,
      ContinuousLinearMap.smul_comp])

@[simp] theorem uniformSharp_smul (a : Symbol n W U m') (hb : b.IsUniform) (c : ℂ) :
    a.uniformSharp (c • b) (hb.smul c) = c • a.uniformSharp b hb := by
  ext p : 2; simp only [coefficient_smul, Pi.smul_apply,
    coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff, ← integral_smul]
  exact integral_congr_ae (.of_forall fun η ↦ by
    simp only [uniformCompIntegrand, weightedSlice_smul,
      congrFun (Real.fourier_const_smul c (weightedSlice b p.1 p.2)) η, Pi.smul_apply,
      ContinuousLinearMap.comp_smul])

@[simp] theorem zero_uniformSharp (hb : b.IsUniform) :
    (0 : Symbol n W U m').uniformSharp b hb = 0 := by simpa using smul_uniformSharp (0 : ℂ) 0 hb

@[simp] theorem uniformSharp_zero (a : Symbol n W U m') :
    a.uniformSharp (0 : Symbol n V W m) isUniform_zero = 0 := by
  simpa using uniformSharp_smul a (isUniform_zero (m := m)) 0

@[simp] theorem neg_uniformSharp (a : Symbol n W U m') (hb : b.IsUniform) :
    (-a).uniformSharp b hb = -a.uniformSharp b hb := by simpa using smul_uniformSharp (-1 : ℂ) a hb

@[simp] theorem uniformSharp_neg (a : Symbol n W U m') (hb : b.IsUniform) :
    a.uniformSharp (-b) hb.neg = -a.uniformSharp b hb := by simpa using uniformSharp_smul a hb (-1)

theorem sub_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ - a₂).uniformSharp b hb = a₁.uniformSharp b hb - a₂.uniformSharp b hb := by
  rw [sub_eq_add_neg, add_uniformSharp, neg_uniformSharp, ← sub_eq_add_neg]

theorem uniformSharp_sub (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) :
    a.uniformSharp (b₁ - b₂) (hb₁.sub hb₂) = a.uniformSharp b₁ hb₁ - a.uniformSharp b₂ hb₂ := by
  rw [eq_sub_iff_add_eq, ← uniformSharp_add a (hb₁.sub hb₂) hb₂]; ext1
  exact coefficient_uniformSharp_congr _ _ rfl (congrArg Symbol.coefficient (sub_add_cancel b₁ b₂))

theorem inclusion_uniformSharp {m'' : ℝ} (h : m' ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    (inclusion h a).uniformSharp b hb = inclusion (by linarith) (a.uniformSharp b hb) := by
  ext1; rw [coefficient_inclusion]; exact coefficient_uniformSharp_congr hb hb (by simp) rfl

theorem uniformSharp_inclusion {m'' : ℝ} (h : m ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    a.uniformSharp (inclusion h b) (hb.inclusion h) =
      inclusion (by linarith) (a.uniformSharp b hb) := by
  ext1; rw [coefficient_inclusion]; exact coefficient_uniformSharp_congr _ hb rfl (by simp)

/-- Composing a smoothing symbol on the right with any uniform symbol yields a smoothing symbol. -/
theorem IsSmoothing.uniformSharp_right (ha : a.IsSmoothing) (b : Symbol n V W m)
    (hb : b.IsUniform) : (a.uniformSharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦
  let ⟨a', ha'⟩ := isSmoothing_iff.1 ha (m'' - m)
  ⟨Symbol.inclusion (by linarith) (a'.uniformSharp b hb),
    by rw [coefficient_inclusion]; exact coefficient_uniformSharp_congr hb hb ha' rfl⟩

/-- Composing on the right with a uniformly smoothing symbol yields a smoothing symbol. -/
theorem IsUniformlySmoothing.isSmoothing_uniformSharp_left {b : Symbol n V W m}
    (hb : b.IsUniformlySmoothing) (a : Symbol n W U m') :
    (a.uniformSharp b hb.isUniform).IsSmoothing := isSmoothing_iff.2 fun m'' ↦
  let ⟨b', hb'u, hb'⟩ := isUniformlySmoothing_iff.mp hb (m'' - m')
  ⟨Symbol.inclusion (by linarith) (a.uniformSharp b' hb'u),
    by rw [coefficient_inclusion]; exact coefficient_uniformSharp_congr hb'u hb.isUniform rfl hb'⟩

/-- Uniformly smoothing symbols form a right ideal under `uniformSharp`. -/
theorem IsUniformlySmoothing.uniformSharp_right (ha : a.IsUniformlySmoothing)
    {b : Symbol n V W m} (hb : b.IsUniform) :
    (a.uniformSharp b hb).IsUniformlySmoothing := isUniformlySmoothing_iff.mpr fun m'' ↦
  let ⟨a', ha'u, ha'⟩ := isUniformlySmoothing_iff.mp ha (m'' - m)
  ⟨Symbol.inclusion (by linarith) (a'.uniformSharp b hb), (ha'u.uniformSharp hb).inclusion _,
    by rw [coefficient_inclusion]; exact coefficient_uniformSharp_congr hb hb ha' rfl⟩

/-- Uniformly smoothing symbols form a left ideal under `uniformSharp`. -/
theorem IsUniformlySmoothing.uniformSharp_left {b : Symbol n V W m}
    (hb : b.IsUniformlySmoothing) {a : Symbol n W U m'} (ha : a.IsUniform) :
    (a.uniformSharp b hb.isUniform).IsUniformlySmoothing := isUniformlySmoothing_iff.mpr fun m'' ↦
  let ⟨b', hb'u, hb'⟩ := isUniformlySmoothing_iff.mp hb (m'' - m')
  ⟨Symbol.inclusion (by linarith) (a.uniformSharp b' hb'u), (ha.uniformSharp hb'u).inclusion _,
    by rw [coefficient_inclusion]; exact coefficient_uniformSharp_congr hb'u hb.isUniform rfl hb'⟩

end UniformSharp

/-! ### Composition of quantizations on Schwartz space -/

section Operator

variable {a : Symbol n W U m'} {b : Symbol n V W m}

private lemma IsUniform.integrable_fourier_smulLeftCLM_prod (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x ζ' : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪q.1, ζ' - q.2⟫) • (((1 + ‖x - q.1‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))) •
        b.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2))) (volume.prod volume) := by
  obtain ⟨Cb, _, hCb⟩ := hb.exists_bound_coefficient
  have hw_int : Integrable fun y : CoordinateSpace n ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)) :=
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.comp_sub_left x).mono'
      (Function.hasTemperateGrowth_one_add_norm_sub_sq_rpow x _).1.continuous.aestronglyMeasurable
      (.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖x - y‖])
          (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]))
  refine (hw_int.mul_prod (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm
      (μ := volume) (2 * π) m).const_mul Cb)).mono'
    ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (((Function.hasTemperateGrowth_one_add_norm_sub_sq_rpow x _).1.continuous.comp
        continuous_fst).smul ((b.contDiff_coefficient.continuous.comp (by fun_prop)).clm_apply
          ((𝓕 u).continuous.comp continuous_snd)))).aestronglyMeasurable
    (.of_forall fun q ↦ by
      rw [Circle.norm_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
      exact (mul_le_mul_of_nonneg_left (((b.coefficient _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hCb q.1 _) (norm_nonneg _))) (by positivity)).trans_eq
        (by ring))

private theorem IsUniform.fourier_smulLeftCLM_quantizeUniformCLM (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x ζ' : CoordinateSpace n) :
    𝓕 (SchwartzMap.smulLeftCLM W (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)))
        (quantizeUniformCLM b hb u)) ζ' =
      ∫ ζ, 𝐞 (-⟪x, ζ' - ζ⟫) • 𝓕 (weightedSlice b x ((2 * π) • ζ)) (ζ' - ζ) (𝓕 u ζ) := by
  set G : CoordinateSpace n × CoordinateSpace n → W := fun q ↦ 𝐞 (-⟪q.1, ζ' - q.2⟫) •
    (((1 + ‖x - q.1‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))) • b.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2))
  have hL : 𝓕 (SchwartzMap.smulLeftCLM W (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)))
      (quantizeUniformCLM b hb u)) ζ' = ∫ y, ∫ ζ, G (y, ζ) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    refine integral_congr_ae (.of_forall fun y ↦ ?_); dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply
        (Function.hasTemperateGrowth_one_add_norm_sub_sq_rpow x _),
      quantizeUniformCLM_apply, quantizeSchwartzValue_def, ← integral_smul, Circle.smul_def,
      ← integral_smul]
    refine integral_congr_ae (.of_forall fun ζ ↦ ?_); dsimp only [G]
    rw [Circle.smul_def, Circle.smul_def, smul_comm ((1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))),
      smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3; rw [inner_sub_right, real_inner_comm ζ y]; ring
  rw [hL, integral_integral_swap (hb.integrable_fourier_smulLeftCLM_prod u x ζ')]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_); dsimp only
  rw [← integral_add_left_eq_self (fun y ↦ G (y, ζ)) x, Real.fourier_eq,
    integral_apply ((Real.fourierIntegral_convergent_iff (ζ' - ζ)).2
      (hb.integrable_weightedSlice x ((2 * π) • ζ))), Circle.smul_def, ← integral_smul]
  exact integral_congr_ae (.of_forall fun z ↦ by
    have hnorm : ‖x - (x + z)‖ = ‖z‖ := by simp
    simp only [G, weightedSlice_apply, hnorm, inner_add_left, neg_add, AddChar.map_add_eq_mul,
      Circle.smul_def, Circle.coe_mul, smul_apply, smul_smul])

private theorem IsUniform.integrable_uniformComposeIntegrand (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪q.2, x⟫ •
      ((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).coefficient (x, (2 * π) • q.1)
        (𝓕 (weightedSlice b x ((2 * π) • q.2)) (q.1 - q.2) (𝓕 u q.2)))
      (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := hb.exists_norm_uniformCompIntegrand_le
    (((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).exists_bound_coefficient {x}
      isCompact_singleton) ((n : ℝ) + 1)
  have hB : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (weightedSlice b x ((2 * π) • q.2)) (q.1 - q.2) := by
    simpa only [Function.comp_def] using hb.continuous_fourier_weightedSlice.comp (by fun_prop :
      Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ ((x, (2 * π) • q.2), q.1 - q.2))
  refine ((((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (μ := volume) (2 * π)
      (m' + m)).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    integrable_one_add_norm_sq_rpow_neg_succ_div_two).const_mul C).mono'
    ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      ((((Symbol.oneSubFrequencyLaplacian (m := m'))^[n + 1] a).contDiff_coefficient.continuous.comp
        (by fun_prop)).clm_apply (hB.clm_apply
          ((𝓕 u).continuous.comp continuous_snd)))).aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  have h := hC x rfl ((2 * π) • q.2) (q.1 - q.2)
  rw [uniformCompIntegrand, ← smul_add, add_sub_cancel] at h
  rw [Circle.norm_smul, ContinuousLinearMap.mul_apply', ← comp_apply]
  exact ((le_opNorm _ (𝓕 u q.2)).trans
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
      Cb).mono' ((Real.continuous_fourierChar.comp (by fun_prop)).smul
        (hB.clm_apply (𝓕 u).continuous)).aestronglyMeasurable (.of_forall fun ζ ↦ ?_)
  have h := hCb x ((2 * π) • ζ) (ζ' - ζ)
  simp only [neg_zero, zero_div, Real.rpow_zero, mul_one] at h; rw [Circle.norm_smul]
  exact ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))).trans_eq (by ring)

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
  have hR : quantizeSchwartzValue aN.coefficient
      (SchwartzMap.smulLeftCLM W (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ)))
        (quantizeUniformCLM b hb u)) x = ∫ ζ', ∫ ζ, F ζ' ζ := by
    rw [quantizeSchwartzValue_def]; refine integral_congr_ae (.of_forall fun ζ' ↦ ?_); dsimp only
    rw [hb.fourier_smulLeftCLM_quantizeUniformCLM u x ζ',
      ← (aN.coefficient (x, (2 * π) • ζ')).integral_comp_comm
        (hb.integrable_fourier_weightedSlice_apply u x ζ'), Circle.smul_def, ← integral_smul]
    refine integral_congr_ae (.of_forall fun ζ ↦ ?_); dsimp only [F]
    rw [Circle.smul_def, Circle.smul_def, map_smul, smul_smul, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul]
    congr 3; rw [real_inner_comm (ζ' - ζ) x, inner_sub_left]; ring
  rw [hR, integral_integral_swap (hb.integrable_uniformComposeIntegrand u x),
    quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_); dsimp only
  rw [← integral_add_right_eq_self (fun ζ' ↦ F ζ' ζ) ζ,
    coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff,
    integral_apply (hb.integrable_uniformCompIntegrand _), Circle.smul_def, ← integral_smul]
  exact integral_congr_ae (.of_forall fun η ↦ by
    simp only [F, uniformCompIntegrand, aN, add_sub_cancel_right, smul_add,
      add_comm ((2 * π) • η), Circle.smul_def, comp_apply])

/-- **Composition of uniform quantizations on Schwartz space**: `Op(a # b) = Op(a) ∘ Op(b)`. -/
theorem quantizeUniformCLM_uniformSharp [CompleteSpace W] [CompleteSpace U]
    (ha : a.IsUniform) (hb : b.IsUniform) :
    quantizeUniformCLM (a.uniformSharp b hb) (ha.uniformSharp hb) =
      (quantizeUniformCLM a ha).comp (quantizeUniformCLM b hb) := by
  ext u x; simp only [quantizeUniformCLM_apply, comp_apply]
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

/-- Left composition with a constant symbol is exact: `T # b = T ∘ b`. -/
theorem const_uniformSharp [CompleteSpace W] [CompleteSpace U] (T : W →L[ℂ] U)
    (hb : b.IsUniform) : (const T).uniformSharp b hb = (const T).comp b := by
  ext ⟨x, ξ⟩ : 2
  obtain ⟨C, -, hC⟩ := hb.exists_norm_fourier_weightedSlice_le ((n : ℝ) + 1)
  have hf_int := hb.integrable_weightedSlice x ξ
  have hFf_int : Integrable (𝓕 (weightedSlice b x ξ)) :=
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
      (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))).mono' hf_int.continuous_fourier.aestronglyMeasurable
      (.of_forall (hC x ξ))
  have hinv : ∫ η, 𝓕 (weightedSlice b x ξ) η = b.coefficient (x, ξ) := by
    simpa [Real.fourierInv_eq] using
      congrFun ((contDiff_weightedSlice b x ξ).continuous.fourierInv_fourier_eq hf_int hFf_int) 0
  rw [coefficient_uniformSharp, iterate_oneSubFrequencyLaplacian_const, coefficient_comp]
  simpa [compL_apply] using ((compL ℂ V W U T).integral_comp_comm hFf_int).trans (congrArg _ hinv)

/-- The constant identity symbol `1` is a left identity for `uniformSharp`. -/
@[simp] theorem const_id_uniformSharp [CompleteSpace W] (hb : b.IsUniform) :
    (const (ContinuousLinearMap.id ℂ W)).uniformSharp b hb = inclusion (by simp) b := by
  rw [const_uniformSharp, const_id_comp]

/-- **Associativity of `uniformSharp`**: `(a # b) # c = a # (b # c)` up to order associativity. -/
theorem uniformSharp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U']
    [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] [CompleteSpace U'] {m'' : ℝ}
    (a : Symbol n U U' m'') {b : Symbol n W U m'} {c : Symbol n V W m}
    (hb : b.IsUniform) (hc : c.IsUniform) :
    (a.uniformSharp b hb).uniformSharp c hc =
      inclusion (add_assoc m'' m' m).ge
        (a.uniformSharp (b.uniformSharp c hc) (hb.uniformSharp hc)) := by
  ext1; rw [coefficient_inclusion]
  exact coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq (hb.uniformSharp hc)
    fun u _ x ↦ by rw [quantizeSchwartzValue_uniformSharp hc, quantizeSchwartzValue_uniformSharp hb,
      quantizeUniformCLM_uniformSharp hb hc, comp_apply]

/-! ### Frequency multipliers and Bessel potentials in the uniform calculus -/

/-- **Right composition with a frequency-only uniform symbol is exact**: if `b` is uniform and
`b(x, ξ) = c(ξ)` for a function `c` of temperate growth, then `a # b = a ∘ b`. -/
theorem uniformSharp_eq_comp_of_coefficient_eq [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {b : Symbol n V W m} (hb : b.IsUniform)
    {c : CoordinateSpace n → V →L[ℂ] W} (hc : c.HasTemperateGrowth)
    (hbc : ∀ p, b.coefficient p = c p.2) : a.uniformSharp b hb = a.comp b := by
  ext1; symm
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq hb fun u _ x ↦ ?_
  have hq : quantizeUniformCLM b hb u = quantizeFrequencyCLM c u := by
    ext y; rw [quantizeUniformCLM_apply, funext hbc, quantizeSchwartzValue_comp_snd hc]
  rw [hq, quantizeSchwartzValue_quantizeFrequencyCLM hc]
  exact congrFun (congrArg (fun f ↦ quantizeSchwartzValue f u) (funext fun p ↦ by simp [hbc p])) x

/-- Right composition with a constant symbol is exact: `a # T = a ∘ T`. -/
theorem uniformSharp_const [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') (T : V →L[ℂ] W) :
    a.uniformSharp (const T) (isUniform_const T) = a.comp (const T) :=
  uniformSharp_eq_comp_of_coefficient_eq a (isUniform_const T) (.const T) (coefficient_const T)

/-- The constant identity symbol `1` is a right identity for `uniformSharp`. -/
@[simp] theorem uniformSharp_const_id [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m) :
    a.uniformSharp (const (ContinuousLinearMap.id ℂ V)) (isUniform_const _) =
      inclusion (by simp) a := by rw [uniformSharp_const, comp_const_id]

/-- **Right composition with a frequency-only symbol is exact**: `a # c(ξ) = a ∘ c(ξ)`. -/
theorem uniformSharp_ofFrequency [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {c : CoordinateSpace n → V →L[ℂ] W} (hc : ContDiff ℝ ∞ c)
    (hcbound : ∀ k : ℕ, ∃ C, ∀ ξ,
      ‖iteratedFDeriv ℝ k c ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2)) :
    a.uniformSharp (ofFrequency c hc hcbound) (isUniform_ofFrequency hc hcbound) =
      a.comp (ofFrequency c hc hcbound) :=
  uniformSharp_eq_comp_of_coefficient_eq a (isUniform_ofFrequency hc hcbound)
    (Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hc hcbound)
    (coefficient_ofFrequency hc hcbound)

/-- **Right composition with the Bessel potential symbol is exact**:
`a # ⟨ξ / 2π⟩ ^ s = a ∘ ⟨ξ / 2π⟩ ^ s`. -/
@[simp] theorem uniformSharp_besselPotential [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (s : ℝ) :
    a.uniformSharp (besselPotential s) (isUniform_besselPotential s) = a.comp (besselPotential s) :=
  uniformSharp_eq_comp_of_coefficient_eq a (isUniform_besselPotential s)
    (c := fun ξ ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    (by fun_prop) (coefficient_besselPotential s)

/-- **Left composition with a frequency-only symbol**: `c(D) ∘ Op(b) = Op(c # b)`. -/
theorem quantizeUniformCLM_ofFrequency_uniformSharp [CompleteSpace W] [CompleteSpace U]
    {c : CoordinateSpace n → W →L[ℂ] U} (hc : ContDiff ℝ ∞ c)
    (hcbound : ∀ k : ℕ, ∃ C, ∀ ξ,
      ‖iteratedFDeriv ℝ k c ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2)) (hb : b.IsUniform) :
    quantizeUniformCLM ((ofFrequency c hc hcbound).uniformSharp b hb)
        ((isUniform_ofFrequency hc hcbound).uniformSharp hb) =
      (quantizeFrequencyCLM c).comp (quantizeUniformCLM b hb) := by
  rw [quantizeUniformCLM_uniformSharp (isUniform_ofFrequency hc hcbound) hb]; congr 1; ext u x
  rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_ofFrequency hc hcbound u x

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
