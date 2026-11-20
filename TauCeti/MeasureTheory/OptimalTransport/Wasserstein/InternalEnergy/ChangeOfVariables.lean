/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Calculus.ApproximatesLinearOn
import TauCeti.Analysis.Calculus.FDeriv.Det.Perturbation
import TauCeti.InformationTheory.KullbackLeibler.ChangeOfReference
import TauCeti.Topology.Algebra.Module.Trace

/-!
# Change of variables for Boltzmann entropy

Changing the reference by a positive density adds the integral of its logarithm to the
entropy relative to the original reference. Together with invariance under simultaneous
pushforward, this yields the Jacobian correction to entropy under a differentiable change
of variables. For a differentiable field `ξ` with uniformly bounded derivative, the first
variation along `x ↦ x + t • ξ x` is the negative integral of `div ξ`. This gives the
entropy term in the first variation of the Jordan–Kinderlehrer–Otto functional
(Jordan–Kinderlehrer–Otto, *The variational formulation of the Fokker–Planck equation*,
SIAM J. Math. Anal. 29 (1998), §4).
-/

public section

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

section Measurable

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {m μ : Measure X}

/-- Boltzmann entropy is invariant under pushing forward both measures by a measurable embedding. -/
theorem _root_.MeasurableEmbedding.boltzmannEntropy_map_map {T : X → Y}
    (hT : MeasurableEmbedding T) [SigmaFinite μ] [SigmaFinite m] :
    boltzmannEntropy (m.map T) (μ.map T) = boltzmannEntropy m μ := by
  let : SigmaFinite (μ.map T) := hT.sigmaFinite_map
  let : SigmaFinite (m.map T) := hT.sigmaFinite_map
  by_cases h : μ ≪ m
  · have heq : (fun x ↦ llr (μ.map T) (m.map T) (T x)) =ᵐ[μ] llr μ m :=
      (h.ae_eq (hT.rnDeriv_map μ m)).mono fun x hx ↦ by simp only [llr_def, hx]
    rw [boltzmannEntropy_eq_potentialEnergy_llr (hT.absolutelyContinuous_map h),
      boltzmannEntropy_eq_potentialEnergy_llr h,
      potentialEnergy_map (measurable_llr _ _) hT.measurable.aemeasurable,
      potentialEnergy_congr_ae heq]
  · have h' : ¬ μ.map T ≪ m.map T := by
      intro hac
      apply h
      intro s hs
      have hz : m.map T (T '' s) = 0 := by rw [hT.map_apply, hT.injective.preimage_image, hs]
      simpa only [hT.map_apply, hT.injective.preimage_image] using hac hz
    rw [boltzmannEntropy_of_not_absolutelyContinuous h',
      boltzmannEntropy_of_not_absolutelyContinuous h]

/-- Weighting the reference by `exp f` subtracts `∫ f dμ` from Boltzmann entropy when `f` is
almost everywhere measurable against the reference and integrable against `μ`. This does not
require `exp f` to be integrable against the reference. -/
theorem boltzmannEntropy_withDensity_exp [SigmaFinite μ] [SigmaFinite m] {f : X → ℝ}
    (hf : AEMeasurable f m) (hi : Integrable f μ) :
    boltzmannEntropy (m.withDensity fun x ↦ ENNReal.ofReal (Real.exp (f x))) μ =
      boltzmannEntropy m μ - ((∫ x, f x ∂μ : ℝ) : EReal) := by
  let m' := m.withDensity fun x ↦ ENNReal.ofReal (Real.exp (f x))
  let : SigmaFinite m' := SigmaFinite.withDensity_of_ne_top' fun _ ↦ ENNReal.ofReal_ne_top
  have h₁ : m' ≪ m := withDensity_absolutelyContinuous _ _
  have h₂ : m ≪ m' := withDensity_absolutelyContinuous' (by fun_prop)
    (.of_forall fun _ ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
  by_cases h : μ ≪ m
  · have h' := h.trans h₂
    have heq : (fun x ↦ llr μ m' x + f x) =ᵐ[μ] llr μ m :=
      ((Filter.EventuallyEq.rfl.add (h.ae_le (llr_withDensity_exp hf))).symm.trans
        (llr_add_llr h' h))
    rw [boltzmannEntropy_eq_potentialEnergy_llr h', boltzmannEntropy_eq_potentialEnergy_llr h,
      ← potentialEnergy_congr_ae heq,
      potentialEnergy_add_of_integrable (measurable_llr _ _).aestronglyMeasurable hi,
      EReal.add_sub_cancel_right]
  · rw [boltzmannEntropy_of_not_absolutelyContinuous (fun h' ↦ h (h'.trans h₁)),
      boltzmannEntropy_of_not_absolutelyContinuous h, EReal.top_sub_coe]

end Measurable

section Jacobian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [SigmaFinite μ]

/-- Pushing a measure through a differentiable bijection subtracts the integral of the log absolute
Jacobian from its entropy relative to additive Haar measure. The formula also holds for infinite
entropy, provided the Jacobian is nonzero Haar-almost everywhere and the logarithmic correction
is integrable against the transported measure. -/
theorem boltzmannEntropy_map_eq_sub_integral_log_abs_det_fderiv
    (m : Measure E) [m.IsAddHaarMeasure] {T : E → E} (hT : Differentiable ℝ T)
    (hbij : Function.Bijective T) (hdet : ∀ᵐ x ∂m, (fderiv ℝ T x).det ≠ 0)
    (hi : Integrable (fun x ↦ Real.log |(fderiv ℝ T x).det|) μ) :
    boltzmannEntropy m (μ.map T) =
      boltzmannEntropy m μ - ((∫ x, Real.log |(fderiv ℝ T x).det| ∂μ : ℝ) : EReal) := by
  have hEmb := hT.continuous.measurable.measurableEmbedding hbij.injective
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar m (s := univ)
    MeasurableSet.univ.nullMeasurableSet
    (fun x _ ↦ (hT x).hasFDerivAt.hasFDerivWithinAt) hbij.injective.injOn
  rw [Measure.restrict_univ, image_univ, hbij.surjective.range_eq, Measure.restrict_univ] at hmap
  have hlog : Measurable fun x ↦ Real.log |(fderiv ℝ T x).det| :=
    Real.measurable_log.comp (continuous_abs.measurable.comp
      ((ContinuousLinearMap.contDiff_det (r := 0)).continuous.measurable.comp
        (measurable_fderiv ℝ T)))
  have hexp : (fun x ↦ ENNReal.ofReal (Real.exp (Real.log |(fderiv ℝ T x).det|))) =ᵐ[m]
      (fun x ↦ ENNReal.ofReal |(fderiv ℝ T x).det|) :=
    hdet.mono fun _ hx ↦ by simp only [Real.exp_log (abs_pos.2 hx)]
  calc
    boltzmannEntropy m (μ.map T) =
        boltzmannEntropy ((m.withDensity fun x ↦ ENNReal.ofReal |(fderiv ℝ T x).det|).map T)
          (μ.map T) := by rw [hmap]
    _ = boltzmannEntropy (m.withDensity fun x ↦ ENNReal.ofReal |(fderiv ℝ T x).det|) μ :=
      hEmb.boltzmannEntropy_map_map
    _ = _ := by
      rw [← withDensity_congr_ae hexp]
      exact boltzmannEntropy_withDensity_exp hlog.aemeasurable hi

end Jacobian

section FirstVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
  {ξ : E → E}

/-- The local change-of-variables formula along a perturbation of the identity. A uniform
bound on the derivative of the field makes the perturbed map bijective for small `t`.
In this range its Jacobian is positive. -/
theorem eventually_boltzmannEntropy_map_add_smul_eq (m : Measure E) [m.IsAddHaarMeasure]
    (hξ : Differentiable ℝ ξ) {K : ℝ≥0} (hK : ∀ x, ‖fderiv ℝ ξ x‖₊ ≤ K) :
    ∀ᶠ t : ℝ in 𝓝 0,
      boltzmannEntropy m (μ.map fun x ↦ x + t • ξ x) = boltzmannEntropy m μ -
        ((∫ x, Real.log (ContinuousLinearMap.id ℝ E + t • fderiv ℝ ξ x).det ∂μ : ℝ) : EReal) := by
  let J := fun B : E →L[ℝ] E ↦ (ContinuousLinearMap.id ℝ E + B).det
  have hJ : Continuous J := (ContinuousLinearMap.contDiff_det (r := 0)).continuous.comp
    (by fun_prop)
  have hJ0 : J 0 = 1 := by simp [J, ContinuousLinearMap.det]
  have hG : ContinuousAt (Real.log ∘ J) 0 := (Real.continuousAt_log (by simp [hJ0])).comp
    hJ.continuousAt
  have hnear : ∀ᶠ B in 𝓝 (0 : E →L[ℝ] E), 0 < J B ∧ ‖Real.log (J B)‖ < 1 :=
    (hJ.continuousAt.eventually (Ioi_mem_nhds (show 0 < J 0 by simp [hJ0]))).and
      (hG.norm.eventually (Iio_mem_nhds (show ‖(Real.log ∘ J) 0‖ < 1 by simp [hJ0])))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hnear
  have htend : Tendsto (fun t : ℝ ↦ ‖t‖ * (K : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_norm.continuousAt (x := (0 : ℝ))).mul_const (K : ℝ)).tendsto
  filter_upwards [htend (Iio_mem_nhds (lt_min hr zero_lt_one))] with t ht
  have ht' : ‖t‖₊ * K < 1 := by exact_mod_cast (lt_min_iff.1 ht).2
  have hsmall (x : E) : t • fderiv ℝ ξ x ∈ Metric.ball (0 : E →L[ℝ] E) r := by
    rw [mem_ball_zero_iff, norm_smul]
    exact (mul_le_mul_of_nonneg_left (show ‖fderiv ℝ ξ x‖ ≤ (K : ℝ) from hK x)
      (norm_nonneg _)).trans_lt (lt_min_iff.1 ht).1
  have hD (x : E) : HasFDerivAt (fun y ↦ y + t • ξ y)
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ ξ x) x :=
    (hasFDerivAt_id x).add ((hξ x).hasFDerivAt.const_smul t)
  -- A perturbation with derivative uniformly close to the identity is bijective.
  have happ : ApproximatesLinearOn (fun x ↦ x + t • ξ x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) univ (‖t‖₊ * K) :=
    convex_univ.approximatesLinearOn_of_nnnorm_fderiv_sub_le (fun x _ ↦ (hD x).differentiableAt)
      (fun x _ ↦ by simpa [(hD x).fderiv, nnNorm_smul] using mul_le_mul_right (hK x) ‖t‖₊)
  have hclose : Subsingleton E ∨ ‖t‖₊ * K <
      ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
    cases subsingleton_or_nontrivial E with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (by simpa using ht')
  have hpos (x : E) : 0 < J (t • fderiv ℝ ξ x) := (hball (hsmall x)).1
  have hint : Integrable (fun x ↦ Real.log (J (t • fderiv ℝ ξ x))) μ :=
    (integrable_const (1 : ℝ)).mono'
      (Real.measurable_log.comp (hJ.measurable.comp
        ((measurable_fderiv ℝ ξ).const_smul t))).aestronglyMeasurable
      (.of_forall fun x ↦ (hball (hsmall x)).2.le)
  have hlog : (fun x ↦ Real.log |(fderiv ℝ (fun y ↦ y + t • ξ y) x).det|) =
      (fun x ↦ Real.log (J (t • fderiv ℝ ξ x))) := by
    funext x
    rw [(hD x).fderiv, abs_of_pos (hpos x)]
  rw [boltzmannEntropy_map_eq_sub_integral_log_abs_det_fderiv m
    (fun x ↦ (hD x).differentiableAt)
    ⟨injOn_univ.1 (happ.injOn hclose), happ.surjective hclose⟩
    (.of_forall fun x ↦ by rw [(hD x).fderiv]; exact (hpos x).ne') (hlog ▸ hint), hlog]

/-- The first variation of finite Boltzmann entropy along `x ↦ x + t • ξ x` is
`-∫ div ξ dμ`. The divergence is the trace of the derivative of the field. No smoothness
or positivity of the density is needed. -/
theorem hasDerivAt_boltzmannEntropy_map_add_smul (m : Measure E) [m.IsAddHaarMeasure]
    (hξ : Differentiable ℝ ξ) {K : ℝ≥0} (hK : ∀ x, ‖fderiv ℝ ξ x‖₊ ≤ K)
    (htop : boltzmannEntropy m μ ≠ ⊤) (hbot : boltzmannEntropy m μ ≠ ⊥) :
    HasDerivAt (fun t : ℝ ↦ (boltzmannEntropy m (μ.map fun x ↦ x + t • ξ x)).toReal)
      (-∫ x, LinearMap.trace ℝ E (fderiv ℝ ξ x).toLinearMap ∂μ) 0 := by
  let A := fderiv ℝ ξ
  let J := fun B : E →L[ℝ] E ↦ (ContinuousLinearMap.id ℝ E + B).det
  let G := Real.log ∘ J
  have hJ : ContDiff ℝ 1 J := ContinuousLinearMap.contDiff_det.comp (by fun_prop)
  have hJ0 : J 0 = 1 := by simp [J, ContinuousLinearMap.det]
  have hG : ContDiffAt ℝ 1 G 0 := hJ.contDiffAt.log (by simp [hJ0])
  -- A neighborhood of the identity in operator norm gives one bound for all positions.
  let C := ‖fderiv ℝ G 0‖ + 1
  have hnear : ∀ᶠ B in 𝓝 (0 : E →L[ℝ] E), 0 < J B ∧ ‖fderiv ℝ G B‖ < C :=
    (hJ.continuous.continuousAt.eventually (Ioi_mem_nhds (show 0 < J 0 by simp [hJ0]))).and
      ((hG.continuousAt_fderiv one_ne_zero).norm.eventually (Iio_mem_nhds (lt_add_one _)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hnear
  have htend : Tendsto (fun t : ℝ ↦ ‖t‖ * (K : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_norm.continuousAt (x := (0 : ℝ))).mul_const (K : ℝ)).tendsto
  let s := {t : ℝ | ‖t‖ * (K : ℝ) < r}
  have hs : s ∈ 𝓝 (0 : ℝ) := htend (Iio_mem_nhds hr)
  have hsmall (t : ℝ) (ht : t ∈ s) (x : E) : t • A x ∈ Metric.ball (0 : E →L[ℝ] E) r := by
    rw [mem_ball_zero_iff, norm_smul]
    exact (mul_le_mul_of_nonneg_left (show ‖A x‖ ≤ (K : ℝ) from hK x) (norm_nonneg _)).trans_lt ht
  have hdiff (x : E) (t : ℝ) (ht : t ∈ s) : HasDerivAt (fun u : ℝ ↦ G (u • A x))
      (fderiv ℝ G (t • A x) (A x)) t := by
    have htJ := (hball (hsmall t ht x)).1.ne'
    have hd : DifferentiableAt ℝ G (t • A x) :=
      ((hJ.differentiable one_ne_zero _).hasFDerivAt.log htJ).differentiableAt
    simpa only [one_smul, Function.comp_def] using
      hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).smul_const (A x))
  have hzero (x : E) : fderiv ℝ G ((0 : ℝ) • A x) (A x) =
      LinearMap.trace ℝ E (A x).toLinearMap := by
    have h := ((A x).hasDerivAt_det_id_add_smul.log (by simp [ContinuousLinearMap.det]))
    exact (hdiff x 0 (by simp [s, hr])).unique (by simpa [G, J, ContinuousLinearMap.det] using h)
  have hmeas (t : ℝ) : AEStronglyMeasurable (fun x ↦ G (t • A x)) μ :=
    (Real.measurable_log.comp (hJ.continuous.measurable.comp
      ((measurable_fderiv ℝ ξ).const_smul t))).aestronglyMeasurable
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) hs
    (.of_forall hmeas) (by simp [G, hJ0])
    (by simp only [hzero, ← traceCLM_apply]; exact
      ((traceCLM ℝ E).continuous.measurable.comp (measurable_fderiv ℝ ξ)).aestronglyMeasurable)
    (.of_forall fun x t ht ↦ ((fderiv ℝ G (t • A x)).le_opNorm (A x)).trans
      (mul_le_mul (hball (hsmall t ht x)).2.le (hK x) (norm_nonneg _) (by dsimp [C]; positivity)))
    (integrable_const (C * (K : ℝ))) (.of_forall hdiff)).2
  have hd := (hasDerivAt_const 0 (boltzmannEntropy m μ).toReal).sub hi
  rw [zero_sub] at hd
  simp only [hzero] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_boltzmannEntropy_map_add_smul_eq (μ := μ) m hξ hK] with t ht
  rw [ht, ← EReal.coe_toReal htop hbot, ← EReal.coe_sub, EReal.toReal_coe]
  rfl

end FirstVariation

end TauCeti
