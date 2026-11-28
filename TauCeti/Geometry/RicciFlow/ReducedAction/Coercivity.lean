/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.ReducedAction
public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import Mathlib.Topology.UniformSpace.UniformConvergence
import TauCeti.Geometry.Manifold.Riemannian.Distance.Energy
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Reduced action bounds and compactness of paths

A scalar-curvature lower bound controls the negative potential in Perelman's square-time
reduced action. Comparison with a fixed Riemannian metric then bounds the reference kinetic
energy. The reference norm is supplied by `RiemannianBundle`, and
`IsRiemannianManifold` ties its length distance to the ambient distance. The comparison
hypothesis explicitly relates this reference norm to the evolving metric. This gives a common
square-root modulus for continuous paths which are `C¹` only in
the interior of their interval. On a complete reference manifold, an anchored sequence with
bounded action, these curvature and metric comparisons, and integrable evolving kinetic and
potential terms has a subsequence converging uniformly on the closed interval.

The limit retains prescribed endpoints. Lower semicontinuity and regularity of a minimizing
limit are separate steps in the direct method.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.2.
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  [T2Space M]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M] in
/-- A lower bound for scalar curvature bounds the square-time scalar potential on a
compact interval. Only the scalar values along the specified path enter the estimate. -/
private theorem neg_two_mul_max_sq_mul_le_two_mul_sq_mul_scalarCurvature
    {α : ℝ → M} {a b T K s : ℝ} (hK : 0 ≤ K) (hs : s ∈ Icc a b)
    (hR : -K ≤ (g (T - s ^ 2)).scalarCurvature (α s)) :
    -(2 * max (a ^ 2) (b ^ 2) * K) ≤ 2 * s ^ 2 * (g (T - s ^ 2)).scalarCurvature (α s) := by
  have hsq : s ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
    have h := pow_le_pow_left₀ (abs_nonneg s) (abs_le_max_abs_abs hs.1 hs.2) 2
    simpa only [max_pow_of_nonneg (abs_nonneg a) (abs_nonneg b), sq_abs] using h
  have h₁ := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2 * s ^ 2)
  have h₂ := mul_le_mul_of_nonneg_right hsq hK
  nlinarith

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] in
/-- An almost-everywhere comparison with the evolving kinetic density makes the measurable
reference kinetic density integrable and gives a curvature-corrected reference-energy bound. -/
theorem energy_le_mul_regularizedReducedAction_add {α : ℝ → M} {a b T K Q : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hkin : IntervalIntegrable (fun s ↦ (g (T - s ^ 2)).inner (α s)
      (curveVelocity I α s) (curveVelocity I α s)) volume a b)
    (hpotential : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * (g (T - s ^ 2)).scalarCurvature (α s)) volume a b)
    (hR : ∀ᵐ s ∂(volume.restrict (Ioo a b)), -K ≤ (g (T - s ^ 2)).scalarCurvature (α s))
    (hcompare : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖curveVelocity I α s‖ ^ 2 ≤
      Q * (g (T - s ^ 2)).inner (α s) (curveVelocity I α s)
        (curveVelocity I α s))
    (hmeas : AEStronglyMeasurable (fun s ↦ ‖curveVelocity I α s‖ ^ 2)
      (volume.restrict (uIoc a b))) :
    IntervalIntegrable (fun s ↦ ‖curveVelocity I α s‖ ^ 2) volume a b ∧
      energy I α a b ≤ Q *
        (regularizedReducedAction I g T α a b + 2 * max (a ^ 2) (b ^ 2) * K * (b - a)) := by
  let P : ℝ → ℝ := fun s ↦ 2 * s ^ 2 * (g (T - s ^ 2)).scalarCurvature (α s)
  let k : ℝ → ℝ := fun s ↦ (g (T - s ^ 2)).inner (α s)
    (curveVelocity I α s) (curveVelocity I α s)
  have hP : IntervalIntegrable P volume a b := hpotential
  have hE : IntervalIntegrable (fun s ↦ ‖curveVelocity I α s‖ ^ 2) volume a b := by
    apply (hkin.const_mul Q).mono_fun' hmeas
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [hcompare] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖curveVelocity I α s‖)]
    exact hs
  have heq : regularizedReducedAction I g T α a b =
      (∫ s in a..b, k s) / 2 + ∫ s in a..b, P s := by
    rw [regularizedReducedAction_def, intervalIntegral.integral_add (hkin.div_const 2) hP,
      intervalIntegral.integral_div]
  have hpot : -(2 * max (a ^ 2) (b ^ 2) * K) * (b - a) ≤ ∫ s in a..b, P s := by
    have hbound : ∀ᵐ s ∂(volume.restrict (Icc a b)),
        -(2 * max (a ^ 2) (b ^ 2) * K) ≤ P s := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hR] with s hs hRs
      exact neg_two_mul_max_sq_mul_le_two_mul_sq_mul_scalarCurvature hK
        (Ioo_subset_Icc_self hs) hRs
    have h := intervalIntegral.integral_mono_ae_restrict hab
      (intervalIntegrable_const (c := -(2 * max (a ^ 2) (b ^ 2) * K))) hP hbound
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have href := intervalIntegral.integral_mono_ae_restrict hab hE (hkin.const_mul Q)
    (by rwa [← restrict_Ioo_eq_restrict_Icc])
  rw [intervalIntegral.integral_const_mul] at href
  refine ⟨hE, ?_⟩
  rw [energy_def]
  have he : (∫ s in a..b, k s) / 2 ≤
      regularizedReducedAction I g T α a b + 2 * max (a ^ 2) (b ^ 2) * K * (b - a) := by
    rw [heq]
    nlinarith
  exact (div_le_div_of_nonneg_right href (by norm_num)).trans
    (by nlinarith [mul_le_mul_of_nonneg_left he hQ])

/-- With a uniform scalar-curvature lower bound, a comparison of the reference norm with the
evolving metrics, and integrable kinetic and potential terms, a reduced-action bound gives a
square-root modulus on the closed interval. Endpoint derivatives are unnecessary. -/
theorem dist_le_sqrt_mul_sqrt_abs_sub_of_regularizedReducedAction_le {α : ℝ → M} {a b T K Q A : ℝ}
    (hα : ContinuousOn α (Icc a b)) (hreg : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Ioo a b))
    (hkin : IntervalIntegrable (fun s ↦ (g (T - s ^ 2)).inner (α s)
      (curveVelocity I α s) (curveVelocity I α s)) volume a b)
    (hpotential : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * (g (T - s ^ 2)).scalarCurvature (α s)) volume a b)
    (hR : ∀ᵐ s ∂(volume.restrict (Ioo a b)), -K ≤ (g (T - s ^ 2)).scalarCurvature (α s))
    (hcompare : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖curveVelocity I α s‖ ^ 2 ≤
      Q * (g (T - s ^ 2)).inner (α s) (curveVelocity I α s) (curveVelocity I α s))
    (hA : regularizedReducedAction I g T α a b ≤ A) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (α s) (α t) ≤
      Real.sqrt (2 * max Q 0 * (A + 2 * max (a ^ 2) (b ^ 2) * max K 0 * (b - a))) *
        Real.sqrt |t - s| := by
  intro s hs t ht
  have hab : a ≤ b := hs.1.trans hs.2
  have hmeas : AEStronglyMeasurable (fun s ↦ ‖curveVelocity I α s‖ ^ 2)
      (volume.restrict (uIoc a b)) := by
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    have hnorm : ContinuousOn (fun s ↦ ‖curveVelocity I α s‖ ^ 2) (Ioo a b) :=
      (hreg.continuousOn_norm_curveVelocity isOpen_Ioo).fun_pow 2
    exact hnorm.aestronglyMeasurable measurableSet_Ioo
  obtain ⟨hE, hbound⟩ := energy_le_mul_regularizedReducedAction_add hab
    (le_max_right K 0) (le_max_right Q 0)
    hkin hpotential (hR.mono fun _ hs ↦ (neg_le_neg (le_max_left K 0)).trans hs)
    (hcompare.mono fun s hs ↦ hs.trans
      (mul_le_mul_of_nonneg_right (le_max_left Q 0)
        ((g (T - s ^ 2)).toRiemannianMetric.inner_self_nonneg _ _))) hmeas
  exact TauCeti.IsRiemannianManifold.dist_le_sqrt_mul_sqrt_abs_sub_of_two_mul_energy_le hα hreg hE
    (by nlinarith [mul_le_mul_of_nonneg_left hA (le_max_right Q 0)]) s hs t ht

end TauCeti.Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- On a complete reference manifold, paths with fixed endpoints, a uniform scalar-curvature
lower bound, a uniform reference/evolving metric comparison, integrable kinetic and potential
terms, and uniformly bounded reduced action have a continuous uniform limit along a subsequence.
Paths need only be `C¹` in the interior; endpoint derivatives are unnecessary. -/
theorem exists_tendstoUniformlyOn_subseq_of_regularizedReducedAction_le
    {α : ℕ → ℝ → M} {a b T K Q A : ℝ} (hab : a ≤ b) (p q : M)
    (hα : ∀ n, ContinuousOn (α n) (Icc a b))
    (hreg : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (α n) (Ioo a b))
    (hkin : ∀ n, IntervalIntegrable (fun s ↦ (g (T - s ^ 2)).inner (α n s)
      (curveVelocity I (α n) s) (curveVelocity I (α n) s)) volume a b)
    (hpotential : ∀ n, IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * (g (T - s ^ 2)).scalarCurvature (α n s)) volume a b)
    (hR : ∀ n, ∀ᵐ s ∂(volume.restrict (Ioo a b)), -K ≤ (g (T - s ^ 2)).scalarCurvature (α n s))
    (hcompare : ∀ n, ∀ᵐ s ∂(volume.restrict (Ioo a b)), ‖curveVelocity I (α n) s‖ ^ 2 ≤
      Q * (g (T - s ^ 2)).inner (α n s) (curveVelocity I (α n) s) (curveVelocity I (α n) s))
    (hA : ∀ n, regularizedReducedAction I g T (α n) a b ≤ A)
    (hp : ∀ n, α n a = p) (hq : ∀ n, α n b = q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ γ : ℝ → M,
      Continuous γ ∧ γ a = p ∧ γ b = q ∧
        TendstoUniformlyOn (fun n ↦ α (φ n)) γ atTop (Icc a b) := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let C := 2 * max Q 0 * (A + 2 * max (a ^ 2) (b ^ 2) * max K 0 * (b - a))
  have hmod (s t : Icc a b) (n : ℕ) :
      dist (α n s) (α n t) ≤ Real.sqrt C * Real.sqrt (dist s t) := by
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using
      dist_le_sqrt_mul_sqrt_abs_sub_of_regularizedReducedAction_le
        (hα n) (hreg n) (hkin n) (hpotential n) (hR n) (hcompare n) (hA n)
        s s.property t t.property
  have hf : Equicontinuous (fun n ↦ (Icc a b).domRestrict (α n)) :=
    Metric.equicontinuous_of_continuity_modulus
    (fun r ↦ Real.sqrt C * Real.sqrt r)
    (by simpa only [Real.sqrt_zero, mul_zero] using
      tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto (0 : ℝ))) _ hmod
  exact hf.exists_tendstoUniformlyOn_Icc_subseq_of_fixed_endpoints hab hp hq
end TauCeti.Manifold
