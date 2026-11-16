/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Weak convergence and extensionality from a dense span of test functions

On a compact space `Ω`, integration against a probability measure is `1`-Lipschitz on `C(Ω, 𝕜)`
(`𝕜` = `ℝ` or `ℂ`), so the test functions with convergent integrals form a closed `𝕜`-linear
subspace. Consequently, if `s ⊆ C(Ω, 𝕜)` has dense linear span, weak convergence is equivalent to
integral convergence on `s`, and (when `ProbabilityMeasure Ω` is Hausdorff) measures are determined
by their integrals on `s`.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace MeasureTheory.ProbabilityMeasure

section Compact

variable (𝕜 : Type*) [RCLike 𝕜] {Ω ι : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

private theorem lipschitzWith_integral_continuousMap (ρ : ProbabilityMeasure Ω) :
    LipschitzWith 1 (fun f : C(Ω, 𝕜) ↦ ∫ x, f x ∂(ρ : Measure Ω)) := by
  have hint (h : C(Ω, 𝕜)) : Integrable (fun x ↦ h x) (ρ : Measure Ω) :=
    BoundedContinuousFunction.integrable (ρ : Measure Ω) (BoundedContinuousFunction.mkOfCompact h)
  refine LipschitzWith.of_dist_le_mul fun f g ↦ ?_
  rw [dist_eq_norm, ← integral_sub (hint f) (hint g)]
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, probReal_univ, mul_one,
    ContinuousMap.sub_apply] using
    norm_integral_le_of_norm_le_const (μ := (ρ : Measure Ω))
      (ae_of_all _ fun x ↦ (f - g).norm_coe_le_norm x)

/-- Weak convergence of probability measures on a compact space is equivalent to convergence of the
integrals of all functions in a set whose linear span is dense in `C(Ω, 𝕜)`. -/
theorem tendsto_iff_forall_integral_tendsto_of_dense_span
    {L : Filter ι} {μs : ι → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    {s : Set C(Ω, 𝕜)} (hs : (Submodule.span 𝕜 s).topologicalClosure = ⊤) :
    Tendsto μs L (𝓝 μ) ↔ ∀ f ∈ s,
      Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure Ω)) L
        (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  refine ⟨fun h f _ ↦ (tendsto_iff_forall_integral_rclike_tendsto 𝕜).1 h
    (BoundedContinuousFunction.mkOfCompact f), fun h ↦ ?_⟩
  let S : Submodule 𝕜 C(Ω, 𝕜) :=
    { carrier := {f | Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure Ω)) L
        (𝓝 (∫ x, f x ∂(μ : Measure Ω)))}
      zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : 𝕜)) L (𝓝 0))
      add_mem' := fun {f g} hf hg ↦ by
        have hint (h' : C(Ω, 𝕜)) (ρ : ProbabilityMeasure Ω) :
            Integrable (fun x ↦ h' x) (ρ : Measure Ω) :=
          BoundedContinuousFunction.integrable (ρ : Measure Ω)
            (BoundedContinuousFunction.mkOfCompact h')
        simpa only [mem_ofPred_eq, ContinuousMap.coe_add, Pi.add_apply,
          integral_add (hint f _) (hint g _)] using hf.add hg
      smul_mem' := fun c _ hf ↦ by
        simpa only [mem_ofPred_eq, ContinuousMap.coe_smul, Pi.smul_apply, integral_smul] using
          hf.const_smul c }
  have hclosed : IsClosed (S : Set C(Ω, 𝕜)) :=
    (LipschitzWith.uniformEquicontinuous _ 1
      (fun i ↦ lipschitzWith_integral_continuousMap 𝕜 (μs i))).equicontinuous
      |>.isClosed_setOfPred_tendsto (lipschitzWith_integral_continuousMap 𝕜 μ).continuous
  have htop := (Submodule.span 𝕜 s).topologicalClosure_minimal
    (Submodule.span_le.mpr (show s ⊆ (S : Set C(Ω, 𝕜)) from h)) hclosed
  rw [hs] at htop
  exact (tendsto_iff_forall_integral_rclike_tendsto 𝕜).2 fun f ↦
    htop (Submodule.mem_top : f.toContinuousMap ∈ (⊤ : Submodule 𝕜 C(Ω, 𝕜)))

/-- On a compact space where `ProbabilityMeasure Ω` is Hausdorff, a probability measure is
determined by its integrals on any set whose linear span is dense in `C(Ω, 𝕜)`. -/
theorem ext_of_forall_integral_eq_of_dense_span
    [T2Space (ProbabilityMeasure Ω)] {μ ν : ProbabilityMeasure Ω}
    {s : Set C(Ω, 𝕜)} (hs : (Submodule.span 𝕜 s).topologicalClosure = ⊤)
    (h : ∀ f ∈ s, ∫ x, f x ∂(μ : Measure Ω) = ∫ x, f x ∂(ν : Measure Ω)) :
    μ = ν :=
  tendsto_nhds_unique (f := fun _ : Unit ↦ μ) (l := pure ()) tendsto_const_nhds <|
    (tendsto_iff_forall_integral_tendsto_of_dense_span 𝕜 hs).2
      fun f hf ↦ by simpa only [h f hf] using tendsto_const_nhds (x := ∫ x, f x ∂(ν : Measure Ω))

end Compact

end MeasureTheory.ProbabilityMeasure
