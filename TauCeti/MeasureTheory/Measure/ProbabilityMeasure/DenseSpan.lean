/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Dense-span criteria for weak convergence of probability measures

On a compact space, integration against a probability measure is `1`-Lipschitz in the supremum norm
on `C(X, 𝕜)`. Consequently, weak convergence of probability measures is equivalent to convergence
of integrals on any family of continuous functions whose linear span is uniformly dense
(`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top`), and
when `ProbabilityMeasure X` is Hausdorff, a probability measure is determined by its integrals on
such a family (`MeasureTheory.ProbabilityMeasure.ext_of_forall_integral_eq_of_span_closure_eq_top`).
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace MeasureTheory.ProbabilityMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {ι : Type*} {L : Filter ι}
  {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}

/-- On a compact space, probability measures converge weakly if and only if their integrals converge
on a set of continuous functions whose linear span is uniformly dense. -/
theorem tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top (𝕜 : Type*) [RCLike 𝕜]
    {S : Set C(X, 𝕜)} (hS : (Submodule.span 𝕜 S).topologicalClosure = ⊤) :
    Tendsto μs L (𝓝 μ) ↔ ∀ f ∈ S,
      Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure X)) L (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  refine ⟨fun h f _ ↦
    (tendsto_iff_forall_integral_rclike_tendsto 𝕜).1 h (.mkOfCompact f), fun h ↦ ?_⟩
  have hint (f : C(X, 𝕜)) (ρ : ProbabilityMeasure X) : Integrable (fun x ↦ f x) (ρ : Measure X) :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)
  have hLip (ρ : ProbabilityMeasure X) :
      LipschitzWith 1 (fun f : C(X, 𝕜) ↦ ∫ x, f x ∂(ρ : Measure X)) :=
    LipschitzWith.of_dist_le_mul fun f g ↦ by
      rw [dist_eq_norm, ← integral_sub (hint f ρ) (hint g ρ)]
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm, probReal_univ, mul_one,
        ContinuousMap.sub_apply] using norm_integral_le_of_norm_le_const (μ := (ρ : Measure X))
          (ae_of_all _ fun x ↦ (f - g).norm_coe_le_norm x)
  -- The test functions with convergent integrals form a closed linear subspace.
  let M : Submodule 𝕜 C(X, 𝕜) :=
    { carrier := {f | Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure X)) L
        (𝓝 (∫ x, f x ∂(μ : Measure X)))}
      zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : 𝕜)) L (𝓝 0))
      add_mem' := fun {f g} hf hg ↦ (by
        simpa only [mem_ofPred_eq, ContinuousMap.coe_add, Pi.add_apply,
          integral_add (hint f _) (hint g _)] using hf.add hg)
      smul_mem' := fun c {f} hf ↦ (by
        simpa only [mem_ofPred_eq, ContinuousMap.coe_smul, Pi.smul_apply,
          integral_smul] using hf.const_smul c) }
  have hclosed : IsClosed (M : Set C(X, 𝕜)) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun i ↦ hLip (μs i)).equicontinuous
      |>.isClosed_setOfPred_tendsto (hLip μ).continuous
  have htop : (⊤ : Submodule 𝕜 C(X, 𝕜)) ≤ M :=
    hS ▸ (Submodule.span 𝕜 S).topologicalClosure_minimal (Submodule.span_le.mpr h) hclosed
  exact (tendsto_iff_forall_integral_rclike_tendsto 𝕜).2 fun f ↦ htop Submodule.mem_top

/-- On a compact space whose space of probability measures is Hausdorff, a probability measure is
determined by its integrals on a set of continuous functions whose linear span is uniformly
dense. -/
theorem ext_of_forall_integral_eq_of_span_closure_eq_top [T2Space (ProbabilityMeasure X)]
    (𝕜 : Type*) [RCLike 𝕜] {ν : ProbabilityMeasure X} {S : Set C(X, 𝕜)}
    (hS : (Submodule.span 𝕜 S).topologicalClosure = ⊤)
    (h : ∀ f ∈ S, ∫ x, f x ∂(μ : Measure X) = ∫ x, f x ∂(ν : Measure X)) :
    μ = ν :=
  tendsto_nhds_unique (tendsto_const_nhds (f := (atTop : Filter ℕ)) (x := μ))
    ((tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top 𝕜 hS).2 fun f hf ↦ by
      simpa only [h f hf] using tendsto_const_nhds)

end MeasureTheory.ProbabilityMeasure
