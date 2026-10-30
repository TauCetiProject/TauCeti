/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Fourier criteria for weak convergence on the circle

Probability measures on an additive circle converge weakly exactly when all their integer
Fourier moments converge. In particular, convergence to Haar probability is equivalent to
vanishing of every nonconstant Fourier moment. This detects the uniform limits of wrapped
distributions without requiring a density representation.

The proof uses Mathlib's `span_fourier_closure_eq_top`, the Stone–Weierstrass density of
trigonometric polynomials. Integration against a probability measure is uniformly Lipschitz
in the supremum norm, so convergence extends from this span to every continuous function.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace MeasureTheory.ProbabilityMeasure

variable {T : ℝ} [Fact (0 < T)] {ι : Type*} {L : Filter ι}
  {μs : ι → ProbabilityMeasure (AddCircle T)} {μ : ProbabilityMeasure (AddCircle T)}

/-- Weak convergence of circle probability measures is equivalent to convergence of all
integer Fourier moments. -/
theorem tendsto_iff_forall_integral_fourier_tendsto :
    Tendsto μs L (𝓝 μ) ↔ ∀ n : ℤ,
      Tendsto (fun i ↦ ∫ x, fourier n x ∂(μs i : Measure (AddCircle T))) L
        (𝓝 (∫ x, fourier n x ∂(μ : Measure (AddCircle T)))) := by
  constructor
  · intro h n
    exact (tendsto_iff_forall_integral_rclike_tendsto ℂ).1 h
      (BoundedContinuousFunction.mkOfCompact (fourier n))
  · intro h
    have hint (f : C(AddCircle T, ℂ)) (ρ : ProbabilityMeasure (AddCircle T)) :
        Integrable (fun x ↦ f x) (ρ : Measure (AddCircle T)) :=
      Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
        (ae_of_all _ f.norm_coe_le_norm)
    have hLip (ρ : ProbabilityMeasure (AddCircle T)) :
        LipschitzWith 1 (fun f : C(AddCircle T, ℂ) ↦ ∫ x, f x ∂(ρ : Measure (AddCircle T))) := by
      apply LipschitzWith.of_dist_le_mul
      intro f g
      rw [dist_eq_norm, ← integral_sub (hint f ρ) (hint g ρ)]
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm, probReal_univ, mul_one,
        ContinuousMap.sub_apply] using
        norm_integral_le_of_norm_le_const (μ := (ρ : Measure (AddCircle T)))
          (ae_of_all _ fun x ↦ (f - g).norm_coe_le_norm x)
    -- The test functions with convergent integrals form a closed linear subspace.
    let S : Submodule ℂ C(AddCircle T, ℂ) :=
      { carrier := {f | Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure (AddCircle T))) L
          (𝓝 (∫ x, f x ∂(μ : Measure (AddCircle T))))}
        zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℂ)) L (𝓝 0))
        add_mem' := by
          intro f g hf hg
          simpa only [mem_ofPred_eq, ContinuousMap.coe_add, Pi.add_apply,
            integral_add (hint f _) (hint g _)] using hf.add hg
        smul_mem' := by
          intro c f hf
          simpa only [mem_ofPred_eq, ContinuousMap.coe_smul, Pi.smul_apply, integral_smul] using
            hf.const_smul c }
    have hclosed : IsClosed (S : Set C(AddCircle T, ℂ)) :=
      (LipschitzWith.uniformEquicontinuous _ 1 (fun i ↦ hLip (μs i))).equicontinuous
        |>.isClosed_setOfPred_tendsto (hLip μ).continuous
    have hspan : Submodule.span ℂ (range (fourier (T := T))) ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact h n
    -- Trigonometric polynomials are dense for the supremum norm.
    have htop := (Submodule.span ℂ (range (fourier (T := T)))).topologicalClosure_minimal
      hspan hclosed
    rw [span_fourier_closure_eq_top] at htop
    apply (tendsto_iff_forall_integral_rclike_tendsto ℂ).2
    intro f
    exact htop (Submodule.mem_top : f.toContinuousMap ∈ (⊤ : Submodule ℂ C(AddCircle T, ℂ)))

/-- Circle probability measures tend weakly to Haar probability exactly when every nonzero
integer Fourier moment tends to zero. -/
theorem tendsto_haarAddCircle_iff :
    Tendsto μs L (𝓝 AddCircle.haarAddCircle.toProbabilityMeasure) ↔ ∀ n : ℤ, n ≠ 0 →
      Tendsto (fun i ↦ ∫ x, fourier n x ∂(μs i : Measure (AddCircle T))) L (𝓝 0) := by
  have hhaar (n : ℤ) : ∫ x, fourier n x ∂(AddCircle.haarAddCircle (T := T)) =
      if n = 0 then 1 else 0 := by
    simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using
      congrFun (fourierCoeff_fourier (T := T) n) 0
  rw [tendsto_iff_forall_integral_fourier_tendsto]
  simp only [Measure.coe_toProbabilityMeasure, hhaar]
  constructor
  · intro h n hn
    simpa [hn] using h n
  · intro h n
    by_cases hn : n = 0
    · subst n
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℂ)) L (𝓝 1))
    · simpa [hn] using h n hn

end MeasureTheory.ProbabilityMeasure
