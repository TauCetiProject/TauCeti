/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Analysis.Fourier.Kronecker

/-!
# Fourier criteria for weak convergence on circles and tori

On a compact space, integration against a probability measure is `1`-Lipschitz in the supremum norm
on `C(X, 𝕜)`, so weak convergence of probability measures is equivalent to convergence of integrals
on any family of continuous functions whose linear span is uniformly dense
(`tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top`).

Applying Stone–Weierstrass density of trigonometric polynomials (`span_fourier_closure_eq_top` on
`AddCircle T` and `UnitAddTorus.span_mFourier_closure_eq_top` on `UnitAddTorus d`), probability
measures on an additive circle or unit torus converge weakly exactly when all their integer Fourier
moments converge. In particular, convergence to Haar probability is equivalent to vanishing of every
nonzero Fourier moment, and a probability measure on a circle or torus is determined by its Fourier
moments.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace MeasureTheory.ProbabilityMeasure

section CompactDenseSpan

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {ι : Type*} {L : Filter ι}
  {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}

/-- On a compact space, probability measures converge weakly if and only if their integrals converge
on a set of continuous functions whose linear span is uniformly dense. -/
theorem tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top (𝕜 : Type*) [RCLike 𝕜]
    {S : Set C(X, 𝕜)} (hS : (Submodule.span 𝕜 S).topologicalClosure = ⊤) :
    Tendsto μs L (𝓝 μ) ↔ ∀ f ∈ S,
      Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure X)) L (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  constructor
  · intro h f _
    exact (tendsto_iff_forall_integral_rclike_tendsto 𝕜).1 h
      (BoundedContinuousFunction.mkOfCompact f)
  · intro h
    have hint (f : C(X, 𝕜)) (ρ : ProbabilityMeasure X) :
        Integrable (fun x ↦ f x) (ρ : Measure X) :=
      Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
        (ae_of_all _ f.norm_coe_le_norm)
    have hLip (ρ : ProbabilityMeasure X) :
        LipschitzWith 1 (fun f : C(X, 𝕜) ↦ ∫ x, f x ∂(ρ : Measure X)) := by
      apply LipschitzWith.of_dist_le_mul
      intro f g
      rw [dist_eq_norm, ← integral_sub (hint f ρ) (hint g ρ)]
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm, probReal_univ, mul_one,
        ContinuousMap.sub_apply] using
        norm_integral_le_of_norm_le_const (μ := (ρ : Measure X))
          (ae_of_all _ fun x ↦ (f - g).norm_coe_le_norm x)
    -- The test functions with convergent integrals form a closed linear subspace.
    let M : Submodule 𝕜 C(X, 𝕜) :=
      { carrier := {f | Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure X)) L
          (𝓝 (∫ x, f x ∂(μ : Measure X)))}
        zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : 𝕜)) L (𝓝 0))
        add_mem' := by
          intro f g hf hg
          simpa only [mem_ofPred_eq, ContinuousMap.coe_add, Pi.add_apply,
            integral_add (hint f _) (hint g _)] using hf.add hg
        smul_mem' := by
          intro c f hf
          simpa only [mem_ofPred_eq, ContinuousMap.coe_smul, Pi.smul_apply, integral_smul] using
            hf.const_smul c }
    have hclosed : IsClosed (M : Set C(X, 𝕜)) :=
      (LipschitzWith.uniformEquicontinuous _ 1 (fun i ↦ hLip (μs i))).equicontinuous
        |>.isClosed_setOfPred_tendsto (hLip μ).continuous
    have hspan : Submodule.span 𝕜 S ≤ M := Submodule.span_le.mpr h
    have htop := (Submodule.span 𝕜 S).topologicalClosure_minimal hspan hclosed
    rw [hS] at htop
    apply (tendsto_iff_forall_integral_rclike_tendsto 𝕜).2
    intro f
    exact htop (Submodule.mem_top : f.toContinuousMap ∈ (⊤ : Submodule 𝕜 C(X, 𝕜)))

/-- On a compact space whose space of probability measures is Hausdorff, a probability measure is
determined by its integrals on a set of continuous functions whose linear span is uniformly
dense. -/
theorem ext_of_forall_integral_eq_of_span_closure_eq_top [T2Space (ProbabilityMeasure X)]
    (𝕜 : Type*) [RCLike 𝕜] {ν : ProbabilityMeasure X} {S : Set C(X, 𝕜)}
    (hS : (Submodule.span 𝕜 S).topologicalClosure = ⊤)
    (h : ∀ f ∈ S, ∫ x, f x ∂(μ : Measure X) = ∫ x, f x ∂(ν : Measure X)) :
    μ = ν := by
  have hlim : Tendsto (fun _ : ℕ ↦ μ) atTop (𝓝 ν) :=
    (tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top 𝕜 hS).2 fun f hf ↦ by
      simpa only [h f hf] using tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end CompactDenseSpan

section AddCircle

variable {T : ℝ} [Fact (0 < T)] {ι : Type*} {L : Filter ι}
  {μs : ι → ProbabilityMeasure (AddCircle T)} {μ : ProbabilityMeasure (AddCircle T)}

/-- Weak convergence of circle probability measures is equivalent to convergence of all
integer Fourier moments. -/
theorem tendsto_iff_forall_integral_fourier_tendsto :
    Tendsto μs L (𝓝 μ) ↔ ∀ n : ℤ,
      Tendsto (fun i ↦ ∫ x, fourier n x ∂(μs i : Measure (AddCircle T))) L
        (𝓝 (∫ x, fourier n x ∂(μ : Measure (AddCircle T)))) := by
  rw [tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top ℂ (span_fourier_closure_eq_top)]
  simp

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

/-- A probability measure on an additive circle is determined by its integer Fourier moments. -/
theorem ext_of_forall_integral_fourier_eq {ν : ProbabilityMeasure (AddCircle T)}
    (h : ∀ n : ℤ, ∫ x, fourier n x ∂(μ : Measure (AddCircle T)) =
      ∫ x, fourier n x ∂(ν : Measure (AddCircle T))) :
    μ = ν :=
  ext_of_forall_integral_eq_of_span_closure_eq_top ℂ span_fourier_closure_eq_top
    (by simpa using h)

end AddCircle

section UnitAddTorus

variable {d : Type*} [Fintype d] {ι : Type*} {L : Filter ι}
  {μs : ι → ProbabilityMeasure (UnitAddTorus d)} {μ : ProbabilityMeasure (UnitAddTorus d)}

/-- Weak convergence of probability measures on `UnitAddTorus d` is equivalent to convergence of all
integer Fourier moments. -/
theorem tendsto_iff_forall_integral_mFourier_tendsto :
    Tendsto μs L (𝓝 μ) ↔ ∀ k : d → ℤ,
      Tendsto (fun i ↦ ∫ x, UnitAddTorus.mFourier k x ∂(μs i : Measure (UnitAddTorus d))) L
        (𝓝 (∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus d)))) := by
  rw [tendsto_iff_forall_integral_tendsto_of_span_closure_eq_top ℂ
    UnitAddTorus.span_mFourier_closure_eq_top]
  simp

/-- Probability measures on `UnitAddTorus d` tend weakly to Haar probability (`volume`) exactly
when every nonzero integer Fourier moment tends to zero. -/
theorem tendsto_volume_unitAddTorus_iff :
    Tendsto μs L (𝓝 (volume : Measure (UnitAddTorus d)).toProbabilityMeasure) ↔
      ∀ k : d → ℤ, k ≠ 0 →
        Tendsto (fun i ↦ ∫ x, UnitAddTorus.mFourier k x ∂(μs i : Measure (UnitAddTorus d))) L
          (𝓝 0) := by
  rw [tendsto_iff_forall_integral_mFourier_tendsto]
  simp only [Measure.coe_toProbabilityMeasure, TauCeti.UnitAddTorus.integral_mFourier]
  constructor
  · intro h k hk
    simpa [hk] using h k
  · intro h k
    by_cases hk : k = 0
    · subst hk
      simpa [UnitAddTorus.mFourier_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (1 : ℂ)) L (𝓝 1))
    · simpa [hk] using h k hk

/-- A probability measure on `UnitAddTorus d` is determined by its integer Fourier moments. -/
theorem ext_of_forall_integral_mFourier_eq {ν : ProbabilityMeasure (UnitAddTorus d)}
    (h : ∀ k : d → ℤ, ∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus d)) =
      ∫ x, UnitAddTorus.mFourier k x ∂(ν : Measure (UnitAddTorus d))) :
    μ = ν :=
  ext_of_forall_integral_eq_of_span_closure_eq_top ℂ UnitAddTorus.span_mFourier_closure_eq_top
    (by simpa using h)

end UnitAddTorus

end MeasureTheory.ProbabilityMeasure
