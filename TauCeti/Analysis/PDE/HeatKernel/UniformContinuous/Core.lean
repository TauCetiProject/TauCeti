/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous.Generator
public import TauCeti.Topology.ContinuousMap.Bounded.Smooth
public import TauCeti.Analysis.Semigroups.Generator.Closed
import TauCeti.Analysis.Semigroups.Generator.Invariance
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# A smooth core for the heat generator on bounded uniformly continuous functions

Smooth functions with bounded derivatives of every order form a core for the heat generator
on bounded uniformly continuous functions. Positive-time heat regularizations converge together
with their generator values, so identities on these smooth functions extend to the entire
generator graph. Compact support is unnecessary. This result does not characterize the domain
by distributional Laplacians.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
* L. C. Evans, *Partial Differential Equations*, Section 7.4.
-/

public section

noncomputable section

namespace TauCeti

open BoundedContinuousFunction Filter InnerProductSpace Laplacian MeasureTheory Semigroups Set
  Topology
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Smooth functions with bounded derivatives of every order belong to the heat generator
domain, and their generator is their classical Laplacian. -/
theorem exists_generator_heatSemigroupBUC_eq_laplacian
    {f : uniformContinuousSubmodule ℝ E F}
    (hf : f ∈ smoothBoundedDerivativesSubmodule ℝ E F) :
    ∃ hf : f ∈ (heatSemigroupBUC (E := E) (F := F)).domain,
      (((heatSemigroupBUC (E := E) (F := F)).generator
        ⟨f, by rw [StronglyContinuousSemigroup.generator_domain]; exact hf⟩).val : E → F) =
          Δ (f.val : E → F) := by
  obtain ⟨hs, hb⟩ := (mem_smoothBoundedDerivativesSubmodule ℝ E F f).mp hf
  obtain ⟨C₁, hC₁⟩ := hb 1
  obtain ⟨C₂, hC₂⟩ := hb 2
  obtain ⟨C₃, hC₃⟩ := hb 3
  have h₁ : ∀ x, ‖fderiv ℝ (f.val : E → F) x‖ ≤ C₁ := by
    simpa only [norm_iteratedFDeriv_one] using hC₁
  have h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ (f.val : E → F)) x‖ ≤ C₂ := by
    intro x
    rw [← norm_iteratedFDeriv_one (fderiv ℝ (f.val : E → F)),
      norm_iteratedFDeriv_fderiv]
    exact hC₂ x
  -- The third derivative makes the second derivative uniformly continuous; the trace then
  -- gives a bounded uniformly continuous Laplacian.
  have hLip := lipschitzWith_of_nnNorm_fderiv_le
    (hs.differentiable_iteratedFDeriv (m := 2)
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))
    (C := ‖C₃‖₊) (fun x => by
      have h := (hC₃ x).trans (le_abs_self C₃)
      rw [← norm_fderiv_iteratedFDeriv (n := 2)] at h
      exact_mod_cast h)
  let L := ∑ i, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) F
    ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]
  have hΔ : Δ (f.val : E → F) = L ∘ iteratedFDeriv ℝ 2 (f.val : E → F) :=
    funext (laplacian_eq_traceL_iteratedFDeriv _)
  have hu : UniformContinuous (Δ (f.val : E → F)) := by
    rw [hΔ]
    exact L.uniformContinuous.comp hLip.uniformContinuous
  let g : E →ᵇ F := .ofNormedAddCommGroup (Δ (f.val : E → F)) hu.continuous
    (Module.finrank ℝ E * C₂) (fun x =>
      (norm_laplacian_le _ x).trans (mul_le_mul_of_nonneg_left (h₂ x) (Nat.cast_nonneg _)))
  let gBUC : uniformContinuousSubmodule ℝ E F :=
    ⟨g, (mem_uniformContinuousSubmodule g).mpr hu⟩
  refine ⟨mem_domain_heatSemigroupBUC (hs.of_le (by simp)) h₁ h₂ (g := gBUC) rfl, ?_⟩
  rw [generator_heatSemigroupBUC (hs.of_le (by simp)) h₁ h₂ (g := gBUC) rfl]
  rfl

/-- Every positive-time heat regularization is smooth with bounded derivatives of all orders. -/
theorem heatCauchyPotentialBUC_mem_smoothBoundedDerivativesSubmodule
    {t : ℝ} (ht : 0 < t) (f : uniformContinuousSubmodule ℝ E F) :
    heatCauchyPotentialBUC t f ∈ smoothBoundedDerivativesSubmodule ℝ E F := by
  refine (mem_smoothBoundedDerivativesSubmodule ℝ E F _).mpr ⟨?_, fun m => ?_⟩
  · rw [coe_heatCauchyPotentialBUC, coe_heatCauchyPotentialBCF_of_pos ht]
    exact contDiff_heatKernel_convolution ht (ae_of_all _ f.val.norm_coe_le_norm)
  · rw [coe_heatCauchyPotentialBUC]
    exact ⟨_, norm_iteratedFDeriv_heatCauchyPotentialBCF_le ht f.val m⟩

/-- The smooth functions with bounded derivatives of every order form a core of the heat
generator on bounded uniformly continuous functions. -/
theorem generator_heatSemigroupBUC_hasCore_smoothBoundedDerivativesSubmodule :
    (heatSemigroupBUC (E := E) (F := F)).generator.HasCore
      (smoothBoundedDerivativesSubmodule ℝ E F) := by
  let S := (heatSemigroupBUC (E := E) (F := F)).toStronglyContinuousSemigroup
  refine (S.isClosed_generator.hasCore_iff_graph_subset_closure fun f hf => ?_).2 ?_
  · rw [S.generator_domain]
    exact (exists_generator_heatSemigroupBUC_eq_laplacian hf).choose
  · intro p hp
    obtain ⟨f, rfl⟩ := S.generator.mem_graph_iff'.mp hp
    have hf : f.val ∈ S.domain := by rw [← S.generator_domain]; exact f.property
    apply mem_closure_of_tendsto
      ((tendsto_heatCauchyPotentialBUC f.val).prodMk_nhds
        (tendsto_heatCauchyPotentialBUC (S.generator f)))
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    let g : (S.generator.domRestrict (smoothBoundedDerivativesSubmodule ℝ E F)).domain :=
      ⟨S.realOperator t f.val, by
        rw [heatSemigroupBUC_realOperator]
        exact heatCauchyPotentialBUC_mem_smoothBoundedDerivativesSubmodule ht f.val, by
          have hdom := S.realOperator_mem_domain (s := t) hf
          simp only [← S.generator_domain] at hdom
          exact hdom⟩
    refine (S.generator.domRestrict _).mem_graph_iff'.mpr ⟨g, Prod.ext ?_ ?_⟩
    · exact congrArg (fun T => T f.val) (heatSemigroupBUC_realOperator t)
    · calc
        _ = S.generator ⟨S.realOperator t f.val, by
            simpa only [← S.generator_domain] using S.realOperator_mem_domain (s := t) hf⟩ :=
          LinearPMap.domRestrict_apply rfl
        _ = _ := by
          simpa only [S, heatSemigroupBUC_realOperator] using
            S.realOperator_generator_map ⟨f.val, hf⟩

end TauCeti
