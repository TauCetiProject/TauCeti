/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.Bounded.UniformContinuous
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth bounded functions with bounded derivatives

The smooth functions with globally bounded derivatives of each order form a vector subspace
of bounded uniformly continuous functions. Each derivative has its own bound; no common bound
across orders is required. This is the natural smooth test space for graph approximation of
diffusion generators in supremum norm, where compactly supported functions need not be dense.
-/

public section

namespace BoundedContinuousFunction

open scoped ContDiff

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Smooth bounded uniformly continuous functions whose derivatives of every order are bounded.
The bounds may depend on the derivative order. -/
def smoothBoundedDerivativesSubmodule : Submodule 𝕜 (uniformContinuousSubmodule 𝕜 E F) where
  carrier := {f | ContDiff 𝕜 ∞ (f.val : E → F) ∧
    ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv 𝕜 m (f.val : E → F) x‖ ≤ C}
  zero_mem' := ⟨contDiff_const, fun m => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf, hfb⟩ ⟨hg, hgb⟩
    refine ⟨hf.add hg, fun m => ?_⟩
    obtain ⟨C, hC⟩ := hfb m
    obtain ⟨D, hD⟩ := hgb m
    refine ⟨C + D, fun x => ?_⟩
    simp only [AddMemClass.coe_add, FunLike.coe_add]
    rw [iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt
      (hg.of_le (by simp)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
  smul_mem' := by
    rintro c f ⟨hf, hfb⟩
    refine ⟨hf.const_smul c, fun m => ?_⟩
    obtain ⟨C, hC⟩ := hfb m
    refine ⟨‖c‖ * C, fun x => ?_⟩
    simp only [SetLike.val_smul, FunLike.coe_smul]
    rw [iteratedFDeriv_const_smul_apply (hf.of_le (by simp)).contDiffAt, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

/-- Membership is smoothness together with a global bound for each derivative order. -/
@[simp]
theorem mem_smoothBoundedDerivativesSubmodule (f : uniformContinuousSubmodule 𝕜 E F) :
    f ∈ smoothBoundedDerivativesSubmodule 𝕜 E F ↔
      ContDiff 𝕜 ∞ (f.val : E → F) ∧
        ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv 𝕜 m (f.val : E → F) x‖ ≤ C :=
  (Iff.rfl)

end BoundedContinuousFunction
