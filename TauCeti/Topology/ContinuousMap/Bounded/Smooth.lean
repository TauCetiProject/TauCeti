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
`TauCeti.smoothBoundedDerivatives` of `E → F`, and hence a vector subspace of bounded uniformly
continuous functions. Each derivative has its own bound; no common bound
across orders is required. This is the natural smooth test space for graph approximation of
diffusion generators in supremum norm, where compactly supported functions need not be dense.
-/

public section

open scoped ContDiff

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- Smooth functions whose derivatives of every order are globally bounded, as a subspace of
`E → F`. The bounds may depend on the derivative order. -/
def smoothBoundedDerivatives : Submodule 𝕜 (E → F) where
  carrier := {f | ContDiff 𝕜 ∞ f ∧ ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv 𝕜 m f x‖ ≤ C}
  zero_mem' := ⟨contDiff_const, fun m => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf, hfb⟩ ⟨hg, hgb⟩
    refine ⟨hf.add hg, fun m => ?_⟩
    obtain ⟨C, hC⟩ := hfb m
    obtain ⟨D, hD⟩ := hgb m
    refine ⟨C + D, fun x => ?_⟩
    rw [iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt
      (hg.of_le (by simp)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
  smul_mem' := by
    rintro c f ⟨hf, hfb⟩
    refine ⟨hf.const_smul c, fun m => ?_⟩
    obtain ⟨C, hC⟩ := hfb m
    refine ⟨‖c‖ * C, fun x => ?_⟩
    rw [iteratedFDeriv_const_smul_apply (hf.of_le (by simp)).contDiffAt, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

/-- Membership is smoothness together with a global bound for each derivative order. -/
@[simp]
theorem mem_smoothBoundedDerivatives {f : E → F} :
    f ∈ smoothBoundedDerivatives 𝕜 E F ↔
      ContDiff 𝕜 ∞ f ∧ ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv 𝕜 m f x‖ ≤ C :=
  Iff.rfl

end TauCeti

namespace BoundedContinuousFunction

/-- Smooth bounded uniformly continuous functions whose derivatives of every order are bounded,
the preimage of `TauCeti.smoothBoundedDerivatives` under the coercion to functions. The bounds
may depend on the derivative order. -/
noncomputable def smoothBoundedDerivativesSubmodule :
    Submodule 𝕜 (uniformContinuousSubmodule 𝕜 E F) :=
  (TauCeti.smoothBoundedDerivatives 𝕜 E F).comap
    ({ toFun := fun f => (f.val : E → F)
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : uniformContinuousSubmodule 𝕜 E F →ₗ[𝕜] E → F)

/-- Membership is smoothness together with a global bound for each derivative order. -/
@[simp]
theorem mem_smoothBoundedDerivativesSubmodule (f : uniformContinuousSubmodule 𝕜 E F) :
    f ∈ smoothBoundedDerivativesSubmodule 𝕜 E F ↔
      ContDiff 𝕜 ∞ (f.val : E → F) ∧
        ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv 𝕜 m (f.val : E → F) x‖ ≤ C :=
  (Iff.rfl)

end BoundedContinuousFunction
