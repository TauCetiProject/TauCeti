/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth functions with bounded derivatives

The smooth functions with globally bounded derivatives of each order form a vector subspace
`TauCeti.smoothBoundedDerivatives` of `E → F`. Each derivative has its own bound; no common bound
across orders is required.
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
