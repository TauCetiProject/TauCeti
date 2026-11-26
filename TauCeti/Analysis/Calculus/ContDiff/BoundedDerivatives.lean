/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Smooth functions with bounded derivatives

The smooth functions with globally bounded derivatives of each order form a vector subspace
`TauCeti.smoothBoundedDerivatives` of `E → F`. Each derivative has its own bound; no common bound
across orders is required.

A directional derivative `x ↦ ∂ᵥf(x)` of a map that is `C^{k+1}` on an open set has, at each
point of the set, its derivative of order `i ≤ k` bounded by `‖v‖` times the derivative of `f` of
order `i + 1` (`ContDiffOn.norm_iteratedFDeriv_fderiv_apply_le`). So bounds on the derivatives of
`f` up to order `k + 1` bound those of `∂ᵥf` up to order `k`, which is how bounded derivatives
pass to the partial derivatives of a coefficient.
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

/-- **Derivatives of a directional derivative.** If `f` is `C^{k+1}` on an open set `s`, then at
each `x ∈ s` the derivative of order `i ≤ k` of `x ↦ ∂ᵥf(x) = fderiv 𝕜 f x v` is bounded by
`‖v‖` times the derivative of `f` of order `i + 1`. -/
theorem ContDiffOn.norm_iteratedFDeriv_fderiv_apply_le {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : E → F} {s : Set E} {k : ℕ} (hf : ContDiffOn 𝕜 (k + 1) f s)
    (hs : IsOpen s) (v : E) {i : ℕ} (hi : i ≤ k) {x : E} (hx : x ∈ s) :
    ‖iteratedFDeriv 𝕜 i (fun y => fderiv 𝕜 f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv 𝕜 (i + 1) f x‖ := by
  have hd : ContDiffAt 𝕜 k (fderiv 𝕜 f) x :=
    (hf.fderiv_of_isOpen hs (by norm_cast)).contDiffAt (hs.mem_nhds hx)
  -- `x ↦ ∂ᵥf(x)` is evaluation at `v` composed with the derivative of `f`.
  have h := (ContinuousLinearMap.apply 𝕜 F v).norm_iteratedFDeriv_comp_left hd
    (by exact_mod_cast hi)
  rw [norm_iteratedFDeriv_fderiv] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun g => by
    simpa only [ContinuousLinearMap.apply_apply, mul_comm] using g.le_opNorm v
