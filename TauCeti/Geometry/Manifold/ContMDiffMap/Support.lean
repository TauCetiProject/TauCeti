/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Operators on smooth functions that do not enlarge supports

A linear operator `D` on `C^∞(E)` does not enlarge supports if `tsupport (D f) ⊆ tsupport f` for
every `f`. Such operators preserve compact support, and the class is closed under scalar
multiplication and finite sums and contains the multiplication operators.

## Main results

* `HasCompactSupport.apply_of_tsupport_subset`: an operator that does not enlarge supports
  preserves compact support.
* `TauCeti.tsupport_mulLeft_apply_subset`, `TauCeti.tsupport_smul_apply_subset`,
  `TauCeti.tsupport_sum_apply_subset`: multiplication operators, scalar multiples and finite sums
  do not enlarge supports.
-/

public section

open Function
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An operator on `C^∞(E)` that does not enlarge supports preserves compact support. -/
theorem _root_.HasCompactSupport.apply_of_tsupport_subset
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    {f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hf : HasCompactSupport f) : HasCompactSupport (D f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (hD f)

/-- Multiplication by a smooth function does not enlarge supports. -/
theorem tsupport_mulLeft_apply_subset (c f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    tsupport (LinearMap.mulLeft ℝ c f) ⊆ tsupport f := by
  rw [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
  exact tsupport_mul_subset_right

/-- A scalar multiple of an operator on `C^∞(E)` that does not enlarge supports does not enlarge
supports. -/
theorem tsupport_smul_apply_subset {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hD : ∀ f, tsupport (D f) ⊆ tsupport f) (c : ℝ) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    tsupport ((c • D) f) ⊆ tsupport f := by
  rw [LinearMap.smul_apply, ContMDiffMap.coe_smul]
  exact (tsupport_smul_subset_right (fun _ ↦ c) _).trans (hD f)

/-- A finite sum of operators on `C^∞(E)` that do not enlarge supports does not enlarge
supports. -/
theorem tsupport_sum_apply_subset {ι : Type*} (s : Finset ι)
    {D : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hD : ∀ i ∈ s, ∀ f, tsupport (D i f) ⊆ tsupport f) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    tsupport ((∑ i ∈ s, D i) f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport _)
  rw [mem_support, LinearMap.coe_sum, Finset.sum_apply, ContMDiffMap.coe_sum,
    Finset.sum_apply] at hx
  obtain ⟨i, hi, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact hD i hi f (subset_tsupport _ hx)

end TauCeti
