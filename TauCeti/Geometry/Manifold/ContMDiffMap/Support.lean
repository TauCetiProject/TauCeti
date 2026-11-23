/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Operators on `C^n` functions that do not enlarge supports

A linear operator `D` on the `C^n` functions on a manifold `M` does not enlarge supports if
`tsupport (D f) ⊆ tsupport f` for every `f`. Such operators preserve compact support
(`HasCompactSupport.mono'`), and the class is closed under scalar multiplication and finite sums
and contains the multiplication operators.

## Main results

* `TauCeti.tsupport_mulLeft_apply_subset`, `TauCeti.tsupport_smul_apply_subset`,
  `TauCeti.tsupport_sum_apply_subset`: multiplication operators, scalar multiples and finite sums
  do not enlarge supports.
-/

public section

open Function
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- Multiplication by a `C^n` function does not enlarge supports. -/
theorem tsupport_mulLeft_apply_subset {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    [ContMDiffRing 𝓘(𝕜, A) n A] (c f : C^n⟮I, M; 𝓘(𝕜, A), A⟯) :
    tsupport (LinearMap.mulLeft 𝕜 c f) ⊆ tsupport f := by
  rw [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
  exact tsupport_mul_subset_right

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A scalar multiple of an operator on `C^n` functions that does not enlarge supports does not
enlarge supports. -/
theorem tsupport_smul_apply_subset {D : C^n⟮I, M; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] C^n⟮I, M; 𝓘(𝕜, V), V⟯}
    (hD : ∀ f, tsupport (D f) ⊆ tsupport f) (c : 𝕜) (f : C^n⟮I, M; 𝓘(𝕜, V), V⟯) :
    tsupport ((c • D) f) ⊆ tsupport f := by
  rw [LinearMap.smul_apply, ContMDiffMap.coe_smul]
  exact (tsupport_smul_subset_right (fun _ ↦ c) _).trans (hD f)

/-- A finite sum of operators on `C^n` functions that do not enlarge supports does not enlarge
supports. -/
theorem tsupport_sum_apply_subset {ι : Type*} (s : Finset ι)
    {D : ι → C^n⟮I, M; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] C^n⟮I, M; 𝓘(𝕜, V), V⟯}
    (hD : ∀ i ∈ s, ∀ f, tsupport (D i f) ⊆ tsupport f) (f : C^n⟮I, M; 𝓘(𝕜, V), V⟯) :
    tsupport ((∑ i ∈ s, D i) f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport _)
  rw [mem_support, LinearMap.coe_sum, Finset.sum_apply, ContMDiffMap.coe_sum,
    Finset.sum_apply] at hx
  obtain ⟨i, hi, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact hD i hi f (subset_tsupport _ hx)

end TauCeti
