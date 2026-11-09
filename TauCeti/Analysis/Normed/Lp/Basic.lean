/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Coordinates on `lp`

The characteristic equation for Mathlib's bundled coordinate evaluation lets users compute
with `lp.evalCLM` without unfolding its construction as a bounded linear map, and the ℓ¹ norm is
the sum of the norms of the coordinates (`lp.hasSum_norm_one`, and `lp.hasSum_enorm_one` for
extended norms). The scalar coordinate vectors are linearly independent, and vectors in their span
vanish outside the corresponding indices. These algebraic facts hold over normed rings at every
exponent.

For a finite exponent `p` and a countable index type, `lp E p` is separable as soon as every
`E i` is (`lp.separableSpace`): the finite sums of coordinate vectors with entries in countable
dense subsets are dense.
-/

public section

open scoped ENNReal

namespace lp

variable {ι 𝕜 : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
  {p : ℝ≥0∞}

/-- The bundled coordinate evaluation returns the corresponding coordinate. -/
@[simp]
theorem evalCLM_apply [Fact (1 ≤ p)] (i : ι) (x : lp E p) : evalCLM 𝕜 E p i x = x i := (rfl)

/-- The ℓ¹ norm is the sum of the norms of the coordinates. -/
theorem hasSum_norm_one (y : lp E 1) : HasSum (fun i ↦ ‖y i‖) ‖y‖ := by
  simpa using lp.hasSum_norm (p := 1) (by simp) y

/-- The extended ℓ¹ norm is the sum of the extended norms of the coordinates. -/
theorem hasSum_enorm_one (y : lp E 1) : HasSum (fun i ↦ ‖y i‖ₑ) ‖y‖ₑ := by
  simp only [enorm_eq_nnnorm]
  exact ENNReal.hasSum_coe.2 (NNReal.hasSum_coe.1 (hasSum_norm_one y))

/-- For a finite exponent and a countable index type, `lp E p` is separable when every `E i` is.
-/
theorem separableSpace [Countable ι] [∀ i, TopologicalSpace.SeparableSpace (E i)]
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) : TopologicalSpace.SeparableSpace (lp E p) := by
  classical
  set S : Set (lp E p) := ⋃ i, Set.range (lp.single p i)
  have hS : TopologicalSpace.IsSeparable S :=
    .iUnion fun i ↦ TopologicalSpace.isSeparable_range (lp.isometry_single i).continuous
  rw [← TopologicalSpace.isSeparable_univ_iff]
  -- Every element is the limit of the finite sums of its coordinate vectors, which lie in the
  -- additive span of `S`.
  refine (hS.span (R := ℕ)).closure.mono fun f _ ↦
    mem_closure_of_tendsto (lp.hasSum_single hp f) (Filter.Eventually.of_forall fun s ↦ ?_)
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span (Set.mem_iUnion.2 ⟨i, f i, rfl⟩)

section Single

variable [DecidableEq ι]

/-- The scalar coordinate vectors in `lp` are linearly independent. -/
theorem linearIndependent_single_one :
    LinearIndependent 𝕜 (fun i : ι ↦ lp.single p i (1 : 𝕜)) := by
  apply LinearIndependent.of_comp (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype
  have hcoe : (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype ∘
      (fun i : ι ↦ lp.single p i (1 : 𝕜)) = fun i ↦ Pi.single i (1 : 𝕜) := by
    funext i
    exact lp.coeFn_single p i 1
  rw [hcoe]
  exact Pi.linearIndependent_single_one ι 𝕜

/-- A vector in the span of a family of coordinate vectors vanishes outside their indices. -/
theorem apply_eq_zero_of_mem_span_single {κ : Type*} (f : κ → ι) {x : ℓ^p(ι, 𝕜)}
    (hx : x ∈ Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (1 : 𝕜)))
    {i : ι} (hi : i ∉ Set.range f) : x i = 0 := by
  have hle : Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (1 : 𝕜)) ≤
      LinearMap.ker (evalₗ (𝕜 := 𝕜) (fun _ : ι ↦ 𝕜) p i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [evalₗ_apply]
    exact lp.single_apply_ne (E := fun _ : ι ↦ 𝕜) p (f j) 1
      (fun hij ↦ hi ⟨j, hij.symm⟩)
  simpa only [evalₗ_apply] using LinearMap.mem_ker.mp (hle hx)

end Single

end lp
