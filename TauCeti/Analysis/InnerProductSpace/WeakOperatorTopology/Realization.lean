/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Simultaneous realization of matrix-coefficient sums

Suppose a parameter acts linearly on several finite-dimensional spaces. If a series of
parameters has convergent matrix coefficients in every space, all the limits are the
matrix coefficients of a single parameter. The parameters themselves need not converge or
carry a topology: it is their joint image that is finite-dimensional and closed.

This is the closed-image step in `New.Data.exists_heckeAlgebra_eq_mul_inner_of_hasSum_rallisTerm`
in `grh/src/New/Spanning/Multiplicities/EqualMultiplicities.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

public section

open scoped InnerProductSpace

namespace LinearMap

/-- For a finite family of actions on finite-dimensional spaces, simultaneous sums of matrix
coefficients are realized by a single parameter. Each action may include a different scalar
normalization, absorbed when assembling `ρ` with `LinearMap.pi`. -/
theorem exists_of_hasSum_inner_apply {𝕜 A J ι : Type*} [RCLike 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [Finite J]
    {E F : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module 𝕜 (E j)]
    [∀ j, NormedAddCommGroup (F j)] [∀ j, InnerProductSpace 𝕜 (F j)]
    [∀ j, FiniteDimensional 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (F j)]
    (ρ : A →ₗ[𝕜] (∀ j, E j →ₗ[𝕜] F j)) {p : ι → A} {B : ∀ j, E j → F j → 𝕜}
    (hB : ∀ j x y, HasSum (fun i ↦ ⟪y, ρ (p i) j x⟫_𝕜) (B j x y)) :
    ∃ a : A, ∀ j x y, ⟪y, ρ a j x⟫_𝕜 = B j x y := by
  let coeff : (∀ j, E j →ₗ[𝕜] F j) →ₗ[𝕜] (∀ j, E j → F j → 𝕜) :=
    LinearMap.pi fun j ↦ LinearMap.pi fun x ↦ LinearMap.pi fun y ↦
      innerₛₗ 𝕜 y ∘ₗ LinearMap.applyₗ x ∘ₗ LinearMap.proj j
  let T := coeff ∘ₗ ρ
  have hT (a : A) (j : J) (x : E j) (y : F j) : T a j x y = ⟪y, ρ a j x⟫_𝕜 := by
    simp only [T, coeff, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      LinearMap.applyₗ_apply_apply, innerₛₗ_apply_apply]
  have hfinite : FiniteDimensional 𝕜 T.range := by
    rw [LinearMap.range_comp]
    infer_instance
  have hsum : HasSum (T ∘ p) B := by
    refine Pi.hasSum.mpr fun j ↦ Pi.hasSum.mpr fun x ↦ Pi.hasSum.mpr fun y ↦ ?_
    simpa only [Function.comp_apply, hT] using hB j x y
  obtain ⟨a, ha⟩ := T.range.isClosed_of_finiteDimensional.mem_of_tendsto hsum
    (Filter.Eventually.of_forall fun s ↦ T.range.sum_mem fun i _ ↦ LinearMap.mem_range_self T (p i))
  exact ⟨a, fun j x y ↦ by rw [← hT, ha]⟩

end LinearMap
