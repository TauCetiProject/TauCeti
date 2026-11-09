/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.StdBasis
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Coordinates on `lp`

The characteristic equation for Mathlib's bundled coordinate evaluation lets users compute
with `lp.evalCLM` without unfolding its construction as a bounded linear map, and the ℓ¹ norm is
the sum of the norms of the coordinates (`lp.hasSum_norm_one`). The scalar
coordinate vectors are linearly independent, and vectors in their span vanish outside the
corresponding indices. These algebraic facts hold over normed rings at every exponent.

For `p ≠ ∞` the coordinate vectors span a dense subspace, so a uniformly bounded family of
operators on `lp E p` that converges on every `single i x` converges at every vector
(`lp.tendsto_apply_of_tendsto_apply_single`).
-/

public section

open scoped ENNReal Topology
open Filter

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

section Density

variable {ι 𝕜 : Type*} {E : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Bounded convergence on coordinate vectors.** For `p ≠ ∞`, a uniformly bounded family of
operators on `lp E p` that converges at every coordinate vector `single i x` converges at every
vector. -/
theorem tendsto_apply_of_tendsto_apply_single [DecidableEq ι] {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace 𝕜 Z] (hp : p ≠ ∞) {α : Type*} {l : Filter α} {f : α → lp E p →L[𝕜] Z}
    {g : lp E p →L[𝕜] Z} {C : ℝ} (hC : ∀ᶠ a in l, ‖f a‖ ≤ C)
    (h : ∀ i (x : E i), Tendsto (fun a ↦ f a (lp.single p i x)) l (𝓝 (g (lp.single p i x))))
    (x : lp E p) : Tendsto (fun a ↦ f a x) l (𝓝 (g x)) := by
  let D : Submodule 𝕜 (lp E p) :=
    { carrier := {y | Tendsto (fun a ↦ f a y) l (𝓝 (g y))}
      add_mem' := fun hy hz ↦ by simpa only [Set.mem_ofPred_eq, map_add] using hy.add hz
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using tendsto_const_nhds
      smul_mem' := fun c y hy ↦ by simpa only [Set.mem_ofPred_eq, map_smul] using hy.const_smul c }
  have hD : Dense (D : Set (lp E p)) := fun y ↦
    mem_closure_of_tendsto (lp.hasSum_single hp y)
      (Eventually.of_forall fun s ↦ D.sum_mem fun i _ ↦ h i (y i))
  exact ContinuousLinearMap.tendsto_apply_of_dense hD hC (fun y hy ↦ hy) x

end Density

end lp
