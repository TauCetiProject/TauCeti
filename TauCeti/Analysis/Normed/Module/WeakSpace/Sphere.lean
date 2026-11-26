/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.Algebra.Module.WeakSpace
import TauCeti.Analysis.Normed.Module.WeakSpace.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spheres of injective linear maps in the weak topology

In an infinite-dimensional space every weak neighbourhood of `0` contains a line through a nonzero
vector (`TauCeti.exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero`). For an injective
linear map `j` into a normed space this line meets the sphere `{u | ‖j u‖ = r}` for every `r ≥ 0`,
so `0` lies in the weak closure of that sphere, the sphere is not weakly closed when `r > 0`, and
`j` is not continuous from the weak topology to the norm topology. This is why weak-to-norm
continuity of compact operators only holds on bounded sets.

In finite dimension none of this happens: the weak topology of a finite-dimensional normed space
is its norm topology (`TauCeti.toWeakSpaceContinuousLinearEquiv`), so a set is weakly closed
exactly when it is closed, every sphere `{u | ‖j u‖ = r}` of a linear map into a normed space is
weakly closed, and every such map is weak-to-norm continuous.

## Main results

* `TauCeti.zero_mem_closure_toWeakSpace_setOf_norm_eq`: `0` lies in the weak closure of every
  sphere of an injective linear map.
* `TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq`: spheres of positive radius are not weakly
  closed.
* `TauCeti.not_continuous_comp_toWeakSpace_symm`: an injective linear map is not weak-to-norm
  continuous.
* `TauCeti.isClosed_toWeakSpace_setOf_norm_eq` and `TauCeti.continuous_comp_toWeakSpace_symm`: in
  finite dimension, spheres of linear maps are weakly closed and linear maps are weak-to-norm
  continuous.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Springer, 2011, §3.2, Example 1 (weak closure of the unit sphere).
-/

public section

open Set Topology

namespace TauCeti

section Sphere

variable {𝕜 V F G : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FunLike G V F] [LinearMapClass G 𝕜 V F] {j : G}

/-- In an infinite-dimensional space, `0` lies in the weak closure of every sphere
`{u | ‖j u‖ = r}` of an injective linear map `j` into a normed space. -/
theorem zero_mem_closure_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) {r : ℝ} (hr : 0 ≤ r) :
    (0 : WeakSpace 𝕜 V) ∈ closure (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := by
  refine mem_closure_iff_nhds.2 fun U hU ↦ ?_
  obtain ⟨x, hx, hxU⟩ := exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero hV hU
  have hjx : ‖j x‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero_iff j hj).2 hx)
  -- Rescale `x` so that its image has norm `r`.
  refine ⟨_, hxU ((r / ‖j x‖ : ℝ) : 𝕜), mem_image_of_mem _ ?_⟩
  simp [map_smul, norm_smul, abs_of_nonneg hr, hjx]

/-- In an infinite-dimensional space, a sphere `{u | ‖j u‖ = r}` of positive radius of an
injective linear map `j` into a normed space is not weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := fun hclosed ↦ by
  obtain ⟨u, hu, hu0⟩ :=
    hclosed.closure_subset (zero_mem_closure_toWeakSpace_setOf_norm_eq hV hj hr.le)
  rw [map_eq_zero_iff _ (toWeakSpace 𝕜 V).injective] at hu0
  subst hu0
  simp only [mem_ofPred_eq, map_zero, norm_zero] at hu
  exact hr.ne hu

/-- In an infinite-dimensional space, an injective linear map into a normed space is not
continuous from the weak topology to the norm topology. -/
theorem not_continuous_comp_toWeakSpace_symm (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) :
    ¬ Continuous fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w) := fun hcont ↦ by
  refine not_isClosed_toWeakSpace_setOf_norm_eq hV hj one_pos ?_
  rw [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  exact isClosed_eq (continuous_norm.comp hcont) continuous_const

end Sphere

section FiniteDimensional

variable {𝕜 V F G : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FunLike G V F]
  [LinearMapClass G 𝕜 V F] (j : G)

/-- In finite dimension, every linear map into a normed space is continuous from the weak
topology to the norm topology. -/
theorem continuous_comp_toWeakSpace_symm :
    Continuous fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w) := by
  simpa [Function.comp_def] using
    (LinearMap.continuous_of_finiteDimensional (LinearMap.ofClass j : V →ₗ[𝕜] F)).comp
      (toWeakSpaceContinuousLinearEquiv 𝕜 V).symm.continuous

/-- In finite dimension, every sphere `{u | ‖j u‖ = r}` of a linear map into a normed space is
weakly closed. -/
theorem isClosed_toWeakSpace_setOf_norm_eq (r : ℝ) :
    IsClosed (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := by
  rw [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  exact isClosed_eq (continuous_norm.comp (continuous_comp_toWeakSpace_symm j)) continuous_const

end FiniteDimensional

end TauCeti
