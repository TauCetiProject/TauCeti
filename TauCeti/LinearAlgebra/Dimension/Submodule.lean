/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Intersections of submodules by dimension

Dimension-counting criteria for nontrivial submodule intersection: two subspaces of a
finite-dimensional space whose dimensions sum to more than the ambient dimension meet
nontrivially, and a subspace of rank greater than the rank of a linear map `f` meets `ker f`
nontrivially.
-/

public section

open Module (finrank)

universe u v

namespace Submodule

variable {𝕜 E : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Two subspaces whose dimensions sum to more than the dimension of the ambient
space have nontrivial intersection. -/
theorem inf_ne_bot_of_finrank_lt [FiniteDimensional 𝕜 E] {V W : Submodule 𝕜 E}
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) : V ⊓ W ≠ ⊥ := fun hbot =>
  absurd (Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot))
    (by omega)

/-- A subspace meeting the kernel of `f` trivially has rank at most the rank of `f`, since `f`
maps it injectively into its range. -/
theorem lift_rank_le_of_disjoint_ker {M : Type u} {N : Type v} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] {V : Submodule 𝕜 M} {f : M →ₗ[𝕜] N}
    (h : Disjoint V (LinearMap.ker f)) :
    Cardinal.lift.{v} (Module.rank 𝕜 V) ≤ Cardinal.lift.{u} f.rank := by
  have hinj : Function.Injective (f ∘ₗ V.subtype) :=
    (injective_iff_map_eq_zero _).mpr fun y hy ↦ Subtype.ext (disjoint_def.mp h y y.2 hy)
  exact (lift_rank_range_of_injective _ hinj).symm.le.trans
    (Cardinal.lift_le.mpr (LinearMap.rank_comp_le_left _ _))

end Submodule

end
