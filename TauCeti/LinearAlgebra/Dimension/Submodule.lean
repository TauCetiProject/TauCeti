/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimensions of submodules

Dimension-counting criteria for nontrivial submodule intersection: two subspaces of a
finite-dimensional space whose dimensions sum to more than the ambient dimension meet
nontrivially, and a subspace of rank greater than the rank of a linear map `f` meets `ker f`
nontrivially. Dually, the preimage of a subspace `W` under a linear map out of an
`m`-dimensional space has codimension at most the codimension of `W`.

The rank of a product `V.prod W` of free submodules is the sum of their ranks over any
semiring satisfying the strong rank condition. Consequently, the rank of a product map
`f.prodMap g` with free ranges is the sum of the ranks of `f` and `g`.
-/

public section

open Module (finrank)

universe u v

namespace Submodule

variable {𝕜 : Type*}

section DivisionRing

variable [DivisionRing 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- Two subspaces whose dimensions sum to more than the dimension of the ambient
space have nontrivial intersection. -/
theorem inf_ne_bot_of_finrank_lt [FiniteDimensional 𝕜 E] {V W : Submodule 𝕜 E}
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) : V ⊓ W ≠ ⊥ := fun hbot =>
  absurd (Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot))
    (by omega)

/-- The preimage of a subspace `W` under a linear map `f : M → N` of finite-dimensional spaces
has codimension at most the codimension of `W`: `dim M + dim W ≤ dim (f⁻¹ W) + dim N`. -/
theorem finrank_add_finrank_le_finrank_comap_add_finrank {M N : Type*} [AddCommGroup M]
    [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N]
    (f : M →ₗ[𝕜] N) (W : Submodule 𝕜 N) :
    finrank 𝕜 M + finrank 𝕜 W ≤ finrank 𝕜 (W.comap f) + finrank 𝕜 N := by
  -- The preimage is the kernel of `M → N ⧸ W`; apply rank–nullity to that map.
  have hker : LinearMap.ker (W.mkQ ∘ₗ f) = W.comap f := by
    rw [LinearMap.ker_comp, ker_mkQ]
  have h₁ := LinearMap.finrank_range_add_finrank_ker (W.mkQ ∘ₗ f)
  have h₂ := (W.mkQ ∘ₗ f).range.finrank_le
  have h₃ := W.finrank_quotient_add_finrank
  rw [hker] at h₁
  omega

end DivisionRing

/-- A submodule meeting the kernel of `f` trivially has rank at most the rank of `f`, since `f`
maps it injectively into its range. -/
theorem lift_rank_le_of_disjoint_ker [Ring 𝕜] {M : Type u} {N : Type v}
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
    {V : Submodule 𝕜 M} {f : M →ₗ[𝕜] N} (h : Disjoint V (LinearMap.ker f)) :
    Cardinal.lift.{v} (Module.rank 𝕜 V) ≤ Cardinal.lift.{u} f.rank := by
  apply (f.rangeRestrict.domRestrict V).lift_rank_le_of_injective
  simpa only [LinearMap.injective_domRestrict_iff, LinearMap.ker_rangeRestrict] using h

/-- The rank of a product of free submodules is the sum of their ranks. -/
theorem rank_prod [Semiring 𝕜] [StrongRankCondition 𝕜] {M : Type u} {N : Type v}
    [AddCommMonoid M] [Module 𝕜 M] [AddCommMonoid N] [Module 𝕜 N]
    (V : Submodule 𝕜 M) (W : Submodule 𝕜 N) [Module.Free 𝕜 V] [Module.Free 𝕜 W] :
    Module.rank 𝕜 (V.prod W) =
      Cardinal.lift.{v} (Module.rank 𝕜 V) + Cardinal.lift.{u} (Module.rank 𝕜 W) := by
  rw [(V.prodEquiv W).rank_eq, _root_.rank_prod]

end Submodule

namespace LinearMap

variable {𝕜 M N : Type*} {M' : Type u} {N' : Type v} [Semiring 𝕜] [StrongRankCondition 𝕜]
  [AddCommMonoid M] [Module 𝕜 M] [AddCommMonoid N] [Module 𝕜 N]
  [AddCommMonoid M'] [Module 𝕜 M'] [AddCommMonoid N'] [Module 𝕜 N']

/-- The rank of a product map with free ranges is the sum of the ranks of its components. -/
theorem rank_prodMap (f : M →ₗ[𝕜] M') (g : N →ₗ[𝕜] N')
    [Module.Free 𝕜 f.range] [Module.Free 𝕜 g.range] :
    (f.prodMap g).rank = Cardinal.lift.{v} f.rank + Cardinal.lift.{u} g.rank := by
  rw [LinearMap.rank, range_prodMap, Submodule.rank_prod]

end LinearMap

end
