/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Finite-dimensional topological vector spaces

The linear-map conversion API preserves composition and recovers a continuous linear map after
forgetting continuity. `LinearMap.toContinuousLinearMap_coe` only needs finite dimension on the
source. `LinearMap.toContinuousLinearMap_comp` needs finite dimension on the source and
intermediate space; the target may be any topological vector space.

A multilinear map `f : MultilinearMap 𝕜 M N` on finitely many finite-dimensional Hausdorff
topological vector spaces over a complete nontrivially normed field is continuous when addition
and scalar multiplication are continuous in the codomain:
`MultilinearMap.continuous_of_finiteDimensional`. The codomain need only be an additive
commutative monoid. No norm is required on the domain modules or codomain, and no bound on the
map is assumed.

This is the multilinear companion of `LinearMap.continuous_of_finiteDimensional`. Mathlib's
`MultilinearMap.continuous_of_bound` asks for an explicit bound, which is exactly what one does
not have when the multilinear map arrives from algebra — a tensor or symmetric-power
construction, say — rather than from analysis.

In the same setting every seminorm on a finite-dimensional Hausdorff topological vector space is
continuous: `Seminorm.continuous_of_finiteDimensional`. Such a seminorm is dominated by a multiple
of the sup norm of the coordinates in a basis, and those coordinates are continuous. This is how a
norm defined by algebra, such as the spectral norm of a finite field extension, is compared with a
topology given in advance.

The inverse of the continuous coordinate equivalence `Module.Basis.equivFunL` of a finite
basis `v` sends a coordinate vector `x` to the linear combination `∑ i, x i • v i`:
`Module.Basis.equivFunL_symm_apply`, the continuous counterpart of
`Module.Basis.equivFun_symm_apply`.
-/

public section

namespace LinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F]

/-- Passing a continuous linear map to a linear map and back returns the original map. -/
@[simp]
theorem toContinuousLinearMap_coe (T : E →L[𝕜] F) :
    (T : E →ₗ[𝕜] F).toContinuousLinearMap = T :=
  ContinuousLinearMap.ext fun _ ↦ rfl

variable [T2Space F] [FiniteDimensional 𝕜 F]
  {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [Module 𝕜 G] [ContinuousSMul 𝕜 G]

/-- Passing a composition of linear maps to continuous linear maps preserves composition. -/
@[simp]
theorem toContinuousLinearMap_comp (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) :
    (g ∘ₗ f).toContinuousLinearMap =
      g.toContinuousLinearMap ∘L f.toContinuousLinearMap :=
  ContinuousLinearMap.ext fun _ ↦ rfl

end LinearMap

namespace MultilinearMap

variable {𝕜 ι : Type*} {M : ι → Type*} {N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Finite ι] [∀ i, AddCommGroup (M i)] [∀ i, Module 𝕜 (M i)] [∀ i, TopologicalSpace (M i)]
  [∀ i, IsTopologicalAddGroup (M i)] [∀ i, ContinuousSMul 𝕜 (M i)] [∀ i, T2Space (M i)]
  [∀ i, FiniteDimensional 𝕜 (M i)] [AddCommMonoid N] [Module 𝕜 N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul 𝕜 N]

/-- A multilinear map on finitely many finite-dimensional Hausdorff topological vector spaces
over a complete nontrivially normed field is continuous when its codomain is an additive
commutative monoid with continuous addition and scalar multiplication. No bound is required. -/
theorem continuous_of_finiteDimensional (f : MultilinearMap 𝕜 M N) : Continuous f := by
  classical
  cases nonempty_fintype ι
  set b : ∀ i, Module.Basis (Fin (Module.finrank 𝕜 (M i))) 𝕜 (M i) :=
    fun i ↦ Module.finBasis 𝕜 (M i) with _
  have key : ⇑f = fun m : ∀ i, M i ↦ ∑ r : ∀ i, Fin (Module.finrank 𝕜 (M i)),
      (∏ i, (b i).repr (m i) (r i)) • f fun i ↦ b i (r i) := by
    funext m
    have hm : f m = f fun i ↦ ∑ j, (b i).repr (m i) j • b i j := by
      congr 1 with i
      exact ((b i).sum_repr (m i)).symm
    rw [hm, f.map_sum]
    exact Finset.sum_congr rfl fun r _ ↦ f.map_smul_univ _ _
  rw [key]
  refine continuous_finsetSum _ fun r _ ↦ Continuous.smul ?_ continuous_const
  refine continuous_finsetProd _ fun i _ ↦ ?_
  exact (((b i).coord (r i)).continuous_of_finiteDimensional.comp
    (continuous_apply i)).congr fun m ↦ Module.Basis.coord_apply _ _ _

end MultilinearMap

namespace Seminorm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

/-- A seminorm on a finite-dimensional Hausdorff topological vector space over a complete
nontrivially normed field is continuous. -/
theorem continuous_of_finiteDimensional (p : Seminorm 𝕜 E) : Continuous p := by
  let b := Module.finBasis 𝕜 E
  -- `p` is dominated by `C` times the sup norm of the coordinates in `b`, with `C = ∑ᵢ p (b i)`
  have hle (x : E) : p x ≤ (∑ i, p (b i)) * ‖b.equivFun x‖ :=
    calc p x = p (∑ i, b.equivFun x i • b i) := by rw [b.sum_equivFun]
      _ ≤ ∑ i, p (b.equivFun x i • b i) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ = ∑ i, ‖b.equivFun x i‖ * p (b i) := by simp only [map_smul_eq_mul]
      _ ≤ ∑ i, ‖b.equivFun x‖ * p (b i) := by
        gcongr with i
        exact norm_le_pi_norm (b.equivFun x) i
      _ = (∑ i, p (b i)) * ‖b.equivFun x‖ := by
        rw [← Finset.mul_sum, mul_comm]
  refine Seminorm.continuous_of_continuousAt_zero ?_
  rw [ContinuousAt, map_zero]
  refine squeeze_zero (fun x ↦ apply_nonneg p x) hle ?_
  have hc : Continuous fun x ↦ (∑ i, p (b i)) * ‖b.equivFun x‖ :=
    continuous_const.mul (continuous_norm.comp (continuous_equivFun_basis b))
  simpa using hc.tendsto 0

end Seminorm

namespace Module.Basis

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [Fintype ι]

/-- The inverse of the continuous coordinate equivalence of a finite basis `v` sends a coordinate
vector `x` to the linear combination `∑ i, x i • v i`. -/
@[simp] theorem equivFunL_symm_apply (v : Basis ι 𝕜 E) (x : ι → 𝕜) :
    v.equivFunL.symm x = ∑ i, x i • v i :=
  v.equivFunL.symm_apply_eq.2 <| funext fun i ↦ by
    rw [equivFunL_apply, ← equivFun_apply, ← v.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end Module.Basis
