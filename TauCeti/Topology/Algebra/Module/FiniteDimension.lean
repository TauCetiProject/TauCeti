/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Multilinear maps on finitely many finite-dimensional spaces are continuous

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

For a bilinear map between normed spaces the same continuity is recorded in the curried form
that analysis consumes, `LinearMap.toContinuousLinearMap₂`: a bilinear form arriving from
algebra can then be fed to results such as Mathlib's integration by parts, which are stated for
`E →L[𝕜] F →L[𝕜] G`. `Continuous.bilinMap` is the form in which continuity of such a pairing is
usually applied, to a pair of continuous maps into the two arguments.
-/

public section

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
    fun i ↦ Module.finBasis 𝕜 (M i) with hb
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

namespace LinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The continuous bilinear map determined by a bilinear map out of two finite-dimensional
spaces, obtained by applying `LinearMap.toContinuousLinearMap` in each argument. -/
noncomputable def toContinuousLinearMap₂ (b : E →ₗ[𝕜] F →ₗ[𝕜] G) : E →L[𝕜] F →L[𝕜] G :=
  toContinuousLinearMap (toContinuousLinearMap.toLinearMap ∘ₗ b)

@[simp]
theorem toContinuousLinearMap₂_apply_apply (b : E →ₗ[𝕜] F →ₗ[𝕜] G) (v : E) (w : F) :
    b.toContinuousLinearMap₂ v w = b v w :=
  (rfl)

end LinearMap

/-- A bilinear map out of two finite-dimensional spaces, paired with two continuous maps into its
arguments, gives a continuous function. -/
theorem Continuous.bilinMap {𝕜 E F G X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [TopologicalSpace X] {f : X → E} {g : X → F}
    (hf : Continuous f) (hg : Continuous g) (b : E →ₗ[𝕜] F →ₗ[𝕜] G) :
    Continuous fun x ↦ b (f x) (g x) :=
  ((b.toContinuousLinearMap₂.continuous.comp hf).clm_apply hg).congr fun _ ↦
    LinearMap.toContinuousLinearMap₂_apply_apply _ _ _
