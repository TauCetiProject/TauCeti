/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Dimension obstructions to surjective derivatives

If the source has smaller finite dimension than the target, every derivative is nonsurjective,
so every source point is critical. This linear-algebraic obstruction holds for topological
modules over any nontrivially normed field, without differentiability assumptions.

Rank also controls kernels: `HasFDerivAt.apply_eq_zero_of_comp_eventuallyEq` shows that if
`P ∘ g` agrees near `z` with a continuous linear map `L` and the derivative of `g` at `z` has rank
at most that of `L`, then this derivative vanishes on the kernel of `L`.
-/

public section

open Filter Function Module Set
open scoped Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- When the source has strictly smaller finite dimension than the codomain, every Fréchet
derivative is nonsurjective. Thus every source point is critical, independently of the regularity
of the function. -/
theorem not_surjective_fderiv_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank 𝕜 E < finrank 𝕜 F) (x : E) :
    ¬ Surjective (fderiv 𝕜 f x) := by
  intro hsurj
  exact (not_le_of_gt hEF) (LinearMap.finrank_le_finrank_of_surjective hsurj)

/-- When the source has strictly smaller finite dimension than the codomain, the critical locus
of any function is the whole source. -/
@[simp]
theorem setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank 𝕜 E < finrank 𝕜 F) :
    {x | ¬ Surjective (fderiv 𝕜 f x)} = (univ : Set E) :=
  eq_univ_of_forall fun x ↦ not_surjective_fderiv_of_finrank_lt_finrank f hEF x

end TauCeti

section NontriviallyNormedField

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- If `P ∘ g` agrees near `z` with a continuous linear map `L`, and the derivative `D` of `g` at
`z` has finite rank at most that of `L`, then `D` vanishes on the kernel of `L`: projecting the
range of `D` with `P` does not lower its dimension, so it does not enlarge its kernel. -/
theorem HasFDerivAt.apply_eq_zero_of_comp_eventuallyEq
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕂 G] {g : E → F} {D : E →L[𝕂] F}
    [FiniteDimensional 𝕂 (LinearMap.range D.toLinearMap)]
    {P : F →L[𝕂] G} {L : E →L[𝕂] G} {z : E} (hg : HasFDerivAt g D z)
    (hPg : (fun w ↦ P (g w)) =ᶠ[𝓝 z] L)
    (hrank : finrank 𝕂 (LinearMap.range D.toLinearMap) ≤
      finrank 𝕂 (LinearMap.range L.toLinearMap))
    {v : E} (hv : L v = 0) : D v = 0 := by
  have hcomp : (P : F →ₗ[𝕂] G) ∘ₗ (D : E →ₗ[𝕂] F) = L := congrArg ContinuousLinearMap.toLinearMap
    ((P.hasFDerivAt.comp z hg).unique (L.hasFDerivAt.congr_of_eventuallyEq hPg))
  have hker := LinearMap.ker_comp_eq_of_finrank_range_le (D : E →ₗ[𝕂] F) (P : F →ₗ[𝕂] G)
    (by rwa [hcomp])
  rw [hcomp] at hker
  have hv' : v ∈ LinearMap.ker (L : E →ₗ[𝕂] G) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact hv
  rw [hker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv'
  exact hv'

end NontriviallyNormedField

end
