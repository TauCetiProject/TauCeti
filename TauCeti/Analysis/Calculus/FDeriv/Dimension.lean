/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Dimension obstructions to surjective derivatives

If the source has smaller finite dimension than the target, every derivative is nonsurjective,
so every source point is critical. This linear-algebraic obstruction holds for topological
modules over any nontrivially normed field, without differentiability assumptions.

Rank also controls kernels: `HasFDerivAt.apply_eq_zero_iff_of_comp_eventuallyEq` shows that if
`P ∘ g` agrees near `z` with a continuous linear map `L` and the derivative of `g` at `z` has rank
at most that of `L`, then this derivative has the same kernel as `L`.
-/

public section

open Filter Function Module Set
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

namespace TauCeti

variable [FiniteDimensional 𝕜 E]

/-- When the source has strictly smaller finite dimension than the codomain, every Fréchet
derivative is nonsurjective. Thus every source point is critical, independently of the regularity
of the function. -/
theorem not_surjective_fderiv_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank 𝕜 E < finrank 𝕜 F) (x : E) :
    ¬ Surjective (fderiv 𝕜 f x) :=
  fun hsurj ↦ hEF.not_ge (LinearMap.finrank_le_finrank_of_surjective hsurj)

/-- When the source has strictly smaller finite dimension than the codomain, the critical locus
of any function is the whole source. -/
@[simp]
theorem setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank 𝕜 E < finrank 𝕜 F) :
    {x | ¬ Surjective (fderiv 𝕜 f x)} = (univ : Set E) :=
  eq_univ_of_forall fun x ↦ not_surjective_fderiv_of_finrank_lt_finrank f hEF x

end TauCeti

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [ContinuousAdd G]
  [ContinuousSMul 𝕜 G] [T2Space G]

/-- If `P ∘ g` agrees near `z` with a continuous linear map `L`, and the derivative `D` of `g` at
`z` has finite rank at most that of `L`, then `D` and `L` have the same kernel: projecting the
range of `D` with `P` does not lower its dimension, so it does not enlarge its kernel. -/
theorem HasFDerivAt.apply_eq_zero_iff_of_comp_eventuallyEq {g : E → F} {D : E →L[𝕜] F}
    [FiniteDimensional 𝕜 (LinearMap.range D.toLinearMap)]
    {P : F →L[𝕜] G} {L : E →L[𝕜] G} {z : E} (hg : HasFDerivAt g D z)
    (hPg : (fun w ↦ P (g w)) =ᶠ[𝓝 z] L)
    (hrank : finrank 𝕜 (LinearMap.range D.toLinearMap) ≤
      finrank 𝕜 (LinearMap.range L.toLinearMap))
    {v : E} : D v = 0 ↔ L v = 0 := by
  -- The chain rule for the continuous linear map `P`, written with the asymptotics of
  -- topological vector spaces since Mathlib states `ContinuousLinearMap.comp_hasFDerivAt` only
  -- for normed spaces.
  have hPD : HasFDerivAt (fun w ↦ P (g w)) (P ∘L D) z := .of_isLittleOTVS <| by
    simpa using P.isBigOTVS_fun_comp.trans_isLittleOTVS hg.isLittleOTVS
  have hcomp : P ∘L D = L := hPD.unique (L.hasFDerivAt.congr_of_eventuallyEq hPg)
  have hker := LinearMap.ker_comp_eq_of_finrank_range_le (D : E →ₗ[𝕜] F) (P : F →ₗ[𝕜] G)
    (by rwa [← ContinuousLinearMap.toLinearMap_comp, hcomp])
  -- Hence `ker L = ker D`.
  rw [← ContinuousLinearMap.toLinearMap_comp, hcomp] at hker
  simpa using (SetLike.ext_iff.1 hker v).symm

end
