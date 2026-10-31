/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# The index under finite-rank perturbations of Fredholm operators

That a finite-rank perturbation of a Fredholm operator is again Fredholm is Mathlib's
`ContinuousLinearMap.IsFredholm.add_hasFiniteRange`. This file records the corresponding index
statement, which follows by restricting both operators to the kernel of the perturbation.

Finiteness of the rank is spelled with Mathlib's `LinearMap.HasFiniteRange`, matching the
hypothesis of `ContinuousLinearMap.IsFredholm.add_hasFiniteRange`.

## Main declarations

* `ContinuousLinearMap.index_add_of_hasFiniteRange`: over a complete nontrivially normed
  field, adding an operator of finite rank between Hausdorff topological vector spaces preserves
  the Fredholm index.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F]
variable {T K : E →L[𝕜] F}


/-- Finite-rank perturbations of Fredholm operators between Hausdorff topological vector spaces
over a complete nontrivially normed field preserve the index. -/
theorem _root_.ContinuousLinearMap.index_add_of_hasFiniteRange
    (hT : ContinuousLinearMap.IsFredholm T)
    (hK : LinearMap.HasFiniteRange (K : E →ₗ[𝕜] F)) :
    ContinuousLinearMap.index (T + K) = ContinuousLinearMap.index T := by
  set ι := (LinearMap.ker (K : E →ₗ[𝕜] F)).subtypeL with hι
  have := hK.cofg_ker
  have hιF : ContinuousLinearMap.IsFredholm ι := K.ker.isFredholm_subtypeL K.isClosed_ker
  have hcomp : (T + K).comp ι = T.comp ι := by
    ext x
    have hx : K (x : E) = 0 := LinearMap.mem_ker.mp x.2
    simp [hι, hx]
  have h₁ : ContinuousLinearMap.index ((T + K).comp ι) =
      ContinuousLinearMap.index (T + K) + ContinuousLinearMap.index ι := by
    simpa only [ContinuousLinearMap.index_def, ContinuousLinearMap.toLinearMap_comp] using
      (hT.add_hasFiniteRange hK).index_comp hιF
  have h₂ : ContinuousLinearMap.index (T.comp ι) =
      ContinuousLinearMap.index T + ContinuousLinearMap.index ι := by
    simpa only [ContinuousLinearMap.index_def, ContinuousLinearMap.toLinearMap_comp] using
      hT.index_comp hιF
  rw [hcomp, h₂] at h₁
  omega


end TauCeti

end
