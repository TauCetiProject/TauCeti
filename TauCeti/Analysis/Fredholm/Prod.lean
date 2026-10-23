/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Products of Fredholm operators

Cartesian products preserve Fredholmness, and their indices add.

Fredholmness is preserved for topological modules over a nontrivially normed field, assuming only
that the domains are topological additive groups. The index formula needs only finite free kernels
and cokernels and is provided by `TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index`.

## Main declarations

* `ContinuousLinearMap.IsFredholm.prodMap`: a product of Fredholm operators is Fredholm.
* `ContinuousLinearMap.index_prodMap`: the Fredholm index is additive under products.
-/

public section

namespace ContinuousLinearMap

variable {K E₁ E₂ F₁ F₂ : Type*}
variable [NontriviallyNormedField K]
variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module K E₁] [IsTopologicalAddGroup E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module K E₂] [IsTopologicalAddGroup E₂]
variable [AddCommGroup F₁] [TopologicalSpace F₁] [Module K F₁]
variable [AddCommGroup F₂] [TopologicalSpace F₂] [Module K F₂]

variable {T : E₁ →L[K] F₁} {S : E₂ →L[K] F₂}

/-- The Cartesian product of two Fredholm operators is Fredholm. -/
lemma IsFredholm.prodMap
    (hT : IsFredholm T) (hS : IsFredholm S) : IsFredholm (T.prodMap S) := by
  have := hT.finite_ker
  have := hS.finite_ker
  have := hT.finite_coker
  have := hS.finite_coker
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `LinearMap.isStrictMap_prodMap` is stated for the underlying linear maps.
    change Topology.IsStrictMap ⇑((T : E₁ →ₗ[K] F₁).prodMap (S : E₂ →ₗ[K] F₂))
    exact LinearMap.isStrictMap_prodMap hT.isStrictMap hS.isStrictMap
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.range_prodMap]
    exact hT.isClosed_range.prod hS.isClosed_range
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.ker_prodMap]
    exact (Submodule.prodEquiv _ _).symm.finiteDimensional
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.range_prodMap]
    exact (Submodule.quotientProdEquiv _ _).symm.finiteDimensional
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.ker_prodMap]
    obtain ⟨PT, hPT⟩ := hT.closedComplemented_ker
    obtain ⟨PS, hPS⟩ := hS.closedComplemented_ker
    let P : E₁ × E₂ →L[K] E₁ × E₂ :=
      (T.ker.subtypeL.prodMap S.ker.subtypeL).comp (PT.prodMap PS)
    refine ⟨P.codRestrict (T.ker.prod S.ker) ?_, ?_⟩
    · rintro ⟨x, y⟩
      exact ⟨(PT x).property, (PS y).property⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩
      apply Subtype.ext
      simp only [P, coe_codRestrict_apply, comp_apply, coe_prodMap', Prod.map_apply,
        Submodule.subtypeL_apply, hPT ⟨x, hx⟩, hPS ⟨y, hy⟩]

end ContinuousLinearMap
