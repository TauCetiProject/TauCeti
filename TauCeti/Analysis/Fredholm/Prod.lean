/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Products of Fredholm operators

Cartesian products preserve Fredholmness, and their indices add.

Fredholmness is preserved for topological modules over a nontrivially normed field, assuming only
that the domains are topological additive groups. The index formula needs only finite free kernels
and cokernels and is provided by `TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index`.

## Main declarations

* `ContinuousLinearMap.IsFredholm.prodMap`: a product of Fredholm operators is Fredholm.
* `ContinuousLinearMap.index_prodMap`: the Fredholm index is additive under products.
* `ContinuousLinearMap.isFredholm_prodMap_iff`: conversely, over a complete field and between
  Hausdorff topological vector spaces, a product is Fredholm only if both factors are.
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

section Factors

open scoped LinearMap.FiniteRangeSetoid

variable [CompleteSpace K] [ContinuousSMul K E₁] [ContinuousSMul K E₂]
variable [IsTopologicalAddGroup F₁] [ContinuousSMul K F₁]
variable [IsTopologicalAddGroup F₂] [ContinuousSMul K F₂]
variable [T2Space E₁] [T2Space E₂] [T2Space F₁] [T2Space F₂]

/-- If a Cartesian product of operators is Fredholm, so is its first factor: compressing a
quasi-inverse of the product to the first factors gives a quasi-inverse of `T`. -/
lemma IsFredholm.of_prodMap_left (h : IsFredholm (T.prodMap S)) : IsFredholm T := by
  obtain ⟨Q, hQ⟩ := h.exists_isQuasiInverse
  let P : E₁ × E₂ →ₗ[K] F₁ × F₂ := (T.prodMap S : E₁ × E₂ →L[K] F₁ × F₂)
  refine .of_isQuasiInverse (v := (fst K E₁ E₂).comp (Q.comp (inl K F₁ F₂))) ⟨?_, ?_⟩
  · change _ ≈ _
    calc ((fst K E₁ E₂).comp (Q.comp (inl K F₁ F₂)) : F₁ →ₗ[K] E₁) ∘ₗ (T : E₁ →ₗ[K] F₁)
        _ = LinearMap.fst K E₁ E₂ ∘ₗ ((Q : F₁ × F₂ →ₗ[K] E₁ × E₂) ∘ₗ P) ∘ₗ
            LinearMap.inl K E₁ E₂ := by
          ext x; simp [P]
        _ ≈ LinearMap.fst K E₁ E₂ ∘ₗ LinearMap.id ∘ₗ LinearMap.inl K E₁ E₂ := by
          grw [hQ.1.equiv]
        _ = LinearMap.id := by ext x; simp
  · change _ ≈ _
    calc (T : E₁ →ₗ[K] F₁) ∘ₗ ((fst K E₁ E₂).comp (Q.comp (inl K F₁ F₂)) : F₁ →ₗ[K] E₁)
        _ = LinearMap.fst K F₁ F₂ ∘ₗ (P ∘ₗ (Q : F₁ × F₂ →ₗ[K] E₁ × E₂)) ∘ₗ
            LinearMap.inl K F₁ F₂ := by
          ext x; simp [P]
        _ ≈ LinearMap.fst K F₁ F₂ ∘ₗ LinearMap.id ∘ₗ LinearMap.inl K F₁ F₂ := by
          grw [hQ.2.equiv]
        _ = LinearMap.id := by ext x; simp

/-- If a Cartesian product of operators is Fredholm, so is its second factor. -/
lemma IsFredholm.of_prodMap_right (h : IsFredholm (T.prodMap S)) : IsFredholm S := by
  refine IsFredholm.of_prodMap_left (S := T) ?_
  have hswap : S.prodMap T = ((ContinuousLinearEquiv.prodComm K F₁ F₂ : F₁ × F₂ →L[K] F₂ × F₁).comp
      (T.prodMap S)).comp (ContinuousLinearEquiv.prodComm K E₂ E₁ : E₂ × E₁ →L[K] E₁ × E₂) := by
    ext x <;> simp
  rw [hswap]
  exact (h.equiv_comp _).comp_equiv _

/-- A Cartesian product of operators is Fredholm if and only if both factors are. -/
lemma isFredholm_prodMap_iff : IsFredholm (T.prodMap S) ↔ IsFredholm T ∧ IsFredholm S :=
  ⟨fun h ↦ ⟨h.of_prodMap_left, h.of_prodMap_right⟩, fun h ↦ h.1.prodMap h.2⟩

end Factors

end ContinuousLinearMap
