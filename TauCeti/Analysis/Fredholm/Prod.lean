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
* `ContinuousLinearMap.isFredholm_prodMap_iff`: conversely, a product is Fredholm only if both
  factors are.
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
  · rw [coe_prodMap T S, LinearMap.range_prodMap]
    exact hT.isClosed_range.prod hS.isClosed_range
  · rw [coe_prodMap T S, LinearMap.ker_prodMap]
    exact (Submodule.prodEquiv _ _).symm.finiteDimensional
  · rw [coe_prodMap T S, LinearMap.range_prodMap]
    exact (Submodule.quotientProdEquiv _ _).symm.finiteDimensional
  · rw [coe_prodMap T S, LinearMap.ker_prodMap]
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

/-- If a Cartesian product of operators is Fredholm, so is its first factor: each of the five
Fredholm conditions on `T.prodMap S` restricts to the first factor. -/
lemma IsFredholm.of_prodMap_left (h : IsFredholm (T.prodMap S)) : IsFredholm T := by
  have hker := h.finite_ker
  have hcoker := h.finite_coker
  have hrange := h.isClosed_range
  rw [coe_prodMap, LinearMap.ker_prodMap] at hker
  rw [coe_prodMap, LinearMap.range_prodMap] at hcoker hrange
  have := (Submodule.prodEquiv T.ker S.ker).finiteDimensional
  have := (Submodule.quotientProdEquiv T.range S.range).finiteDimensional
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `LinearMap.isStrictMap_prodMap_iff` is stated for the underlying linear maps.
    exact (LinearMap.isStrictMap_prodMap_iff (fₗ := (T : E₁ →ₗ[K] F₁))
      (gₗ := (S : E₂ →ₗ[K] F₂))).mp h.isStrictMap |>.1
  · -- The range of `T` is the slice of the closed set `range T ×ˢ range S` through `0`.
    simpa using hrange.preimage (continuous_id.prodMk continuous_const : Continuous
      fun y : F₁ ↦ (y, (0 : F₂)))
  · exact Module.Finite.of_surjective (LinearMap.fst K T.ker S.ker) LinearMap.fst_surjective
  · exact Module.Finite.of_surjective (LinearMap.fst K (F₁ ⧸ T.range) (F₂ ⧸ S.range))
      LinearMap.fst_surjective
  · obtain ⟨P, hP⟩ := h.closedComplemented_ker
    have hmem (x : E₁) : (P (x, 0) : E₁ × E₂).1 ∈ T.ker :=
      congr($(LinearMap.mem_ker.mp (P (x, 0)).2).1)
    refine ⟨((fst K E₁ E₂).comp ((Submodule.subtypeL _).comp (P.comp (inl K E₁ E₂)))).codRestrict
      _ hmem, fun x ↦ Subtype.ext ?_⟩
    have hx : ((x : E₁), (0 : E₂)) ∈ (T.prodMap S : E₁ × E₂ →ₗ[K] F₁ × F₂).ker := by
      simp
    -- The compressed projection sends `x` to the first component of `P (x, 0) = (x, 0)`.
    exact congr(($(hP ⟨_, hx⟩) : E₁ × E₂).1)

/-- If a Cartesian product of operators is Fredholm, so is its second factor. -/
lemma IsFredholm.of_prodMap_right (h : IsFredholm (T.prodMap S)) : IsFredholm S := by
  refine IsFredholm.of_prodMap_left (S := T) ?_
  have hswap : S.prodMap T = ((ContinuousLinearEquiv.prodComm K F₁ F₂ : F₁ × F₂ →L[K] F₂ × F₁).comp
      (T.prodMap S)).comp (ContinuousLinearEquiv.prodComm K E₂ E₁ : E₂ × E₁ →L[K] E₁ × E₂) := by
    ext x <;> simp
  rw [hswap]
  exact (h.equiv_comp _).comp_equiv _

/-- A Cartesian product of operators is Fredholm if and only if both factors are. -/
@[simp]
lemma isFredholm_prodMap_iff : IsFredholm (T.prodMap S) ↔ IsFredholm T ∧ IsFredholm S :=
  ⟨fun h ↦ ⟨h.of_prodMap_left, h.of_prodMap_right⟩, fun h ↦ h.1.prodMap h.2⟩

end ContinuousLinearMap
