/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.SchurComplement

/-!
# Fredholm block operators and their Schur complements

Let `M = ((A.coprod B).prod (C.coprod D)) : E₁ × E₂ → F₁ × F₂` be a `2 × 2` block operator whose
upper left block `A : E₁ ≃L[K] F₁` is invertible, with Schur complement `S = D - C A⁻¹ B`.
Up to continuous linear equivalences of domain and codomain, `M` is the block-diagonal operator
`A ⊕ S` (`ContinuousLinearEquiv.exists_coprod_prod_coprod_eq_comp_prodMap_comp`). Hence `M` is
Fredholm exactly when `S` is (`ContinuousLinearEquiv.isFredholm_coprod_prod_coprod_iff`), and
then the two indices agree (`ContinuousLinearEquiv.index_coprod_prod_coprod`).

This is how the Fredholm theory of an operator with an invertible *fast* block is reduced to that
of its *slow* Schur complement.
-/

public section

open ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {K E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField K]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module K E₁] [IsTopologicalAddGroup E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module K E₂] [IsTopologicalAddGroup E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module K F₁] [IsTopologicalAddGroup F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module K F₂] [IsTopologicalAddGroup F₂]

variable (A : E₁ ≃L[K] F₁) (B : E₂ →L[K] F₁) (C : E₁ →L[K] F₂) (D : E₂ →L[K] F₂)

/-- A block operator with invertible upper left block `A` is Fredholm exactly when its Schur
complement `D - C A⁻¹ B` is. -/
theorem isFredholm_coprod_prod_coprod_iff :
    (((A : E₁ →L[K] F₁).coprod B).prod (C.coprod D)).IsFredholm ↔
      (A.schurComplement B C D).IsFredholm := by
  obtain ⟨L, U, h⟩ := exists_coprod_prod_coprod_eq_comp_prodMap_comp A B C D
  have hL : (L.symm : F₁ × F₂ →L[K] F₁ × F₂) ∘L ((A : E₁ →L[K] F₁).coprod B).prod (C.coprod D) =
      ((A : E₁ →L[K] F₁).prodMap (A.schurComplement B C D)) ∘L
        (U : E₁ × E₂ →L[K] E₁ × E₂) := by
    rw [h]
    ext x <;> simp
  rw [isFredholm_iff_of_comp_eq U L.symm hL, isFredholm_prodMap_iff, and_iff_right A.isFredholm]

/-- The index of a block operator with invertible upper left block `A` is the index of its Schur
complement `D - C A⁻¹ B`, when the latter is Fredholm. -/
theorem index_coprod_prod_coprod (hS : (A.schurComplement B C D).IsFredholm) :
    (((A : E₁ →L[K] F₁).coprod B).prod (C.coprod D)).index =
      (A.schurComplement B C D).index := by
  obtain ⟨L, U, h⟩ := exists_coprod_prod_coprod_eq_comp_prodMap_comp A B C D
  have := A.isFredholm.finite_ker
  have := A.isFredholm.finite_coker
  have := hS.finite_ker
  have := hS.finite_coker
  rw [h, index_equiv_comp, index_comp_equiv, index_prodMap, A.index_eq_zero, zero_add]

end ContinuousLinearEquiv
