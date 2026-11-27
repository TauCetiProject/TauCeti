/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Tactic.Abel

/-!
# Schur complements of block operators

A continuous linear map `M : E₁ × E₂ → F₁ × F₂` is a `2 × 2` block operator

`M (x₁, x₂) = (A x₁ + B x₂, C x₁ + D x₂)`,

written `((A.coprod B).prod (C.coprod D))`. When the block `A : E₁ ≃L[R] F₁` is invertible, the
equation `M x = y` can be solved for `x₁ = A⁻¹ (y₁ - B x₂)`, and what remains is an equation for
`x₂` alone, governed by the **Schur complement** `S = D - C A⁻¹ B : E₂ → F₂`
(`ContinuousLinearEquiv.schurComplement`):

`S x₂ = y₂ - C A⁻¹ y₁`

(`ContinuousLinearEquiv.coprod_prod_coprod_apply_eq_iff`). This is the reduction used when an
operator splits into a *fast* part, inverted directly, and a *slow* part, whose analysis is the
analysis of the Schur complement: Lyapunov–Schmidt reductions and the adiabatic limits of gauge
theory (for instance the reduction of the linearized Seiberg–Witten operator near a concentrating
vortex to an operator on the normal bundle of the limiting curve) all take this form.

Explicitly, `M` has the LDU factorization

`M = (1 0; C A⁻¹ 1) ∘ (A ⊕ S) ∘ (1 A⁻¹ B; 0 1)`

(`ContinuousLinearEquiv.coprod_prod_coprod_eq_comp`), in which the outer factors are continuous
linear equivalences. Consequently every invertibility property of `M` is the corresponding
property of `S`:

* `x` lies in the kernel of `M` exactly when `x₂` lies in the kernel of `S` and
  `x₁ = -A⁻¹ B x₂` (`ContinuousLinearEquiv.mem_ker_coprod_prod_coprod_iff`);
* `y` lies in the range of `M` exactly when `y₂ - C A⁻¹ y₁` lies in the range of `S`
  (`ContinuousLinearEquiv.mem_range_coprod_prod_coprod_iff`);
* `M` is injective, surjective, or invertible exactly when `S` is
  (`ContinuousLinearEquiv.injective_coprod_prod_coprod_iff`,
  `ContinuousLinearEquiv.surjective_coprod_prod_coprod_iff`,
  `ContinuousLinearEquiv.isInvertible_coprod_prod_coprod_iff`).

Two Schur complements differ by an explicit expression in the differences of their blocks
(`ContinuousLinearEquiv.schurComplement_sub_schurComplement`), with the difference of the inverses
`A⁻¹ - A'⁻¹ = A'⁻¹ (A' - A) A⁻¹` written out. This is what controls the Schur complement of a
family of block operators by the variation of its blocks.

The Fredholm property and the index are transferred in
`TauCeti.Analysis.Fredholm.SchurComplement`, and quantitative bounds in
`TauCeti.Analysis.Normed.Operator.SchurComplement`.

This is the operator form of the matrix identity `Matrix.fromBlocks_eq_of_invertible₁₁`.

## References

* F. Zhang (ed.), *The Schur Complement and Its Applications*, Numerical Methods and
  Algorithms 4, Springer, 2005, Chapter 1.
-/

public section

open ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂] [IsTopologicalAddGroup F₂]

variable (A : E₁ ≃L[R] F₁) (B : E₂ →L[R] F₁) (C : E₁ →L[R] F₂) (D : E₂ →L[R] F₂)

/-- The **Schur complement** `D - C A⁻¹ B : E₂ → F₂` of the invertible block `A` in the block
operator `(A B; C D) : E₁ × E₂ → F₁ × F₂`. -/
def schurComplement : E₂ →L[R] F₂ :=
  D - C ∘L (A.symm : F₁ →L[R] E₁) ∘L B

theorem schurComplement_def :
    A.schurComplement B C D = D - C ∘L (A.symm : F₁ →L[R] E₁) ∘L B :=
  (rfl)

@[simp]
theorem schurComplement_apply (x : E₂) :
    A.schurComplement B C D x = D x - C (A.symm (B x)) :=
  (rfl)

/-- The Schur complement written with the inverse `ContinuousLinearMap.inverse` of the block `A`
viewed as a continuous linear map. This is the form taken by the Schur complement of a family of
block operators whose upper left block is invertible at the points of interest. -/
theorem schurComplement_eq_sub_comp_inverse :
    A.schurComplement B C D = D - C ∘L (A : E₁ →L[R] F₁).inverse ∘L B := by
  rw [inverse_equiv, schurComplement_def]

variable [ContinuousAdd F₁]

/-- **Solving a block system.** With `A` invertible, `M (x₁, x₂) = (y₁, y₂)` determines
`x₁ = A⁻¹ (y₁ - B x₂)`, and `x₂` solves the equation `S x₂ = y₂ - C A⁻¹ y₁` of the Schur
complement `S = D - C A⁻¹ B`. -/
theorem coprod_prod_coprod_apply_eq_iff {x : E₁ × E₂} {y : F₁ × F₂} :
    ((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D) x = y ↔
      x.1 = A.symm (y.1 - B x.2) ∧
        (A.schurComplement B C D) x.2 = y.2 - C (A.symm y.1) := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  simp only [ContinuousLinearMap.prod_apply, coprod_apply, coe_coe, Prod.mk.injEq,
    schurComplement_apply]
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [A.symm.map_add, symm_apply_apply, C.map_add]
    abel
  · rintro ⟨rfl, h⟩
    refine ⟨by simp, ?_⟩
    rw [sub_eq_iff_eq_add.mp h.symm, A.symm.map_sub, C.map_sub]
    abel

/-- A point lies in the kernel of a block operator with invertible upper left block `A` exactly
when its second component `x₂` lies in the kernel of the Schur complement `D - C A⁻¹ B` and its
first component is `-A⁻¹ B x₂`. -/
theorem mem_ker_coprod_prod_coprod_iff {x : E₁ × E₂} :
    x ∈ (((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D)).ker ↔
      x.1 = -A.symm (B x.2) ∧ x.2 ∈ (A.schurComplement B C D).ker := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  exact (coprod_prod_coprod_apply_eq_iff A B C D (y := 0)).trans (by simp)

/-- A block operator with invertible upper left block `A` is injective exactly when its Schur
complement `D - C A⁻¹ B` is. -/
theorem injective_coprod_prod_coprod_iff :
    Function.Injective (((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D)) ↔
      Function.Injective (A.schurComplement B C D) := by
  simp only [injective_iff_map_eq_zero]
  constructor
  · intro h z hz
    have hx := h (-A.symm (B z), z) ((mem_ker_coprod_prod_coprod_iff A B C D).2 ⟨rfl, hz⟩)
    exact congrArg Prod.snd hx
  · intro h x hx
    obtain ⟨h₁, h₂⟩ := (mem_ker_coprod_prod_coprod_iff A B C D).1 hx
    have hx₂ : x.2 = 0 := h _ h₂
    exact Prod.ext (by simp [h₁, hx₂]) hx₂

/-- A point `y` lies in the range of a block operator with invertible upper left block `A`
exactly when `y₂ - C A⁻¹ y₁` lies in the range of its Schur complement `D - C A⁻¹ B`. -/
theorem mem_range_coprod_prod_coprod_iff {y : F₁ × F₂} :
    y ∈ (((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D)).range ↔
      y.2 - C (A.symm y.1) ∈ (A.schurComplement B C D).range := by
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.2, ((coprod_prod_coprod_apply_eq_iff A B C D).1 hx).2⟩
  · rintro ⟨x₂, hx₂⟩
    exact ⟨(A.symm (y.1 - B x₂), x₂), (coprod_prod_coprod_apply_eq_iff A B C D).2 ⟨rfl, hx₂⟩⟩

/-- A block operator with invertible upper left block `A` is surjective exactly when its Schur
complement `D - C A⁻¹ B` is. -/
theorem surjective_coprod_prod_coprod_iff :
    Function.Surjective (((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D)) ↔
      Function.Surjective (A.schurComplement B C D) := by
  constructor
  · intro h z
    obtain ⟨x₂, hx₂⟩ := (mem_range_coprod_prod_coprod_iff A B C D (y := (0, z))).1 (h _)
    exact ⟨x₂, by simpa using hx₂⟩
  · intro h y
    exact (mem_range_coprod_prod_coprod_iff A B C D).2 (h _)

section Factorization

variable [ContinuousAdd E₂]

section ContinuousAdd

variable [ContinuousAdd E₁]

/-- **LDU factorization** of a block operator whose upper left block `A` is invertible: it is
the composite of a lower unitriangular operator, the block-diagonal operator `A ⊕ S` with the
Schur complement `S = D - C A⁻¹ B`, and an upper unitriangular operator. -/
theorem coprod_prod_coprod_eq_comp :
    ((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D) =
      (((ContinuousLinearMap.id R F₁).coprod 0).prod
          ((C ∘L (A.symm : F₁ →L[R] E₁)).coprod (.id R F₂))) ∘L
        ((A : E₁ →L[R] F₁).prodMap (A.schurComplement B C D)) ∘L
          (((ContinuousLinearMap.id R E₁).coprod ((A.symm : F₁ →L[R] E₁) ∘L B)).prod
            ((0 : E₁ →L[R] E₂).coprod (.id R E₂))) := by
  ext x <;> simp

end ContinuousAdd

variable [IsTopologicalAddGroup E₁]

/-- A block operator with invertible upper left block `A` is the block-diagonal operator `A ⊕ S`,
with the Schur complement `S = D - C A⁻¹ B`, up to continuous linear equivalences of its domain
and codomain. The equivalences are the unitriangular factors of
`ContinuousLinearEquiv.coprod_prod_coprod_eq_comp`. -/
theorem exists_coprod_prod_coprod_eq_comp_prodMap_comp :
    ∃ (L : (F₁ × F₂) ≃L[R] F₁ × F₂) (U : (E₁ × E₂) ≃L[R] E₁ × E₂),
      ((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D) =
        (L : F₁ × F₂ →L[R] F₁ × F₂) ∘L
          ((A : E₁ →L[R] F₁).prodMap (A.schurComplement B C D)) ∘L
            (U : E₁ × E₂ →L[R] E₁ × E₂) := by
  let T : E₂ →L[R] E₁ := (A.symm : F₁ →L[R] E₁) ∘L B
  refine ⟨(ContinuousLinearEquiv.refl R F₁).skewProd (.refl R F₂) (C ∘L (A.symm : F₁ →L[R] E₁)),
    .ofContinuousLinearMap (((ContinuousLinearMap.id R E₁).coprod T).prod (snd R E₁ E₂))
      (((ContinuousLinearMap.id R E₁).coprod (-T)).prod (snd R E₁ E₂)) ?_ ?_, ?_⟩
  · ext x <;> simp
  · ext x <;> simp
  · rw [coprod_prod_coprod_eq_comp]
    ext x <;> simp [T, add_comm]

/-- A block operator with invertible upper left block `A` is invertible exactly when its Schur
complement `D - C A⁻¹ B` is. -/
theorem isInvertible_coprod_prod_coprod_iff :
    (((A : E₁ →L[R] F₁).coprod B).prod (C.coprod D)).IsInvertible ↔
      (A.schurComplement B C D).IsInvertible := by
  obtain ⟨L, U, h⟩ := exists_coprod_prod_coprod_eq_comp_prodMap_comp A B C D
  rw [h, isInvertible_equiv_comp, isInvertible_comp_equiv, isInvertible_prodMap_iff]
  simp

end Factorization

section Difference

variable [IsTopologicalAddGroup F₁]

omit [ContinuousAdd F₁] in
/-- **The difference of two Schur complements.** For block operators `(A B; C D)` and
`(A' B'; C' D')` with invertible upper left blocks,

`(D - C A⁻¹ B) - (D' - C' A'⁻¹ B') =
  (D - D') - (C - C') A⁻¹ B + C' A'⁻¹ (A - A') A⁻¹ B - C' A'⁻¹ (B - B')`.

Each term on the right contains one difference of blocks, so the Schur complement varies with the
blocks as long as the inverse `A⁻¹` stays bounded. -/
theorem schurComplement_sub_schurComplement (A' : E₁ ≃L[R] F₁) (B' : E₂ →L[R] F₁)
    (C' : E₁ →L[R] F₂) (D' : E₂ →L[R] F₂) :
    A.schurComplement B C D - A'.schurComplement B' C' D' =
      D - D' - (C - C') ∘L (A.symm : F₁ →L[R] E₁) ∘L B +
        C' ∘L (A'.symm : F₁ →L[R] E₁) ∘L ((A : E₁ →L[R] F₁) - (A' : E₁ →L[R] F₁)) ∘L
          (A.symm : F₁ →L[R] E₁) ∘L B -
        C' ∘L (A'.symm : F₁ →L[R] E₁) ∘L (B - B') := by
  ext x
  simp only [sub_apply, add_apply, comp_apply, schurComplement_apply, coe_coe, map_sub,
    apply_symm_apply, symm_apply_apply]
  rw [C'.map_sub, C'.map_sub]
  abel

end Difference

end ContinuousLinearEquiv
