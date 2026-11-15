/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic.Abel

/-!
# Upper-triangular `2 × 2` block continuous linear maps and parametrices

For `A : E₁ →L[R] F₁`, `B : E₂ →L[R] F₁`, and `D : E₂ →L[R] F₂`,
`ContinuousLinearMap.upperTriangularBlock A B D` is the continuous linear operator
`E₁ × E₂ →L[R] F₁ × F₂` sending `(x, y)` to `(A x + B y, D y)`.

Over a ring, given candidate one-sided inverses or parametrices `P_A : F₁ →L[R] E₁` and
`P_D : F₂ →L[R] E₂` of the diagonal blocks, `ContinuousLinearMap.upperTriangularBlockParametrix`
constructs `[[P_A, -P_A ∘ B ∘ P_D], [0, P_D]]` and expresses both `P ∘ M - 1` and `M ∘ P - 1` in
upper-triangular block form (`ContinuousLinearMap.upperTriangularBlockParametrix_comp_sub_one`,
`ContinuousLinearMap.comp_upperTriangularBlockParametrix_sub_one`).

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace ContinuousLinearMap

section Semiring

variable {R E₁ E₂ F₁ F₂ G₁ G₂ : Type*} [Semiring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommMonoid F₁] [Module R F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]
  [TopologicalSpace G₁] [AddCommMonoid G₁] [Module R G₁] [ContinuousAdd G₁]
  [TopologicalSpace G₂] [AddCommMonoid G₂] [Module R G₂]

/-- The **upper-triangular block operator** `[[A, B], [0, D]] : E₁ × E₂ →L[R] F₁ × F₂` sending
`(x, y)` to `(A x + B y, D y)`. -/
def upperTriangularBlock (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    E₁ × E₂ →L[R] F₁ × F₂ :=
  (A ∘L fst R E₁ E₂ + B ∘L snd R E₁ E₂).prod (D ∘L snd R E₁ E₂)

theorem upperTriangularBlock_def (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    upperTriangularBlock A B D =
      (A ∘L fst R E₁ E₂ + B ∘L snd R E₁ E₂).prod (D ∘L snd R E₁ E₂) :=
  (rfl)

@[simp]
theorem upperTriangularBlock_apply (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    (x : E₁ × E₂) :
    upperTriangularBlock A B D x = (A x.1 + B x.2, D x.2) :=
  (rfl)

@[simp]
theorem upperTriangularBlock_zero_mid (A : E₁ →L[R] F₁) (D : E₂ →L[R] F₂) :
    upperTriangularBlock A 0 D = A.prodMap D := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext <;> simp

/-- Composition of upper-triangular block operators multiplies blocks by `[[A₁, B₁], [0, D₁]] ∘
[[A₂, B₂], [0, D₂]] = [[A₁ ∘ A₂, A₁ ∘ B₂ + B₁ ∘ D₂], [0, D₁ ∘ D₂]]`. -/
theorem upperTriangularBlock_comp (A₁ : F₁ →L[R] G₁) (B₁ : F₂ →L[R] G₁) (D₁ : F₂ →L[R] G₂)
    (A₂ : E₁ →L[R] F₁) (B₂ : E₂ →L[R] F₁) (D₂ : E₂ →L[R] F₂) :
    upperTriangularBlock A₁ B₁ D₁ ∘L upperTriangularBlock A₂ B₂ D₂ =
      upperTriangularBlock (A₁ ∘L A₂) (A₁ ∘L B₂ + B₁ ∘L D₂) (D₁ ∘L D₂) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext <;> simp [add_assoc]

/-- Composing `upperTriangularBlock A B D` on the right with `inl` factors `A` through `inl`. -/
@[simp]
theorem upperTriangularBlock_comp_inl (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    upperTriangularBlock A B D ∘L inl R E₁ E₂ = inl R F₁ F₂ ∘L A := by
  ext x <;> simp

/-- Composing `upperTriangularBlock A B D` on the right with `inr` extracts the second column
`B.prod D`. -/
@[simp]
theorem upperTriangularBlock_comp_inr (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    upperTriangularBlock A B D ∘L inr R E₁ E₂ = B.prod D := by
  ext x <;> simp

/-- Composing `fst` on the left of `upperTriangularBlock A B D` extracts the top row
`A.coprod B`. -/
@[simp]
theorem fst_comp_upperTriangularBlock (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    fst R F₁ F₂ ∘L upperTriangularBlock A B D = A.coprod B := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  simp

/-- Composing `snd` on the left of `upperTriangularBlock A B D` factors `D` through `snd`. -/
@[simp]
theorem snd_comp_upperTriangularBlock (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    snd R F₁ F₂ ∘L upperTriangularBlock A B D = D ∘L snd R E₁ E₂ := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

end Semiring

section Ring

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁] [IsTopologicalAddGroup E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]

/-- Candidate **upper-triangular block parametrix** `[[P_A, -P_A ∘ B ∘ P_D], [0, P_D]]` built from
one-sided inverses or parametrices `P_A` of `A` and `P_D` of `D`. -/
def upperTriangularBlockParametrix
    (P_A : F₁ →L[R] E₁) (B : E₂ →L[R] F₁) (P_D : F₂ →L[R] E₂) :
    F₁ × F₂ →L[R] E₁ × E₂ :=
  upperTriangularBlock P_A (-(P_A ∘L B ∘L P_D)) P_D

theorem upperTriangularBlockParametrix_def
    (P_A : F₁ →L[R] E₁) (B : E₂ →L[R] F₁) (P_D : F₂ →L[R] E₂) :
    upperTriangularBlockParametrix P_A B P_D =
      upperTriangularBlock P_A (-(P_A ∘L B ∘L P_D)) P_D :=
  (rfl)

@[simp]
theorem upperTriangularBlockParametrix_apply
    (P_A : F₁ →L[R] E₁) (B : E₂ →L[R] F₁) (P_D : F₂ →L[R] E₂) (y : F₁ × F₂) :
    upperTriangularBlockParametrix P_A B P_D y = (P_A y.1 - P_A (B (P_D y.2)), P_D y.2) := by
  simp [upperTriangularBlockParametrix, sub_eq_add_neg]

/-- Left remainder of `upperTriangularBlockParametrix`:
`[[P_A, -P_A B P_D], [0, P_D]] ∘ [[A, B], [0, D]] - 1` is upper-triangular with blocks
`P_A ∘ A - 1`, `-(P_A ∘ B ∘ (P_D ∘ D - 1))`, and `P_D ∘ D - 1`. -/
theorem upperTriangularBlockParametrix_comp_sub_one
    [IsTopologicalAddGroup E₂] [ContinuousAdd F₁]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    (P_A : F₁ →L[R] E₁) (P_D : F₂ →L[R] E₂) :
    upperTriangularBlockParametrix P_A B P_D ∘L upperTriangularBlock A B D - 1 =
      upperTriangularBlock (P_A ∘L A - 1) (-(P_A ∘L B ∘L (P_D ∘L D - 1))) (P_D ∘L D - 1) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext
  · simp only [sub_apply, comp_apply, upperTriangularBlock_apply,
      upperTriangularBlockParametrix_apply, neg_apply, one_apply_eq_self, Prod.fst_sub, map_add,
      map_sub]
    abel
  · simp

/-- Right remainder of `upperTriangularBlockParametrix`:
`[[A, B], [0, D]] ∘ [[P_A, -P_A B P_D], [0, P_D]] - 1` is upper-triangular with blocks
`A ∘ P_A - 1`, `-((A ∘ P_A - 1) ∘ B ∘ P_D)`, and `D ∘ P_D - 1`. -/
theorem comp_upperTriangularBlockParametrix_sub_one
    [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    (P_A : F₁ →L[R] E₁) (P_D : F₂ →L[R] E₂) :
    upperTriangularBlock A B D ∘L upperTriangularBlockParametrix P_A B P_D - 1 =
      upperTriangularBlock (A ∘L P_A - 1) (-((A ∘L P_A - 1) ∘L B ∘L P_D)) (D ∘L P_D - 1) := by
  apply ContinuousLinearMap.ext
  rintro ⟨y₁, y₂⟩
  ext
  · simp only [sub_apply, comp_apply, upperTriangularBlock_apply,
      upperTriangularBlockParametrix_apply, neg_apply, one_apply_eq_self, Prod.fst_sub, map_sub]
    abel
  · simp

end Ring

end ContinuousLinearMap

namespace TauCeti

/-- The upper-triangular block operator with identity diagonal blocks and zero off-diagonal block
is the identity on `E₁ × E₂`. -/
theorem upperTriangularBlock_id {R E₁ E₂ : Type*} [Semiring R]
    [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁] [ContinuousAdd E₁]
    [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂] :
    ContinuousLinearMap.upperTriangularBlock (.id R E₁) 0 (.id R E₂) = .id R (E₁ × E₂) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext <;> simp

end TauCeti
