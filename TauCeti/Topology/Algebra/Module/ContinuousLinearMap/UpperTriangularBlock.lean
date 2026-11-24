/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
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

Over a semiring with `[IsTopologicalAddGroup F₁]` and `[AddCommGroup E₂]`,
`ContinuousLinearMap.upperTriangularBlockShear` defines the shear equivalence
`(y, x) ↦ (y + B x, x)` on `F₁ × E₂`, giving the factorization
`ContinuousLinearMap.upperTriangularBlock_eq_prodMap_comp_shear_comp_prodMap`.

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
  (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)

/-- The **upper-triangular block operator** `[[A, B], [0, D]] : E₁ × E₂ →L[R] F₁ × F₂` sending
`(x, y)` to `(A x + B y, D y)`. -/
def upperTriangularBlock : E₁ × E₂ →L[R] F₁ × F₂ :=
  (A ∘L fst R E₁ E₂ + B ∘L snd R E₁ E₂).prod (D ∘L snd R E₁ E₂)

theorem upperTriangularBlock_def :
    upperTriangularBlock A B D =
      (A ∘L fst R E₁ E₂ + B ∘L snd R E₁ E₂).prod (D ∘L snd R E₁ E₂) := (rfl)

@[simp] theorem upperTriangularBlock_apply (x : E₁ × E₂) :
    upperTriangularBlock A B D x = (A x.1 + B x.2, D x.2) := (rfl)

@[simp] theorem upperTriangularBlock_zero_mid :
    upperTriangularBlock A 0 D = A.prodMap D := by
  apply ContinuousLinearMap.ext; rintro ⟨x₁, x₂⟩; ext <;> simp

/-- Composition of upper-triangular block operators multiplies blocks by `[[A₁, B₁], [0, D₁]] ∘
[[A₂, B₂], [0, D₂]] = [[A₁ ∘ A₂, A₁ ∘ B₂ + B₁ ∘ D₂], [0, D₁ ∘ D₂]]`. -/
theorem upperTriangularBlock_comp (A₁ : F₁ →L[R] G₁) (B₁ : F₂ →L[R] G₁) (D₁ : F₂ →L[R] G₂)
    (A₂ : E₁ →L[R] F₁) (B₂ : E₂ →L[R] F₁) (D₂ : E₂ →L[R] F₂) :
    upperTriangularBlock A₁ B₁ D₁ ∘L upperTriangularBlock A₂ B₂ D₂ =
      upperTriangularBlock (A₁ ∘L A₂) (A₁ ∘L B₂ + B₁ ∘L D₂) (D₁ ∘L D₂) := by
  apply ContinuousLinearMap.ext; rintro ⟨x₁, x₂⟩; ext <;> simp [add_assoc]

/-- Composing `upperTriangularBlock A B D` on the right with `inl` factors `A` through `inl`. -/
@[simp] theorem upperTriangularBlock_comp_inl :
    upperTriangularBlock A B D ∘L inl R E₁ E₂ = inl R F₁ F₂ ∘L A := by ext x <;> simp

/-- Composing `upperTriangularBlock A B D` on the right with `inr` extracts the second column
`B.prod D`. -/
@[simp] theorem upperTriangularBlock_comp_inr :
    upperTriangularBlock A B D ∘L inr R E₁ E₂ = B.prod D := by ext x <;> simp

/-- Composing `fst` on the left of `upperTriangularBlock A B D` extracts the top row
`A.coprod B`. -/
@[simp] theorem fst_comp_upperTriangularBlock :
    fst R F₁ F₂ ∘L upperTriangularBlock A B D = A.coprod B := by ext x <;> simp

/-- Composing `snd` on the left of `upperTriangularBlock A B D` factors `D` through `snd`. -/
@[simp] theorem snd_comp_upperTriangularBlock :
    snd R F₁ F₂ ∘L upperTriangularBlock A B D = D ∘L snd R E₁ E₂ := by ext x <;> simp

/-- Composing `fst` on the left and `inr` on the right of `upperTriangularBlock A B D` extracts
the off-diagonal block `B`. -/
theorem fst_comp_upperTriangularBlock_comp_inr :
    fst R F₁ F₂ ∘L upperTriangularBlock A B D ∘L inr R E₁ E₂ = B := by ext x; simp

end Semiring

section Recognition

variable {R E₁ E₂ F₁ F₂ : Type*} [Semiring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommMonoid F₁] [Module R F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]

/-- Recognition lemma for upper-triangular block operators: any continuous linear map
`M : E₁ × E₂ →L[R] F₁ × F₂` satisfying the commuting squares `M ∘L inl = inl ∘L A` and
`snd ∘L M = D ∘L snd` equals `upperTriangularBlock A (fst ∘L M ∘L inr) D`. -/
theorem eq_upperTriangularBlock_of_comm (M : E₁ × E₂ →L[R] F₁ × F₂)
    {A : E₁ →L[R] F₁} {D : E₂ →L[R] F₂}
    (h₁ : M ∘L inl R E₁ E₂ = inl R F₁ F₂ ∘L A)
    (h₂ : snd R F₁ F₂ ∘L M = D ∘L snd R E₁ E₂) :
    M = upperTriangularBlock A (fst R F₁ F₂ ∘L M ∘L inr R E₁ E₂) D := by
  apply ContinuousLinearMap.ext; rintro ⟨x₁, x₂⟩
  have hsplit : (x₁, x₂) = inl R E₁ E₂ x₁ + inr R E₁ E₂ x₂ := by ext <;> simp
  have h1 : (M (inl R E₁ E₂ x₁)).1 = A x₁ := by
    simpa using congrArg Prod.fst (DFunLike.congr_fun h₁ x₁)
  have h2 : (M (x₁, x₂)).2 = D x₂ := by
    simpa using DFunLike.congr_fun h₂ (x₁, x₂)
  ext
  · calc (M (x₁, x₂)).1
      _ = (M (inl R E₁ E₂ x₁ + inr R E₁ E₂ x₂)).1 := by rw [← hsplit]
      _ = (M (inl R E₁ E₂ x₁)).1 + (M (inr R E₁ E₂ x₂)).1 := by rw [map_add, Prod.fst_add]
      _ = A x₁ + (fst R F₁ F₂ ∘L M ∘L inr R E₁ E₂) x₂ := by
          simp only [h1, comp_apply, coe_fst']
      _ = (upperTriangularBlock A (fst R F₁ F₂ ∘L M ∘L inr R E₁ E₂) D (x₁, x₂)).1 := by
          simp only [upperTriangularBlock_apply]
  · simpa only [upperTriangularBlock_apply] using h2

/-- Characterization of `M = upperTriangularBlock A B D` in terms of the commuting squares
`M ∘L inl = inl ∘L A`, `fst ∘L M ∘L inr = B`, and `snd ∘L M = D ∘L snd`. -/
theorem eq_upperTriangularBlock_iff (M : E₁ × E₂ →L[R] F₁ × F₂)
    {A : E₁ →L[R] F₁} {B : E₂ →L[R] F₁} {D : E₂ →L[R] F₂} :
    M = upperTriangularBlock A B D ↔
      M ∘L inl R E₁ E₂ = inl R F₁ F₂ ∘L A ∧
        fst R F₁ F₂ ∘L M ∘L inr R E₁ E₂ = B ∧
          snd R F₁ F₂ ∘L M = D ∘L snd R E₁ E₂ := by
  refine ⟨?_, fun ⟨h₁, hB, h₂⟩ ↦ hB ▸ M.eq_upperTriangularBlock_of_comm h₁ h₂⟩
  rintro rfl
  exact ⟨upperTriangularBlock_comp_inl A B D,
    fst_comp_upperTriangularBlock_comp_inr A B D,
    snd_comp_upperTriangularBlock A B D⟩

end Recognition

section Shear

variable {R E₁ E₂ F₁ F₂ : Type*} [Semiring R]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁] [IsTopologicalAddGroup F₁]

/-- The **upper-triangular shear equivalence** `(y, x) ↦ (y + B x, x)` on `F₁ × E₂` associated
to `B : E₂ →L[R] F₁`. -/
def upperTriangularBlockShear (B : E₂ →L[R] F₁) : (F₁ × E₂) ≃L[R] F₁ × E₂ :=
  ((ContinuousLinearEquiv.prodComm R F₁ E₂).trans
    ((ContinuousLinearEquiv.refl R E₂).skewProd (ContinuousLinearEquiv.refl R F₁) B)).trans
    (ContinuousLinearEquiv.prodComm R E₂ F₁)

@[simp] theorem upperTriangularBlockShear_apply (B : E₂ →L[R] F₁) (y : F₁ × E₂) :
    B.upperTriangularBlockShear y = (y.1 + B y.2, y.2) := (rfl)

@[simp] theorem upperTriangularBlockShear_symm_apply (B : E₂ →L[R] F₁) (y : F₁ × E₂) :
    B.upperTriangularBlockShear.symm y = (y.1 - B y.2, y.2) := (rfl)

/-- **Shear factorization** of an upper-triangular block operator:
`upperTriangularBlock A B D = (id.prodMap D) ∘L B.upperTriangularBlockShear ∘L (A.prodMap id)`. -/
theorem upperTriangularBlock_eq_prodMap_comp_shear_comp_prodMap
    [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
    [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂) :
    upperTriangularBlock A B D =
      ((ContinuousLinearMap.id R F₁).prodMap D) ∘L
        (B.upperTriangularBlockShear : F₁ × E₂ →L[R] F₁ × E₂) ∘L
          (A.prodMap (ContinuousLinearMap.id R E₂)) := by
  apply ContinuousLinearMap.ext; rintro ⟨x₁, x₂⟩; ext <;> simp

end Shear

section Ring

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁] [IsTopologicalAddGroup E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]

section Parametrix

variable (P_A : F₁ →L[R] E₁) (B : E₂ →L[R] F₁) (P_D : F₂ →L[R] E₂)

/-- Candidate **upper-triangular block parametrix** `[[P_A, -P_A ∘ B ∘ P_D], [0, P_D]]` built from
one-sided inverses or parametrices `P_A` of `A` and `P_D` of `D`. -/
def upperTriangularBlockParametrix : F₁ × F₂ →L[R] E₁ × E₂ :=
  upperTriangularBlock P_A (-(P_A ∘L B ∘L P_D)) P_D

theorem upperTriangularBlockParametrix_def :
    upperTriangularBlockParametrix P_A B P_D =
      upperTriangularBlock P_A (-(P_A ∘L B ∘L P_D)) P_D := (rfl)

@[simp] theorem upperTriangularBlockParametrix_apply (y : F₁ × F₂) :
    upperTriangularBlockParametrix P_A B P_D y = (P_A y.1 - P_A (B (P_D y.2)), P_D y.2) := by
  simp [upperTriangularBlockParametrix, sub_eq_add_neg]

end Parametrix

/-- Left remainder of `upperTriangularBlockParametrix`:
`[[P_A, -P_A B P_D], [0, P_D]] ∘ [[A, B], [0, D]] - 1` is upper-triangular with blocks
`P_A ∘ A - 1`, `-(P_A ∘ B ∘ (P_D ∘ D - 1))`, and `P_D ∘ D - 1`. -/
theorem upperTriangularBlockParametrix_comp_sub_one
    [IsTopologicalAddGroup E₂] [ContinuousAdd F₁]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    (P_A : F₁ →L[R] E₁) (P_D : F₂ →L[R] E₂) :
    upperTriangularBlockParametrix P_A B P_D ∘L upperTriangularBlock A B D - 1 =
      upperTriangularBlock (P_A ∘L A - 1) (-(P_A ∘L B ∘L (P_D ∘L D - 1))) (P_D ∘L D - 1) := by
  apply ContinuousLinearMap.ext; rintro ⟨x₁, x₂⟩; ext
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
  apply ContinuousLinearMap.ext; rintro ⟨y₁, y₂⟩; ext
  · simp only [sub_apply, comp_apply, upperTriangularBlock_apply,
      upperTriangularBlockParametrix_apply, neg_apply, one_apply_eq_self, Prod.fst_sub, map_sub]
    abel
  · simp

end Ring

end ContinuousLinearMap
