/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import Mathlib.Data.Matrix.Basis

/-!
# Entrywise maps, reindexing, and corner embeddings for `CStarMatrix`

Entrywise functoriality (`map_zero`, `map_one`, `map_algebraMap`, `map_add`, `map_neg`, `map_sub`,
`map_smul`, `map_mul`, `map_conjTranspose`, `map_star`), bundled `⋆`-homomorphism lifts
(`mapₙₐ`, `mapₐ`), rectangular and square reindexing equivalences (`reindexₗ`, `reindexₐ`), and
diagonal corner embeddings (`singleNonUnitalStarAlgHom`).

## Main declarations

* `CStarMatrix.mapₐ`, `CStarMatrix.mapₙₐ_eq_map`, `CStarMatrix.reindexₗ_mul`,
  `CStarMatrix.reindexₗ_self_eq_reindexₐ`, `CStarMatrix.isStarProjection_reindexₐ_iff`,
  `CStarMatrix.singleNonUnitalStarAlgHom`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

open Matrix

namespace CStarMatrix

section MapAndReindex
variable {k l m n o p R A B C F : Type*}
@[simp] theorem map_zero [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (0 : CStarMatrix m n A).map f = 0 := by ext; simp [hf]
@[simp] protected theorem map_one [DecidableEq n] [Zero A] [One A] [Zero B] [One B]
    {f : A → B} (h₀ : f 0 = 0) (h₁ : f 1 = 1) : (1 : CStarMatrix n n A).map f = 1 :=
  ofMatrix.symm.injective (Matrix.map_one f h₀ h₁)
@[simp] theorem map_algebraMap [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (r : R) {f : A → B} (hf : f 0 = 0)
    (hf₂ : f (algebraMap R A r) = algebraMap R B r) :
    (algebraMap R (CStarMatrix n n A) r).map f = algebraMap R (CStarMatrix n n B) r :=
  ofMatrix.symm.injective (Matrix.map_algebraMap r f hf hf₂)
theorem map_add [AddZeroClass A] [AddZeroClass B] [FunLike F A B] [AddMonoidHomClass F A B]
    (φ : F) (M N : CStarMatrix m n A) : (M + N).map φ = M.map φ + N.map φ := by ext; simp
section
variable [AddGroup A] [SubtractionMonoid B] [FunLike F A B] [AddMonoidHomClass F A B] (φ : F)
  (M N : CStarMatrix m n A)
protected theorem map_neg : (-M).map φ = -(M.map φ) := by ext; simp
protected theorem map_sub : (M - N).map φ = M.map φ - N.map φ := by ext; simp
end
protected theorem map_smul [SMul R A] [SMul R B] [FunLike F A B] [MulActionHomClass F R A B]
    (φ : F) (r : R) (M : CStarMatrix m n A) : (r • M).map φ = r • M.map φ := by ext; simp
/-- Mapping entries by a non-unital ring homomorphism commutes with rectangular multiplication. -/
theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] (φ : F) (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) : (M * N).map φ = M.map φ * N.map φ := by ext; simp [mul_apply, map_sum]
section
variable [Star A] [Star B] [FunLike F A B] [StarHomClass F A B] (φ : F)
/-- Mapping entries by a `⋆`-homomorphism commutes with `conjTranspose`. -/
theorem map_conjTranspose (M : CStarMatrix m n A) :
    M.conjTranspose.map φ = (M.map φ).conjTranspose := by ext; simp [map_star]
/-- Mapping entries of a square matrix by a `⋆`-homomorphism commutes with `star`. -/
protected theorem map_star (M : CStarMatrix n n A) : (star M).map φ = star (M.map φ) :=
  map_conjTranspose φ M
end
section
variable [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
/-- Applying `mapₙₐ φ` acts entrywise as `CStarMatrix.map φ`. -/
theorem mapₙₐ_eq_map [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (φ : A →⋆ₙₐ[R] B)
    (M : CStarMatrix n n A) : mapₙₐ φ M = M.map φ := by simp [mapₙₐ_apply, mapₗ_apply]
@[simp] theorem mapₙₐ_id : mapₙₐ (.id R A) = .id R (CStarMatrix n n A) := by ext; rfl
theorem mapₙₐ_comp [NonUnitalNonAssocSemiring B] [Module R B] [Star B] [NonUnitalNonAssocSemiring C]
    [Module R C] [Star C] (ψ : B →⋆ₙₐ[R] C) (φ : A →⋆ₙₐ[R] B) :
    mapₙₐ (ψ.comp φ) = (mapₙₐ (n := n) ψ).comp (mapₙₐ φ) := by ext; rfl
end
section
variable [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]
/-- Entrywise lift of a unital `⋆`-algebra homomorphism to square matrix algebras. -/
def mapₐ (φ : A →⋆ₐ[R] B) : CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B :=
  { mapₙₐ φ.toNonUnitalStarAlgHom with
    map_one' := (mapₙₐ_eq_map _ 1).trans (CStarMatrix.map_one φ.map_zero φ.map_one)
    commutes' r := (mapₙₐ_eq_map _ _).trans (map_algebraMap r φ.map_zero (φ.commutes r)) }
@[simp low] theorem mapₐ_apply (φ : A →⋆ₐ[R] B) (M : CStarMatrix n n A) :
    mapₐ φ M = M.map φ := mapₙₐ_eq_map φ.toNonUnitalStarAlgHom M
@[simp] theorem mapₐ_id : mapₐ (.id R A) = .id R (CStarMatrix n n A) := by ext; rfl
theorem mapₐ_comp [Semiring C] [Algebra R C] [Star C] (ψ : B →⋆ₐ[R] C) (φ : A →⋆ₐ[R] B) :
    mapₐ (ψ.comp φ) = (mapₐ (n := n) ψ).comp (mapₐ φ) := by ext; rfl
/-- `mapₐ φ` is injective whenever `φ` is injective. -/
theorem mapₐ_injective {φ : A →⋆ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapₐ φ : CStarMatrix n n A → CStarMatrix n n B) := fun _ _ h =>
  map_injective hφ (by simpa only [mapₐ_apply] using h)
end
section
variable [Semiring R] [AddCommMonoid A] [Module R A]
@[simp] theorem conjTranspose_reindexₗ [Star A] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := by ext; rfl
/-- `reindexₗ` is multiplicative across matching intermediate equivalences. -/
@[simp] theorem reindexₗ_mul [Fintype m] [Fintype o] [Mul A] (eₗ : l ≃ k) (eₘ : m ≃ o) (eₙ : n ≃ p)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    reindexₗ R A eₗ eₘ M * reindexₗ R A eₘ eₙ N = reindexₗ R A eₗ eₙ (M * N) := by
  ext i j; simp only [mul_apply, reindexₗ_apply]; exact Fintype.sum_equiv eₘ.symm _ _ fun _ => rfl
@[simp] theorem reindexₗ_refl :
    reindexₗ R A (.refl m) (.refl n) = LinearEquiv.refl R (CStarMatrix m n A) := by ext; rfl
@[simp] theorem reindexₗ_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    reindexₗ R A eₘ.symm eₙ.symm = (reindexₗ R A eₘ eₙ).symm := by ext; rfl
theorem reindexₗ_trans (e₁ : m ≃ l) (e₂ : l ≃ k) (f₁ : n ≃ o) (f₂ : o ≃ p) :
    reindexₗ R A (e₁.trans e₂) (f₁.trans f₂) =
      (reindexₗ R A e₁ f₁).trans (reindexₗ R A e₂ f₂) := by ext; rfl
section
variable [Fintype l] [Fintype m] [Fintype n] [Mul A] [Star A]
/-- Reindexing rows and columns of a square `CStarMatrix` by `e` via `reindexₗ` is `reindexₐ`. -/
theorem reindexₗ_self_eq_reindexₐ (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₗ R A e e M = reindexₐ R A e M := by ext; simp
@[simp] theorem reindexₐ_refl :
    reindexₐ R A (Equiv.refl n) = StarAlgEquiv.refl R (CStarMatrix n n A) := by ext; rfl
theorem reindexₐ_trans (e₁ : l ≃ m) (e₂ : m ≃ n) :
    reindexₐ R A (e₁.trans e₂) = (reindexₐ R A e₁).trans (reindexₐ R A e₂) := by ext; rfl
/-- Reindexing a square `CStarMatrix` along `e : m ≃ n` preserves star projections. -/
@[simp] theorem isStarProjection_reindexₐ_iff (e : m ≃ n) {p : CStarMatrix m m A} :
    IsStarProjection (reindexₐ R A e p) ↔ IsStarProjection p :=
  ⟨fun h => (reindexₐ R A e).symm_apply_apply p ▸ h.map _, fun h => h.map _⟩
end
end
section
variable [Fintype n] [DecidableEq n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [StarAddMonoid A]
/-- Diagonal `(i, i)`-corner embedding `a ↦ single i i a` as a non-unital `⋆`-algebra morphism. -/
def singleNonUnitalStarAlgHom (R : Type*) [Semiring R] [Module R A] (i : n) :
    A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := ofMatrix (Matrix.single i i a)
  map_smul' _ _ := by simp [smul_of, Matrix.smul_single]
  map_zero' := by rw [Matrix.single_zero, of_zero]
  map_add' _ _ := by rw [of_add_of, Matrix.single_add]
  map_mul' _ _ := ofMatrix.symm.injective (by simp)
  map_star' _ := by rw [star_of, Matrix.conjTranspose_single]
@[simp low] theorem singleNonUnitalStarAlgHom_apply (i : n) (a : A) :
    singleNonUnitalStarAlgHom R i a = ofMatrix (Matrix.single i i a) := (rfl)
/-- The diagonal `(i, i)`-corner embedding `singleNonUnitalStarAlgHom` is injective. -/
theorem singleNonUnitalStarAlgHom_injective (i : n) :
    Function.Injective (singleNonUnitalStarAlgHom R i : A → CStarMatrix n n A) := fun _ _ h => by
  simpa using congr_fun (congr_fun (congrArg ofMatrix.symm h) i) i
end
end MapAndReindex

end CStarMatrix
