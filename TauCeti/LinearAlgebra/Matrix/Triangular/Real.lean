/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.LinearAlgebra.Matrix.Realify

/-!
# Upper-triangular matrices with real diagonal

Real diagonal is stable under addition and multiplication of upper-triangular matrices.
The resulting real associative subalgebra retains arbitrary complex off-diagonal entries.

## Main definitions

* `TauCeti.upperTriangularRealDiagonal`: the set of upper-triangular matrices with real diagonal.
* `TauCeti.upperTriangularRealDiagonalSubalgebra`: the real associative subalgebra.
* `Matrix.isUpperTriangular_interleavedRealifyAlgHom`: preservation of upper triangularity for
  matrices in `TauCeti.upperTriangularRealDiagonalSubalgebra`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Chapter I, §5,
  Corollary 1.30, p.22, for the real triangular algebra motivating split solvability.
-/

public noncomputable section

namespace TauCeti

open Matrix

/-- The upper-triangular matrices with real diagonal. -/
def upperTriangularRealDiagonal (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [LinearOrder ι] :
    Set (Matrix ι ι 𝕜) :=
  {A | A.IsUpperTriangular ∧ ∀ i, RCLike.im (A i i) = 0}

/-- Membership is upper triangularity and a real diagonal. -/
@[simp]
theorem mem_upperTriangularRealDiagonal_iff {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [LinearOrder ι]
    {A : Matrix ι ι 𝕜} : A ∈ upperTriangularRealDiagonal 𝕜 ι ↔
      A.IsUpperTriangular ∧ ∀ i, RCLike.im (A i i) = 0 := Iff.rfl

/-- Upper-triangular matrices with real diagonal, as a real associative subalgebra. -/
def upperTriangularRealDiagonalSubalgebra (𝕜 : Type*) [RCLike 𝕜]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] : Subalgebra ℝ (Matrix ι ι 𝕜) where
  carrier := upperTriangularRealDiagonal 𝕜 ι
  zero_mem' := ⟨blockTriangular_zero, by simp⟩
  one_mem' := ⟨blockTriangular_one, by simp⟩
  add_mem' := by
    rintro A B ⟨hA, ha⟩ ⟨hB, hb⟩
    exact ⟨hA.add hB, fun i ↦ by simp [Matrix.add_apply, ha, hb]⟩
  mul_mem' := by
    rintro A B ⟨hA, ha⟩ ⟨hB, hb⟩
    refine ⟨hA.mul hB, fun i ↦ ?_⟩
    rw [mul_apply_diag_of_isUpperTriangular hA hB]
    simp [RCLike.mul_im, ha, hb]
  algebraMap_mem' := by
    intro r
    constructor
    · intro i j hji
      simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, show i ≠ j from ne_of_gt hji]
    · intro i
      simp [Matrix.algebraMap_eq_diagonal]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]

/-- Membership means upper triangularity and real diagonal. -/
@[simp]
theorem mem_upperTriangularRealDiagonalSubalgebra_iff [LinearOrder ι] {A : Matrix ι ι 𝕜} :
    A ∈ upperTriangularRealDiagonalSubalgebra 𝕜 ι ↔
      A.IsUpperTriangular ∧ ∀ i, RCLike.im (A i i) = 0 := Iff.rfl

end TauCeti

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]

/-- A real-diagonal upper-triangular matrix has upper-triangular interleaved realification. -/
theorem isUpperTriangular_interleavedRealifyAlgHom [LinearOrder ι] (X : Matrix ι ι 𝕜)
    (hX : X ∈ TauCeti.upperTriangularRealDiagonalSubalgebra 𝕜 ι) :
    (interleavedRealifyAlgHom X).IsUpperTriangular := by
  obtain ⟨hX, hr⟩ := TauCeti.mem_upperTriangularRealDiagonalSubalgebra_iff.mp hX
  intro a b hba
  obtain ⟨⟨i, s⟩, rfl⟩ := toLex.surjective a
  obtain ⟨⟨j, t⟩, rfl⟩ := toLex.surjective b
  rw [interleavedRealifyAlgHom_apply]
  rcases Prod.Lex.toLex_lt_toLex.mp hba with hji | ⟨hji, hts⟩
  · have hz : X i j = 0 := hX hji
    cases s <;> cases t <;> simp [hz]
  · dsimp only at hji hts
    subst j
    cases s <;> cases t <;> simp_all

end Matrix
