/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.DotProduct
public import Mathlib.FieldTheory.Finiteness

/-!
# Euclidean duals of linear codes

A linear code on a finite coordinate type is a submodule of the corresponding function space.
Its Euclidean dual consists of the words whose dot product with every codeword vanishes. This
file gives that construction its order-theoretic API and proves that dot-product duality is an
involution over a field. In particular, the dimensions of a code and its dual add to the number
of coordinates, and over a finite field their cardinalities multiply to the cardinality of the
whole word space.

The dot-product convention and the resulting Euclidean dual follow Huffman and Pless,
*Fundamentals of Error-Correcting Codes*, §§1.2–1.4.
-/

public section

namespace TauCeti

open Matrix Module
open LinearMap (BilinForm)

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The Euclidean dual of a linear code: its orthogonal complement for the standard dot product. -/
def euclideanDual (C : Submodule R (ι → R)) : Submodule R (ι → R) :=
  LinearMap.BilinForm.orthogonal (dotProductBilin R R) C

/-- The Euclidean dual is the orthogonal submodule for the standard dot-product bilinear form. -/
theorem euclideanDual_def (C : Submodule R (ι → R)) :
    euclideanDual C = LinearMap.BilinForm.orthogonal (dotProductBilin R R) C :=
  (rfl)

/-- Membership in the Euclidean dual means having zero dot product with every codeword. -/
@[simp]
theorem mem_euclideanDual {C : Submodule R (ι → R)} {y : ι → R} :
    y ∈ euclideanDual C ↔ ∀ x ∈ C, x ⬝ᵥ y = 0 :=
  Iff.rfl

/-- The dual of the zero code is the whole word space. -/
@[simp]
theorem euclideanDual_bot :
    euclideanDual (⊥ : Submodule R (ι → R)) = ⊤ :=
  by simp [euclideanDual]

/-- The dual of the whole word space is the zero code. -/
@[simp]
theorem euclideanDual_top :
    euclideanDual (⊤ : Submodule R (ι → R)) = ⊥ :=
  by simpa only [euclideanDual] using
    LinearMap.BilinForm.orthogonal_top_eq_bot
      (B := dotProductBilin R R) nondegenerate_dotProductBilin

/-- Euclidean duality reverses inclusion. -/
theorem euclideanDual_antitone : Antitone (euclideanDual (R := R) (ι := ι)) :=
  fun _ _ h ↦ LinearMap.BilinForm.orthogonal_le h

/-- Orthogonality of two codes is symmetric. -/
theorem le_euclideanDual_iff {C D : Submodule R (ι → R)} :
    C ≤ euclideanDual D ↔ D ≤ euclideanDual C := by
  constructor
  · intro h y hy
    rw [mem_euclideanDual]
    intro x hx
    rw [dotProduct_comm]
    exact mem_euclideanDual.mp (h hx) y hy
  · intro h y hy
    rw [mem_euclideanDual]
    intro x hx
    rw [dotProduct_comm]
    exact mem_euclideanDual.mp (h hx) y hy

/-- A code is self-orthogonal exactly when any two of its words have zero dot product. -/
theorem le_euclideanDual_self_iff {C : Submodule R (ι → R)} :
    C ≤ euclideanDual C ↔ ∀ x ∈ C, ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  constructor
  · intro h x hx y hy
    exact mem_euclideanDual.mp (h hy) x hx
  · intro h y hy
    rw [mem_euclideanDual]
    exact fun x hx ↦ h x hx y hy

/-- The Euclidean dual of a sum is the intersection of the Euclidean duals. -/
@[simp]
theorem euclideanDual_sup (C D : Submodule R (ι → R)) :
    euclideanDual (C ⊔ D) = euclideanDual C ⊓ euclideanDual D :=
  by
    unfold euclideanDual LinearMap.BilinForm.orthogonal
    exact Submodule.orthogonalBilin_sup (B := dotProductBilin R R) C D

section Field

variable {K : Type*} [Field K]

/-- Taking the Euclidean dual twice recovers the original code. -/
@[simp]
theorem euclideanDual_euclideanDual (C : Submodule K (ι → K)) :
    euclideanDual (euclideanDual C) = C := by
  simpa only [euclideanDual] using
    LinearMap.BilinForm.orthogonal_orthogonal
      (B := dotProductBilin K K) nondegenerate_dotProductBilin
        (isSymm_dotProductBilin (R := K) (ι := ι)).isRefl C

/-- Dual inclusion is equivalent to inclusion in the opposite direction. -/
theorem euclideanDual_le_euclideanDual_iff {C D : Submodule K (ι → K)} :
    euclideanDual C ≤ euclideanDual D ↔ D ≤ C := by
  constructor
  · intro h
    simpa only [euclideanDual_euclideanDual] using euclideanDual_antitone (R := K) h
  · exact fun h ↦ euclideanDual_antitone (R := K) h

/-- Two codes have the same Euclidean dual exactly when they are equal. -/
theorem euclideanDual_injective :
    Function.Injective (euclideanDual (R := K) (ι := ι)) := by
  intro C D h
  simpa only [euclideanDual_euclideanDual] using congrArg euclideanDual h

/-- The Euclidean dual of an intersection is the sum of the Euclidean duals. -/
@[simp]
theorem euclideanDual_inf (C D : Submodule K (ι → K)) :
    euclideanDual (C ⊓ D) = euclideanDual C ⊔ euclideanDual D := by
  apply euclideanDual_injective
  simp only [euclideanDual_euclideanDual, euclideanDual_sup]

/-- The dimensions of a code and its Euclidean dual add to the number of coordinates. -/
theorem finrank_add_finrank_euclideanDual (C : Submodule K (ι → K)) :
    finrank K C + finrank K (euclideanDual C) = Fintype.card ι := by
  have hdual := LinearMap.BilinForm.finrank_orthogonal
    (B := dotProductBilin K K)
      (nondegenerate_dotProductBilin (R := K) (ι := ι)) C
  have hdual' : finrank K (euclideanDual C) = finrank K (ι → K) - finrank K C := by
    unfold euclideanDual
    exact hdual
  rw [hdual', Module.finrank_fintype_fun_eq_card]
  have hle : finrank K C ≤ Fintype.card ι := by
    simpa only [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le C
  exact Nat.add_sub_of_le hle

/-- A self-dual code has twice its dimension equal to its length. -/
theorem two_mul_finrank_of_eq_euclideanDual {C : Submodule K (ι → K)}
    (hC : C = euclideanDual C) : 2 * finrank K C = Fintype.card ι := by
  have h := finrank_add_finrank_euclideanDual C
  rw [← hC] at h
  simpa only [two_mul] using h

/-- A self-orthogonal code has dimension at most half the length. -/
theorem two_mul_finrank_le_of_le_euclideanDual {C : Submodule K (ι → K)}
    (hC : C ≤ euclideanDual C) : 2 * finrank K C ≤ Fintype.card ι := by
  rw [two_mul, ← finrank_add_finrank_euclideanDual C]
  exact Nat.add_le_add_left (Submodule.finrank_mono hC) _

/-- A self-orthogonal code of half the ambient dimension is self-dual. -/
theorem eq_euclideanDual_of_le_of_two_mul_finrank_eq {C : Submodule K (ι → K)}
    (hC : C ≤ euclideanDual C) (hdim : 2 * finrank K C = Fintype.card ι) :
    C = euclideanDual C := by
  apply Submodule.eq_of_le_of_finrank_le hC
  rw [← Nat.add_le_add_iff_left (n := finrank K C), finrank_add_finrank_euclideanDual C]
  simpa only [two_mul] using hdim.symm.le

/-- A code is self-dual exactly when it is self-orthogonal and has half the ambient dimension. -/
theorem eq_euclideanDual_iff {C : Submodule K (ι → K)} :
    C = euclideanDual C ↔
      C ≤ euclideanDual C ∧ 2 * finrank K C = Fintype.card ι := by
  constructor
  · intro hC
    exact ⟨hC.le, two_mul_finrank_of_eq_euclideanDual hC⟩
  · rintro ⟨hC, hdim⟩
    exact eq_euclideanDual_of_le_of_two_mul_finrank_eq hC hdim

/-- Over a finite field, the cardinalities of a code and its Euclidean dual multiply to the
cardinality of the whole word space. -/
theorem natCard_mul_natCard_euclideanDual (C : Submodule K (ι → K)) :
    Nat.card C * Nat.card (euclideanDual C) = Nat.card K ^ Fintype.card ι := by
  calc
    Nat.card C * Nat.card (euclideanDual C) =
        Nat.card K ^ finrank K C * Nat.card K ^ finrank K (euclideanDual C) := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := C),
        Module.natCard_eq_pow_finrank (K := K) (V := euclideanDual C)]
    _ = Nat.card K ^ Fintype.card ι := by
      rw [← pow_add, finrank_add_finrank_euclideanDual]

end Field

end TauCeti
