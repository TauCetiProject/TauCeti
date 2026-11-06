/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import TauCeti.LinearAlgebra.Matrix.IdealEntries
public import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Lifting symplectic matrices

A symplectic matrix lifts across a quotient by a square-zero ideal. Starting with arbitrary
lifts of its entries, the failure to preserve the standard alternating form is an alternating
matrix with entries in the ideal. Its strict upper triangle gives an integral solution of the
linearized symplectic equation; this avoids division by two and therefore works in characteristic
two. The quadratic correction terms vanish because the ideal is square-zero.

## Main declaration

* `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot`: entrywise reduction modulo a
  square-zero ideal is surjective on symplectic groups.

## References

* The Stacks Project, Tag 00TH, for the infinitesimal lifting criterion for formal smoothness.
* SGA 3, Exposé XXII, for the smooth split symplectic group scheme over `ℤ`.

This is the infinitesimal lifting input for the smoothness of the symplectic group scheme, a
prerequisite for the `Sp_{2n}` reductivity example in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

universe u

noncomputable section

variable {l : Type*} [DecidableEq l] [Fintype l]
variable {R : Type u} [CommRing R]

/-- The strict upper-triangular part of a matrix. -/
private def upperPart {n : Type*} [LinearOrder n] (A : Matrix n n R) : Matrix n n R :=
  fun i j => if i < j then A i j else 0

private theorem upperPart_sub_transpose_eq {n : Type*} [LinearOrder n]
    (A : Matrix n n R) (hdiag : forall i, A i i = 0) (htranspose : A.transpose = -A) :
    upperPart A - (upperPart A).transpose = A := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [upperPart, hij, hij.not_gt]
  · simp [upperPart, hdiag]
  · have hskew : -(A j i) = A i j := by
      have := congrFun (congrFun htranspose j) i
      simpa using this.symm
    simp [upperPart, hji, hji.not_gt, hskew]

/-- The defect `M * J * Mᵀ - J` of a matrix is antisymmetric. -/
private theorem transpose_mul_J_mul_transpose_sub_J (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    (M * Matrix.J l R * M.transpose - Matrix.J l R).transpose =
      -(M * Matrix.J l R * M.transpose - Matrix.J l R) := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.J_transpose]
  noncomm_ring

/-- The defect `M * J * Mᵀ - J` of a matrix has zero diagonal. -/
private theorem mul_J_mul_transpose_sub_J_apply_self (M : Matrix (l ⊕ l) (l ⊕ l) R)
    (i : l ⊕ l) : (M * Matrix.J l R * M.transpose - Matrix.J l R) i i = 0 := by
  rw [Matrix.sub_apply, Matrix.mul_J_mul_transpose_apply_self]
  simpa using Matrix.mul_J_mul_transpose_apply_self (1 : Matrix (l ⊕ l) (l ⊕ l) R) i

/-- An alternating matrix with entries in an ideal `I` is minus the linearized symplectic
defect `X * J + J * Xᵀ` of a matrix `X` with entries in `I`. The matrix `X` is built from the
strict upper triangle, which avoids division by two. -/
private theorem exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero (I : Ideal R)
    (E : Matrix (l ⊕ l) (l ⊕ l) R) (hE_mem : ∀ i j, E i j ∈ I) (hE_transpose : E.transpose = -E)
    (hE_diag : ∀ i, E i i = 0) :
    ∃ X : Matrix (l ⊕ l) (l ⊕ l) R, (∀ i j, X i j ∈ I) ∧
      E + X * Matrix.J l R + Matrix.J l R * X.transpose = 0 := by
  classical
  let _ : LinearOrder (l ⊕ l) := (Fintype.equivFin (l ⊕ l)).linearOrder
  let Y : Matrix (l ⊕ l) (l ⊕ l) R := upperPart (-E)
  have hY_mem : ∀ i j, Y i j ∈ I := by
    intro i j
    by_cases hij : i < j
    · simp only [Y, upperPart, hij, ite_true, Matrix.neg_apply]
      exact I.neg_mem (hE_mem i j)
    · simp only [Y, upperPart, hij, ite_false]
      exact I.zero_mem
  have hY_sub : Y - Y.transpose = -E := by
    apply upperPart_sub_transpose_eq
    · intro i
      simp [hE_diag]
    · rw [Matrix.transpose_neg, hE_transpose]
  have hX_mul_J : -(Y * Matrix.J l R) * Matrix.J l R = Y := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.J_squared]
    simp
  have hJ_mul_Xt : Matrix.J l R * (-(Y * Matrix.J l R)).transpose = -Y.transpose := by
    rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.J_transpose, Matrix.neg_mul,
      neg_neg, ← Matrix.mul_assoc, Matrix.J_squared]
    simp
  refine ⟨-(Y * Matrix.J l R), fun i j => ?_, ?_⟩
  · simp only [Matrix.neg_apply]
    exact I.neg_mem (I.sum_mem fun k _ => I.mul_mem_right _ (hY_mem i k))
  · rw [hX_mul_J, hJ_mul_Xt]
    calc
      E + Y + -Y.transpose = E + (Y - Y.transpose) := by abel
      _ = E + -E := by rw [hY_sub]
      _ = 0 := add_neg_cancel E

/-- Correcting a matrix `M` with `M * J * Mᵀ = J + E` by `1 + X`, where `E` and `X` have entries in
a square-zero ideal and `E + X * J + J * Xᵀ = 0`, gives a symplectic matrix. -/
private theorem one_add_mul_mem_symplecticGroup {I : Ideal R} (hI : I ^ 2 = (⊥ : Ideal R))
    {M E X : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M * Matrix.J l R * M.transpose = Matrix.J l R + E)
    (hE_mem : ∀ i j, E i j ∈ I) (hX_mem : ∀ i j, X i j ∈ I)
    (hX : E + X * Matrix.J l R + Matrix.J l R * X.transpose = 0) :
    (1 + X) * M ∈ Matrix.symplecticGroup l R := by
  have hXt_mem : ∀ i j, X.transpose i j ∈ I := fun i j => hX_mem j i
  have hXJ_mem : ∀ i j, (X * Matrix.J l R) i j ∈ I := fun i j =>
    I.sum_mem fun k _ => I.mul_mem_right _ (hX_mem i k)
  have hX_mul_E : X * E = 0 := Matrix.mul_eq_zero_of_sq_eq_bot hI hX_mem hE_mem
  have hE_mul_Xt : E * X.transpose = 0 := Matrix.mul_eq_zero_of_sq_eq_bot hI hE_mem hXt_mem
  have hXJ_mul_Xt : X * Matrix.J l R * X.transpose = 0 :=
    Matrix.mul_eq_zero_of_sq_eq_bot hI hXJ_mem hXt_mem
  rw [SymplecticGroup.mem_iff]
  calc
    (1 + X) * M * Matrix.J l R * ((1 + X) * M).transpose =
        (1 + X) * (M * Matrix.J l R * M.transpose) * (1 + X.transpose) := by
          rw [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
    _ = (1 + X) * (Matrix.J l R + E) * (1 + X.transpose) := by rw [hM]
    _ = Matrix.J l R + (E + X * Matrix.J l R + Matrix.J l R * X.transpose) +
          X * E + E * X.transpose + X * Matrix.J l R * X.transpose + X * E * X.transpose := by
        noncomm_ring
    _ = Matrix.J l R := by
        rw [hX, hX_mul_E, hE_mul_Xt, hXJ_mul_Xt]
        simp

/-- Every symplectic matrix modulo a square-zero ideal lifts to a symplectic matrix.

The result is valid over an arbitrary commutative ring, in every characteristic, and for the
zero-dimensional symplectic group. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) :
    Function.Surjective (GLSymplectic.map l (Ideal.Quotient.mk I)) := by
  classical
  intro g
  choose m hm using fun i j => Ideal.Quotient.mk_surjective
    (((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) i j)
  let M : Matrix (l ⊕ l) (l ⊕ l) R := m
  let qMat : Matrix (l ⊕ l) (l ⊕ l) R →+*
      Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I) :=
    RingHom.mapMatrix (Ideal.Quotient.mk I)
  have hM_map : qMat M =
      ((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) := by
    ext i j
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply] using hm i j
  have hJ_map : qMat (Matrix.J l R) = Matrix.J l (R ⧸ I) := by
    simpa only [qMat, RingHom.mapMatrix_apply] using
      Matrix.map_J (l := l) (Ideal.Quotient.mk I)
  have hM_transpose_map : qMat M.transpose = (qMat M).transpose := by
    simpa only [qMat, RingHom.mapMatrix_apply] using
      (Matrix.transpose_map (f := Ideal.Quotient.mk I) (M := M))
  have hE_map : qMat (M * Matrix.J l R * M.transpose - Matrix.J l R) = 0 := by
    rw [map_sub, map_mul, map_mul, hM_transpose_map, hM_map, hJ_map,
      (GLSymplectic.mem_iff).mp g.2]
    exact sub_self _
  have hE_mem : ∀ i j, (M * Matrix.J l R * M.transpose - Matrix.J l R) i j ∈ I := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] using
      congrFun (congrFun hE_map i) j
  obtain ⟨X, hX_mem, hX⟩ := exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero I _ hE_mem
    (transpose_mul_J_mul_transpose_sub_J M) (mul_J_mul_transpose_sub_J_apply_self M)
  have hN_mem := one_add_mul_mem_symplecticGroup hI
    (by abel : M * Matrix.J l R * M.transpose =
      Matrix.J l R + (M * Matrix.J l R * M.transpose - Matrix.J l R)) hE_mem hX_mem hX
  let s : Matrix.symplecticGroup l R := ⟨(1 + X) * M, hN_mem⟩
  have hX_map : qMat X = 0 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hX_mem a b
  refine ⟨⟨ofSymplecticGroup l R s, ofSymplecticGroup_mem l R s⟩, ?_⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hij := congrFun (congrFun (show qMat ((1 + X) * M) = _ by
    rw [map_mul, map_add, map_one, hX_map, add_zero, one_mul, hM_map]) i) j
  simpa only [coe_map, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, coe_ofSymplecticGroup, s, qMat] using hij

end

end TauCeti.GLSymplectic
