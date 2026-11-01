/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Scalar, diagonal and determinant facts for orthogonal matrices

A scalar matrix `c • 1` over a nonempty index type lies in the orthogonal group of the standard
symmetric form only when `c ^ 2 = 1`. For an empty index type every scalar qualifies.

Over a ring without zero divisors an orthogonal matrix has determinant `1` or `-1`, and both values
occur as soon as the index type is nonempty: the diagonal reflection negating one coordinate is an
orthogonal matrix of determinant `-1`. When `2 ≠ 0`, the products of the signs of these
reflections on two pairs of indices agree only if the four indices pair off.

Permutation matrices are orthogonal. For a trivial star operation the unitary elements of the
general linear group are the orthogonal matrices.

## Main definitions

* `TauCeti.orthogonalDiagonalReflection`: the diagonal orthogonal matrix negating one coordinate.

## Main declarations

* `TauCeti.sq_eq_one_of_smul_one_mem_orthogonalGroup`: a scalar orthogonal matrix over a nonempty
  index type has scalar a square root of one.
* `TauCeti.det_eq_one_or_neg_one_of_mem_orthogonalGroup`: the determinant of an orthogonal matrix
  is `1` or `-1`.
* `TauCeti.det_orthogonalDiagonalReflection`: the diagonal reflection has determinant `-1`.
* `TauCeti.pattern_of_forall_update_mul_eq`: if every diagonal reflection gives the same product
  of signs on two pairs of indices, the four indices pair off.
* `Matrix.permMatrix_mem_orthogonalGroup`: a permutation matrix is orthogonal.
* `Matrix.GeneralLinearGroup.mem_unitarySubgroup_iff_mem_orthogonalGroup`: for a trivial star
  operation, the unitary elements of `GL n R` are the orthogonal matrices.
-/

public section

namespace TauCeti

/-- A scalar matrix preserving the standard symmetric form has scalar a square root of one,
provided the index type is nonempty: the orthogonality relation reads `c ^ 2 • 1 = 1`. -/
theorem sq_eq_one_of_smul_one_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {R : Type*} [CommRing R] {c : R}
    (h : c • (1 : Matrix n n R) ∈ Matrix.orthogonalGroup n R) : c ^ 2 = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff] at h
  have hentry := congrFun (congrFun h (Classical.arbitrary n)) (Classical.arbitrary n)
  simpa [sq] using hentry

/-- Over a ring without zero divisors, the determinant of an orthogonal matrix is `1` or `-1`: the
orthogonality relation `Aᵀ * A = 1` gives `det A * det A = 1`. -/
theorem det_eq_one_or_neg_one_of_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [NoZeroDivisors R] {A : Matrix n n R}
    (hA : A ∈ Matrix.orthogonalGroup n R) : A.det = 1 ∨ A.det = -1 := by
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff n R).1 hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.1 h

section DiagonalReflection

variable {n : Type*} [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]

/-- The diagonal reflection negating the coordinate `i`: the diagonal matrix with entry `-1` at
`i` and `1` elsewhere, an orthogonal matrix of determinant `-1`
(`TauCeti.det_orthogonalDiagonalReflection`). -/
def orthogonalDiagonalReflection (i : n) : Matrix.orthogonalGroup n R :=
  ⟨Matrix.diagonal (Function.update 1 i (-1)), by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases hj : j = i <;> simp [hj]⟩

/-- The diagonal reflection negating the coordinate `i` has underlying matrix the diagonal matrix
with entry `-1` at `i` and `1` elsewhere. -/
@[simp]
theorem coe_orthogonalDiagonalReflection (i : n) :
    (orthogonalDiagonalReflection R i : Matrix n n R) =
      Matrix.diagonal (Function.update 1 i (-1)) :=
  (rfl)

/-- The diagonal reflection negating one coordinate has determinant `-1`. -/
theorem det_orthogonalDiagonalReflection (i : n) :
    (orthogonalDiagonalReflection R i : Matrix n n R).det = -1 := by
  rw [coe_orthogonalDiagonalReflection, Matrix.det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

end DiagonalReflection

/-- Let `2 ≠ 0` in `R`. If, for every `a`, the sign vector `Function.update 1 a (-1)` (the diagonal
of `TauCeti.orthogonalDiagonalReflection R a`) gives the same product of signs on the two pairs of
indices `(v 0, v 1)` and `(u 0, u 1)`, then the four indices pair off: the two pairs are both
constant, or equal, or swapped. -/
theorem pattern_of_forall_update_mul_eq {R ι : Type*} [CommRing R] [DecidableEq ι]
    (h2 : (2 : R) ≠ 0) {v u : Fin 2 → ι}
    (h : ∀ a, Function.update (1 : ι → R) a (-1) (v 0) *
        Function.update (1 : ι → R) a (-1) (v 1) =
      Function.update (1 : ι → R) a (-1) (u 0) * Function.update (1 : ι → R) a (-1) (u 1)) :
    (v 0 = v 1 ∧ u 0 = u 1) ∨ v = u ∨ (u 0 = v 1 ∧ u 1 = v 0) := by
  have hne : (-1 : R) ≠ 1 := fun h ↦ h2 (by linear_combination -h)
  -- A product of two signs is `-1` exactly when one of the two labels is `a`.
  have key : ∀ a x y : ι, Function.update (1 : ι → R) a (-1) x *
      Function.update (1 : ι → R) a (-1) y = -1 ↔ (x = a ↔ y ≠ a) := fun a x y ↦ by
    simp only [Function.update_apply, Pi.one_apply]
    split_ifs <;> simp_all [hne.symm]
  rw [funext_iff, Fin.forall_fin_two]
  by_cases hv : v 0 = v 1
  · -- both signs of `v` agree, so those of `u` agree too: `u` is constant.
    refine .inl ⟨hv, by_contra fun hu ↦ ?_⟩
    have h' := h (u 0)
    rw [hv, ((key _ _ _).mpr ⟨fun _ ↦ Ne.symm hu, fun _ ↦ rfl⟩)] at h'
    have := (key (u 0) (v 1) (v 1)).mp h'
    tauto
  · -- each of `v 0` and `v 1` occurs exactly once in `u`.
    have h₀ := (key _ _ _).mp ((h (v 0)).symm.trans ((key _ _ _).mpr ⟨fun _ ↦ Ne.symm hv,
      fun _ ↦ rfl⟩))
    have h₁ := (key _ _ _).mp ((h (v 1)).symm.trans ((key _ _ _).mpr ⟨fun h ↦ absurd h hv,
      fun h ↦ absurd rfl h⟩))
    by_cases hu : u 0 = v 0
    · have hu1 : u 1 = v 1 := by_contra fun h ↦ hv (hu.symm.trans (h₁.mpr h))
      exact .inr (.inl ⟨hu.symm, hu1.symm⟩)
    · have hu1 : u 1 = v 0 := by_contra fun h ↦ hu (h₀.mpr h)
      exact .inr (.inr ⟨h₁.mpr fun h ↦ hv (hu1.symm.trans h), hu1⟩)

end TauCeti

namespace Matrix

/-- A permutation matrix is orthogonal. This is `Matrix.permMatrix_mem_unitaryGroup` for the
trivial star operation `starRingOfComm`, which defines `Matrix.orthogonalGroup`. -/
theorem permMatrix_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n] (R : Type*)
    [CommRing R] (σ : Equiv.Perm n) : σ.permMatrix R ∈ orthogonalGroup n R :=
  letI := starRingOfComm (R := R)
  permMatrix_mem_unitaryGroup σ

end Matrix

namespace Matrix.GeneralLinearGroup

/-- For a trivial star operation, the unitary elements of `GL n R` are the orthogonal matrices. -/
theorem mem_unitarySubgroup_iff_mem_orthogonalGroup {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [StarRing R] [TrivialStar R] {M : GL n R} :
    M ∈ unitarySubgroup (GL n R) ↔ (M : Matrix n n R) ∈ orthogonalGroup n R := by
  rw [mem_orthogonalGroup_iff, ← conjTranspose_eq_transpose_of_trivial]
  simp [Units.unitary_eq, mem_unitaryGroup_iff, star_eq_conjTranspose]

end Matrix.GeneralLinearGroup
