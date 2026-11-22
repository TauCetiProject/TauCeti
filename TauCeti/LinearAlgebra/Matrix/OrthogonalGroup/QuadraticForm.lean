/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Quadratic and matrix orthogonal groups

When multiplication by two is injective in the base ring, a linear automorphism preserves the
standard quadratic form exactly when its matrix is orthogonal. The equivalence
`TauCeti.standardOrthogonalGroupEquiv` bundles this criterion, with inverse given by matrix-vector
multiplication. Adding determinant one
identifies the two special orthogonal groups. These criteria transfer quadratic-space results
to the matrix models of the classical groups.

A quadratic form `Q` is compared with the matrix groups only along a specified isometry `e` to the
standard form: transporting along `e` and then taking coordinate matrices identifies `O(Q)` and
`SO(Q)` with the matrix orthogonal and special orthogonal groups. Without such an isometry the
matrix groups are the wrong models: in a basis with Gram matrix `D`, the matrices of the
isometries of `Q` are those with `Aᵀ D A = D`, not `Aᵀ A = 1`.

The criteria apply to any finite index type, including the empty type, and to rings such as
`ℤ` where two is regular but not invertible.

## Main results

* `TauCeti.toMatrix_mem_orthogonalGroup_iff`: the coordinate criterion for the orthogonal group.
* `TauCeti.toMatrix_mem_specialOrthogonalGroup_iff`: the coordinate criterion for the special
  orthogonal group.
* `TauCeti.standardOrthogonalGroupEquiv` and `TauCeti.standardSpecialOrthogonalGroupEquiv`: the
  orthogonal and special orthogonal groups of the standard form are the matrix groups.
* `TauCeti.orthogonalGroupEquivMatrix` and `TauCeti.specialOrthogonalGroupEquivMatrix`: the
  comparisons of `O(Q)` and `SO(Q)` with the matrix groups along an isometry to the standard form,
  with `orthogonalGroupEquivMatrix_refl` and `orthogonalGroupEquivMatrix_trans` (and their special
  orthogonal versions) for the identity and composite isometries.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance] starRingOfComm

universe u v

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The quadratic form of the identity matrix sends a vector to its dot product with itself.

This is not a `simp` lemma: `TauCeti.PDE.toQuadraticForm'_one` already normalises the same
left-hand side to `‖ξ‖ ^ 2` on `EuclideanSpace ℝ n`, and the two cannot both be simp-normal. -/
theorem toQuadraticForm'_one_apply (x : n → R) :
    Matrix.toQuadraticForm' (1 : Matrix n n R) x = x ⬝ᵥ x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

/-- The polar form of the standard quadratic form is twice the dot product. -/
@[simp]
theorem polar_toQuadraticForm'_one (x y : n → R) :
    QuadraticMap.polar (Matrix.toQuadraticForm' (1 : Matrix n n R)) x y = 2 * (x ⬝ᵥ y) := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply', Matrix.one_mulVec, two_mul, dotProduct_comm y x]

/-- The coordinate matrix of a linear automorphism is orthogonal exactly when the
automorphism preserves the standard quadratic form. -/
@[simp]
theorem toMatrix_mem_orthogonalGroup_iff (R : Type u) [CommRing R]
    (n : Type v) [Fintype n] [DecidableEq n] (h2 : IsSMulRegular R (2 : R))
    (e : (n → R) ≃ₗ[R] (n → R)) :
    LinearMap.toMatrix' e.toLinearMap ∈ Matrix.orthogonalGroup n R ↔
      e ∈ QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R)) := by
  let B : LinearMap.BilinForm R (n → R) := Matrix.toLinearMap₂' R (1 : Matrix n n R)
  have hgram :
      BilinForm.IsIsometry B e.toLinearMap ↔
        LinearMap.toMatrix' e.toLinearMap ∈ Matrix.orthogonalGroup n R := by
    rw [BilinForm.isIsometry_iff_toMatrix (Pi.basisFun R n)]
    simp only [B, LinearMap.toMatrix_eq_toMatrix', LinearMap.BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix', LinearMap.toMatrix'_toLinearMap₂', mul_one,
      Matrix.mem_orthogonalGroup_iff']
  rw [← hgram, QuadraticMap.mem_orthogonalGroup_iff_polar h2]
  have hpolar (x y : n → R) :
      QuadraticMap.polar (Matrix.toQuadraticForm' (1 : Matrix n n R)) x y =
        (2 : R) • B x y := by
    simp only [polar_toQuadraticForm'_one, B, Matrix.toLinearMap₂'_apply', Matrix.one_mulVec,
      smul_eq_mul]
  simp only [hpolar, h2.eq_iff, BilinForm.isIsometry_iff, LinearEquiv.coe_coe]

/-- The orthogonal group of the standard quadratic form is the matrix orthogonal group,
provided multiplication by two is injective. -/
noncomputable def standardOrthogonalGroupEquiv (h2 : IsSMulRegular R (2 : R)) :
    QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R)) ≃*
      Matrix.orthogonalGroup n R where
  toFun g := ⟨LinearMap.toMatrix' (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap,
    (toMatrix_mem_orthogonalGroup_iff R n h2 _).mpr g.property⟩
  invFun A := ⟨Matrix.UnitaryGroup.toLinearEquiv A,
    (toMatrix_mem_orthogonalGroup_iff R n h2 _).mp (by
      simp [Matrix.UnitaryGroup.toLinearEquiv])⟩
  left_inv g := Subtype.ext <| LinearEquiv.ext fun x ↦ by
    simp [Matrix.UnitaryGroup.toLinearEquiv]
  right_inv A := Subtype.ext <| by simp [Matrix.UnitaryGroup.toLinearEquiv]
  map_mul' g h := Subtype.ext <| by
    simpa using LinearMap.toMatrix'_mul
      (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap
      (h : (n → R) ≃ₗ[R] (n → R)).toLinearMap

/-- The standard orthogonal comparison takes the coordinate matrix of an automorphism. -/
@[simp]
theorem coe_standardOrthogonalGroupEquiv_apply (h2 : IsSMulRegular R (2 : R))
    (g : QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    (standardOrthogonalGroupEquiv h2 g : Matrix n n R) =
      LinearMap.toMatrix' (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap := (rfl)

/-- The inverse standard orthogonal comparison acts by matrix-vector multiplication. -/
@[simp]
theorem standardOrthogonalGroupEquiv_symm_apply (h2 : IsSMulRegular R (2 : R))
    (A : Matrix.orthogonalGroup n R) (x : n → R) :
    ((standardOrthogonalGroupEquiv h2).symm A : (n → R) ≃ₗ[R] (n → R)) x =
      (A : Matrix n n R) *ᵥ x := (rfl)

/-- The coordinate matrix is special orthogonal exactly when the linear automorphism is
special orthogonal for the standard quadratic form. -/
@[simp]
theorem toMatrix_mem_specialOrthogonalGroup_iff (R : Type u) [CommRing R]
    (n : Type v) [Fintype n] [DecidableEq n] (h2 : IsSMulRegular R (2 : R))
    (e : (n → R) ≃ₗ[R] (n → R)) :
    LinearMap.toMatrix' e.toLinearMap ∈ Matrix.specialOrthogonalGroup n R ↔
      e ∈ QuadraticMap.specialOrthogonalGroup
        (Matrix.toQuadraticForm' (1 : Matrix n n R)) := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, toMatrix_mem_orthogonalGroup_iff R n h2,
    QuadraticMap.mem_specialOrthogonalGroup_iff, LinearMap.det_toMatrix',
    ← LinearEquiv.coe_det]
  simp only [Units.val_eq_one]

/-- The special orthogonal group of the standard quadratic form is the matrix special orthogonal
group, provided multiplication by two is injective. -/
noncomputable def standardSpecialOrthogonalGroupEquiv (h2 : IsSMulRegular R (2 : R)) :
    QuadraticMap.specialOrthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R)) ≃*
      Matrix.specialOrthogonalGroup n R where
  toFun g := ⟨LinearMap.toMatrix' (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap,
    (toMatrix_mem_specialOrthogonalGroup_iff R n h2 _).mpr g.property⟩
  invFun A := ⟨Matrix.UnitaryGroup.toLinearEquiv
      ⟨A, (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1⟩,
    (toMatrix_mem_specialOrthogonalGroup_iff R n h2 _).mp (by
      simp [Matrix.UnitaryGroup.toLinearEquiv])⟩
  left_inv g := Subtype.ext <| LinearEquiv.ext fun x ↦ by
    simp [Matrix.UnitaryGroup.toLinearEquiv]
  right_inv A := Subtype.ext <| by simp [Matrix.UnitaryGroup.toLinearEquiv]
  map_mul' g h := Subtype.ext <| by
    simpa using LinearMap.toMatrix'_mul
      (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap
      (h : (n → R) ≃ₗ[R] (n → R)).toLinearMap

/-- The standard special orthogonal comparison takes the coordinate matrix of an automorphism. -/
@[simp]
theorem coe_standardSpecialOrthogonalGroupEquiv_apply (h2 : IsSMulRegular R (2 : R))
    (g : QuadraticMap.specialOrthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    (standardSpecialOrthogonalGroupEquiv h2 g : Matrix n n R) =
      LinearMap.toMatrix' (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap := (rfl)

/-- The inverse standard special orthogonal comparison acts by matrix-vector multiplication. -/
@[simp]
theorem standardSpecialOrthogonalGroupEquiv_symm_apply (h2 : IsSMulRegular R (2 : R))
    (A : Matrix.specialOrthogonalGroup n R) (x : n → R) :
    ((standardSpecialOrthogonalGroupEquiv h2).symm A : (n → R) ≃ₗ[R] (n → R)) x =
      (A : Matrix n n R) *ᵥ x := (rfl)

section Isometry

variable {V : Type*} [AddCommGroup V] [Module R V] {Q : QuadraticForm R V}

/-- An isometry from `Q` to the standard quadratic form identifies the orthogonal group of `Q`
with the matrix orthogonal group: an automorphism is sent to the matrix of its conjugate by the
isometry. -/
noncomputable def orthogonalGroupEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    QuadraticMap.orthogonalGroup Q ≃* Matrix.orthogonalGroup n R :=
  e.orthogonalGroupCongr.trans (standardOrthogonalGroupEquiv h2)

/-- The orthogonal coordinate comparison is transport along the isometry followed by the standard
comparison. -/
theorem orthogonalGroupEquivMatrix_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.orthogonalGroup Q) :
    orthogonalGroupEquivMatrix h2 e g =
      standardOrthogonalGroupEquiv h2 (e.orthogonalGroupCongr g) :=
  (rfl)

/-- The orthogonal coordinate comparison takes the matrix of the conjugate automorphism. -/
@[simp]
theorem coe_orthogonalGroupEquivMatrix_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.orthogonalGroup Q) :
    (orthogonalGroupEquivMatrix h2 e g : Matrix n n R) =
      LinearMap.toMatrix' (e.orthogonalGroupCongr g : Module.End R (n → R)) := (rfl)

/-- The matrix of an orthogonal automorphism acts on coordinates as the automorphism acts on the
corresponding vectors. -/
theorem orthogonalGroupEquivMatrix_mulVec (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.orthogonalGroup Q) (x : n → R) :
    (orthogonalGroupEquivMatrix h2 e g : Matrix n n R) *ᵥ x =
      e ((g : V ≃ₗ[R] V) (e.symm x)) := by
  simp

/-- The inverse orthogonal coordinate comparison acts by matrix-vector multiplication in the
chosen coordinates. -/
@[simp]
theorem orthogonalGroupEquivMatrix_symm_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (A : Matrix.orthogonalGroup n R) (x : V) :
    ((orthogonalGroupEquivMatrix h2 e).symm A : V ≃ₗ[R] V) x =
      e.symm ((A : Matrix n n R) *ᵥ e x) := by
  simp [orthogonalGroupEquivMatrix]

/-- The orthogonal coordinate comparison along the identity isometry of the standard form is the
standard comparison. -/
@[simp]
theorem orthogonalGroupEquivMatrix_refl (h2 : IsSMulRegular R (2 : R)) :
    orthogonalGroupEquivMatrix h2
        (_root_.QuadraticMap.IsometryEquiv.refl (Matrix.toQuadraticForm' (1 : Matrix n n R))) =
      standardOrthogonalGroupEquiv h2 := by
  ext g : 2
  simp

/-- The orthogonal coordinate comparison along a composite isometry first transports along the
first isometry. -/
theorem orthogonalGroupEquivMatrix_trans {W : Type*} [AddCommGroup W] [Module R W]
    {P : QuadraticForm R W} (h2 : IsSMulRegular R (2 : R)) (f : P.IsometryEquiv Q)
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    orthogonalGroupEquivMatrix h2 (f.trans e) =
      f.orthogonalGroupCongr.trans (orthogonalGroupEquivMatrix h2 e) := by
  ext g : 2
  simp

/-- The orthogonal coordinate comparison preserves the determinant. -/
theorem det_orthogonalGroupEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.orthogonalGroup Q) :
    (orthogonalGroupEquivMatrix h2 e g : Matrix n n R).det =
      (_root_.QuadraticMap.orthogonalDet Q g : R) := by
  rw [coe_orthogonalGroupEquivMatrix_apply, LinearMap.det_toMatrix',
    ← LinearEquiv.coe_det, ← _root_.QuadraticMap.orthogonalDet_apply,
    e.orthogonalDet_orthogonalGroupCongr]

/-- An isometry from `Q` to the standard quadratic form identifies the special orthogonal group
of `Q` with the matrix special orthogonal group: an automorphism is sent to the matrix of its
conjugate by the isometry. -/
noncomputable def specialOrthogonalGroupEquivMatrix (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    QuadraticMap.specialOrthogonalGroup Q ≃* Matrix.specialOrthogonalGroup n R :=
  e.specialOrthogonalGroupCongr.trans (standardSpecialOrthogonalGroupEquiv h2)

/-- The special orthogonal coordinate comparison is transport along the isometry followed by the
standard comparison. -/
theorem specialOrthogonalGroupEquivMatrix_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.specialOrthogonalGroup Q) :
    specialOrthogonalGroupEquivMatrix h2 e g =
      standardSpecialOrthogonalGroupEquiv h2 (e.specialOrthogonalGroupCongr g) :=
  (rfl)

/-- The special orthogonal coordinate comparison takes the matrix of the conjugate
automorphism. -/
@[simp]
theorem coe_specialOrthogonalGroupEquivMatrix_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.specialOrthogonalGroup Q) :
    (specialOrthogonalGroupEquivMatrix h2 e g : Matrix n n R) =
      LinearMap.toMatrix' (e.specialOrthogonalGroupCongr g : Module.End R (n → R)) := (rfl)

/-- The matrix of a special orthogonal automorphism acts on coordinates as the automorphism acts
on the corresponding vectors. -/
theorem specialOrthogonalGroupEquivMatrix_mulVec (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.specialOrthogonalGroup Q) (x : n → R) :
    (specialOrthogonalGroupEquivMatrix h2 e g : Matrix n n R) *ᵥ x =
      e ((g : V ≃ₗ[R] V) (e.symm x)) := by
  simp

/-- The inverse special orthogonal coordinate comparison acts by matrix-vector multiplication in
the chosen coordinates. -/
@[simp]
theorem specialOrthogonalGroupEquivMatrix_symm_apply (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (A : Matrix.specialOrthogonalGroup n R) (x : V) :
    ((specialOrthogonalGroupEquivMatrix h2 e).symm A : V ≃ₗ[R] V) x =
      e.symm ((A : Matrix n n R) *ᵥ e x) := by
  simp [specialOrthogonalGroupEquivMatrix]

/-- The special orthogonal coordinate comparison along the identity isometry of the standard form
is the standard comparison. -/
@[simp]
theorem specialOrthogonalGroupEquivMatrix_refl (h2 : IsSMulRegular R (2 : R)) :
    specialOrthogonalGroupEquivMatrix h2
        (_root_.QuadraticMap.IsometryEquiv.refl (Matrix.toQuadraticForm' (1 : Matrix n n R))) =
      standardSpecialOrthogonalGroupEquiv h2 := by
  ext g : 2
  simp

/-- The special orthogonal coordinate comparison along a composite isometry first transports along
the first isometry. -/
theorem specialOrthogonalGroupEquivMatrix_trans {W : Type*} [AddCommGroup W] [Module R W]
    {P : QuadraticForm R W} (h2 : IsSMulRegular R (2 : R)) (f : P.IsometryEquiv Q)
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    specialOrthogonalGroupEquivMatrix h2 (f.trans e) =
      f.specialOrthogonalGroupCongr.trans (specialOrthogonalGroupEquivMatrix h2 e) := by
  ext g : 2
  simp

/-- The special orthogonal coordinate comparison is the orthogonal one on the underlying
orthogonal automorphism. -/
theorem coe_specialOrthogonalGroupEquivMatrix_eq_orthogonalGroupEquivMatrix
    (h2 : IsSMulRegular R (2 : R))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n R)))
    (g : QuadraticMap.specialOrthogonalGroup Q) :
    (specialOrthogonalGroupEquivMatrix h2 e g : Matrix n n R) =
      orthogonalGroupEquivMatrix h2 e (QuadraticMap.specialOrthogonalToOrthogonal Q g) := by
  ext i j
  simp

end Isometry

end TauCeti
