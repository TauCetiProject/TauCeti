/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Coordinate.Bialgebra
public import TauCeti.LinearAlgebra.Matrix.Exponential.UpperTriangular

/-!
# Polynomial exponential coordinates on the upper-unitriangular group

Over a commutative rational algebra, finite exponential and logarithm give inverse regular
maps between strictly upper-triangular matrices and upper-unitriangular matrices. Both
spaces have polynomial coordinate ring `CoordinateRing R m`, with one variable per entry
strictly above the diagonal. In the first space the generic matrix is `genericMatrix R m - 1`;
in the second it is `genericMatrix R m`.

`expComap` and `logComap` are the pullbacks on these coordinate rings, and
`expCoordinateEquiv` packages their two-sided inverse identities. They describe an isomorphism
of affine schemes, without asserting compatibility with addition and matrix multiplication.
The evaluation equations hold over every commutative value algebra, including nonreduced
algebras. Empty finite index types are included.

This uses the finite exponential/logarithm inverse identities in
`TauCeti.RingTheory.Nilpotent.Log` and the existing polynomial coordinates of
`TauCeti.UpperUnitriangular`.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
-/

public section

namespace TauCeti.UpperUnitriangular

open Matrix

universe u v w

variable (R : Type u) [CommRing R] [Algebra ℚ R]
variable (m : Type v) [Fintype m] [LinearOrder m]

/-- Pullback by the finite exponential from strictly upper-triangular matrices to `U_m`.
The source and target are polynomial rings on the same strict-upper indices. -/
noncomputable def expComap : CoordinateRing R m →ₐ[R] CoordinateRing R m :=
  MvPolynomial.aeval fun ij : Index m ↦
    IsNilpotent.exp (genericMatrix R m - 1) ij.1.1 ij.1.2

/-- Pullback by the finite logarithm from `U_m` to strictly upper-triangular matrices. -/
noncomputable def logComap : CoordinateRing R m →ₐ[R] CoordinateRing R m :=
  MvPolynomial.aeval fun ij : Index m ↦
    IsNilpotent.log (genericMatrix R m) ij.1.1 ij.1.2

/-- Exponential pullback on a coordinate is the corresponding finite-exponential entry. -/
@[simp]
theorem expComap_X (ij : Index m) :
    expComap R m (MvPolynomial.X ij) =
      IsNilpotent.exp (genericMatrix R m - 1) ij.1.1 ij.1.2 := by
  simp [expComap]

/-- Logarithm pullback on a coordinate is the corresponding finite-logarithm entry. -/
@[simp]
theorem logComap_X (ij : Index m) :
    logComap R m (MvPolynomial.X ij) =
      IsNilpotent.log (genericMatrix R m) ij.1.1 ij.1.2 := by
  simp [logComap]

/-- Exponential pullback evaluates the generic unitriangular matrix at the exponential. -/
@[simp]
theorem map_expComap_genericMatrix :
    (genericMatrix R m).map (expComap R m) =
      IsNilpotent.exp (genericMatrix R m - 1) := by
  apply map_aeval_genericMatrix
  apply IsUpperTriangular.isUpperUnitriangular_exp
  · exact (isUpperUnitriangular_genericMatrix R m).isUpperTriangular.sub blockTriangular_one
  · intro i
    simp

/-- Logarithm pullback evaluates the generic unitriangular matrix at one plus the logarithm. -/
@[simp]
theorem map_logComap_genericMatrix :
    (genericMatrix R m).map (logComap R m) =
      IsNilpotent.log (genericMatrix R m) + 1 := by
  have hU := isUpperUnitriangular_genericMatrix R m
  apply (hU.map (logComap R m)).ext
    ((Matrix.isUpperUnitriangular_def _).mpr
      ⟨hU.isUpperTriangular_log.add blockTriangular_one, by intro i; simp [hU.log_apply_diag]⟩)
  intro i j hij
  simp [Matrix.map_apply, genericMatrix_apply_of_lt R m hij, Matrix.one_apply_ne hij.ne]

/-- Logarithm pullback after exponential pullback is the identity on the coordinate ring. -/
@[simp]
theorem logComap_comp_expComap :
    (logComap R m).comp (expComap R m) = AlgHom.id R (CoordinateRing R m) := by
  classical
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, expComap_X, AlgHom.id_apply]
  have h := IsNilpotent.map_exp (isUpperUnitriangular_genericMatrix R m).isNilpotent_sub_one
    (logComap R m).mapMatrix
  have hmap : (logComap R m).mapMatrix (genericMatrix R m - 1) =
      IsNilpotent.log (genericMatrix R m) := by
    simp only [map_sub, map_one, AlgHom.mapMatrix_apply, map_logComap_genericMatrix,
      add_sub_cancel_right]
  rw [hmap, IsNilpotent.exp_log (isUpperUnitriangular_genericMatrix R m).isNilpotent_sub_one] at h
  exact (congrFun (congrFun h ij.1.1) ij.1.2).trans
    (genericMatrix_apply_of_lt R m ij.2)

/-- Exponential pullback after logarithm pullback is the identity on the coordinate ring. -/
@[simp]
theorem expComap_comp_logComap :
    (expComap R m).comp (logComap R m) = AlgHom.id R (CoordinateRing R m) := by
  classical
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, logComap_X, AlgHom.id_apply]
  have h := IsNilpotent.map_log (isUpperUnitriangular_genericMatrix R m).isNilpotent_sub_one
    (expComap R m).mapMatrix
  simp only [AlgHom.mapMatrix_apply, map_expComap_genericMatrix,
    IsNilpotent.log_exp (isUpperUnitriangular_genericMatrix R m).isNilpotent_sub_one] at h
  exact (congrFun (congrFun h ij.1.1) ij.1.2).trans (by
    simp [Matrix.one_apply_ne ij.2.ne, genericMatrix_apply_of_lt R m ij.2])

/-- The polynomial coordinate isomorphism whose forward map is exponential pullback and
whose inverse is logarithm pullback. Contravariantly it identifies the strictly
upper-triangular affine space with the upper-unitriangular group scheme. -/
noncomputable def expCoordinateEquiv : CoordinateRing R m ≃ₐ[R] CoordinateRing R m :=
  AlgEquiv.ofAlgHom (expComap R m) (logComap R m)
    (expComap_comp_logComap R m) (logComap_comp_expComap R m)

/-- The forward coordinate isomorphism is exponential pullback. -/
@[simp]
theorem expCoordinateEquiv_toAlgHom :
    (expCoordinateEquiv R m).toAlgHom = expComap R m := (rfl)

/-- The inverse coordinate isomorphism is logarithm pullback. -/
@[simp]
theorem expCoordinateEquiv_symm_toAlgHom :
    (expCoordinateEquiv R m).symm.toAlgHom = logComap R m := (rfl)

/-- Applying the coordinate isomorphism pulls a polynomial back by exponential. -/
@[simp]
theorem expCoordinateEquiv_apply (p : CoordinateRing R m) :
    expCoordinateEquiv R m p = expComap R m p := (rfl)

/-- Applying the inverse coordinate isomorphism pulls a polynomial back by logarithm. -/
@[simp]
theorem expCoordinateEquiv_symm_apply (p : CoordinateRing R m) :
    (expCoordinateEquiv R m).symm p = logComap R m p := (rfl)

section Evaluation

variable {A : Type w} [CommRing A] [Algebra ℚ A] [Algebra R A]

/-- Evaluating exponential pullback at any strictly upper-triangular matrix evaluates the
original polynomial at its exponential. This holds over arbitrary commutative value algebras. -/
theorem aeval_comp_expComap (M : Matrix m m A) (hM : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 0) :
    (MvPolynomial.aeval (R := R) fun ij : Index m ↦ M ij.1.1 ij.1.2).comp (expComap R m) =
      MvPolynomial.aeval fun ij : Index m ↦ IsNilpotent.exp M ij.1.1 ij.1.2 := by
  classical
  let f := MvPolynomial.aeval (R := R) fun ij : Index m ↦ M ij.1.1 ij.1.2
  have hmap : f.mapMatrix (genericMatrix R m - 1) = M := by
    have hU : (M + 1).IsUpperUnitriangular := (Matrix.isUpperUnitriangular_def _).mpr
      ⟨hM.add blockTriangular_one, by intro i; simp [hdiag]⟩
    have h := map_aeval_genericMatrix R m (M + 1) hU
    have hf : (MvPolynomial.aeval (R := R)
        fun ij : Index m ↦ (M + 1) ij.1.1 ij.1.2) = f := by
      apply MvPolynomial.algHom_ext
      intro ij
      simp [f, Matrix.one_apply_ne ij.2.ne]
    rw [hf] at h
    simp only [map_sub, map_one, AlgHom.mapMatrix_apply, h, add_sub_cancel_right]
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, expComap_X, MvPolynomial.aeval_X]
  have h := IsNilpotent.map_exp (isUpperUnitriangular_genericMatrix R m).isNilpotent_sub_one
    f.mapMatrix
  rw [hmap] at h
  exact congrFun (congrFun h ij.1.1) ij.1.2

/-- Evaluating logarithm pullback at an upper-unitriangular matrix evaluates the original
polynomial at its logarithm, including over nonreduced value algebras. -/
theorem aeval_comp_logComap (M : Matrix m m A) (hM : M.IsUpperUnitriangular) :
    (MvPolynomial.aeval (R := R) fun ij : Index m ↦ M ij.1.1 ij.1.2).comp (logComap R m) =
      MvPolynomial.aeval fun ij : Index m ↦ IsNilpotent.log M ij.1.1 ij.1.2 := by
  classical
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, logComap_X, MvPolynomial.aeval_X]
  have h := IsNilpotent.map_log (isUpperUnitriangular_genericMatrix R m).isNilpotent_sub_one
    (MvPolynomial.aeval (R := R) fun ij : Index m ↦ M ij.1.1 ij.1.2).mapMatrix
  simp only [AlgHom.mapMatrix_apply, map_aeval_genericMatrix R m M hM] at h
  exact congrFun (congrFun h ij.1.1) ij.1.2

end Evaluation

end TauCeti.UpperUnitriangular
