/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

/-!
# Scalar multiples of determinant-one matrices

Over an algebraically closed field, every invertible matrix is a determinant-one matrix
times a scalar matrix. Consequently, a subspace stable under the special linear group
and scalar matrices is stable under the general linear group.

The factorization uses Mathlib's `ProjectiveSpecialLinearGroup.toPGL_surj_of_roots`
when units have roots, and `ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed` over
algebraically closed fields.
The empty matrix index is included.

The same factorization compares conjugacy of matrices under the two groups. Over any commutative
ring, a conjugate `g X g⁻¹` by `g ∈ GL(n, R)` is also a conjugate by `SL(n, R)` exactly when the
determinant of `g` can be corrected inside the centralizer of `X`: some invertible matrix commuting
with `X` has the same determinant as `g`. When every unit has a root of degree the matrix size, a
scalar matrix supplies this correction, so the conjugation orbits of `SL(n, K)` and `GL(n, K)` on
`Matrix n n K` agree. Over an algebraically closed field they agree for every index type, including
the empty and the one-element ones.

## Main results

* `ConjAct.toConjAct_toGL_smul`: conjugating by `s ∈ SL(n, R)` is conjugating by its image in
  `GL(n, R)`.
* `Matrix.GeneralLinearGroup.exists_toGL_mul_scalar_eq`: over an algebraically closed field, an
  invertible matrix is a determinant-one matrix times a scalar matrix.
* `Matrix.GeneralLinearGroup.toConjAct_smul_mem_orbit_specialLinearGroup_iff`: a
  `GL(n, R)`-conjugate is an `SL(n, R)`-conjugate exactly when the determinant of the conjugator
  is the determinant of an invertible matrix in the centralizer.
* `Matrix.GeneralLinearGroup.orbit_conjAct_specialLinearGroup_subset`: an `SL(n, R)`-conjugate is
  a `GL(n, R)`-conjugate.
* `Matrix.GeneralLinearGroup.orbit_conjAct_specialLinearGroup_eq_of_roots` and
  `Matrix.GeneralLinearGroup.orbit_conjAct_specialLinearGroup_eq`: when units have roots of degree
  the matrix size, and over an algebraically closed field, the `SL(n, K)`- and
  `GL(n, K)`-conjugacy classes of a matrix agree.
-/

public section

namespace ConjAct

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Conjugating a matrix by the image of `s ∈ SL(n, R)` in `GL(n, R)` is conjugating it by `s`. -/
@[simp]
theorem toConjAct_toGL_smul (s : Matrix.SpecialLinearGroup ι R) (X : Matrix ι ι R) :
    toConjAct (Matrix.SpecialLinearGroup.toGL s) • X = toConjAct s • X := by
  rw [units_smul_def, specialLinearGroup_smul_def, ofConjAct_toConjAct, ofConjAct_toConjAct,
    ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

end ConjAct

namespace Matrix.GeneralLinearGroup

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

/-- If every unit has a root of degree equal to the matrix size, an invertible matrix
is a determinant-one matrix times a scalar matrix. -/
theorem exists_toGL_mul_scalar_eq_of_roots [CommRing K] (g : GL ι K)
    (hK : ∀ r : Kˣ, ∃ z : Kˣ, z ^ Fintype.card ι = r) :
    ∃ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s * scalar ι z = g := by
  obtain ⟨s, hs⟩ := ProjectiveSpecialLinearGroup.toPGL_surj_of_roots hK (ProjGenLinGroup.mk g)
  induction s using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨z, hz⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hs
    exact ⟨s, z, hz⟩

/-- **Determinant correction of conjugators.** Over a commutative ring `K`, the conjugate
`g X g⁻¹` of a matrix `X` by `g ∈ GL(n, K)` is also a conjugate of `X` by `SL(n, K)` exactly when
some invertible matrix commuting with `X` has the determinant of `g`. -/
theorem toConjAct_smul_mem_orbit_specialLinearGroup_iff [CommRing K] {g : GL ι K}
    {X : Matrix ι ι K} :
    ConjAct.toConjAct g • X ∈ MulAction.orbit (ConjAct (SpecialLinearGroup ι K)) X ↔
      ∃ c : GL ι K, Commute (c : Matrix ι ι K) X ∧ det c = det g := by
  -- An invertible matrix fixes `X` under conjugation exactly when it commutes with `X`.
  have hfix (c : GL ι K) : ConjAct.toConjAct c • X = X ↔ Commute (c : Matrix ι ι K) X := by
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, Units.mul_inv_eq_iff_eq_mul]
    exact (commute_iff_eq _ _).symm
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨s, rfl⟩ := ConjAct.toConjAct.surjective s
    refine ⟨(SpecialLinearGroup.toGL s)⁻¹ * g, (hfix _).mp ?_, by simp⟩
    rw [ConjAct.toConjAct_mul, mul_smul, ← hs, ← ConjAct.toConjAct_toGL_smul, ← mul_smul,
      ← ConjAct.toConjAct_mul, inv_mul_cancel, ConjAct.toConjAct_one, one_smul]
  · rintro ⟨c, hc, hdet⟩
    obtain ⟨s, hs⟩ : g * c⁻¹ ∈ (SpecialLinearGroup.toGL (n := ι) (R := K)).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, map_mul, map_inv, hdet,
        mul_inv_cancel]
    refine ⟨ConjAct.toConjAct s, ?_⟩
    rw [← ConjAct.toConjAct_toGL_smul, hs, ConjAct.toConjAct_mul, mul_smul,
      ConjAct.toConjAct_inv]
    congr 1
    rw [inv_smul_eq_iff, (hfix c).mpr hc]

/-- An `SL(n, K)`-conjugate of a matrix is a `GL(n, K)`-conjugate. -/
theorem orbit_conjAct_specialLinearGroup_subset [CommRing K] (X : Matrix ι ι K) :
    MulAction.orbit (ConjAct (SpecialLinearGroup ι K)) X ⊆
      MulAction.orbit (ConjAct (GL ι K)) X := by
  rintro _ ⟨s, rfl⟩
  exact ⟨ConjAct.toConjAct (SpecialLinearGroup.toGL (ConjAct.ofConjAct s)), by simp⟩

/-- A scalar matrix with the determinant of `g` corrects `g` to a determinant-one conjugator. -/
private theorem toConjAct_smul_mem_orbit_specialLinearGroup_of_det_scalar [CommRing K]
    (g : GL ι K) (z : Kˣ) (hz : det (scalar ι z) = det g) (X : Matrix ι ι K) :
    ConjAct.toConjAct g • X ∈ MulAction.orbit (ConjAct (SpecialLinearGroup ι K)) X := by
  refine toConjAct_smul_mem_orbit_specialLinearGroup_iff.mpr ⟨scalar ι z, ?_, hz⟩
  rw [coe_scalar]
  exact Matrix.scalar_commute _ (Commute.all _) X

/-- If every unit has a root of degree equal to the matrix size, the conjugation orbit of a square
matrix under `SL(n, K)` is its conjugation orbit under `GL(n, K)`: a scalar matrix with the
determinant of the conjugator corrects it. -/
theorem orbit_conjAct_specialLinearGroup_eq_of_roots [CommRing K]
    (hK : ∀ r : Kˣ, ∃ z : Kˣ, z ^ Fintype.card ι = r) (X : Matrix ι ι K) :
    MulAction.orbit (ConjAct (SpecialLinearGroup ι K)) X =
      MulAction.orbit (ConjAct (GL ι K)) X := by
  refine (orbit_conjAct_specialLinearGroup_subset X).antisymm ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨z, hz⟩ := hK (det (ConjAct.ofConjAct g))
  rw [← ConjAct.toConjAct_ofConjAct g]
  exact toConjAct_smul_mem_orbit_specialLinearGroup_of_det_scalar _ z (by rw [det_scalar, hz]) X

variable [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, an invertible matrix is a determinant-one
matrix times a scalar matrix. This also holds for the empty matrix index. -/
theorem exists_toGL_mul_scalar_eq (g : GL ι K) :
    ∃ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s * scalar ι z = g := by
  classical
  obtain ⟨s, hs⟩ := (ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed
    (n := ι) (F := K)).symm.surjective (ProjGenLinGroup.mk g)
  have hs' : ProjectiveSpecialLinearGroup.toPGL s = ProjGenLinGroup.mk g := by
    -- Both branches of Mathlib's equivalence invert the same inclusion into PGL.
    simp only [ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed,
      ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty] at hs
    split_ifs at hs <;> exact hs
  induction s using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨z, hz⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hs'
    exact ⟨s, z, hz⟩

/-- **`SL` and `GL` conjugacy agree over an algebraically closed field.** The conjugation orbit of
a square matrix under `SL(n, K)` is its conjugation orbit under `GL(n, K)`: a conjugator `g` is a
determinant-one matrix times a scalar matrix, and the scalar matrix commutes with everything.
This includes the empty and the one-element index types. -/
theorem orbit_conjAct_specialLinearGroup_eq (X : Matrix ι ι K) :
    MulAction.orbit (ConjAct (SpecialLinearGroup ι K)) X =
      MulAction.orbit (ConjAct (GL ι K)) X := by
  refine (orbit_conjAct_specialLinearGroup_subset X).antisymm ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨s, z, hsz⟩ := exists_toGL_mul_scalar_eq (ConjAct.ofConjAct g)
  rw [← ConjAct.toConjAct_ofConjAct g]
  exact toConjAct_smul_mem_orbit_specialLinearGroup_of_det_scalar _ z
    (by rw [← hsz, map_mul, SpecialLinearGroup.coeToGL_det, one_mul]) X

end Matrix.GeneralLinearGroup
