/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.CrossProduct
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Frame

/-!
# The axis of a rotation

**Euler's rotation theorem.** A special orthogonal matrix `A` in odd dimension satisfies
`det (A - 1) = 0`, provided two is a non-zero-divisor: from `A Aᵀ = 1` and `det A = 1` one gets
`det (A - 1) = det (A (1 - Aᵀ)) = det (1 - A) = -det (A - 1)`. Over an integral domain of
characteristic different from two, `A` therefore fixes a nonzero vector.

In dimension three over an ordered field, a rotation fixing two linearly independent vectors `u`
and `v` is the identity: it also fixes their cross product `u ⨯₃ v`, and `u`, `v`, `u ⨯₃ v` are
the columns of the frame matrix `TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame u v`, whose
determinant is `(u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) ≠ 0`. So the vectors fixed by a
nonidentity rotation form a line, its axis. Over `ℝ` the axis meets the unit sphere in exactly two
antipodal points `p` and `-p`, the poles of the rotation. These are the poles counted in the
classification of the finite rotation groups.

## Main declarations

* `Matrix.det_sub_one_eq_zero_of_mem_specialOrthogonalGroup`: `det (A - 1) = 0` for a special
  orthogonal matrix in odd dimension.
* `Matrix.exists_mulVec_eq_self_of_mem_specialOrthogonalGroup`: over an integral domain of
  characteristic different from two, such a matrix fixes a nonzero vector.
* `Matrix.eq_one_of_mulVec_eq_self_of_linearIndependent`: a rotation of three-space over an
  ordered field fixing two linearly independent vectors is the identity.
* `Matrix.mulVec_eq_self_iff_exists_smul_eq`: the vectors fixed by a nonidentity rotation are the
  multiples of any nonzero fixed vector.
* `Matrix.exists_setOf_mulVec_eq_self_eq_pair`: a nonidentity rotation of real three-space fixes
  exactly two unit vectors, `p` and `-p`.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 5.1.
-/

public section

namespace Matrix

/-- **Euler's rotation theorem**, determinant form: a special orthogonal matrix `A` in odd
dimension has `det (A - 1) = 0`, over any commutative ring where two is a non-zero-divisor. -/
theorem det_sub_one_eq_zero_of_mem_specialOrthogonalGroup {n R : Type*} [Fintype n]
    [DecidableEq n] [CommRing R] (h2 : IsRegular (2 : R)) (hn : Odd (Fintype.card n))
    {A : Matrix n n R} (hA : A ∈ specialOrthogonalGroup n R) : (A - 1).det = 0 := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff] at hA
  obtain ⟨hAA, hdet⟩ := hA
  have h : (A - 1).det = -(A - 1).det :=
    calc (A - 1).det = (A * (1 - Aᵀ)).det := by rw [mul_sub, mul_one, hAA]
      _ = (1 - A).det := by
        rw [det_mul, hdet, one_mul, ← det_transpose, transpose_sub, transpose_one,
          transpose_transpose]
      _ = -(A - 1).det := by rw [← neg_sub, det_neg, hn.neg_one_pow, neg_one_mul]
  have hzero : (2 : R) * (A - 1).det = 0 := by linear_combination h
  exact h2.left.mul_left_eq_zero_iff.mp hzero

/-- **Euler's rotation theorem**: over an integral domain of characteristic different from two, a
special orthogonal matrix in odd dimension fixes a nonzero vector. -/
theorem exists_mulVec_eq_self_of_mem_specialOrthogonalGroup {n R : Type*} [Fintype n]
    [DecidableEq n] [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0) (hn : Odd (Fintype.card n))
    {A : Matrix n n R} (hA : A ∈ specialOrthogonalGroup n R) : ∃ v ≠ 0, A *ᵥ v = v := by
  obtain ⟨v, hv, h⟩ := exists_mulVec_eq_zero_iff.mpr
    (det_sub_one_eq_zero_of_mem_specialOrthogonalGroup (.of_ne_zero h2) hn hA)
  exact ⟨v, hv, by rwa [sub_mulVec, one_mulVec, sub_eq_zero] at h⟩

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {A : Matrix (Fin 3) (Fin 3) K}

open TauCeti.Matrix.SpecialOrthogonalGroup in
/-- A rotation of three-space over an ordered field which fixes two linearly independent vectors
is the identity. -/
theorem eq_one_of_mulVec_eq_self_of_linearIndependent
    (hA : A ∈ specialOrthogonalGroup (Fin 3) K) {u v : Fin 3 → K}
    (huv : LinearIndependent K ![u, v]) (hu : A *ᵥ u = u) (hv : A *ᵥ v = v) : A = 1 := by
  -- `A` fixes the frame `(u, v, u ⨯₃ v)`, so `A N = N` for the frame matrix `N = ofFrame u v`,
  -- which is invertible, its determinant being `(u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) ≠ 0`. Hence `A = 1`.
  have hN : A * ofFrame u v = ofFrame u v := by rw [← ofFrame_mulVec_mulVec hA, hu, hv]
  have hdet : IsUnit (ofFrame u v).det := by
    rw [det_ofFrame]
    exact isUnit_iff_ne_zero.mpr (dotProduct_self_eq_zero.not.mpr
      (crossProduct_ne_zero_iff_linearIndependent.mpr huv))
  calc A = A * (ofFrame u v * (ofFrame u v)⁻¹) := by rw [mul_nonsing_inv _ hdet, mul_one]
    _ = 1 := by rw [← Matrix.mul_assoc, hN, mul_nonsing_inv _ hdet]

/-- **The axis of a nonidentity rotation.** If a rotation `A ≠ 1` of three-space over an ordered
field fixes a nonzero vector `v`, then the vectors it fixes are exactly the multiples of `v`. -/
theorem mulVec_eq_self_iff_exists_smul_eq (hA : A ∈ specialOrthogonalGroup (Fin 3) K)
    (hA1 : A ≠ 1) {v : Fin 3 → K} (hv0 : v ≠ 0) (hv : A *ᵥ v = v) {x : Fin 3 → K} :
    A *ᵥ x = x ↔ ∃ c : K, c • v = x := by
  refine ⟨fun hx ↦ ?_, fun ⟨c, hc⟩ ↦ by rw [← hc, mulVec_smul, hv]⟩
  by_contra h
  push Not at h
  exact hA1 (eq_one_of_mulVec_eq_self_of_linearIndependent hA
    ((LinearIndependent.pair_iff' hv0).mpr h) hv hx)

end OrderedField

/-- **The poles of a nonidentity rotation.** A rotation `A ≠ 1` of real three-space fixes exactly
two unit vectors: a unit vector `p` on its axis and its antipode `-p`. -/
theorem exists_setOf_mulVec_eq_self_eq_pair {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A ∈ specialOrthogonalGroup (Fin 3) ℝ) (hA1 : A ≠ 1) :
    ∃ p : Fin 3 → ℝ, p ⬝ᵥ p = 1 ∧ A *ᵥ p = p ∧ {x | x ⬝ᵥ x = 1 ∧ A *ᵥ x = x} = {p, -p} := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_self_of_mem_specialOrthogonalGroup two_ne_zero
    (by decide) hA
  have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (by simpa using dotProduct_star_self_nonneg v)
    (Ne.symm (dotProduct_self_eq_zero.not.mpr hv0))
  set p := (√(v ⬝ᵥ v))⁻¹ • v with hp_def
  have hp1 : p ⬝ᵥ p = 1 := by
    simp only [hp_def, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
    exact (Real.sq_sqrt hpos.le).symm
  have hp0 : p ≠ 0 := by
    rintro h
    simp [h] at hp1
  have hp : A *ᵥ p = p := by rw [hp_def, mulVec_smul, hv]
  refine ⟨p, hp1, hp, Set.ext fun x ↦ ⟨fun ⟨hx1, hx⟩ ↦ ?_, ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (mulVec_eq_self_iff_exists_smul_eq hA hA1 hp0 hp).mp hx
    rw [smul_dotProduct, dotProduct_smul, hp1, smul_eq_mul, smul_eq_mul, mul_one] at hx1
    rcases mul_self_eq_one_iff.mp hx1 with rfl | rfl
    · simp
    · simp
  · rintro (rfl | rfl)
    · exact ⟨hp1, hp⟩
    · exact ⟨by rw [neg_dotProduct, dotProduct_neg, neg_neg, hp1], by rw [mulVec_neg, hp]⟩

end Matrix
