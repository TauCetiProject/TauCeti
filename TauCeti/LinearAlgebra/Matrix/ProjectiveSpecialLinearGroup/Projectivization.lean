/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# `PSL(n, K)` as a subset of the projective space of matrices

A matrix of `SL(n, K)` is nonzero, so it spans a line of the matrix space and defines a point of
the projective space `ℙ K (Matrix n n K)`. Central elements of `SL(n, K)` are scalar matrices, so
this point only depends on the class of the matrix in `PSL(n, K) = SL(n, K) ⧸ Z(SL(n, K))`. This
gives a map `Matrix.ProjectiveSpecialLinearGroup.toProjectivization`, which is injective: if two
matrices of determinant one are proportional, the factor is an `n`-th root of unity, and the
corresponding scalar matrix is central.

Since `det (c • A) = c ^ n * det A`, whether `det A` vanishes only depends on the line of `A`
(`Matrix.det_rep_mk_ne_zero_iff`), and the line of a nonzero matrix `A` lies in the image exactly
when `det A` is the `n`-th power of a unit. Over an algebraically closed field the image is the
whole locus `{x | x.rep.det ≠ 0}` of lines of invertible matrices; for `n = 2` this is the
complement of the determinant quadric in `ℙ³`. Over `ℂ` the map is a homeomorphism onto this
open locus, which is proved in
`TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.Projectivization`.

## Main declarations

* `Matrix.ProjectiveSpecialLinearGroup.toProjectivization`: the map `PSL(n, K) → ℙ K (Matrix n n K)`
  sending the class of `A` to the line of `A`.
* `Matrix.ProjectiveSpecialLinearGroup.toProjectivization_injective`: it is injective.
* `Matrix.ProjectiveSpecialLinearGroup.mk_mem_range_toProjectivization_iff`: the line of `A` lies
  in its image exactly when `det A` is the `n`-th power of a unit.
* `Matrix.ProjectiveSpecialLinearGroup.range_toProjectivization`: over an algebraically closed
  field the image is the locus of lines of invertible matrices.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

namespace ProjectiveSpecialLinearGroup

omit [Nonempty n] in
/-- `A⁻¹ * B` is the scalar matrix `r` exactly when `B = r • A`. -/
private theorem scalar_eq_coe_inv_mul_iff {R : Type*} [CommRing R] {A B : SpecialLinearGroup n R}
    {r : R} : scalar n r = ((A⁻¹ * B : SpecialLinearGroup n R) : Matrix n n R) ↔
      (B : Matrix n n R) = r • (A : Matrix n n R) := by
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv, scalar_apply, ← smul_one_eq_diagonal]
  constructor
  · intro h
    rw [← mul_one (A : Matrix n n R), ← Matrix.mul_smul, h, ← Matrix.mul_assoc,
      mul_adjugate, A.det_coe, one_smul, Matrix.one_mul]
  · intro h
    rw [h, Matrix.mul_smul, adjugate_mul, A.det_coe, one_smul]

omit [Nonempty n] in
/-- Two matrices of `SL(n, R)` which are proportional define the same element of `PSL(n, R)`. -/
theorem coe_eq_coe_of_coe_eq_smul {R : Type*} [CommRing R] {A B : SpecialLinearGroup n R} {c : R}
    (h : (B : Matrix n n R) = c • (A : Matrix n n R)) :
    (A : ProjectiveSpecialLinearGroup n R) = B := by
  have hc : c ^ Fintype.card n = 1 := by
    simpa [A.det_coe, B.det_coe] using (congrArg det h).symm
  rw [QuotientGroup.eq, SpecialLinearGroup.mem_center_iff]
  exact ⟨c, hc, scalar_eq_coe_inv_mul_iff.2 h⟩

section Field

variable {K : Type*} [Field K]

variable (n K) in
/-- The point of the projective space of `n × n` matrices defined by an element of `PSL(n, K)`:
the line spanned by any matrix of `SL(n, K)` representing it. -/
def toProjectivization : ProjectiveSpecialLinearGroup n K → ℙ K (Matrix n n K) :=
  Quotient.lift (fun A : SpecialLinearGroup n K ↦ .mk K (A : Matrix n n K) A.coe_ne_zero)
    fun A B h ↦ by
      obtain ⟨r, -, hr⟩ := SpecialLinearGroup.mem_center_iff.1 (QuotientGroup.leftRel_apply.1 h)
      refine (Projectivization.mk_eq_mk_iff' K _ _ _ _).2 ⟨r⁻¹, ?_⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (A⁻¹ * B).coe_ne_zero (by rw [← hr, map_zero])
      rw [scalar_eq_coe_inv_mul_iff.1 hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]

@[simp]
theorem toProjectivization_mk (A : SpecialLinearGroup n K) :
    toProjectivization n K A = .mk K (A : Matrix n n K) A.coe_ne_zero :=
  (rfl)

/-- An element of `PSL(n, K)` is determined by the line of its representing matrices. -/
theorem toProjectivization_injective : Function.Injective (toProjectivization n K) := by
  intro g h hgh
  induction g using QuotientGroup.induction_on with | H A => ?_
  induction h using QuotientGroup.induction_on with | H B => ?_
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).1 hgh
  exact (coe_eq_coe_of_coe_eq_smul hc.symm).symm

omit [Nonempty n] in
/-- Whether the determinant vanishes only depends on the line of a matrix. -/
theorem _root_.Matrix.det_rep_mk_ne_zero_iff {A : Matrix n n K} (hA : A ≠ 0) :
    (Projectivization.mk K A hA).rep.det ≠ 0 ↔ A.det ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K A hA
  rw [← ha, Units.smul_def, det_smul, mul_ne_zero_iff, and_iff_right (pow_ne_zero _ a.ne_zero)]

/-- If `c ^ n = det A` for a nonzero `c`, then `c⁻¹ • A` is a matrix of `SL(n, K)` whose class
maps to the line of `A`. -/
theorem exists_coe_eq_inv_smul_of_pow_eq_det {A : Matrix n n K} (hA : A ≠ 0) {c : K} (hc0 : c ≠ 0)
    (hc : c ^ Fintype.card n = A.det) : ∃ B : SpecialLinearGroup n K,
      (B : Matrix n n K) = c⁻¹ • A ∧ toProjectivization n K B = .mk K A hA := by
  refine ⟨⟨c⁻¹ • A, by simp [← hc, hc0]⟩, rfl, ?_⟩
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).2 ⟨c⁻¹, rfl⟩

/-- The line of a nonzero matrix `A` comes from `PSL(n, K)` exactly when `det A` is the `n`-th
power of a unit. -/
theorem mk_mem_range_toProjectivization_iff {A : Matrix n n K} (hA : A ≠ 0) :
    Projectivization.mk K A hA ∈ Set.range (toProjectivization n K) ↔
      ∃ c : Kˣ, (c : K) ^ Fintype.card n = A.det := by
  constructor
  · rintro ⟨g, hg⟩
    induction g using QuotientGroup.induction_on with | H B => ?_
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).1 hg
    have hdet := congrArg det ha
    rw [Units.smul_def, det_smul, B.det_coe] at hdet
    exact ⟨a⁻¹, by simpa using (eq_inv_of_mul_eq_one_right hdet).symm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨B, -, hB⟩ := exists_coe_eq_inv_smul_of_pow_eq_det hA c.ne_zero hc
    exact ⟨B, hB⟩

/-- Over an algebraically closed field, the image of `PSL(n, K)` in the projective space of
matrices is the locus of lines of invertible matrices. -/
theorem range_toProjectivization [IsAlgClosed K] :
    Set.range (toProjectivization n K) = {x | x.rep.det ≠ 0} := by
  ext x
  induction x using Projectivization.ind with | h A hA => ?_
  rw [mk_mem_range_toProjectivization_iff, Set.mem_ofPred_eq, det_rep_mk_ne_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact hc ▸ pow_ne_zero _ c.ne_zero
  · intro h
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq A.det (Fintype.card_pos (α := n))
    exact ⟨Units.mk0 c (by rintro rfl; exact h (by rw [← hc, zero_pow Fintype.card_ne_zero])), hc⟩

end Field

end ProjectiveSpecialLinearGroup

end Matrix
