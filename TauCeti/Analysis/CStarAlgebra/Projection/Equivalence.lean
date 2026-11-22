/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import TauCeti.Algebra.Star.Projection.Basic

/-!
# Rectangular Murray–von Neumann equivalence

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular matrix. The index types may differ, so this relation identifies
a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, compatibility with block sums,
and preservation by nonunital star homomorphisms. These are the relations needed to form the
projection monoid. No unit, separability, or cancellation is assumed.

The algebraic matrix calculations use Mathlib's underlying `Matrix` operations, which are the
operations used to define `CStarMatrix` multiplication and conjugate transpose.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, §4.6 (Definition 4.6.1) and §5.1.
-/

public section

open scoped Matrix

namespace CStarMatrix

variable {A B m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

section Algebraic

variable [NonUnitalSemiring A] [StarRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A} {r : CStarMatrix k k A}

/-- An ordinary matrix star projection lifts to a `CStarMatrix` star projection. -/
theorem isStarProjection_ofMatrix {p : Matrix m m A} (hp : IsStarProjection p) :
    IsStarProjection (ofMatrix p) := by
  rw [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint]
  exact ⟨ofMatrix.symm.injective (by simpa [ofMatrix_symm_mul] using hp.isIdempotentElem.eq),
    ofMatrix.symm.injective (by
      simpa [ofMatrix_symm_star, ← Matrix.star_eq_conjTranspose] using hp.isSelfAdjoint.star_eq)⟩

/-- Viewing a `CStarMatrix` star projection as an ordinary matrix gives a star projection. -/
theorem isStarProjection_ofMatrix_symm {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    IsStarProjection (ofMatrix.symm p) := by
  rw [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint]
  exact ⟨by simpa [ofMatrix_symm_mul] using congrArg ofMatrix.symm hp.isIdempotentElem.eq,
    by simpa [ofMatrix_symm_star, Matrix.star_eq_conjTranspose] using
      congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq⟩

/-- Two matrix projections are Murray–von Neumann equivalent when a rectangular matrix has
them as its initial and final projections. The projection conditions are part of the relation. -/
def MurrayVonNeumannEquiv (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

/-- Murray–von Neumann equivalence of ordinary matrices transports to `CStarMatrix`. -/
theorem murrayVonNeumannEquiv_ofMatrix {p : Matrix m m A} {q : Matrix n n A}
    (h : Matrix.IsMurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquiv (ofMatrix p) (ofMatrix q) := by
  obtain ⟨v, hv₁, hv₂⟩ := h.exists_conjTranspose_mul_self_eq
  exact ⟨isStarProjection_ofMatrix h.isStarProjection_left,
    isStarProjection_ofMatrix h.isStarProjection_right, ofMatrix v,
    ofMatrix.symm.injective (by simpa [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using hv₁),
    ofMatrix.symm.injective (by simpa [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using hv₂)⟩

/-- Viewing a `CStarMatrix` Murray–von Neumann equivalence as an ordinary matrix equivalence. -/
theorem isMurrayVonNeumannEquivalent_ofMatrix_symm {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  obtain ⟨hp, hq, v, hv₁, hv₂⟩ := h
  exact ⟨isStarProjection_ofMatrix_symm hp, isStarProjection_ofMatrix_symm hq, ofMatrix.symm v,
    by simpa [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hv₁,
    by simpa [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hv₂⟩

/-- `CStarMatrix.MurrayVonNeumannEquiv` agrees with `Matrix.IsMurrayVonNeumannEquivalent` under
`ofMatrix`. -/
theorem murrayVonNeumannEquiv_ofMatrix_iff {p : Matrix m m A} {q : Matrix n n A} :
    MurrayVonNeumannEquiv (ofMatrix p) (ofMatrix q) ↔ Matrix.IsMurrayVonNeumannEquivalent p q :=
  ⟨fun h => by
      simpa only [Equiv.symm_apply_apply] using isMurrayVonNeumannEquivalent_ofMatrix_symm h,
    murrayVonNeumannEquiv_ofMatrix⟩

namespace MurrayVonNeumannEquiv

/-- The initial matrix of a Murray–von Neumann equivalence is a projection. -/
theorem isStarProjection_left (h : MurrayVonNeumannEquiv p q) : IsStarProjection p :=
  h.1

/-- The final matrix of a Murray–von Neumann equivalence is a projection. -/
theorem isStarProjection_right (h : MurrayVonNeumannEquiv p q) : IsStarProjection q :=
  h.2.1

/-- Extract a rectangular implementing matrix. -/
theorem exists_matrix (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  h.2.2

/-- Every matrix projection is Murray–von Neumann equivalent to itself. -/
protected theorem refl (hp : IsStarProjection p) : MurrayVonNeumannEquiv p p :=
  ⟨hp, hp, p, by simpa only [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using
    hp.isIdempotentElem.eq, by simpa only [← star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq] using hp.isIdempotentElem.eq⟩

/-- Rectangular Murray–von Neumann equivalence is symmetric. -/
protected theorem symm (h : MurrayVonNeumannEquiv p q) : MurrayVonNeumannEquiv q p := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  exact ⟨hq, hp, v.conjTranspose, by simpa using hv', by simpa using hv⟩

/-- Zero projections of any two finite sizes are equivalent. -/
protected theorem zero : MurrayVonNeumannEquiv (0 : CStarMatrix m m A)
    (0 : CStarMatrix n n A) :=
  ⟨.zero _, .zero _, 0, by simp, by simp⟩

/-- Block-diagonal sums of equivalent projections are equivalent. -/
theorem fromBlocks {p' : CStarMatrix k k A} {q' : CStarMatrix l l A}
    (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv p' q') :
    MurrayVonNeumannEquiv (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (ofMatrix.symm p')))
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm q) 0 0 (ofMatrix.symm q'))) :=
  murrayVonNeumannEquiv_ofMatrix
    ((isMurrayVonNeumannEquivalent_ofMatrix_symm h).fromBlocks
      (isMurrayVonNeumannEquivalent_ofMatrix_symm h'))

/-- A nonunital star ring homomorphism preserves rectangular equivalence entrywise. -/
theorem map [NonUnitalSemiring B] [StarRing B] {F : Type*} [FunLike F A B]
    [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (h : MurrayVonNeumannEquiv p q) (f : F) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) := by
  have hp : p.map f = ofMatrix ((ofMatrix.symm p).map f) := rfl
  have hq : q.map f = ofMatrix ((ofMatrix.symm q).map f) := rfl
  rw [hp, hq]
  exact murrayVonNeumannEquiv_ofMatrix ((isMurrayVonNeumannEquivalent_ofMatrix_symm h).map f)

/-- Padding a projection by a zero block does not change its rectangular equivalence class. -/
theorem pad_zero (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix k k A)) := by
  have h := murrayVonNeumannEquiv_ofMatrix
    ((isStarProjection_ofMatrix_symm hp).isMurrayVonNeumannEquivalent_fromBlocks_zero (n := k))
  simpa only [of_fromBlocks, of_zero, Equiv.apply_symm_apply] using h

/-- A Murray–von Neumann equivalence is implemented by a matrix supported on its initial
projection. -/
theorem exists_matrix_mul_eq_self (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A,
      v.conjTranspose * v = p ∧ v * v.conjTranspose = q ∧ v * p = v := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hpc : p.conjTranspose = p := by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  refine ⟨v * p, ?_, ?_, by rw [mul_assoc_rectangular, hpp]⟩
  · calc
      _ = p * (v.conjTranspose * v) * p := by
        simp only [conjTranspose_mul, hpc, mul_assoc_rectangular]
      _ = p := by rw [hv, hpp, hpp]
  · calc
      _ = v * (p * p) * v.conjTranspose := by
        simp only [conjTranspose_mul, hpc, mul_assoc_rectangular]
      _ = (v * v.conjTranspose) * (v * v.conjTranspose) := by
        rw [hpp, ← hv]
        simp only [mul_assoc_rectangular]
      _ = q := by rw [hv', hq.isIdempotentElem.eq]

/-- Rectangular Murray–von Neumann equivalence is transitive. -/
protected theorem trans (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r := by
  obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
  obtain ⟨w, hw, hw', hwq⟩ := h'.exists_matrix_mul_eq_self
  have hqv : q * v = v := by
    rw [← hv', mul_assoc_rectangular, hv, hvp]
  refine ⟨h.isStarProjection_left, h'.isStarProjection_right, w * v, ?_, ?_⟩
  · calc
      _ = v.conjTranspose * (w.conjTranspose * w) * v := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = v.conjTranspose * v := by rw [hw, mul_assoc_rectangular, hqv]
      _ = p := hv
  · calc
      _ = w * (v * v.conjTranspose) * w.conjTranspose := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = w * w.conjTranspose := by rw [hv', hwq]
      _ = r := hw'

end MurrayVonNeumannEquiv

/-- The witness criterion for Murray–von Neumann equivalence of given projections. -/
theorem murrayVonNeumannEquiv_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_matrix, fun h => ⟨hp, hq, h⟩⟩

/-- Reflexivity characterizes the matrices on which the relation is defined. -/
@[simp]
theorem murrayVonNeumannEquiv_self_iff : MurrayVonNeumannEquiv p p ↔ IsStarProjection p :=
  ⟨MurrayVonNeumannEquiv.isStarProjection_left, MurrayVonNeumannEquiv.refl⟩

/-- For equal matrix sizes, two matrices are Murray–von Neumann equivalent if and only if they
are the initial and final projections of some partial isometry. -/
theorem murrayVonNeumannEquiv_iff_exists_partialIsometry {q : CStarMatrix m m A} :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix m m A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧
        v * star v = q := by
  constructor
  · intro h
    obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
    simp only [← star_eq_conjTranspose] at hv hv'
    refine ⟨v, ?_, hv, hv'⟩
    rw [TauCeti.isPartialIsometry_iff, mul_assoc, hv]
    exact hvp
  · rintro ⟨v, hv, rfl, rfl⟩
    exact ⟨hv.isStarProjection_star_mul_self, hv.isStarProjection_mul_star_self, v,
      by rw [star_eq_conjTranspose], by rw [star_eq_conjTranspose]⟩

/-- Only the zero projection is equivalent to a zero projection, in any matrix size. -/
@[simp]
theorem murrayVonNeumannEquiv_zero_iff :
    MurrayVonNeumannEquiv p (0 : CStarMatrix n n A) ↔ p = 0 := by
  refine ⟨?_, fun h => h ▸ .zero⟩
  rintro ⟨hp, _, v, hv, hv'⟩
  calc
    p = p * p := hp.isIdempotentElem.eq.symm
    _ = v.conjTranspose * (v * v.conjTranspose) * v := by
      rw [← hv]
      simp only [mul_assoc_rectangular]
    _ = 0 := by rw [hv', CStarMatrix.mul_zero, CStarMatrix.zero_mul]

/-- Only zero is equivalent to the zero projection on the initial side. -/
@[simp]
theorem zero_murrayVonNeumannEquiv_iff :
    MurrayVonNeumannEquiv (0 : CStarMatrix n n A) p ↔ p = 0 :=
  ⟨fun h => murrayVonNeumannEquiv_zero_iff.mp h.symm,
    fun h => h ▸ MurrayVonNeumannEquiv.zero⟩

end Algebraic

/-- Unitary conjugacy implies Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_unitary_conj [Semiring B] [StarRing B] [DecidableEq m]
    {p : CStarMatrix m m B} (hp : IsStarProjection p) (u : unitary (CStarMatrix m m B)) :
    MurrayVonNeumannEquiv p ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) := by
  have hq : IsStarProjection ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) :=
    ⟨by simp only [IsIdempotentElem, mul_assoc,
        ← mul_assoc (star (u : CStarMatrix m m B)), Unitary.coe_star_mul_self,
        one_mul, ← mul_assoc p, hp.isIdempotentElem.eq], hp.isSelfAdjoint.conjugate u⟩
  refine ⟨hp, hq, (u : CStarMatrix m m B) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]
    exact hp.star_mul_mul_self_of_mem_unitary u.property
  · rw [← star_eq_conjTranspose]
    exact hp.mul_star_mul_eq_mul_mul_star _

end CStarMatrix
