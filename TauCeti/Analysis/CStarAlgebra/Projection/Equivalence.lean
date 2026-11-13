/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.LinearAlgebra.Matrix.PartialIsometry
import TauCeti.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.ColumnRowPartitioned

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

* B. Blackadar, *K-Theory for Operator Algebras*, Definition 4.6.1 and Propositions 4.6.2–4.6.6.
-/

public section

open scoped Matrix

namespace CStarMatrix

variable {A B m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

section Algebraic

variable [NonUnitalRing A] [StarRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A} {r : CStarMatrix k k A}

/-- Two matrix projections are Murray–von Neumann equivalent when a rectangular matrix has
them as its initial and final projections. The projection conditions are part of the relation. -/
def MurrayVonNeumannEquiv (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

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

/-- Every matrix projection is equivalent to itself, implemented by the projection. -/
protected theorem refl (hp : IsStarProjection p) : MurrayVonNeumannEquiv p p :=
  ⟨hp, hp, p, by simpa only [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using
    hp.isIdempotentElem.eq, by simpa only [← star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq] using hp.isIdempotentElem.eq⟩

/-- Adjointing the rectangular implementing matrix reverses equivalence. -/
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
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm q) 0 0 (ofMatrix.symm q'))) := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  obtain ⟨hp', hq', w, hw, hw'⟩ := h'
  refine ⟨⟨hp.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ hp'.isIdempotentElem,
    hp.isSelfAdjoint.isHermitian.fromBlocks (by simp) hp'.isSelfAdjoint.isHermitian⟩,
    ⟨hq.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ hq'.isIdempotentElem,
      hq.isSelfAdjoint.isHermitian.fromBlocks (by simp) hq'.isSelfAdjoint.isHermitian⟩,
    ofMatrix (Matrix.fromBlocks (ofMatrix.symm v) 0 0 (ofMatrix.symm w)), ?_, ?_⟩
  · apply ofMatrix.symm.injective
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      using congrArg₂ (fun x y => Matrix.fromBlocks x 0 0 y)
        (congrArg ofMatrix.symm hv) (congrArg ofMatrix.symm hw)
  · apply ofMatrix.symm.injective
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      using congrArg₂ (fun x y => Matrix.fromBlocks x 0 0 y)
        (congrArg ofMatrix.symm hv') (congrArg ofMatrix.symm hw')

/-- A nonunital star algebra homomorphism preserves rectangular equivalence entrywise. -/
theorem map {R : Type*} [Semiring R] [Module R A]
    [NonUnitalRing B] [StarRing B] [Module R B]
    (h : MurrayVonNeumannEquiv p q) (f : A →⋆ₙₐ[R] B) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  refine ⟨hp.map (mapₙₐ f), hq.map (mapₙₐ f), v.map f, ?_, ?_⟩
  · ext i j
    simpa only [map_apply, mul_apply, conjTranspose_apply, map_sum, map_mul,
      map_star] using congrArg f (congrFun (congrFun hv i) j)
  · ext i j
    simpa only [map_apply, mul_apply, conjTranspose_apply, map_sum, map_mul,
      map_star] using congrArg f (congrFun (congrFun hv' i) j)

/-- Padding a projection by a zero block does not change its rectangular equivalence class. -/
theorem pad_zero (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (0 : Matrix k k A))) := by
  have hsa : (ofMatrix.symm p)ᴴ = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_star] using congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq
  have hid : ofMatrix.symm p * ofMatrix.symm p = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_mul] using congrArg ofMatrix.symm hp.isIdempotentElem.eq
  refine ⟨hp, ⟨hp.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ .zero,
    hp.isSelfAdjoint.isHermitian.fromBlocks (by simp) Matrix.isHermitian_zero⟩,
    ofMatrix (Matrix.fromRows (ofMatrix.symm p) (0 : Matrix k m A)), ?_, ?_⟩ <;>
    apply ofMatrix.symm.injective
  · simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_zero, hsa]
    ext i j
    simpa [Matrix.mul_apply] using congrFun (congrFun hid i) j
  · simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_zero, hsa]
    ext (i | i) (j | j)
    · simpa [Matrix.mul_apply] using congrFun (congrFun hid i) j
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]

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

end Algebraic

section OrderedStar

variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A} {r : CStarMatrix k k A}

/-- An implementing rectangular matrix is supported on its initial projection. -/
theorem mul_eq_self_of_conjTranspose_mul_eq (v : CStarMatrix n m A)
    (hp : IsIdempotentElem p) (hv : v.conjTranspose * v = p) : v * p = v := by
  have hp' : IsIdempotentElem (v.conjTranspose * v) := by
    rw [hv]
    exact hp
  have hpM := congrArg ofMatrix.symm hp'.eq
  simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] at hpM
  have h := Matrix.mul_conjTranspose_mul_self_of_isIdempotentElem (ofMatrix.symm v) hpM
  rw [← hv]
  apply ofMatrix.symm.injective
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Matrix.mul_assoc] using h

namespace MurrayVonNeumannEquiv

/-- Rectangular equivalence is transitive; compose the implementing matrices. -/
protected theorem trans (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  obtain ⟨_, hr, w, hw, hw'⟩ := h'
  have hwp := mul_eq_self_of_conjTranspose_mul_eq w hq.isIdempotentElem hw
  have hvp := mul_eq_self_of_conjTranspose_mul_eq v hp.isIdempotentElem hv
  have hqv : q * v = v := by
    rw [← hv', mul_assoc_rectangular, hv, hvp]
  refine ⟨hp, hr, w * v, ?_, ?_⟩
  · calc
      _ = v.conjTranspose * (w.conjTranspose * w) * v := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = v.conjTranspose * v := by rw [hw, mul_assoc_rectangular, hqv]
      _ = p := hv
  · calc
      _ = w * (v * v.conjTranspose) * w.conjTranspose := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = w * w.conjTranspose := by rw [hv', hwp]
      _ = r := hw'

end MurrayVonNeumannEquiv

/-- For equal matrix sizes, the implementing matrices are exactly partial isometries with the
specified initial and final projections. -/
theorem murrayVonNeumannEquiv_iff_exists_partialIsometry {q : CStarMatrix m m A} :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix m m A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧
        v * star v = q := by
  constructor
  · rintro ⟨hp, _, v, hv, hv'⟩
    have hvp := mul_eq_self_of_conjTranspose_mul_eq v hp.isIdempotentElem hv
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
  rintro ⟨_, _, v, hv, hv'⟩
  have h := congrArg ofMatrix.symm hv'
  simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] at h
  have hz : ofMatrix.symm v = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp h
  have hv0 : v = 0 := by
    ext i j
    exact congrFun (congrFun hz i) j
  simpa only [hv0, conjTranspose_zero, CStarMatrix.zero_mul] using hv.symm

/-- Only zero is equivalent to the zero projection on the initial side. -/
@[simp]
theorem zero_murrayVonNeumannEquiv_iff :
    MurrayVonNeumannEquiv (0 : CStarMatrix n n A) p ↔ p = 0 :=
  ⟨fun h => murrayVonNeumannEquiv_zero_iff.mp h.symm,
    fun h => h ▸ MurrayVonNeumannEquiv.zero⟩


end OrderedStar

/-- Unitary conjugacy implies Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_unitary_conj [Ring B] [StarRing B] [DecidableEq m]
    {p : CStarMatrix m m B} (hp : IsStarProjection p) (u : unitary (CStarMatrix m m B)) :
    MurrayVonNeumannEquiv p ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) := by
  have hq : IsStarProjection ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) :=
    ⟨by simp only [IsIdempotentElem, mul_assoc,
        ← mul_assoc (star (u : CStarMatrix m m B)), Unitary.coe_star_mul_self,
        one_mul, ← mul_assoc p, hp.isIdempotentElem.eq], hp.isSelfAdjoint.conjugate u⟩
  refine ⟨hp, hq, (u : CStarMatrix m m B) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq]
    simp only [mul_assoc, ← mul_assoc (star (u : CStarMatrix m m B)),
      Unitary.coe_star_mul_self, one_mul, hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq]
    simp only [mul_assoc, ← mul_assoc p, hp.isIdempotentElem.eq]


end CStarMatrix
