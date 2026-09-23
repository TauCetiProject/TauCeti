/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization

/-!
# Signatures of quadratic forms at real places

This file packages the positive and negative indices of the localization of a quadratic form at a
real place.  The projections are the real-place invariants used in the local-global theory of
quadratic forms over number fields.

The signature is invariant under equivalence, additive under orthogonal products, exchanges its
components under negation or negative scaling, and is unchanged by positive scaling.  For a
nondegenerate form, the two indices add to the global rank.

Sylvester's law of inertia turns that invariant into a complete one: at a real place regular
forms are isometric exactly when their signatures agree, so at a fixed global rank the positive
index alone separates them, and the localization is isometric to the normal form
`QuadraticForm.realSignatureForm p q` exactly when `(p, q)` is its signature.  This is the real
half of the archimedean classification; the complex half is in
`TauCeti.NumberTheory.QuadraticForm.Global.ComplexPlaces`.

## Main definitions

* `QuadraticForm.realSignature`: the positive and negative indices at a real place.
* `QuadraticForm.realPositiveIndex`: the positive component of the real signature.
* `QuadraticForm.realNegativeIndex`: the negative component of the real signature.

## Main results

* `QuadraticForm.realPositiveIndex_add_realNegativeIndex_eq_finrank`: the indices of a
  nondegenerate form add to its rank.
* `QuadraticMap.Equivalent.realSignature_eq`: equivalent forms have equal real signatures.
* `QuadraticForm.realSignature_prod`: real-place signatures are additive under orthogonal
  products.
* `QuadraticForm.equivalent_atRealPlace_iff_realSignature_eq`: at a real place regular forms are
  classified by their signature.
* `QuadraticForm.equivalent_atRealPlace_iff_realPositiveIndex_eq_of_finrank_eq`: at a fixed
  global rank the positive index alone classifies them.
* `QuadraticForm.equivalent_atRealPlace_realSignatureForm_iff_realSignature_eq` and
  `QuadraticForm.equivalent_atRealPlace_realSignatureForm`: the localization is the normal form
  `p⟨1⟩ ⊥ q⟨-1⟩` exactly when `(p, q)` is its signature, hence is always the normal form of its
  own signature.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), §61 for the archimedean
  classification.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace

universe u v v'

namespace QuadraticForm

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The pair consisting of the positive and negative indices of a quadratic form at a real
place. -/
def realSignature (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) : ℕ × ℕ :=
  (sigPos (Q.atRealPlace w), sigNeg (Q.atRealPlace w))

/-- The positive index of a quadratic form at a real place. -/
def realPositiveIndex (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) : ℕ :=
  (Q.realSignature w).1

/-- The negative index of a quadratic form at a real place. -/
def realNegativeIndex (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) : ℕ :=
  (Q.realSignature w).2

/-- The first component of the real signature is the positive index. -/
@[simp]
theorem realSignature_fst (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.realSignature w).1 = Q.realPositiveIndex w := by
  simp [realPositiveIndex]

/-- The second component of the real signature is the negative index. -/
@[simp]
theorem realSignature_snd (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.realSignature w).2 = Q.realNegativeIndex w := by
  simp [realNegativeIndex]

/-- The real signature is a prescribed pair exactly when the two indices are its components. -/
@[simp]
theorem realSignature_eq_iff (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) (p q : ℕ) :
    Q.realSignature w = (p, q) ↔ Q.realPositiveIndex w = p ∧ Q.realNegativeIndex w = q := by
  rw [Prod.ext_iff, realSignature_fst, realSignature_snd]

/-- The positive index at a real place is Mathlib's positive index of the localized form. -/
theorem realPositiveIndex_eq_sigPos (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Q.realPositiveIndex w = sigPos (Q.atRealPlace w) := by
  simp [realPositiveIndex, realSignature]

/-- The negative index at a real place is Mathlib's negative index of the localized form. -/
theorem realNegativeIndex_eq_sigNeg (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Q.realNegativeIndex w = sigNeg (Q.atRealPlace w) := by
  simp [realNegativeIndex, realSignature]

/-- The positive and negative indices of a nondegenerate form at a real place add to its global
rank. -/
theorem realPositiveIndex_add_realNegativeIndex_eq_finrank [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Q.realPositiveIndex w + Q.realNegativeIndex w = Module.finrank K V := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  have hlocal : (Q.atRealPlace w).Nondegenerate := by
    rw [atRealPlace_def]
    exact QuadraticForm.Nondegenerate.baseChange hQ
  have hsum := sigPos_add_sigNeg_add_radical (Q := Q.atRealPlace w)
  rw [hlocal.radical_eq_bot, finrank_bot, add_zero, Module.finrank_baseChange] at hsum
  simpa only [realPositiveIndex_eq_sigPos, realNegativeIndex_eq_sigNeg] using hsum

variable {W : Type v'} [AddCommGroup W] [Module K W]
variable {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}

/-- Equivalent quadratic forms have the same signature at every real place. -/
theorem _root_.QuadraticMap.Equivalent.realSignature_eq (h : Q.Equivalent R)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Q.realSignature w = R.realSignature w := by
  have hlocal := h.atRealPlace w
  apply Prod.ext
  · simpa only [realSignature_fst, realPositiveIndex_eq_sigPos] using hlocal.sigPos_eq
  · simpa only [realSignature_snd, realNegativeIndex_eq_sigNeg] using hlocal.sigNeg_eq

/-- Equivalent quadratic forms have the same positive index at every real place. -/
theorem _root_.QuadraticMap.Equivalent.realPositiveIndex_eq (h : Q.Equivalent R)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Q.realPositiveIndex w = R.realPositiveIndex w := by
  rw [← realSignature_fst Q w, ← realSignature_fst R w, h.realSignature_eq w]

/-- Equivalent quadratic forms have the same negative index at every real place. -/
theorem _root_.QuadraticMap.Equivalent.realNegativeIndex_eq (h : Q.Equivalent R)
    (w : {w : InfinitePlace K // w.IsReal}) :
    Q.realNegativeIndex w = R.realNegativeIndex w := by
  rw [← realSignature_snd Q w, ← realSignature_snd R w, h.realSignature_eq w]

section Prod

/-- The positive index at a real place is additive under orthogonal products. -/
@[simp]
theorem realPositiveIndex_prod (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (w : {w : InfinitePlace K // w.IsReal})
    [FiniteDimensional ℝ (TauCeti.RealScalarExtension (V := V) w)]
    [FiniteDimensional ℝ (TauCeti.RealScalarExtension (V := W) w)] :
    realPositiveIndex (Q.prod R) w = Q.realPositiveIndex w + R.realPositiveIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  have hlocal : (atRealPlace (Q.prod R) w).Equivalent
      ((Q.atRealPlace w).prod (R.atRealPlace w)) := by
    simpa only [atRealPlace_def] using
      ⟨baseChangeProd (A := ℝ) Q R⟩
  rw [realPositiveIndex_eq_sigPos, hlocal.sigPos_eq, sigPos_prod,
    ← realPositiveIndex_eq_sigPos, ← realPositiveIndex_eq_sigPos]

/-- The negative index at a real place is additive under orthogonal products. -/
@[simp]
theorem realNegativeIndex_prod (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (w : {w : InfinitePlace K // w.IsReal})
    [FiniteDimensional ℝ (TauCeti.RealScalarExtension (V := V) w)]
    [FiniteDimensional ℝ (TauCeti.RealScalarExtension (V := W) w)] :
    realNegativeIndex (Q.prod R) w = Q.realNegativeIndex w + R.realNegativeIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  have hlocal : (atRealPlace (Q.prod R) w).Equivalent
      ((Q.atRealPlace w).prod (R.atRealPlace w)) := by
    simpa only [atRealPlace_def] using
      ⟨baseChangeProd (A := ℝ) Q R⟩
  rw [realNegativeIndex_eq_sigNeg, hlocal.sigNeg_eq, sigNeg_prod,
    ← realNegativeIndex_eq_sigNeg, ← realNegativeIndex_eq_sigNeg]

/-- The real signature of an orthogonal product is the componentwise sum of the signatures. -/
@[simp]
theorem realSignature_prod (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (w : {w : InfinitePlace K // w.IsReal})
    [FiniteDimensional ℝ (TauCeti.RealScalarExtension (V := V) w)]
    [FiniteDimensional ℝ (TauCeti.RealScalarExtension (V := W) w)] :
    realSignature (Q.prod R) w =
      (Q.realPositiveIndex w + R.realPositiveIndex w,
        Q.realNegativeIndex w + R.realNegativeIndex w) := by
  apply Prod.ext
  · simpa only [realSignature_fst] using realPositiveIndex_prod Q R w
  · simpa only [realSignature_snd] using realNegativeIndex_prod Q R w

end Prod

/-- Negation exchanges the positive and negative indices at a real place. -/
@[simp]
theorem realPositiveIndex_neg (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (-Q).realPositiveIndex w = Q.realNegativeIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [realPositiveIndex_eq_sigPos, realNegativeIndex_eq_sigNeg, atRealPlace_def,
    atRealPlace_def, baseChange_neg, sigPos_neg]

/-- Negation exchanges the negative and positive indices at a real place. -/
@[simp]
theorem realNegativeIndex_neg (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (-Q).realNegativeIndex w = Q.realPositiveIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [realNegativeIndex_eq_sigNeg, realPositiveIndex_eq_sigPos, atRealPlace_def,
    atRealPlace_def, baseChange_neg, sigNeg_neg]

/-- Negation exchanges the two components of the real signature. -/
@[simp]
theorem realSignature_neg (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (-Q).realSignature w = (Q.realNegativeIndex w, Q.realPositiveIndex w) := by
  apply Prod.ext
  · simpa only [realSignature_fst] using realPositiveIndex_neg Q w
  · simpa only [realSignature_snd] using realNegativeIndex_neg Q w

section Scaling

variable (Q : _root_.QuadraticForm K V) (w : {w : InfinitePlace K // w.IsReal}) (a : K)
variable [FiniteDimensional ℝ (TauCeti.RealScalarExtension (V := V) w)]

/-- Scaling by a scalar positive at a real place preserves its positive index. -/
@[simp]
theorem realPositiveIndex_smul_of_pos (ha : 0 < embedding_of_isReal w.2 a) :
    (a • Q).realPositiveIndex w = Q.realPositiveIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [realPositiveIndex_eq_sigPos, realPositiveIndex_eq_sigPos, atRealPlace_def,
    atRealPlace_def, baseChange_smul, RingHom.algebraMap_toAlgebra,
    sigPos_smul_of_pos _ ha]

/-- Scaling by a scalar positive at a real place preserves its negative index. -/
@[simp]
theorem realNegativeIndex_smul_of_pos (ha : 0 < embedding_of_isReal w.2 a) :
    (a • Q).realNegativeIndex w = Q.realNegativeIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [realNegativeIndex_eq_sigNeg, realNegativeIndex_eq_sigNeg, atRealPlace_def,
    atRealPlace_def, baseChange_smul, RingHom.algebraMap_toAlgebra,
    sigNeg_smul_of_pos _ ha]

/-- Scaling by a scalar positive at a real place preserves its signature. -/
@[simp]
theorem realSignature_smul_of_pos (ha : 0 < embedding_of_isReal w.2 a) :
    (a • Q).realSignature w = Q.realSignature w := by
  apply Prod.ext
  · simpa only [realSignature_fst] using realPositiveIndex_smul_of_pos Q w a ha
  · simpa only [realSignature_snd] using realNegativeIndex_smul_of_pos Q w a ha

/-- Scaling by a scalar negative at a real place exchanges the positive and negative indices. -/
@[simp]
theorem realPositiveIndex_smul_of_neg (ha : embedding_of_isReal w.2 a < 0) :
    (a • Q).realPositiveIndex w = Q.realNegativeIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [realPositiveIndex_eq_sigPos, realNegativeIndex_eq_sigNeg, atRealPlace_def,
    atRealPlace_def, baseChange_smul, RingHom.algebraMap_toAlgebra,
    sigPos_smul_of_neg _ ha]

/-- Scaling by a scalar negative at a real place exchanges the negative and positive indices. -/
@[simp]
theorem realNegativeIndex_smul_of_neg (ha : embedding_of_isReal w.2 a < 0) :
    (a • Q).realNegativeIndex w = Q.realPositiveIndex w := by
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [realNegativeIndex_eq_sigNeg, realPositiveIndex_eq_sigPos, atRealPlace_def,
    atRealPlace_def, baseChange_smul, RingHom.algebraMap_toAlgebra,
    sigNeg_smul_of_neg _ ha]

/-- Scaling by a scalar negative at a real place exchanges the signature components. -/
@[simp]
theorem realSignature_smul_of_neg (ha : embedding_of_isReal w.2 a < 0) :
    (a • Q).realSignature w = (Q.realNegativeIndex w, Q.realPositiveIndex w) := by
  apply Prod.ext
  · simpa only [realSignature_fst] using realPositiveIndex_smul_of_neg Q w a ha
  · simpa only [realSignature_snd] using realNegativeIndex_smul_of_neg Q w a ha

end Scaling

section Classification

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- **Sylvester's law of inertia at a real place.** Two regular quadratic forms become isometric
at a real place exactly when their signatures there agree. -/
@[simp]
theorem equivalent_atRealPlace_iff_realSignature_eq (hQ : Q.Nondegenerate) (hR : R.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace w).Equivalent (R.atRealPlace w) ↔ Q.realSignature w = R.realSignature w := by
  rw [equivalent_iff_sigPos_eq_and_sigNeg_eq (Nondegenerate.atRealPlace hQ w)
    (Nondegenerate.atRealPlace hR w)]
  simp only [Prod.ext_iff, realSignature_fst, realSignature_snd, realPositiveIndex_eq_sigPos,
    realNegativeIndex_eq_sigNeg]

/-- At a real place the positive index is already a complete invariant of regular forms of equal
global rank, because the negative index is the rank minus the positive index. -/
theorem equivalent_atRealPlace_iff_realPositiveIndex_eq_of_finrank_eq (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) (hrank : Module.finrank K V = Module.finrank K W)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace w).Equivalent (R.atRealPlace w) ↔
      Q.realPositiveIndex w = R.realPositiveIndex w := by
  have hQsum := realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w
  have hRsum := realPositiveIndex_add_realNegativeIndex_eq_finrank hR w
  rw [equivalent_atRealPlace_iff_realSignature_eq hQ hR w]
  simp only [Prod.ext_iff, realSignature_fst, realSignature_snd]
  omega

/-- A regular quadratic form is isometric at a real place to the normal form `p⟨1⟩ ⊥ q⟨-1⟩`
exactly when `(p, q)` is its signature there. -/
@[simp]
theorem equivalent_atRealPlace_realSignatureForm_iff_realSignature_eq (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) (p q : ℕ) :
    (Q.atRealPlace w).Equivalent (realSignatureForm p q) ↔ Q.realSignature w = (p, q) := by
  rw [equivalent_realSignatureForm_iff_sigPos_eq_and_sigNeg_eq
    (Nondegenerate.atRealPlace hQ w), realSignature_eq_iff, realPositiveIndex_eq_sigPos,
    realNegativeIndex_eq_sigNeg]

/-- A regular quadratic form is isometric at a real place to the normal form of its signature
there. -/
theorem equivalent_atRealPlace_realSignatureForm (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace w).Equivalent
      (realSignatureForm (Q.realPositiveIndex w) (Q.realNegativeIndex w)) :=
  (equivalent_atRealPlace_realSignatureForm_iff_realSignature_eq hQ w _ _).mpr (by simp)

end Classification

end QuadraticForm
