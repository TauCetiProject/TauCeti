/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
  let : CharZero K := RingHom.charZero w.1.embedding
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  have hlocal : (Q.atRealPlace w).Equivalent (R.atRealPlace w) := by
    simpa only [atRealPlace_def] using h.baseChange ℝ
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

end QuadraticForm
