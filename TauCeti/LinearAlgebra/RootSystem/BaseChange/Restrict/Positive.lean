/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Base
public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# Root heights and positive roots under scalar restriction

This file proves that root heights, root positivity, and the positive and negative root sets and
finsets of a restricted base `b.restrictScalars' K` coincide with those of `b`.

## Main results

* `RootPairing.Base.height_restrictScalars'` and `RootPairing.Base.isPos_restrictScalars'_iff`:
  heights and positivity agree under scalar restriction.
* `RootPairing.posRoots_restrictScalars'`, `RootPairing.negRoots_restrictScalars'`,
  `RootPairing.posRootsFinset_restrictScalars'`, and `RootPairing.negRootsFinset_restrictScalars'`:
  equality of positive and negative root sets and finsets.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

open TauCeti

namespace RootPairing

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  {P : RootPairing ι L M N} (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K] (b : P.Base)

/-- Root heights with respect to `b.restrictScalars' K` agree with those with respect to `b`. -/
@[simp]
theorem Base.height_restrictScalars' [CharZero K] [CharZero L] (i : ι) :
    (b.restrictScalars' K).height i = b.height i := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  have hfK : (P.restrictScalars' K).root i =
      ∑ j ∈ (b.restrictScalars' K).support, f j • (P.restrictScalars' K).root j := by
    ext; simpa using hf
  rw [(b.restrictScalars' K).height_eq_sum hfK, b.height_eq_sum hf, support_restrictScalars']

/-- Positivity of a root index with respect to `b.restrictScalars' K` agrees with positivity with
respect to `b`. -/
@[simp]
theorem Base.isPos_restrictScalars'_iff [CharZero K] [CharZero L] (i : ι) :
    (b.restrictScalars' K).IsPos i ↔ b.IsPos i := by
  simp only [Base.isPos_iff, Base.height_restrictScalars']

/-- The set of positive roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem posRoots_restrictScalars' [CharZero K] [CharZero L] :
    posRoots (P.restrictScalars' K) (b.restrictScalars' K) = posRoots P b := by
  ext i
  simp only [mem_posRoots, Base.isPos_restrictScalars'_iff]

/-- The set of negative roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem negRoots_restrictScalars' [CharZero K] [CharZero L] :
    negRoots (P.restrictScalars' K) (b.restrictScalars' K) = negRoots P b := by
  ext i
  simp only [mem_negRoots, Base.isPos_restrictScalars'_iff]

/-- The finset of positive roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem posRootsFinset_restrictScalars' [Finite ι] [CharZero K] [CharZero L] :
    posRootsFinset (P.restrictScalars' K) (b.restrictScalars' K) = posRootsFinset P b := by
  ext i
  simp only [mem_posRootsFinset, posRoots_restrictScalars']

/-- The finset of negative roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem negRootsFinset_restrictScalars' [Finite ι] [CharZero K] [CharZero L] :
    negRootsFinset (P.restrictScalars' K) (b.restrictScalars' K) = negRootsFinset P b := by
  ext i
  simp only [mem_negRootsFinset, negRoots_restrictScalars']

end RootPairing
