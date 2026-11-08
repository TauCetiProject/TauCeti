/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Lowering positive roots by simple reflections

This file records how reflection in a root changes the height relative to a root-pairing base:
reflection in a simple root subtracts the corresponding Cartan integer. When the root index type
is finite, the coefficient ring is a domain and the pairing is reduced, a positive root that is
not simple can be lowered by a simple reflection while remaining positive.

## Main results

* `RootPairing.Base.height_reflectionPerm` computes the height after an arbitrary root reflection.
* `RootPairing.Base.height_reflectionPerm_lt_iff` characterizes strict height decrease under a
  simple reflection by positivity of the corresponding Cartan integer.
* `RootPairing.Base.IsPos.exists_mem_support_height_reflectionPerm_lt` gives the positive-root
  lowering step for a nonsimple positive root.

## References

The argument follows Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.

Mathlib already carries out this height computation and lowering step inside the proof of
`RootPairing.Base.IsPos.induction_on_reflect`, where it is packaged as a strong induction
principle rather than exposed. The declarations below state that computation and the resulting
lowering step in their own right.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} (b : P.Base) [CharZero R] [P.IsCrystallographic]

/-- Reflection in the root indexed by `i` changes the height of `j` by the Cartan integer
`P.pairingIn ℤ j i` times the height of `i`. -/
lemma height_reflectionPerm (i j : ι) :
    b.height (P.reflectionPerm i j) = b.height j - P.pairingIn ℤ j i * b.height i := by
  rw [b.height_add_zsmul (i := j) (j := i) (z := -P.pairingIn ℤ j i)
    (by rw [root_reflectionPerm, reflection_apply_root' ℤ]; module)]
  simp [sub_eq_add_neg]

/-- Reflection in a simple root subtracts the corresponding Cartan integer from the height. -/
@[simp]
lemma height_reflectionPerm_of_mem_support {i j : ι} (hi : i ∈ b.support) :
    b.height (P.reflectionPerm i j) = b.height j - P.pairingIn ℤ j i := by
  rw [height_reflectionPerm, height_one_of_mem_support hi, mul_one]

/-- Reflection in a simple root strictly decreases height exactly when the corresponding Cartan
integer is positive. -/
lemma height_reflectionPerm_lt_iff {i j : ι} (hi : i ∈ b.support) :
    b.height (P.reflectionPerm i j) < b.height j ↔ 0 < P.pairingIn ℤ j i := by
  simp [hi]

variable {b}

/-- A nonsimple positive root admits a simple reflection that remains positive and has strictly
smaller height. This is the positive-root lowering step used by induction on height. -/
theorem IsPos.exists_mem_support_height_reflectionPerm_lt [Finite ι] [IsDomain R]
    [P.IsReduced] {j : ι} (hj : b.IsPos j) (hj' : j ∉ b.support) :
    ∃ i ∈ b.support, b.IsPos (P.reflectionPerm i j) ∧
      b.height (P.reflectionPerm i j) < b.height j := by
  -- Mathlib provides the transposed pairing; finiteness makes the two pairings have the same sign.
  obtain ⟨i, hi, hpair⟩ := hj.exists_mem_support_pos_pairingIn
  refine ⟨i, hi, hj.reflectionPerm hi (ne_of_mem_of_not_mem hi hj').symm, ?_⟩
  rwa [height_reflectionPerm_lt_iff b hi, P.zero_lt_pairingIn_iff']

end RootPairing.Base
