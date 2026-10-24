/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Action.Basic

/-!
# Averaging a constant

Over a ring in which the number of terms is invertible, the average `⅟#s • ∑ i ∈ s, f i` of a
family is the usual normalised sum. Averaging a constant family returns the constant. This is the
step that closes averaging arguments (Reynolds operators, Bochner averages, Maschke-type
projections) once the averaged terms have been shown to coincide.

## Main results

* `Finset.invOf_card_smul_sum_const`: `⅟#s • ∑ _i ∈ s, v = v`.
* `Fintype.invOf_card_smul_sum_const`: the same over all of a finite type.
-/

public section

variable {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Averaging a constant over a finset returns it. -/
theorem Finset.invOf_card_smul_sum_const (s : Finset ι) [Invertible (s.card : R)] (v : M) :
    ⅟(s.card : R) • ∑ _i ∈ s, v = v := by
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul R, invOf_smul_smul]

/-- Averaging a constant over a finite type returns it. -/
theorem Fintype.invOf_card_smul_sum_const [Fintype ι] [Invertible (Fintype.card ι : R)] (v : M) :
    ⅟(Fintype.card ι : R) • ∑ _i : ι, v = v := by
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, invOf_smul_smul]
