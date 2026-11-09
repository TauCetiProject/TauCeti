/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith

/-!
# Measurable positive and negative parts

A measurable real-valued function with values in `[-1,1]` is a difference of two measurable
`[0,1]`-valued functions. This decomposition extends bounds for nonnegative test functions to
signed test functions.
-/

public section

open Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable `[-1,1]`-valued function is the difference of its positive and negative parts,
two measurable `[0,1]`-valued functions. -/
theorem Measurable.exists_eq_sub_of_mem_Icc {u : Ω → ℝ} (hu : Measurable u)
    (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) :
    ∃ p n : Ω → ℝ, Measurable p ∧ Measurable n ∧ (∀ x, p x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, n x ∈ Icc (0 : ℝ) 1) ∧ u = p - n :=
  ⟨fun x => Max.max (u x) 0, fun x => Max.max (-u x) 0, hu.max measurable_const,
    hu.neg.max measurable_const, fun x => ⟨le_max_right _ _, max_le (hu1 x).2 zero_le_one⟩,
    fun x => ⟨le_max_right _ _, max_le (by linarith [(hu1 x).1]) zero_le_one⟩,
    funext fun x => (max_zero_sub_max_neg_zero_eq_self (u x)).symm⟩
