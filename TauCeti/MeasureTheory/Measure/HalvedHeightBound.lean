/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Measure bounds from powers of a halved height

A bound on `(s / 2) ^ q * ν X` for a set `X` is a bound on `ν X` itself, with the constant
`2 ^ q * (s ^ q)⁻¹`. This is the elementary step that turns a weak-type estimate at the height
`s / 2` into an estimate at the height `s`.

## Main statements

* `TauCeti.measure_le_two_rpow_mul_inv_rpow_mul`: the bound on `ν X` from one on
  `(s / 2) ^ q * ν X`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- A bound on `(s / 2) ^ q * ν X` bounds `ν X`. -/
theorem measure_le_two_rpow_mul_inv_rpow_mul {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {q : ℝ} {s : ℝ≥0∞}
    (hs : s ≠ 0) (hs' : s ≠ ∞) {X : Set β} {B : ℝ≥0∞}
    (h : (s / 2) ^ q * ν X ≤ B) : ν X ≤ 2 ^ q * (s ^ q)⁻¹ * B := by
  have hs2 : s / 2 ≠ 0 := ENNReal.div_ne_zero.2 ⟨hs, ENNReal.ofNat_ne_top⟩
  have hs2' : s / 2 ≠ ∞ := ENNReal.div_ne_top hs' two_ne_zero
  rw [ENNReal.mul_le_iff_le_inv (ENNReal.rpow_pos (pos_iff_ne_zero.2 hs2) hs2').ne'
    (ENNReal.rpow_ne_top_of_ne_zero hs2 hs2')] at h
  convert h using 2
  rw [div_eq_mul_inv, ENNReal.mul_rpow_of_ne_zero hs (by simp), ENNReal.inv_rpow]
  rw [ENNReal.mul_inv
    (Or.inr (ENNReal.inv_ne_top.2 (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'))
    (Or.inl (ENNReal.rpow_ne_top_of_ne_zero hs hs')), inv_inv, mul_comm]

end TauCeti
