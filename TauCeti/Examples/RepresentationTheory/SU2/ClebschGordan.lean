/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.ClebschGordan.SpecialValues

/-!
# Checks for the Clebsch–Gordan coefficients of `SU(2)`

Sanity checks of the admissible triples `TauCeti.SU2.IsTriad` and of the Clebsch–Gordan
coefficients `TauCeti.SU2.clebschGordan` against the familiar values for the coupling of two
spins `½` and of two spins `1` (Edmonds, *Angular Momentum in Quantum Mechanics*, §3.5), with
negative controls
showing that each ingredient of the definitions is needed. Recall that
`clebschGordan d₁ d₂ d i₁ i₂ i` is `(j₁ m₁ j₂ m₂ | j₁ j₂ j m)` with `j_r = d_r / 2` and
`m_r = i_r - d_r / 2`.

* `½ ⊗ ½ = 0 ⊕ 1`: the spins `0` and `1` are admissible, `½` is not, and the coefficients of the
  triplet and of the singlet `(e_↑ ⊗ e_↓ - e_↓ ⊗ e_↑)/√2` are the expected ones.
* `1 ⊗ 1`: `(1 1 1 0 | 1 1) = 1/√2` and `(1 0 1 0 | 1 0) = 0`.
* The dimension count, and its failure without the parity condition.
* The selection rule `m = m₁ + m₂` is not a consequence of Racah's sum.
* The special values of Edmonds (3.5.12)–(3.5.13) and of the stretched coefficients.
-/

public section

open Finset TauCeti.SU2

/-! ### Admissible triples -/

/-- `½ ⊗ ½ = 0 ⊕ 1`: the spins `0` and `1` are admissible. -/
example : IsTriad 1 1 0 ∧ IsTriad 1 1 2 := by decide

/-- The spin `½` is not admissible in `½ ⊗ ½`, since `½ + ½ + ½` is not an integer, and `4` is
not admissible in `1 ⊗ 2` by the triangle inequality. -/
example : ¬IsTriad 1 1 1 ∧ ¬IsTriad 2 4 8 := by decide

/-- The admissible spins in `1 ⊗ 3/2` are `½`, `3/2` and `5/2`, of dimensions adding up to
`2 + 4 + 6 = 12 = 3 · 4`. -/
example : (range 6).filter (IsTriad 2 3) = {1, 3, 5} ∧
    ∑ d ∈ (range 6).filter (IsTriad 2 3), (d + 1) = 3 * 4 :=
  ⟨by decide, sum_isTriad_succ 2 3⟩

/-- Negative control: without the parity condition the spins `0`, `½`, `1` would all occur in
`½ ⊗ ½`, of total dimension `1 + 2 + 3 = 6 ≠ 4`. -/
example : ∑ d ∈ (range 3).filter (fun d ↦ d ≤ 1 + 1 ∧ 1 ≤ 1 + d), (d + 1) = 6 := by decide

/-! ### The coefficients -/

/-- `(½ ½ ½ ½ | 1 1) = 1`. -/
example : clebschGordan 1 1 2 1 1 2 = 1 := by
  rw [clebschGordan_of_isTriad (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num [sum_range_succ, clebschGordanTerm_def, clebschGordanPrefactor_def, Nat.factorial]

/-- The singlet: `(½ ½ ½ -½ | 0 0) = 1/√2`. -/
example : clebschGordan 1 1 0 1 0 0 = 1 / Real.sqrt 2 := by
  rw [clebschGordan_of_isTriad (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num [sum_range_succ, clebschGordanTerm_def, clebschGordanPrefactor_def, Nat.factorial]

/-- The singlet: `(½ -½ ½ ½ | 0 0) = -1/√2`. -/
example : clebschGordan 1 1 0 0 1 0 = -1 / Real.sqrt 2 := by
  rw [clebschGordan_of_isTriad (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num [sum_range_succ, clebschGordanTerm_def, clebschGordanPrefactor_def, Nat.factorial,
    neg_div]

/-- `(1 1 1 0 | 1 1) = 1/√2`. -/
example : clebschGordan 2 2 2 2 1 2 = 1 / Real.sqrt 2 := by
  rw [clebschGordan_of_isTriad (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num [sum_range_succ, clebschGordanTerm_def, clebschGordanPrefactor_def, Nat.factorial]

/-- `(1 0 1 0 | 1 0) = 0`: an admissible coefficient at which Racah's sum cancels. -/
example : clebschGordan 2 2 2 1 1 1 = 0 := by
  rw [clebschGordan_of_isTriad (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num [sum_range_succ, clebschGordanTerm_def, clebschGordanPrefactor_def, Nat.factorial]

/-- `Δ(0 0 0) = 1` and `Δ(1 1 1) = √(1/24)`. -/
example : triangleCoefficient 0 0 0 = 1 ∧ triangleCoefficient 2 2 2 = Real.sqrt (1 / 24) := by
  norm_num [triangleCoefficient_def, Nat.factorial]

/-- Negative control: `(½ ½ ½ ½ | 1 0) = 0` by the selection rule, since `m₁ + m₂ = 1 ≠ 0 = m`,
while Racah's expression without the projection condition is `1/√2` there. -/
example : clebschGordan 1 1 2 1 1 1 = 0 ∧
    Real.sqrt (clebschGordanPrefactor 1 1 2 1 1 1) *
      ∑ z ∈ range 1, clebschGordanTerm 1 1 2 1 1 z = 1 / Real.sqrt 2 := by
  refine ⟨clebschGordan_eq_zero_of_ne (by norm_num), ?_⟩
  norm_num [clebschGordanTerm_def, clebschGordanPrefactor_def, Nat.factorial]

/-- Negative control: without the factor `2j + 1` under the square root, `(½ ½ ½ ½ | 1 1)` would
be `1/√3`, not a unit vector component. -/
example : Real.sqrt (clebschGordanPrefactor 1 1 2 1 1 2 / 3) *
      ∑ z ∈ range 1, clebschGordanTerm 1 1 2 1 1 z = 1 / Real.sqrt 3 := by
  norm_num [clebschGordanTerm_def, clebschGordanPrefactor_def, Nat.factorial]

/-! ### Special values -/

/-- The stretched coefficient `(½ ½ ½ -½ | 1 0) = 1/√2`, the symmetric triplet vector. -/
example : clebschGordan 1 1 2 1 0 1 = 1 / Real.sqrt 2 := by
  rw [clebschGordan_stretched (d₁ := 1) (d₂ := 1) (i₁ := 1) (i₂ := 0) le_rfl zero_le_one]
  norm_num [Nat.factorial]

/-- `(1 -1 ½ ½ | 3/2 -½) = √(1/3)`. -/
example : clebschGordan 2 1 3 0 1 1 = Real.sqrt (1 / 3) := by
  rw [clebschGordan_spinHalf (d := 2) (i := 0) zero_le_two]
  norm_num

/-- Coupling to spin zero carries the sign `(-1)^{j - m}`: `(½ -½ ½ ½ | 0 0) = -1/√2`. -/
example : clebschGordan 1 1 0 0 1 0 = -1 / Real.sqrt 2 := by
  rw [clebschGordan_spin_zero (d := 1) (i := 0) zero_le_one]
  norm_num

/-- Coupling with spin zero is the identity: `(1 0 0 0 | 1 0) = 1`. -/
example : clebschGordan 2 0 2 1 0 1 = 1 := clebschGordan_zero_right one_le_two
