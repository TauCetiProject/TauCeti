/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.Zigzag
import Mathlib.Tactic.NormNum
import TauCeti.Algebra.AddCircle

/-!
# Examples of the zigzag walk

* The Legendre pair `α = (1/2, 1/2)`, `β = (1, 1)`: the sorted list is `1/2, 1/2, 1, 1` and the
  walk is `0, 1, 2, 1, 0`. The two copies of `1/2` are recorded at `0` and `1`, which the block
  form gives as `Z(1/2) - 2` and `Z(1/2) - 1` with `Z(1/2) = 2`; recording every copy at
  `Z(1/2) - 1` would give `1, 1`.
* The pair `α = (1/2, 1/2)`, `β = (1/4, 3/4)`: the sorted list is `1/4, 1/2, 1/2, 3/4` and the
  walk is `0, -1, 0, 1, 0`, so the copies of `1/2` are recorded at `-1` and `0`.
* For a pair of degree `0` the walk is constantly `0`.
-/

public section

open TauCeti.Hypergeometric Set

namespace TauCeti.Hypergeometric.Examples

private theorem coe_ne_coe {x y : ℚ} (hx : x ∈ Ioc (0 : ℚ) 1) (hy : y ∈ Ioc (0 : ℚ) 1)
    (hxy : x ≠ y) : (x : AddCircle (1 : ℚ)) ≠ y :=
  (AddCircle.coe_eq_coe_iff_of_mem_Ioc (a := 0) (by simpa using hx) (by simpa using hy)).not.2 hxy

/-- The Legendre pair `α = (1/2, 1/2)`, `β = (1, 1)`. -/
noncomputable def zigzagLegendre : Parameters where
  α := {((1 / 2 : ℚ) : AddCircle (1 : ℚ)), ((1 / 2 : ℚ) : AddCircle (1 : ℚ))}
  β := {((1 : ℚ) : AddCircle (1 : ℚ)), ((1 : ℚ) : AddCircle (1 : ℚ))}
  card_eq := rfl
  disjoint := by
    simp only [Multiset.disjoint_iff_ne, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton, or_self]
    rintro _ rfl _ rfl
    exact coe_ne_coe (by norm_num) (by norm_num) (by norm_num)

private theorem rep_half : rep ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 1 / 2 :=
  rep_coe_of_mem (by norm_num)

private theorem rep_one : rep ((1 : ℚ) : AddCircle (1 : ℚ)) = 1 :=
  rep_coe_of_mem (by norm_num)

theorem sortedReps_zigzagLegendre : zigzagLegendre.sortedReps = [1 / 2, 1 / 2, 1, 1] := by
  rw [Parameters.sortedReps_eq_iff, List.sortedLE_iff_pairwise]
  refine ⟨by simp; norm_num, ?_⟩
  simp only [zigzagLegendre, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
    Multiset.map_cons, Multiset.map_singleton, rep_half, rep_one]
  rfl

theorem countingFunction_zigzagLegendre : zigzagLegendre.countingFunction (1 / 2) = 2 := by
  simp only [Parameters.countingFunction_def, zigzagLegendre, Multiset.insert_eq_cons,
    Multiset.filter_cons, Multiset.filter_singleton, rep_half, rep_one]
  norm_num

-- The walk `0, 1, 2, 1, 0`.
example : (List.range 5).map zigzagLegendre.height = [0, 1, 2, 1, 0] := by
  have h₁ : zigzagLegendre.step 2⁻¹ = 1 :=
    zigzagLegendre.step_of_mem (by simp [zigzagLegendre])
  have h₂ : zigzagLegendre.step 1 = -1 := by
    refine zigzagLegendre.step_of_notMem ?_
    simp only [zigzagLegendre, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      or_self]
    exact (coe_ne_coe (by norm_num) (by norm_num) (by norm_num))
  simp [List.range_succ, Parameters.height_def, sortedReps_zigzagLegendre, h₁, h₂]

-- The block of `1/2` starts at position `0`, and the block form records its two copies at
-- `Z(1/2) - 2 + 0 = 0` and `Z(1/2) - 2 + 1 = 1`.
example : zigzagLegendre.blockStart ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 ∧
    zigzagLegendre.height 0 = 0 ∧ zigzagLegendre.height 1 = 1 := by
  have hmem : ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) ∈ zigzagLegendre.α := by simp [zigzagLegendre]
  have hcount : zigzagLegendre.α.count ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 2 := by
    simp [zigzagLegendre]
  have h0 : zigzagLegendre.blockStart ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    simp only [Parameters.blockStart_def, zigzagLegendre, Multiset.insert_eq_cons,
      Multiset.cons_add, Multiset.singleton_add, Multiset.filter_cons, Multiset.filter_singleton,
      rep_half, rep_one]
    norm_num
  have hblock (j : ℕ) (hj : j ≤ 2) :
      zigzagLegendre.height j = j := by
    have h := zigzagLegendre.height_blockStart_add_of_mem_α hmem (j := j) (hcount ▸ hj)
    rw [h0, zero_add, rep_half, countingFunction_zigzagLegendre, hcount] at h
    rw [h]
    ring
  exact ⟨h0, (hblock 0 (by norm_num)).trans Nat.cast_zero,
    (hblock 1 (by norm_num)).trans Nat.cast_one⟩

/-- The pair `α = (1/2, 1/2)`, `β = (1/4, 3/4)`. -/
noncomputable def zigzagHalfQuarter : Parameters where
  α := {((1 / 2 : ℚ) : AddCircle (1 : ℚ)), ((1 / 2 : ℚ) : AddCircle (1 : ℚ))}
  β := {((1 / 4 : ℚ) : AddCircle (1 : ℚ)), ((3 / 4 : ℚ) : AddCircle (1 : ℚ))}
  card_eq := rfl
  disjoint := by
    simp only [Multiset.disjoint_iff_ne, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton, or_self]
    rintro _ rfl _ (rfl | rfl) <;> exact coe_ne_coe (by norm_num) (by norm_num) (by norm_num)

theorem sortedReps_zigzagHalfQuarter :
    zigzagHalfQuarter.sortedReps = [1 / 4, 1 / 2, 1 / 2, 3 / 4] := by
  rw [Parameters.sortedReps_eq_iff, List.sortedLE_iff_pairwise]
  refine ⟨by simp; norm_num, ?_⟩
  simp only [zigzagHalfQuarter, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
    Multiset.map_cons, Multiset.map_singleton, rep_half,
    rep_coe_of_mem (show (1 / 4 : ℚ) ∈ Ioc 0 1 by norm_num),
    rep_coe_of_mem (show (3 / 4 : ℚ) ∈ Ioc 0 1 by norm_num)]
  rw [Multiset.cons_swap (1 / 2 : ℚ) (1 / 4), Multiset.cons_swap (1 / 2 : ℚ) (1 / 4)]
  rfl

-- The walk `0, -1, 0, 1, 0`.
example : (List.range 5).map zigzagHalfQuarter.height = [0, -1, 0, 1, 0] := by
  have h₁ : zigzagHalfQuarter.step 2⁻¹ = 1 :=
    zigzagHalfQuarter.step_of_mem (by simp [zigzagHalfQuarter])
  have hβ {q : ℚ} (hq : q ∈ Ioc (0 : ℚ) 1) (h₁ : q ≠ 1 / 2) : zigzagHalfQuarter.step q = -1 := by
    refine zigzagHalfQuarter.step_of_notMem ?_
    simp only [zigzagHalfQuarter, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton, or_self]
    exact coe_ne_coe hq (by norm_num) h₁
  have h₂ : zigzagHalfQuarter.step 4⁻¹ = -1 := hβ (by norm_num) (by norm_num)
  have h₃ : zigzagHalfQuarter.step (3 / 4) = -1 := hβ (by norm_num) (by norm_num)
  simp [List.range_succ, Parameters.height_def, sortedReps_zigzagHalfQuarter, h₁, h₂, h₃]

-- For a pair of degree `0` the walk is constantly `0`.
example (P : Parameters) (hP : P.degree = 0) (i : ℕ) : P.height i = 0 :=
  P.height_of_two_mul_degree_le (by omega)

end TauCeti.Hypergeometric.Examples
