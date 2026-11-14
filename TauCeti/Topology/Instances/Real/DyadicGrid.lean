/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic grids of a closed real interval

The dyadic grid of level `n` of `[a, b]` consists of the points `a + k * ((b - a) / 2 ^ n)` for
`k ≤ 2 ^ n`. The grids are nested, and their points of all levels are dense in `[a, b]`.

## Main results

* `TauCeti.dyadicPoint`: the finite-indexed dyadic grid as points of the closed interval.
* `TauCeti.exists_dyadicPoint_eq_of_le`: the finite-indexed dyadic grids are nested.
* `TauCeti.dense_iUnion_range_dyadicPoint`: the union of the finite-indexed grids is dense
  for `a ≤ b`, including the singleton interval `a = b`.
* `TauCeti.exists_eq_add_mul_div_two_pow_of_le`: a point of the dyadic grid of level `m` lies on
  the dyadic grids of all levels `n ≥ m`.
* `TauCeti.dense_setOfPred_eq_add_mul_div_two_pow`: the points of the dyadic grids of `[a, b]`,
  of all levels, are dense in `[a, b]` for `a ≤ b`.
* `TauCeti.nnrealDyadicPoint`: the `ℝ≥0`-valued level-`n` dyadic grid on `[0, t]`.
-/

public section

open Set
open scoped NNReal

namespace TauCeti

/-- The `k`th point of the level-`n` dyadic grid on `[a,b]`, including both endpoints. -/
noncomputable def dyadicPoint {a b : ℝ} (hab : a ≤ b) (n : ℕ) (k : Fin (2 ^ n + 1)) : Icc a b :=
  ⟨a + k * ((b - a) / (2 : ℝ) ^ n), by
    have hh : 0 ≤ (b - a) / (2 : ℝ) ^ n := by positivity
    have hk : (k : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast k.is_le
    have heq : (2 : ℝ) ^ n * ((b - a) / (2 : ℝ) ^ n) = b - a :=
      mul_div_cancel₀ _ (by positivity)
    constructor <;> nlinarith [mul_nonneg (k.val.cast_nonneg : (0 : ℝ) ≤ k) hh]⟩

/-- The real coordinate of a dyadic grid point. -/
@[simp]
theorem coe_dyadicPoint {a b : ℝ} (hab : a ≤ b) (n : ℕ) (k : Fin (2 ^ n + 1)) :
    (dyadicPoint hab n k : ℝ) = a + k * ((b - a) / (2 : ℝ) ^ n) :=
  (rfl)

/-- A point of the dyadic grid of level `m` of `[a, b]` lies on the dyadic grids of all levels
`n ≥ m`. -/
lemma exists_eq_add_mul_div_two_pow_of_le {K : Type*} [DivisionRing K] [NeZero (2 : K)]
    {a b t : K} {m n k : ℕ} (hk : k ≤ 2 ^ m) (ht : t = a + k * ((b - a) / 2 ^ m)) (hmn : m ≤ n) :
    ∃ j : ℕ, j ≤ 2 ^ n ∧ t = a + j * ((b - a) / 2 ^ n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ⟨k * 2 ^ d, by rw [pow_add]; gcongr, ?_⟩
  -- `K` is only a division ring, so `field_simp` does not apply: the central element `2 ^ d` is
  -- commuted past `b - a` by hand before it cancels.
  have h : (2 : K) ^ d * ((b - a) / 2 ^ d / 2 ^ m) = (b - a) / 2 ^ m := by
    rw [← mul_div_assoc, ← mul_div_assoc, ((Commute.ofNat_left 2 (b - a)).pow_left d).eq,
      mul_div_cancel_right₀ _ (pow_ne_zero d two_ne_zero)]
  rw [ht]
  push_cast
  rw [mul_assoc, pow_add, div_mul_eq_div_div_swap, h]

/-- A finite-indexed dyadic grid point also belongs to every finer grid. -/
theorem exists_dyadicPoint_eq_of_le {a b : ℝ} (hab : a ≤ b) {m n : ℕ}
    (k : Fin (2 ^ m + 1)) (hmn : m ≤ n) :
    ∃ j, dyadicPoint hab m k = dyadicPoint hab n j := by
  obtain ⟨j, hj, heq⟩ := exists_eq_add_mul_div_two_pow_of_le
    (a := a) (b := b) k.is_le rfl hmn
  refine ⟨⟨j, Nat.lt_succ_of_le hj⟩, Subtype.ext ?_⟩
  simpa only [coe_dyadicPoint, Fin.val_mk] using heq

/-- The points of the dyadic grids of `[a, b]`, of all levels, are dense in `[a, b]`, including
for a singleton interval. -/
theorem dense_setOfPred_eq_add_mul_div_two_pow {a b : ℝ} (hab : a ≤ b) :
    Dense {t : Icc a b | ∃ n k : ℕ, k ≤ 2 ^ n ∧ (t : ℝ) = a + k * ((b - a) / 2 ^ n)} := by
  rcases hab.eq_or_lt with rfl | hab
  · exact fun t ↦ subset_closure ⟨0, 0, by simp, by simpa using t.2.2.antisymm t.2.1⟩
  refine Metric.dense_iff.2 fun t r hr ↦ ?_
  have hba : 0 < b - a := sub_pos.2 hab
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr hba) (one_half_lt_one (α := ℝ))
  set h := (b - a) / 2 ^ n with h_def
  have hh : 0 < h := by positivity
  have hhr : h < r := calc
    h = (1 / 2) ^ n * (b - a) := by rw [h_def, one_div_pow]; ring
    _ < r := (lt_div_iff₀ hba).1 hn
  set k := ⌊((t : ℝ) - a) / h⌋₊
  have hta : 0 ≤ ((t : ℝ) - a) / h := div_nonneg (sub_nonneg.2 t.2.1) hh.le
  have hk₁ : (k : ℝ) * h ≤ t - a := (le_div_iff₀ hh).1 (Nat.floor_le hta)
  have hk₂ : (t : ℝ) - a < (k + 1) * h := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one _)
  have hkn : k ≤ 2 ^ n := by
    refine Nat.floor_le_of_le ?_
    push_cast
    rw [div_le_iff₀ hh, h_def, mul_div_cancel₀ _ (by positivity)]
    linarith [t.2.2]
  refine ⟨⟨a + k * h, by nlinarith [hh.le, (k.cast_nonneg : (0 : ℝ) ≤ k)], by linarith [t.2.2]⟩,
    ?_, n, k, hkn, rfl⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
  constructor <;> simp only <;> nlinarith

/-- The union of the finite-indexed dyadic grids is dense, including for a singleton interval. -/
theorem dense_iUnion_range_dyadicPoint {a b : ℝ} (hab : a ≤ b) :
    Dense (⋃ n, range (dyadicPoint hab n)) := by
  apply (dense_setOfPred_eq_add_mul_div_two_pow hab).mono
  rintro t ⟨n, k, hk, ht⟩
  refine mem_iUnion.2 ⟨n, ⟨⟨k, Nat.lt_succ_of_le hk⟩, Subtype.ext ?_⟩⟩
  simpa only [coe_dyadicPoint, Fin.val_mk] using ht.symm

/-- The `k`th point of the level-`n` dyadic grid on `[0, t]` in `ℝ≥0`. -/
noncomputable def nnrealDyadicPoint (t : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n + 1)) : ℝ≥0 :=
  NNReal.mk (dyadicPoint t.coe_nonneg n k : ℝ) (dyadicPoint t.coe_nonneg n k).2.1

/-- The real coordinate of an `ℝ≥0` dyadic grid point on `[0, t]`. -/
@[simp] theorem coe_nnrealDyadicPoint (t : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n + 1)) :
    (nnrealDyadicPoint t n k : ℝ) = k * ((t : ℝ) / (2 : ℝ) ^ n) := by simp [nnrealDyadicPoint]

/-- The initial point of the `ℝ≥0` dyadic grid on `[0, t]` is `0`. -/
@[simp] theorem nnrealDyadicPoint_zero (t : ℝ≥0) (n : ℕ) : nnrealDyadicPoint t n 0 = 0 := by
  ext; simp

/-- The terminal point of the `ℝ≥0` dyadic grid on `[0, t]` is `t`. -/
@[simp] theorem nnrealDyadicPoint_last (t : ℝ≥0) (n : ℕ) :
    nnrealDyadicPoint t n (Fin.last (2 ^ n)) = t := by
  ext; simp [mul_div_cancel₀ (t : ℝ) (by positivity : (2 : ℝ) ^ n ≠ 0)]

/-- Each level-`n` dyadic grid on `[0, t]` is monotone in the grid index. -/
theorem monotone_nnrealDyadicPoint (t : ℝ≥0) (n : ℕ) : Monotone (nnrealDyadicPoint t n) :=
  fun _ _ hij ↦ NNReal.coe_le_coe.mp (by
    simp only [coe_nnrealDyadicPoint]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity))

/-- Every point of the `ℝ≥0` dyadic grid on `[0, t]` is at most `t`. -/
theorem nnrealDyadicPoint_le (t : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n + 1)) :
    nnrealDyadicPoint t n k ≤ t := NNReal.coe_le_coe.mp (dyadicPoint t.coe_nonneg n k).2.2

/-- Every point of the level-`m` dyadic grid on `[0, t]` belongs to every finer grid `n ≥ m`. -/
theorem exists_nnrealDyadicPoint_eq_of_le (t : ℝ≥0) {m n : ℕ} (k : Fin (2 ^ m + 1))
    (hmn : m ≤ n) : ∃ j, nnrealDyadicPoint t m k = nnrealDyadicPoint t n j := by
  obtain ⟨j, hj⟩ := exists_dyadicPoint_eq_of_le t.coe_nonneg k hmn
  exact ⟨j, by simp only [nnrealDyadicPoint, hj]⟩

/-- Consecutive points of the level-`n` dyadic grid on `[0, t]` are at distance `t / 2 ^ n`. -/
theorem dist_nnrealDyadicPoint_succ (t : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n)) :
    dist (nnrealDyadicPoint t n k.succ) (nnrealDyadicPoint t n k.castSucc) = (t : ℝ) / 2 ^ n := by
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr
    (NNReal.coe_le_coe.mpr (monotone_nnrealDyadicPoint t n k.castSucc_le_succ)))]
  simp only [coe_nnrealDyadicPoint, Fin.val_succ, Fin.val_castSucc]; push_cast; ring

/-- Any open set of `ℝ≥0` meeting `[0, t]` contains a dyadic grid point on `[0, t]`. -/
theorem exists_nnrealDyadicPoint_mem_open {t s : ℝ≥0} (hst : s ≤ t) {U : Set ℝ≥0} (hU : IsOpen U)
    (hs : s ∈ U) : ∃ n : ℕ, ∃ k : Fin (2 ^ n + 1), nnrealDyadicPoint t n k ∈ U := by
  let f : Icc (0 : ℝ) t → ℝ≥0 := fun x ↦ NNReal.mk x.1 x.2.1
  obtain ⟨x, hx_grid, hxU⟩ := (dense_iUnion_range_dyadicPoint t.coe_nonneg).exists_mem_open
    (hU.preimage (Continuous.subtype_mk continuous_subtype_val _ : Continuous f))
    ⟨⟨s, s.coe_nonneg, hst⟩, hs⟩
  obtain ⟨n, k, rfl⟩ := by simpa only [mem_iUnion, mem_range] using hx_grid
  exact ⟨n, k, hxU⟩

end TauCeti
