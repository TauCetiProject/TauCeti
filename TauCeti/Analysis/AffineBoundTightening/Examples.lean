/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.AffineBoundTightening.Limit
public import TauCeti.Analysis.AffineBoundTightening.LinearProgram
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Worked examples for simultaneous affine bound tightening

This file records concrete examples exercising joint interval packing, endpoint containment, total
width, signed affine image arithmetic, simultaneous step evaluation, empty absorption, graph-point
survival, fixed-tuple containment, non-terminating geometric convergence, the endpoint limit of the
iteration, and the scalar linear program of fixed boxes.

## Main examples

* `TauCeti.AffineBoundTightening.Examples.rawRun_twoRow`: for `1 < a`, initial variable box
  `[0, 1]²`, and equality rows `a * x₀ - x₁ = 0` and `x₀ - a * x₁ = 0`, the simultaneous iterates
  keep all lower endpoints and row endpoints at `0` while shrinking both variable upper endpoints to
  `1 / a ^ k`. Total width `2 / a ^ k` stays strictly positive at every finite `k` and converges to
  `0`, so the iteration does not stabilize in finitely many steps
  (`twoRow_width_tendsto_and_no_stabilization`). At `a = 2`, one simultaneous step yields variable
  uppers `(1/2, 1/2)` whereas sequential row-by-row updates yield `(1/2, 1/4)`
  (`twoRow_two_step`).
* `TauCeti.AffineBoundTightening.Examples.fourRow_feasible_without_graph_point`: three variables
  in `[-1, 1]` with equality rows `x₀ + x₁ + x₂ = 0`, `x₀ + x₁ - x₂ = 0`, `x₀ - x₁ + x₂ = 0` and
  `-x₀ + x₁ + x₂ = 1` form an ordered fixed box with a feasible canonical assignment, although the
  equations have no common solution.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, pp. 65–76.
* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *On the convergence of feasibility based bounds
  tightening*, Mathematical Programming Computation (2012), Example 2.4, p. 8 (adapted from
  sequential row-by-row iteration to the simultaneous operator).
-/

public section

open scoped BigOperators Topology
open Filter Set

namespace TauCeti.AffineBoundTightening.Examples

noncomputable section

private theorem erase_zero_fin2 : Finset.univ.erase (0 : Fin 2) = {1} := by decide

private theorem erase_one_fin2 : Finset.univ.erase (1 : Fin 2) = {0} := by decide

/-! ### Joint intervals, width, and signed affine images -/

/-- `([1], [0])` packs to `⊥`, `[0, 1]` contains `1/2`, and a singleton box contains exactly its
endpoint. -/
theorem pack_inverted_unit_singleton :
    let qBad : Raw 1 0 := (fun _ => 1, fun _ => 0)
    let qUnit : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let x : Coord 1 0 → ℝ := fun _ => 3
    pack qBad = ⊥ ∧ (fun _ : Coord 1 0 => (1 / 2 : ℝ)) ∈ pack qUnit ∧
      ∀ y, y ∈ pack (x, x) ↔ y = x := by
  intro qBad qUnit x
  refine ⟨pack_eq_bot_iff.mpr fun h => ?_,
    mem_pack_iff.mpr ⟨fun _ => by norm_num, fun _ => by norm_num⟩, fun _ => by simp⟩
  have := h (.inl 0)
  norm_num [qBad] at this

/-- At `n = m = 0`, every raw tuple packs to a nonbottom state containing the empty coordinate
function; both mixed zero-dimensional cases (`n = 0, m = 1` and `n = 1, m = 0`) also admit
nonbottom states. -/
theorem pack_zero_dim (q : Raw 0 0) (x : Coord 0 0 → ℝ) :
    (pack q ≠ ⊥ ∧ x ∈ pack q) ∧
      pack ((fun _ : Coord 0 1 => (0 : ℝ)), (fun _ => 1)) ≠ ⊥ ∧
      pack ((fun _ : Coord 1 0 => (0 : ℝ)), (fun _ => 1)) ≠ ⊥ := by
  refine ⟨⟨pack_ne_bot_iff.mpr fun c => c.elim Fin.elim0 Fin.elim0,
      mem_pack_iff.mpr ⟨fun c => c.elim Fin.elim0 Fin.elim0, fun c => c.elim Fin.elim0 Fin.elim0⟩⟩,
    pack_ne_bot_iff.mpr fun _ => by norm_num, pack_ne_bot_iff.mpr fun _ => by norm_num⟩

/-- `[0, 1]` and `[1, 2]` have equal width `1` yet are unequal and incomparable under `Within`;
`[0, 1]` lies strictly within `[0, 2]` with strictly smaller width; singleton and zero-coordinate
tuples have width `0`. -/
theorem width_unit_intervals_and_within (q₀ : Raw 0 0) :
    let q₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let q₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    let q₃ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    (width q₁ = 1 ∧ width q₂ = 1 ∧ q₁ ≠ q₂ ∧ ¬ Within q₁ q₂ ∧ ¬ Within q₂ q₁) ∧
      (Within q₁ q₃ ∧ width q₁ < width q₃) ∧
      (width ((fun _ : Coord 1 0 => (3 : ℝ)), (fun _ => 3)) = 0 ∧ width q₀ = 0) := by
  intro q₁ q₂ q₃
  have hw13 : Within q₁ q₃ := within_iff.mpr ⟨fun _ => le_rfl, fun _ => by norm_num [q₁, q₃]⟩
  refine ⟨⟨by simp [q₁, width_eq_sum_add_sum], by simp [q₂, width_eq_sum_add_sum]; norm_num,
      fun h => by have := congrFun (congrArg Prod.fst h) (.inl 0); norm_num [q₁, q₂] at this,
      fun h => by have := h.fst_le (.inl 0); norm_num [q₁, q₂] at this,
      fun h => by have := h.le_snd (.inl 0); norm_num [q₁, q₂] at this⟩,
    ⟨hw13, hw13.width_lt_of_ne fun h => by
        have := congrFun (congrArg Prod.snd h) (.inl 0); norm_num [q₁, q₃] at this⟩,
    ⟨width_pure _, by simp [width_eq_sum_add_sum]⟩⟩

/-- For `a = -2` and `X = [1, 3]`, the signed product is `[-6, -2]` and encloses `(-2) * 2 = -4`. -/
theorem neg_coeff_signed_product :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![-2]
    let q : Raw 1 1 := (Sum.elim ![1] ![0], Sum.elim ![3] ![0])
    zLo A q 0 0 = -6 ∧ zHi A q 0 0 = -2 ∧ A 0 0 * 2 = -4 ∧
      A 0 0 * 2 ∈ Icc (zLo A q 0 0) (zHi A q 0 0) := by
  intro A q
  have hneg : A 0 0 ≤ 0 := by norm_num [A]
  have hlo : zLo A q 0 0 = -6 := by rw [zLo_of_nonpos hneg]; norm_num [A, q]
  have hhi : zHi A q 0 0 = -2 := by rw [zHi_of_nonpos hneg]; norm_num [A, q]
  have hval : A 0 0 * 2 = -4 := by norm_num [A]
  exact ⟨hlo, hhi, hval, ⟨zLo_le_mul (by norm_num [q]), mul_le_zHi (by norm_num [q])⟩⟩

/-- Zero coefficients give `[0, 0]` even for positive-width variables, zero rows give image
`[0, 0]`, zero columns contribute zero, zero variables give image `[0, 0]`, and one variable gives
omitted sum `0`. -/
theorem zero_coeff_row_col_and_low_dim
    (A₀ : Matrix (Fin 1) (Fin 0) ℝ) (q₀ : Raw 0 1)
    (A₁ : Matrix (Fin 1) (Fin 1) ℝ) (q₁ : Raw 1 1)
    (q₂ : Raw 2 1) :
    let AZero : Matrix (Fin 1) (Fin 2) ℝ := !![0, 0]
    let qPos : Raw 2 1 := (Sum.elim ![1, 2] ![0], Sum.elim ![5, 4] ![0])
    let ACol : Matrix (Fin 1) (Fin 2) ℝ := !![0, 3]
    (zLo AZero qPos 0 0 = 0 ∧ zHi AZero qPos 0 0 = 0 ∧
        imageLo AZero qPos 0 = 0 ∧ imageHi AZero qPos 0 = 0) ∧
      (imageLo ACol q₂ 0 = restLo ACol q₂ 0 0 ∧ imageHi ACol q₂ 0 = restHi ACol q₂ 0 0) ∧
      (imageLo A₀ q₀ 0 = 0 ∧ imageHi A₀ q₀ 0 = 0) ∧
      (restLo A₁ q₁ 0 0 = 0 ∧ restHi A₁ q₁ 0 0 = 0) := by
  intro AZero qPos ACol
  have hrow : ∀ j : Fin 2, AZero 0 j = 0 := fun j => by fin_cases j <;> simp [AZero]
  have hz : ACol 0 0 = 0 := by simp [ACol]
  exact ⟨⟨zLo_of_zero (hrow 0), zHi_of_zero (hrow 0),
      imageLo_eq_zero_of_row_zero hrow, imageHi_eq_zero_of_row_zero hrow⟩,
    ⟨imageLo_eq_restLo_of_zero hz, imageHi_eq_restHi_of_zero hz⟩,
    ⟨imageLo_eq_zero_of_row_zero fun j => Fin.elim0 j,
      imageHi_eq_zero_of_row_zero fun j => Fin.elim0 j⟩,
    ⟨restLo_eq_zero_of_subsingleton A₁ q₁ 0 0, restHi_eq_zero_of_subsingleton A₁ q₁ 0 0⟩⟩

/-! ### Two-row non-terminating geometric simultaneous example -/

/-- Coefficient matrix `!![a, -1; 1, -a]` for the two-row equality system
`a * x₀ - x₁ = 0`, `x₀ - a * x₁ = 0`. -/
def twoRowMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, -1; 1, -a]

/-- Symmetric raw tuple with variable box `[0, u]²` and equality rows `[0, 0]²`. -/
def twoRowBox (u : ℝ) : Raw 2 2 :=
  (fun _ => 0, Sum.elim (fun _ => u) (fun _ => 0))

/-- Lower endpoints of `twoRowBox u` are all `0`. -/
@[simp]
theorem twoRowBox_fst (u : ℝ) (c : Coord 2 2) : (twoRowBox u).1 c = 0 :=
  (rfl)

/-- Variable upper endpoints of `twoRowBox u` equal `u`. -/
@[simp]
theorem twoRowBox_snd_inl (u : ℝ) (j : Fin 2) : (twoRowBox u).2 (.inl j) = u :=
  (rfl)

/-- Row upper endpoints of `twoRowBox u` equal `0`. -/
@[simp]
theorem twoRowBox_snd_inr (u : ℝ) (i : Fin 2) : (twoRowBox u).2 (.inr i) = 0 :=
  (rfl)

/-- Total width of `twoRowBox u` is `2 * u`. -/
theorem width_twoRowBox (u : ℝ) : width (twoRowBox u) = 2 * u := by
  rw [width_eq_sum_add_sum]
  simp [two_mul]

/-- `twoRowBox u` lies within `twoRowBox v` whenever `u ≤ v`. -/
theorem twoRowBox_within {u v : ℝ} (huv : u ≤ v) : Within (twoRowBox u) (twoRowBox v) := by
  refine within_iff.mpr ⟨fun _ => le_rfl, fun c => ?_⟩
  cases c with
  | inl _ => exact huv
  | inr _ => exact le_rfl

private theorem up_twoRowBox {a u : ℝ} (ha : 0 < a) (hu0 : 0 ≤ u) :
    up (twoRowMatrix a) (twoRowBox u) = twoRowBox u := by
  have hA00 : twoRowMatrix a 0 0 = a := by simp [twoRowMatrix]
  have hA01 : twoRowMatrix a 0 1 = -1 := by simp [twoRowMatrix]
  have hA10 : twoRowMatrix a 1 0 = 1 := by simp [twoRowMatrix]
  have hA11 : twoRowMatrix a 1 1 = -a := by simp [twoRowMatrix]
  refine up_eq_self_iff.mpr fun i => ?_
  fin_cases i <;> dsimp only [Fin.zero_eta, Fin.mk_one]
  · rw [imageLo_def, imageHi_def, Fin.sum_univ_two, Fin.sum_univ_two,
      zLo_of_nonneg (hA00 ▸ ha.le), zLo_of_nonpos (by norm_num [hA01]),
      zHi_of_nonneg (hA00 ▸ ha.le), zHi_of_nonpos (by norm_num [hA01])]
    simp only [hA00, hA01, twoRowBox_fst, twoRowBox_snd_inl, twoRowBox_snd_inr, mul_zero,
      zero_add, add_zero, neg_one_mul]
    exact ⟨by grind, mul_nonneg ha.le hu0⟩
  · rw [imageLo_def, imageHi_def, Fin.sum_univ_two, Fin.sum_univ_two,
      zLo_of_nonneg (by norm_num [hA10]), zLo_of_nonpos (by rw [hA11]; grind),
      zHi_of_nonneg (by norm_num [hA10]), zHi_of_nonpos (by rw [hA11]; grind)]
    simp only [hA10, hA11, twoRowBox_fst, twoRowBox_snd_inl, twoRowBox_snd_inr, mul_zero,
      zero_add, add_zero, one_mul, neg_mul]
    exact ⟨neg_nonpos.mpr (mul_nonneg ha.le hu0), hu0⟩

private theorem inverseLo_twoRowBox {a u : ℝ} (ha : 0 < a) (i j : Fin 2) :
    inverseLo (twoRowMatrix a) (twoRowBox u) i j = 0 := by
  have hA00 : twoRowMatrix a 0 0 = a := by simp [twoRowMatrix]
  have hA01 : twoRowMatrix a 0 1 = -1 := by simp [twoRowMatrix]
  have hA10 : twoRowMatrix a 1 0 = 1 := by simp [twoRowMatrix]
  have hA11 : twoRowMatrix a 1 1 = -a := by simp [twoRowMatrix]
  fin_cases i <;> fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one]
  · rw [inverseLo_of_pos (hA00 ▸ ha), restHi_def, erase_zero_fin2, Finset.sum_singleton,
      zHi_of_nonpos (by norm_num [hA01])]
    simp [hA01]
  · rw [inverseLo_of_neg (by norm_num [hA01]), restLo_def, erase_one_fin2, Finset.sum_singleton,
      zLo_of_nonneg (hA00 ▸ ha.le)]
    simp [hA00]
  · rw [inverseLo_of_pos (by norm_num [hA10]), restHi_def, erase_zero_fin2, Finset.sum_singleton,
      zHi_of_nonpos (by rw [hA11]; grind)]
    simp [hA11]
  · rw [inverseLo_of_neg (by rw [hA11]; grind), restLo_def, erase_one_fin2, Finset.sum_singleton,
      zLo_of_nonneg (by norm_num [hA10])]
    simp [hA10]

private theorem inverseHi_twoRowBox {a u : ℝ} (ha : 0 < a) :
    inverseHi (twoRowMatrix a) (twoRowBox u) 0 0 = u / a ∧
      inverseHi (twoRowMatrix a) (twoRowBox u) 0 1 = a * u ∧
      inverseHi (twoRowMatrix a) (twoRowBox u) 1 0 = a * u ∧
      inverseHi (twoRowMatrix a) (twoRowBox u) 1 1 = u / a := by
  have hA00 : twoRowMatrix a 0 0 = a := by simp [twoRowMatrix]
  have hA01 : twoRowMatrix a 0 1 = -1 := by simp [twoRowMatrix]
  have hA10 : twoRowMatrix a 1 0 = 1 := by simp [twoRowMatrix]
  have hA11 : twoRowMatrix a 1 1 = -a := by simp [twoRowMatrix]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inverseHi_of_pos (hA00 ▸ ha), restLo_def, erase_zero_fin2, Finset.sum_singleton,
      zLo_of_nonpos (by norm_num [hA01])]
    simp [hA00, hA01]
  · rw [inverseHi_of_neg (by norm_num [hA01]), restHi_def, erase_one_fin2, Finset.sum_singleton,
      zHi_of_nonneg (hA00 ▸ ha.le)]
    simp [hA00, hA01]
  · rw [inverseHi_of_pos (by norm_num [hA10]), restLo_def, erase_zero_fin2, Finset.sum_singleton,
      zLo_of_nonpos (by rw [hA11]; grind)]
    simp [hA10, hA11]
  · rw [inverseHi_of_neg (by rw [hA11]; grind), restHi_def, erase_one_fin2, Finset.sum_singleton,
      zHi_of_nonneg (by norm_num [hA10])]
    simp [hA10, hA11]

private theorem down_twoRowBox {a u : ℝ} (ha : 1 < a) (hu0 : 0 ≤ u) :
    down (twoRowMatrix a) (twoRowBox u) = twoRowBox (u / a) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  obtain ⟨h00, h01, h10, h11⟩ := inverseHi_twoRowBox (u := u) ha0
  have hdiv : u / a ≤ u := div_le_self hu0 ha.le
  have hmul : u ≤ a * u := le_mul_of_one_le_left hu0 ha.le
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_)
  · cases c with
    | inl j =>
      exact le_antisymm
        (down_fst_inl_le_iff.mpr ⟨le_rfl, fun i => (inverseLo_twoRowBox ha0 i j).le⟩)
        ((down_within (twoRowMatrix a) (twoRowBox u)).fst_le (.inl j))
    | inr i => simp
  · cases c with
    | inl j =>
      refine le_antisymm ?_ (le_down_snd_inl_iff.mpr ⟨hdiv, fun i => ?_⟩)
      · fin_cases j
        · exact (down_snd_inl_le_inverseHi _ _ 0 0).trans h00.le
        · exact (down_snd_inl_le_inverseHi _ _ 1 1).trans h11.le
      · fin_cases j <;> fin_cases i
        · exact h00.ge
        · exact hdiv.trans (hmul.trans h10.ge)
        · exact hdiv.trans (hmul.trans h01.ge)
        · exact h11.ge
    | inr i => simp

/-- One simultaneous step on the two-row system shrinks `[0, u]²` to `[0, u / a]²` whenever `1 < a`
and `0 ≤ u ≤ 1`. -/
theorem step_twoRowBox {a u : ℝ} (ha : 1 < a) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    step (twoRowMatrix a) (twoRowBox 1) (twoRowBox u) = twoRowBox (u / a) := by
  rw [step_def, clip_eq_left_iff.mpr (twoRowBox_within hu1),
    up_twoRowBox (zero_lt_one.trans ha) hu0, down_twoRowBox ha hu0]

/-- Exact formula for every raw iterate of the two-row simultaneous system with `1 < a`: lower
endpoints and row endpoints stay `0` while both variable upper endpoints equal `1 / a ^ k`. -/
theorem rawRun_twoRow {a : ℝ} (ha : 1 < a) (k : ℕ) :
    rawRun (twoRowMatrix a) (twoRowBox 1) k = twoRowBox (1 / a ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 1 ≤ a ^ k := one_le_pow₀ ha.le
    rw [rawRun_succ, ih,
      step_twoRowBox ha (by positivity) (div_le_one_of_le₀ hpow (by positivity))]
    congr 1
    rw [pow_succ, div_div]

/-- In the two-row system with `1 < a`, every finite iterate has strictly positive width
`2 / a ^ k`, total width converges to `0`, and no finite iterate stabilizes. -/
theorem twoRow_width_tendsto_and_no_stabilization {a : ℝ} (ha : 1 < a) :
    (∀ k, width (rawRun (twoRowMatrix a) (twoRowBox 1) k) = 2 / a ^ k) ∧
    (∀ k, 0 < width (rawRun (twoRowMatrix a) (twoRowBox 1) k)) ∧
    Tendsto (fun k => width (rawRun (twoRowMatrix a) (twoRowBox 1) k)) atTop (𝓝 0) ∧
    (∀ k, rawRun (twoRowMatrix a) (twoRowBox 1) (k + 1) ≠
      rawRun (twoRowMatrix a) (twoRowBox 1) k) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hw : ∀ k, width (rawRun (twoRowMatrix a) (twoRowBox 1) k) = 2 / a ^ k := fun k => by
    rw [rawRun_twoRow ha k, width_twoRowBox]
    ring
  refine ⟨hw, fun k => by rw [hw]; positivity, ?_, fun k h => ?_⟩
  · have hinv : Tendsto (fun k : ℕ => (a⁻¹) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr ha0.le) (inv_lt_one_of_one_lt₀ ha)
    simpa [hw, div_eq_mul_inv, inv_pow] using hinv.const_mul 2
  · rw [rawRun_twoRow ha (k + 1), rawRun_twoRow ha k] at h
    have hEq : (1 : ℝ) / a ^ (k + 1) = 1 / a ^ k := by
      simpa using congrFun (congrArg Prod.snd h) (.inl 0)
    have hpow : a ^ k < a ^ (k + 1) := by
      rw [pow_succ]
      exact lt_mul_of_one_lt_right (pow_pos ha0 k) ha
    exact (one_div_lt_one_div_of_lt (pow_pos ha0 k) hpow).ne hEq

/-! ### Simultaneous vs sequential updates, contraction, absorption, and fixed points -/

/-- At `a = 2`, one simultaneous step from `[0, 1]²` gives variable uppers `(1/2, 1/2)`, whereas
updating row `0` immediately before evaluating row `1` yields `(1/2, 1/4)`; moreover `[0, 1/2]²`
maps to `[0, 1/4]²` inside the step image of `[0, 1]²`. -/
theorem twoRow_two_step :
    let A := twoRowMatrix 2
    let q₀ := twoRowBox 1
    let q₁ := step A q₀ q₀
    let qMid : Raw 2 2 := (fun _ => 0, Sum.elim ![1 / 2, 1] ![0, 0])
    (q₁.2 (.inl 0) = 1 / 2 ∧ q₁.2 (.inl 1) = 1 / 2) ∧
      (inverseHi A q₀ 0 0 = 1 / 2 ∧ inverseHi A qMid 1 1 = 1 / 4) ∧
      (step A q₀ (twoRowBox (1 / 2)) = twoRowBox (1 / 4) ∧
        Within (step A q₀ (twoRowBox (1 / 2))) q₁) := by
  intro A q₀ q₁ qMid
  have hstep : q₁ = twoRowBox (1 / 2) := step_twoRowBox (by norm_num) zero_le_one le_rfl
  have hhalf : step A q₀ (twoRowBox (1 / 2)) = twoRowBox (1 / 4) := by
    have := step_twoRowBox (a := 2) (u := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hA10 : A 1 0 = 1 := by simp [A, twoRowMatrix]
  have hA11 : A 1 1 = -2 := by simp [A, twoRowMatrix]
  refine ⟨⟨by simp [hstep], by simp [hstep]⟩,
    ⟨(inverseHi_twoRowBox (a := 2) (u := 1) (by norm_num)).1, ?_⟩,
    ⟨hhalf, (twoRowBox_within (by norm_num)).step A q₀⟩⟩
  rw [inverseHi_of_neg (by norm_num [hA11]), restHi_def, erase_one_fin2, Finset.sum_singleton,
    zHi_of_nonneg (by norm_num [hA10])]
  norm_num [qMid, hA10, hA11]

/-- With `a = -1`, `B = [0, 0]`, and rest interval `[-2, 2]`, sign reversal swaps bounds to give
inverse interval `[-2, 2]`. -/
theorem neg_one_inverse_example :
    let A : Matrix (Fin 1) (Fin 2) ℝ := !![-1, 1]
    let q : Raw 2 1 := (Sum.elim ![0, -2] ![0], Sum.elim ![0, 2] ![0])
    restLo A q 0 0 = -2 ∧ restHi A q 0 0 = 2 ∧
      inverseLo A q 0 0 = -2 ∧ inverseHi A q 0 0 = 2 := by
  intro A q
  have hA00 : A 0 0 = -1 := by simp [A]
  have hA01 : A 0 1 = 1 := by simp [A]
  have hrLo : restLo A q 0 0 = -2 := by
    rw [restLo_def, erase_zero_fin2, Finset.sum_singleton, zLo_of_nonneg (by norm_num [hA01])]
    norm_num [q, hA01]
  have hrHi : restHi A q 0 0 = 2 := by
    rw [restHi_def, erase_zero_fin2, Finset.sum_singleton, zHi_of_nonneg (by norm_num [hA01])]
    norm_num [q, hA01]
  exact ⟨hrLo, hrHi,
    by rw [inverseLo_of_neg (by norm_num [hA00]), hrLo]; norm_num [q, hA00],
    by rw [inverseHi_of_neg (by norm_num [hA00]), hrHi]; norm_num [q, hA00]⟩

/-- With no rows, `q = [1, 0]` remains invalid after clipping against `q₀ = [0, 2]` and after
applying `step`; with `A = 0`, `step 0` is continuous and row images are identically zero. -/
theorem invalidity_and_zero_matrix {n m : ℕ} (A₀ : Matrix (Fin 0) (Fin 1) ℝ)
    (r₀ : Raw n m) :
    let q : Raw 1 0 := (fun _ => 1, fun _ => 0)
    let q₀ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    (¬ (clip q q₀).1 ≤ (clip q q₀).2 ∧ ¬ (step A₀ q₀ q).1 ≤ (step A₀ q₀ q).2) ∧
      Continuous (step (0 : Matrix (Fin m) (Fin n) ℝ) r₀) ∧
      ∀ r i, imageLo (0 : Matrix (Fin m) (Fin n) ℝ) r i = 0 ∧
        imageHi (0 : Matrix (Fin m) (Fin n) ℝ) r i = 0 := by
  intro q q₀
  have hq : ¬ q.1 ≤ q.2 := fun h => by
    have := h (.inl 0)
    norm_num [q] at this
  exact ⟨⟨fun hc => hq ((clip_within_left q q₀).le_of_le hc), not_le_step_of_not_le hq⟩,
    continuous_step 0 r₀, fun r i => ⟨imageLo_zero r i, imageHi_zero r i⟩⟩

/-- A zero-coefficient row with `B = [1, 1]` becomes invalid in `up`, absorbs into `publicRun = ⊥`
for all `k ≥ 1`, and admits no enclosed graph point; the same empty absorption holds for `n = 0`
with conflicting row `[1, 1]`. -/
theorem conflicting_row_absorption (A₀ : Matrix (Fin 1) (Fin 0) ℝ) :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let q₀ : Raw 1 1 := (Sum.elim ![0] ![1], Sum.elim ![1] ![1])
    let r₀ : Raw 0 1 := (fun _ => 1, fun _ => 1)
    (¬ (up A q₀).1 ≤ (up A q₀).2 ∧ (∀ k, 1 ≤ k → publicRun A q₀ k = ⊥) ∧
        ∀ x : Fin 1 → ℝ, graph A x ∉ Icc q₀.1 q₀.2) ∧
      (imageLo A₀ r₀ 0 = 0 ∧ imageHi A₀ r₀ 0 = 0 ∧ ∀ k, 1 ≤ k → publicRun A₀ r₀ k = ⊥) := by
  intro A q₀ r₀
  have hup : ¬ (up A q₀).1 ≤ (up A q₀).2 := fun h => by
    have h0 := h (.inr 0)
    simp [A, q₀, up_fst_inr, up_snd_inr] at h0
    norm_num at h0
  have h1 : publicRun A q₀ 1 = ⊥ := by
    rw [publicRun_eq_pack_rawRun, pack_eq_bot_iff, rawRun_succ, rawRun_zero, step_def, clip_self]
    exact fun hd => hup ((down_within A _).le_of_le hd)
  have hlo : imageLo A₀ r₀ 0 = 0 := imageLo_eq_zero_of_row_zero fun j => Fin.elim0 j
  have hhi : imageHi A₀ r₀ 0 = 0 := imageHi_eq_zero_of_row_zero fun j => Fin.elim0 j
  have hr1 : publicRun A₀ r₀ 1 = ⊥ := by
    rw [publicRun_eq_pack_rawRun, pack_eq_bot_iff, rawRun_succ, rawRun_zero, step_def, clip_self]
    intro hd
    have h0 := (down_within A₀ _).le_of_le hd (.inr 0)
    simp [r₀, up_fst_inr, up_snd_inr, hlo, hhi] at h0
    norm_num at h0
  refine ⟨⟨hup, fun k hk => publicRun_eq_bot_of_le hk h1, fun x hx => ?_⟩,
    ⟨hlo, hhi, fun k hk => publicRun_eq_bot_of_le hk hr1⟩⟩
  have h0 := hx.1 (.inr 0)
  simp [A, q₀] at h0
  norm_num at h0

/-- With no rows, every initial tuple is fixed by `step` and stays constant along `rawRun`; at
`n = m = 0`, every public iterate is nonbottom and every raw tuple is fixed and contained in every
iterate. -/
theorem zero_rows_and_empty_dim_fixed {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ) (q₀ : Raw n 0)
    (A₀ : Matrix (Fin 0) (Fin 0) ℝ) (r₀ r : Raw 0 0) :
    Function.IsFixedPt (step A q₀) q₀ ∧ (∀ k, rawRun A q₀ k = q₀) ∧
      (∀ k, publicRun A₀ r₀ k ≠ ⊥) ∧ Function.IsFixedPt (step A₀ r₀) r ∧
      (∀ k, Within r (rawRun A₀ r₀ k)) := by
  have hfix : Function.IsFixedPt (step A q₀) q₀ :=
    (isFixedPt_step_zero_rows_iff A q₀ q₀).mpr Within.rfl
  have hfix0 : Function.IsFixedPt (step A₀ r₀) r :=
    (isFixedPt_step_zero_rows_iff A₀ r₀ r).mpr
      (within_iff.mpr ⟨fun c => c.elim Fin.elim0 Fin.elim0, fun c => c.elim Fin.elim0 Fin.elim0⟩)
  exact ⟨hfix, fun k => by rw [rawRun_def]; exact hfix.iterate k,
    fun k => (publicRun_ne_bot_iff A₀ r₀ k).mpr fun c => c.elim Fin.elim0 Fin.elim0,
    hfix0, within_rawRun_of_isFixedPt_step hfix0⟩

/-- `(0, 0)` survives every public iterate of the `a = 2` two-row example, and for `A = !![-2]` and
`x = ![1]` the graph point has row value `-2` and survives its singleton box. -/
theorem graph_survival_examples :
    (∀ k, graph (twoRowMatrix 2) 0 ∈
        (publicRun (twoRowMatrix 2) (twoRowBox 1) k : Set (Coord 2 2 → ℝ))) ∧
      (let A : Matrix (Fin 1) (Fin 1) ℝ := !![-2]
       let x : Fin 1 → ℝ := ![1]
       graph A x (.inr 0) = -2 ∧
         ∀ k, graph A x ∈ (publicRun A (graph A x, graph A x) k : Set (Coord 1 1 → ℝ))) := by
  refine ⟨fun k => graph_survives (twoRowMatrix 2) (twoRowBox 1) 0
      (mem_Icc_graph_iff.mpr ⟨fun _ => by simp, fun _ => by simp⟩) k, ?_⟩
  intro A x
  exact ⟨by simp [A, x, Matrix.mulVec, dotProduct],
    fun k => graph_survives A _ x ⟨le_rfl, le_rfl⟩ k⟩

/-- With no rows and initial box `[0, 2]`, both `[0, 1]` and `[1, 2]` are fixed and lie in every
raw iterate, whereas `[0, 3]` fails fixedness because clipping reduces its upper endpoint to `2`. -/
theorem zero_rows_fixed_and_nonfixed (A : Matrix (Fin 0) (Fin 1) ℝ) :
    let q₀ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    let q₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let q₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    let q₃ : Raw 1 0 := (fun _ => 0, fun _ => 3)
    (∀ k, Within q₁ (rawRun A q₀ k)) ∧
      (∀ k, Within q₂ (rawRun A q₀ k)) ∧
      ¬ Function.IsFixedPt (step A q₀) q₃ := by
  intro q₀ q₁ q₂ q₃
  have h1 : Function.IsFixedPt (step A q₀) q₁ :=
    (isFixedPt_step_zero_rows_iff A q₀ q₁).mpr
      (within_iff.mpr ⟨fun _ => le_rfl, fun _ => by norm_num [q₀, q₁]⟩)
  have h2 : Function.IsFixedPt (step A q₀) q₂ :=
    (isFixedPt_step_zero_rows_iff A q₀ q₂).mpr
      (within_iff.mpr ⟨fun _ => by norm_num [q₀, q₂], fun _ => le_rfl⟩)
  refine ⟨within_rawRun_of_isFixedPt_step h1, within_rawRun_of_isFixedPt_step h2, fun h3 => ?_⟩
  have hle := ((isFixedPt_step_zero_rows_iff A q₀ q₃).mp h3).le_snd (.inl 0)
  norm_num [q₀, q₃] at hle

/-! ### The endpoint limit -/

/-- In the two-row system with `1 < a`, every public iterate is nonempty, the endpoint limit is the
all-zero singleton `twoRowBox 0`, which is a fixed tuple, and no finite iterate reaches it. -/
theorem twoRow_endpointLimit {a : ℝ} (ha : 1 < a) :
    (∀ k, (publicRun (twoRowMatrix a) (twoRowBox 1) k : Set (Coord 2 2 → ℝ)).Nonempty) ∧
      endpointLimit (twoRowMatrix a) (twoRowBox 1) = twoRowBox 0 ∧
      (twoRowBox 0).1 = (twoRowBox 0).2 ∧
      Function.IsFixedPt (step (twoRowMatrix a) (twoRowBox 1)) (twoRowBox 0) ∧
      (∀ k, rawRun (twoRowMatrix a) (twoRowBox 1) k ≠ twoRowBox 0) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hord (k : ℕ) :
      (rawRun (twoRowMatrix a) (twoRowBox 1) k).1 ≤ (rawRun (twoRowMatrix a) (twoRowBox 1) k).2 :=
    fun c => by
      rw [rawRun_twoRow ha k]
      cases c with
      | inl j => simp only [twoRowBox_fst, twoRowBox_snd_inl]; positivity
      | inr i => simp
  have hinv : Tendsto (fun k : ℕ => 1 / a ^ k) atTop (𝓝 0) := by
    simpa [one_div, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr ha0.le) (inv_lt_one_of_one_lt₀ ha)
  have hlim : endpointLimit (twoRowMatrix a) (twoRowBox 1) = twoRowBox 0 := by
    refine Prod.ext (funext fun c => ?_) (funext fun c => ?_)
    · exact tendsto_nhds_unique (tendsto_rawRun_fst hord c) (by simp [rawRun_twoRow ha])
    · cases c with
      | inl j =>
        exact tendsto_nhds_unique (tendsto_rawRun_snd hord _)
          (by simpa [rawRun_twoRow ha] using hinv)
      | inr i => exact tendsto_nhds_unique (tendsto_rawRun_snd hord _) (by simp [rawRun_twoRow ha])
  refine ⟨fun k => (coe_publicRun_nonempty_iff _ _ k).mpr (hord k), hlim,
    funext fun c => by cases c <;> simp, hlim ▸ isFixedPt_step_endpointLimit hord, fun k h => ?_⟩
  · rw [rawRun_twoRow ha k] at h
    have h0 : (1 : ℝ) / a ^ k = 0 := by simpa using congrFun (congrArg Prod.snd h) (.inl 0)
    exact (one_div_pos.mpr (pow_pos ha0 k)).ne' h0

/-- With no rows, the endpoint limit is the initial tuple; for the initial box `[0, 2]`, the smaller
fixed boxes `[0, 1]` and `[1, 2]` both lie within it. -/
theorem zero_rows_endpointLimit {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ) (q₀ : Raw n 0)
    (A₁ : Matrix (Fin 0) (Fin 1) ℝ) :
    let r₀ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    let r₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let r₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    endpointLimit A q₀ = q₀ ∧ Within r₁ (endpointLimit A₁ r₀) ∧
      Within r₂ (endpointLimit A₁ r₀) := by
  intro r₀ r₁ r₂
  have h1 : Function.IsFixedPt (step A₁ r₀) r₁ :=
    (isFixedPt_step_zero_rows_iff A₁ r₀ r₁).mpr
      (within_iff.mpr ⟨fun _ => le_rfl, fun _ => by norm_num [r₀, r₁]⟩)
  have h2 : Function.IsFixedPt (step A₁ r₀) r₂ :=
    (isFixedPt_step_zero_rows_iff A₁ r₀ r₂).mpr
      (within_iff.mpr ⟨fun _ => by norm_num [r₀, r₂], fun _ => le_rfl⟩)
  exact ⟨endpointLimit_eq_self_of_isFixedPt ((isFixedPt_step_zero_rows_iff A q₀ q₀).mpr Within.rfl),
    within_endpointLimit_of_isFixedPt_step h1, within_endpointLimit_of_isFixedPt_step h2⟩

/-- At `n = m = 0`, the endpoint limit is the unique raw tuple and its public state is
nonbottom. -/
theorem empty_dim_endpointLimit (A : Matrix (Fin 0) (Fin 0) ℝ) (q₀ q : Raw 0 0) :
    endpointLimit A q₀ = q ∧ pack (endpointLimit A q₀) ≠ ⊥ :=
  ⟨Subsingleton.elim _ _, pack_ne_bot_iff.mpr fun c => c.elim Fin.elim0 Fin.elim0⟩

/-- The zero-coefficient row with `B = [1, 1]` has an empty public iterate, and hence no ordered raw
fixed tuple. -/
theorem conflicting_row_no_fixed :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let q₀ : Raw 1 1 := (Sum.elim ![0] ![1], Sum.elim ![1] ![1])
    ¬ (∀ k, (publicRun A q₀ k : Set (Coord 1 1 → ℝ)).Nonempty) ∧
      ¬ ∃ q : Raw 1 1, q.1 ≤ q.2 ∧ Function.IsFixedPt (step A q₀) q := by
  intro A q₀
  have h1 : publicRun A q₀ 1 = ⊥ := (conflicting_row_absorption 0).1.2.1 1 le_rfl
  have hne : ¬ ∀ k, (publicRun A q₀ k : Set (Coord 1 1 → ℝ)).Nonempty := fun h => by
    have h1' := h 1
    rw [h1, Interval.coe_bot] at h1'
    exact not_nonempty_empty h1'
  exact ⟨hne, fun hq => hne
    ((forall_coe_publicRun_nonempty_iff_exists_isFixedPt_step A q₀).mpr hq)⟩

/-! ### The scalar linear program -/

/-- For `A = !![-2]` and `x = ![1]`, the singleton graph assignment has both products `-2`, both
inverse endpoints of the singleton box are `1`, and the assignment is feasible for that box. -/
theorem neg_coeff_graphAssignment :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![-2]
    let x : Fin 1 → ℝ := ![1]
    let q : Raw 1 1 := (graph A x, graph A x)
    (graphAssignment A x).zL 0 0 = -2 ∧ (graphAssignment A x).zU 0 0 = -2 ∧
      inverseLo A q 0 0 = 1 ∧ inverseHi A q 0 0 = 1 ∧ IsFeasible A q (graphAssignment A x) := by
  intro A x q
  have hA : A 0 0 < 0 := by norm_num [A]
  have hrow : graph A x (.inr 0) = -2 := by simp [A, x, Matrix.mulVec, dotProduct]
  refine ⟨by simp [A, x], by simp [A, x], ?_, ?_, isFeasible_graphAssignment ⟨le_rfl, le_rfl⟩⟩
  · rw [inverseLo_of_neg hA, restLo_eq_zero_of_subsingleton]
    norm_num [q, hrow, A]
  · rw [inverseHi_of_neg hA, restHi_eq_zero_of_subsingleton]
    norm_num [q, hrow, A]

/-- For `A = !![1, 0]`, both product unknowns at the zero coefficient of every feasible
assignment are `0`, so they cannot act as free variables in the row sum. -/
theorem zero_coeff_products_of_isFeasible {q₀ : Raw 2 1} {p : Assignment 2 1}
    (h : IsFeasible !![1, 0] q₀ p) : p.zL 0 1 = 0 ∧ p.zU 0 1 = 0 :=
  ⟨h.zL_eq_zero rfl, h.zU_eq_zero rfl⟩

/-- With no rows and initial box `[0, 2]`, the canonical assignments of `[0, 1]` and `[1, 2]` are
feasible with objective `1` and that of `[0, 2]` is feasible with objective `2`, whereas `[0, 3]` is
neither fixed nor feasible. -/
theorem zero_rows_feasible_assignments (A : Matrix (Fin 0) (Fin 1) ℝ) :
    let q₀ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    let q₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let q₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    let q₃ : Raw 1 0 := (fun _ => 0, fun _ => 3)
    (IsFeasible A q₀ (canonical A q₁) ∧ objective (canonical A q₁) = 1) ∧
      (IsFeasible A q₀ (canonical A q₂) ∧ objective (canonical A q₂) = 1) ∧
      (IsFeasible A q₀ (canonical A q₀) ∧ objective (canonical A q₀) = 2) ∧
      ¬ Function.IsFixedPt (step A q₀) q₃ ∧ ¬ IsFeasible A q₀ (canonical A q₃) := by
  intro q₀ q₁ q₂ q₃
  obtain ⟨h1, h2, h3⟩ := zero_rows_fixed_and_nonfixed A
  have hfeas : ∀ q : Raw 1 0, q.1 ≤ q.2 → Within q q₀ → IsFeasible A q₀ (canonical A q) :=
    fun q hq hw => isFeasible_canonical_iff.mpr ⟨hq, (isFixedPt_step_zero_rows_iff A q₀ q).mpr hw⟩
  refine ⟨⟨hfeas q₁ (fun _ => by norm_num [q₁]) (rawRun_zero A q₀ ▸ h1 0),
      by simp [q₁, objective_eq_sum_add_sum]⟩,
    ⟨hfeas q₂ (fun _ => by norm_num [q₂]) (rawRun_zero A q₀ ▸ h2 0),
      by norm_num [q₂, objective_eq_sum_add_sum]⟩,
    ⟨hfeas q₀ (fun _ => by norm_num [q₀]) Within.rfl, by simp [q₀, objective_eq_sum_add_sum]⟩,
    h3, fun h => h3 (isFeasible_canonical_iff.mp h).2⟩

/-- A zero row with row bounds `[1, 1]` admits no feasible assignment, since by
`conflicting_row_no_fixed` it has no ordered fixed tuple; with zero variables and row bounds
`[1, 1]`, no graph point lies in the initial box and the program is again infeasible. -/
theorem zero_row_conflict_infeasible (A₀ : Matrix (Fin 1) (Fin 0) ℝ) :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let q₀ : Raw 1 1 := (Sum.elim ![0] ![1], Sum.elim ![1] ![1])
    let r₀ : Raw 0 1 := (fun _ => 1, fun _ => 1)
    (¬ ∃ p, IsFeasible A q₀ p) ∧
      (∀ x, graph A₀ x ∉ Icc r₀.1 r₀.2) ∧ ¬ ∃ p, IsFeasible A₀ r₀ p := by
  intro A q₀ r₀
  refine ⟨exists_isFeasible_iff.not.mpr conflicting_row_no_fixed.2, fun x hx => ?_,
    fun ⟨p, h⟩ => ?_⟩
  · have h0 := hx.1 (.inr 0)
    simp [r₀, Matrix.mulVec, dotProduct] at h0
    norm_num at h0
  · have hu := h.le_sum_zU 0
    have hw := h.within.fst_le (.inr 0)
    have ho := h.fst_le_snd (.inr 0)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hu
    simp only [r₀] at hw
    linarith

/-- Coefficient matrix of the equality rows `x₀ + x₁ + x₂`, `x₀ + x₁ - x₂`, `x₀ - x₁ + x₂` and
`-x₀ + x₁ + x₂`. -/
def fourRowMatrix : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1, 1, 1; 1, 1, -1; 1, -1, 1; -1, 1, 1]

/-- Variable box `[-1, 1]³` with row values `0, 0, 0, 1`. -/
def fourRowBox : Raw 3 4 :=
  (Sum.elim (fun _ => -1) ![0, 0, 0, 1], Sum.elim (fun _ => 1) ![0, 0, 0, 1])

private theorem fourRowMatrix_eq (i : Fin 4) (j : Fin 3) :
    fourRowMatrix i j = 1 ∨ fourRowMatrix i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp [fourRowMatrix]

private theorem zLo_fourRowBox (i : Fin 4) (j : Fin 3) :
    zLo fourRowMatrix fourRowBox i j = -1 := by
  rcases fourRowMatrix_eq i j with h | h
  · rw [zLo_of_nonneg (by rw [h]; norm_num), h]
    simp [fourRowBox]
  · rw [zLo_of_nonpos (by rw [h]; norm_num), h]
    simp [fourRowBox]

private theorem zHi_fourRowBox (i : Fin 4) (j : Fin 3) :
    zHi fourRowMatrix fourRowBox i j = 1 := by
  rcases fourRowMatrix_eq i j with h | h
  · rw [zHi_of_nonneg (by rw [h]; norm_num), h]
    simp [fourRowBox]
  · rw [zHi_of_nonpos (by rw [h]; norm_num), h]
    simp [fourRowBox]

private theorem fourRowBox_inr (i : Fin 4) :
    0 ≤ fourRowBox.1 (.inr i) ∧ fourRowBox.2 (.inr i) ≤ 1 ∧
      fourRowBox.1 (.inr i) = fourRowBox.2 (.inr i) := by
  fin_cases i <;> norm_num [fourRowBox]

/-- In the four-row example every inverse interval contains the variable interval `[-1, 1]`. -/
theorem fourRow_inverse_bounds (i : Fin 4) (j : Fin 3) :
    inverseLo fourRowMatrix fourRowBox i j ≤ -1 ∧ 1 ≤ inverseHi fourRowMatrix fourRowBox i j := by
  have hrLo : restLo fourRowMatrix fourRowBox i j = -2 := by
    simp [restLo_def, zLo_fourRowBox, Finset.card_erase_of_mem]
  have hrHi : restHi fourRowMatrix fourRowBox i j = 2 := by
    simp [restHi_def, zHi_fourRowBox, Finset.card_erase_of_mem]
  obtain ⟨h0, h1, h2⟩ := fourRowBox_inr i
  rcases fourRowMatrix_eq i j with h | h
  · rw [inverseLo_of_pos (by rw [h]; norm_num), inverseHi_of_pos (by rw [h]; norm_num), hrLo,
      hrHi, h]
    constructor <;> linarith
  · rw [inverseLo_of_neg (by rw [h]; norm_num), inverseHi_of_neg (by rw [h]; norm_num), hrLo,
      hrHi, h]
    constructor <;> linarith

/-- The four-row box is an ordered fixed tuple for itself as initial box, so its canonical
assignment is feasible, yet no graph point lies in it: the first three equalities force `x = 0`,
contradicting the fourth. Thus feasibility of the program does not give an affine graph point. -/
theorem fourRow_feasible_without_graph_point :
    fourRowBox.1 ≤ fourRowBox.2 ∧ Function.IsFixedPt (step fourRowMatrix fourRowBox) fourRowBox ∧
      IsFeasible fourRowMatrix fourRowBox (canonical fourRowMatrix fourRowBox) ∧
      ∀ x, graph fourRowMatrix x ∉ Icc fourRowBox.1 fourRowBox.2 := by
  have hle : fourRowBox.1 ≤ fourRowBox.2 := fun c => by
    cases c with
    | inl j => norm_num [fourRowBox]
    | inr i => exact (fourRowBox_inr i).2.2.le
  have hfix : Function.IsFixedPt (step fourRowMatrix fourRowBox) fourRowBox := by
    refine isFixedPt_step_iff.mpr ⟨Within.rfl, fun i => ?_, fun i j => ?_⟩
    · obtain ⟨h0, h1, -⟩ := fourRowBox_inr i
      simp only [imageLo_def, imageHi_def, zLo_fourRowBox, zHi_fourRowBox, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      constructor <;> linarith
    · obtain ⟨hlo, hhi⟩ := fourRow_inverse_bounds i j
      exact ⟨hlo.trans_eq (by simp [fourRowBox]), (by simp [fourRowBox] : _ = (1 : ℝ)).trans_le hhi⟩
  refine ⟨hle, hfix, isFeasible_canonical_iff.mpr ⟨hle, hfix⟩, fun x hx => ?_⟩
  obtain ⟨-, hrow⟩ := mem_Icc_graph_iff.mp hx
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h3 := hrow 3
  simp [fourRowMatrix, fourRowBox, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2 h3
  linarith

end

end TauCeti.AffineBoundTightening.Examples
