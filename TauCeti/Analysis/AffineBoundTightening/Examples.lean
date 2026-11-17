/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.AffineBoundTightening.Step
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Worked examples for finite simultaneous affine bound tightening

This file records concrete sanity checks for joint endpoint intervals, signed affine arithmetic,
simultaneous propagation, invalidity absorption, graph-point retention, and fixed-tuple containment,
and analyzes the two-row linear system `a * x₁ - x₂ = 0`, `x₁ - a * x₂ = 0` on `[0, 1]²`.

Under simultaneous tightening with `a ≥ 1`, the `k`-th iterate is `[0, 1 / a ^ k]² × [0, 0]²` with
total width `2 / a ^ k`. When `a > 1`, the width stays strictly positive for every `k` and tends to
`0`, so the simultaneous iteration does not stabilize in finitely many steps while retaining the
graph point `(0, 0)`. At `a = 2`, a single simultaneous step gives variable uppers `(1 / 2, 1 / 2)`,
whereas updating row `0` and feeding the updated box immediately into row `1` gives upper bound
`1 / 4` on the second variable.

## Main definitions

* `TauCeti.AffineBoundTightening.twoRowMatrix`: the `2 × 2` matrix `!![a, -1; 1, -a]`.
* `TauCeti.AffineBoundTightening.twoRowBox`: the symmetric joint box `[0, t]² × [0, 0]²`.

## Main results

* `TauCeti.AffineBoundTightening.step_twoRowBox`: for `1 ≤ a` and `0 ≤ t ≤ 1`, one simultaneous step
  maps `twoRowBox t` to `twoRowBox (t / a)`.
* `TauCeti.AffineBoundTightening.rawRun_twoRow`: for `1 ≤ a`, the `k`-th simultaneous iterate is
  `twoRowBox (1 / a ^ k)`.
* `TauCeti.AffineBoundTightening.tendsto_width_rawRun_twoRow`,
  `TauCeti.AffineBoundTightening.rawRun_twoRow_succ_ne`: for `1 < a`, the total width tends to `0`
  and the sequence never stabilizes in finitely many steps.
* `TauCeti.AffineBoundTightening.graph_zero_mem_publicRun_twoRow`: the graph point `(0, 0)` belongs
  to every public iterate.
* `TauCeti.AffineBoundTightening.twoRow_sequential_inverseHi_lt_simultaneous`: at `a = 2`, one
  sequential row-0-then-row-1 inverse upper bound for `x₂` is strictly tighter than the simultaneous
  step.

## References

* P. Belotti et al., *On feasibility based bounds tightening*, Optimization Online (2012),
  Example 2.4, p. 8 (adapted from sequential row-by-row updates to simultaneous updates).
-/

public section

open scoped Topology
open Filter Function Set

namespace TauCeti.AffineBoundTightening

/-! ### Endpoint, width, and signed-arithmetic checks -/

-- Unordered endpoints `([1], [0])` pack to `⊥`, while `[0, 1]` contains `1 / 2`.
example :
    pack ((fun _ => (1 : ℝ), fun _ => (0 : ℝ)) : Raw 1 0) = ⊥ ∧
      (fun _ => (1 / 2 : ℝ)) ∈ pack ((fun _ => (0 : ℝ), fun _ => (1 : ℝ)) : Raw 1 0) := by
  refine ⟨(pack_eq_bot_iff _).mpr fun h => ?_, (mem_pack _ _).mpr ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · linarith [h (.inl 0)]
  · norm_num
  · norm_num

-- A singleton packed interval contains exactly its endpoint.
example {n m : ℕ} (y z : Coord n m → ℝ) : z ∈ pack (y, y) ↔ z = y := by
  simp [le_antisymm_iff]

-- At `n = m = 0`, every raw tuple packs to a nonbottom state containing the empty function,
-- has width `0`, is fixed by `step`, and lies within every raw iterate.
example (A : Matrix (Fin 0) (Fin 0) ℝ) (q₀ q : Raw 0 0) (k : ℕ) :
    pack q ≠ ⊥ ∧
      (Sum.elim Fin.elim0 Fin.elim0 : Coord 0 0 → ℝ) ∈ pack q ∧
      width q = 0 ∧
      IsFixedPt (step A q₀) q ∧
      Within q (rawRun A q₀ k) ∧
      publicRun A q₀ k ≠ ⊥ := by
  have hfix : IsFixedPt (step A q₀) q := by
    rw [IsFixedPt, step_eq_clip_of_zero_rows]
    exact raw_ext (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  refine ⟨by simp, (mem_pack q _).mpr ⟨fun c => c.elim Fin.elim0 Fin.elim0,
    fun c => c.elim Fin.elim0 Fin.elim0⟩, by simp [width_def], hfix,
    within_rawRun_of_isFixedPt hfix k, ?_⟩
  rw [publicRun_eq_pack_rawRun]
  simp

-- Degenerate dimensions `(0, 1)` and `(1, 0)` pack ordered tuples to nonbottom states, and with
-- zero variables every row image is `[0, 0]`.
example (A : Matrix (Fin 1) (Fin 0) ℝ) :
    pack ((fun _ => (0 : ℝ), fun _ => (1 : ℝ)) : Raw 0 1) ≠ ⊥ ∧
      pack ((fun _ => (0 : ℝ), fun _ => (1 : ℝ)) : Raw 1 0) ≠ ⊥ ∧
      imageLo A (fun _ => 0, fun _ => 1) 0 = 0 ∧
      imageHi A (fun _ => 0, fun _ => 1) 0 = 0 := by
  refine ⟨?_, ?_, by simp [imageLo_def], by simp [imageHi_def]⟩
  · rw [ne_eq, pack_eq_bot_iff, not_not]
    exact fun _ => by norm_num
  · rw [ne_eq, pack_eq_bot_iff, not_not]
    exact fun _ => by norm_num

-- `[0, 1]` and `[1, 2]` have equal width `1` yet are unequal and incomparable, while `[0, 1]`
-- lies inside `[0, 2]` with strictly smaller width.
example :
    let q₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let q₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    let q₃ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    width q₁ = 1 ∧ width q₂ = 1 ∧ q₁ ≠ q₂ ∧ ¬ Within q₁ q₂ ∧ ¬ Within q₂ q₁ ∧
      Within q₁ q₃ ∧ width q₁ < width q₃ := by
  dsimp only
  have hw1 : width ((fun _ => (0 : ℝ), fun _ => (1 : ℝ)) : Raw 1 0) = 1 := by
    simp [width_eq_sum_var_add_row]
  have hw2 : width ((fun _ => (1 : ℝ), fun _ => (2 : ℝ)) : Raw 1 0) = 1 := by
    simp [width_eq_sum_var_add_row]
    norm_num
  have hw3 : width ((fun _ => (0 : ℝ), fun _ => (2 : ℝ)) : Raw 1 0) = 2 := by
    simp [width_eq_sum_var_add_row]
  refine ⟨hw1, hw2, ?_, ?_, ?_, within_def.mpr ⟨fun _ => le_rfl, fun _ => by norm_num⟩, ?_⟩
  · intro h
    have h0 := congrFun (congrArg Prod.fst h) (.inl 0)
    norm_num at h0
  · intro h
    linarith [h.le_fst (.inl 0)]
  · intro h
    linarith [h.snd_le (.inl 0)]
  · linarith

-- Signed product for `a = -2`, `X = [1, 3]` is `[-6, -2]` enclosing `-4` at `x = 2`; one-variable
-- omitted sum is `0`; zero coefficients and zero rows yield `[0, 0]`.
example :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![-2]
    let q : Raw 1 1 := (Sum.elim ![1] ![0], Sum.elim ![3] ![0])
    zLo A q 0 0 = -6 ∧ zHi A q 0 0 = -2 ∧
      A.mulVec ![2] 0 = -4 ∧ A.mulVec ![2] 0 ∈ Icc (zLo A q 0 0) (zHi A q 0 0) ∧
      restLo A q 0 0 = 0 ∧ restHi A q 0 0 = 0 ∧
      zLo (0 : Matrix (Fin 1) (Fin 1) ℝ) q 0 0 = 0 ∧
      zHi (0 : Matrix (Fin 1) (Fin 1) ℝ) q 0 0 = 0 ∧
      imageLo (0 : Matrix (Fin 1) (Fin 1) ℝ) q 0 = 0 ∧
      imageHi (0 : Matrix (Fin 1) (Fin 1) ℝ) q 0 = 0 := by
  dsimp only
  have hneg : (!![(-2 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 ≤ 0 := by norm_num
  have hzL : zLo !![(-2 : ℝ)] (Sum.elim ![1] ![0], Sum.elim ![3] ![0]) 0 0 = -6 := by
    rw [zLo_of_nonpos hneg]
    norm_num
  have hzU : zHi !![(-2 : ℝ)] (Sum.elim ![1] ![0], Sum.elim ![3] ![0]) 0 0 = -2 := by
    rw [zHi_of_nonpos hneg]
    norm_num
  have hmul : (!![(-2 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ).mulVec ![2] 0 = -4 := by
    simp [Matrix.mulVec, dotProduct]
    norm_num
  refine ⟨hzL, hzU, hmul, ?_, by simp [restLo_def], by simp [restHi_def],
    zLo_zero _ 0 0, zHi_zero _ 0 0, imageLo_zero _ 0, imageHi_zero _ 0⟩
  rw [hmul, hzL, hzU]
  constructor <;> norm_num

-- A zero column contributes zero to every row, and with `A = 0` row images are continuously zero.
example {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n)
    (hcol : ∀ i, A i j = 0) (i : Fin m) :
    restLo A q i j = imageLo A q i ∧ restHi A q i j = imageHi A q i ∧
      Continuous (fun r : Raw n m => imageLo (0 : Matrix (Fin m) (Fin n) ℝ) r i) ∧
      Continuous (fun r : Raw n m => imageHi (0 : Matrix (Fin m) (Fin n) ℝ) r i) :=
  ⟨restLo_eq_imageLo_of_eq_zero (hcol i), restHi_eq_imageHi_of_eq_zero (hcol i),
    continuous_imageLo 0 i, continuous_imageHi 0 i⟩

/-! ### Operator, invalidity, and graph-survival checks -/

-- Negative row inversion (`a = -1`, `B = [0, 0]`, rest `[-2, 2]`) swaps row/rest bounds.
example :
    let A : Matrix (Fin 1) (Fin 2) ℝ := !![-1, 1]
    let q : Raw 2 1 := (Sum.elim ![0, -2] ![0], Sum.elim ![0, 2] ![0])
    restLo A q 0 0 = -2 ∧ restHi A q 0 0 = 2 ∧
      inverseLo A q 0 0 = -2 ∧ inverseHi A q 0 0 = 2 := by
  dsimp only
  have herase : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have hpos : 0 ≤ (!![(-1 : ℝ), 1] : Matrix (Fin 1) (Fin 2) ℝ) 0 1 := by norm_num
  have hneg : (!![(-1 : ℝ), 1] : Matrix (Fin 1) (Fin 2) ℝ) 0 0 < 0 := by norm_num
  have hrestL : restLo !![(-1 : ℝ), 1]
      (Sum.elim ![0, -2] ![0], Sum.elim ![0, 2] ![0]) 0 0 = -2 := by
    rw [restLo_def, herase, Finset.sum_singleton, zLo_of_nonneg hpos]
    norm_num
  have hrestU : restHi !![(-1 : ℝ), 1]
      (Sum.elim ![0, -2] ![0], Sum.elim ![0, 2] ![0]) 0 0 = 2 := by
    rw [restHi_def, herase, Finset.sum_singleton, zHi_of_nonneg hpos]
    norm_num
  refine ⟨hrestL, hrestU, ?_, ?_⟩
  · rw [inverseLo_of_neg hneg, hrestL]
    norm_num
  · rw [inverseHi_of_neg hneg, hrestU]
    norm_num

-- With no rows, an unordered tuple stays invalid under `clip` and `step`, subboxes `[0, 1]` and
-- `[1, 2]` of `[0, 2]` are fixed and lie within every iterate, and `[0, 3]` is not fixed.
example (A : Matrix (Fin 0) (Fin 1) ℝ) (k : ℕ) :
    let q₀ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    let qBad : Raw 1 0 := (fun _ => 1, fun _ => 0)
    let q₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let q₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    let qOut : Raw 1 0 := (fun _ => 0, fun _ => 3)
    ¬ (clip qBad q₀).1 ≤ (clip qBad q₀).2 ∧
      ¬ (step A q₀ qBad).1 ≤ (step A q₀ qBad).2 ∧
      IsFixedPt (step A q₀) q₀ ∧
      rawRun A q₀ k = q₀ ∧
      IsFixedPt (step A q₀) q₁ ∧ Within q₁ (rawRun A q₀ k) ∧
      IsFixedPt (step A q₀) q₂ ∧ Within q₂ (rawRun A q₀ k) ∧
      ¬ IsFixedPt (step A q₀) qOut := by
  dsimp only
  have hbad : ¬ ((fun _ => (1 : ℝ), fun _ => (0 : ℝ)) : Raw 1 0).1 ≤ (fun _ => (0 : ℝ)) :=
    fun h => by linarith [h (.inl 0)]
  have hfix0 : IsFixedPt (step A (fun _ => 0, fun _ => 2)) (fun _ => 0, fun _ => 2) := by
    simp [IsFixedPt]
  have hfix1 : IsFixedPt (step A (fun _ => 0, fun _ => 2)) (fun _ => 0, fun _ => 1) := by
    rw [IsFixedPt, step_eq_clip_of_zero_rows]
    exact clip_eq_self_of_within (within_def.mpr ⟨fun _ => le_rfl, fun _ => by norm_num⟩)
  have hfix2 : IsFixedPt (step A (fun _ => 0, fun _ => 2)) (fun _ => 1, fun _ => 2) := by
    rw [IsFixedPt, step_eq_clip_of_zero_rows]
    exact clip_eq_self_of_within (within_def.mpr ⟨fun _ => by norm_num, fun _ => le_rfl⟩)
  refine ⟨(clip_within_left _ _).not_le_of_not_le hbad,
    not_le_step_of_not_le A _ hbad, hfix0, rawRun_eq_of_isFixedPt hfix0 k,
    hfix1, within_rawRun_of_isFixedPt hfix1 k,
    hfix2, within_rawRun_of_isFixedPt hfix2 k, ?_⟩
  intro hfixOut
  have hstep := congrFun (congrArg Prod.snd hfixOut.eq) (.inl 0)
  rw [step_eq_clip_of_zero_rows, clip_snd] at hstep
  norm_num at hstep

-- A zero row with conflicting target `B = [1, 1]` becomes invalid in `up`, absorbs to `⊥` from
-- step `1` onward (for every `n`, including `n = 0`), and admits no graph point.
example (n : ℕ) :
    let A : Matrix (Fin 1) (Fin n) ℝ := 0
    let q₀ : Raw n 1 := (Sum.elim (fun _ => 0) ![1], Sum.elim (fun _ => 1) ![1])
    ¬ (up A q₀).1 ≤ (up A q₀).2 ∧
      (∀ k, 1 ≤ k → publicRun A q₀ k = ⊥) ∧
      (∀ x : Fin n → ℝ, graph A x ∉ Icc q₀.1 q₀.2) := by
  dsimp only
  have hup : ¬ (up (0 : Matrix (Fin 1) (Fin n) ℝ)
      (Sum.elim (fun _ => 0) ![1], Sum.elim (fun _ => 1) ![1])).1 ≤
      (up (0 : Matrix (Fin 1) (Fin n) ℝ)
        (Sum.elim (fun _ => 0) ![1], Sum.elim (fun _ => 1) ![1])).2 := by
    intro h
    have h0 := h (.inr 0)
    simp at h0
    norm_num at h0
  have hstep1 : publicRun (0 : Matrix (Fin 1) (Fin n) ℝ)
      (Sum.elim (fun _ => 0) ![1], Sum.elim (fun _ => 1) ![1]) 1 = ⊥ := by
    rw [publicRun_eq_bot_iff, rawRun_succ, rawRun_zero, step_def, clip_self]
    exact (down_within _ _).not_le_of_not_le hup
  refine ⟨hup, fun k hk => publicRun_eq_bot_of_le _ _ hk hstep1, fun x hx => ?_⟩
  have h0 := hx.1 (.inr 0)
  simp at h0
  norm_num at h0

-- For `A = (-2)` and `x = 1`, the graph point has row value `-2` and survives its singleton box.
example (k : ℕ) :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![-2]
    let x : Fin 1 → ℝ := ![1]
    graph A x (.inr 0) = -2 ∧
      graph A x ∈ (publicRun A (graph A x, graph A x) k : Set (Coord 1 1 → ℝ)) := by
  dsimp only
  refine ⟨?_, graph_survives _ _ _ (left_mem_Icc.mpr le_rfl) k⟩
  simp [Matrix.mulVec, dotProduct]

/-! ### Non-stabilizing two-row simultaneous recurrence (`a > 1`) -/

/-- The `2 × 2` coefficient matrix for `a * x₁ - x₂ = 0` and `x₁ - a * x₂ = 0`. -/
def twoRowMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, -1; 1, -a]

/-- Symmetric joint box `[0, t]² × [0, 0]²` for the two-row recurrence. -/
def twoRowBox (t : ℝ) : Raw 2 2 :=
  (fun _ => 0, Sum.elim (fun _ => t) (fun _ => 0))

@[simp]
theorem twoRowMatrix_zero_zero (a : ℝ) : twoRowMatrix a 0 0 = a := (rfl)

@[simp]
theorem twoRowMatrix_zero_one (a : ℝ) : twoRowMatrix a 0 1 = -1 := (rfl)

@[simp]
theorem twoRowMatrix_one_zero (a : ℝ) : twoRowMatrix a 1 0 = 1 := (rfl)

@[simp]
theorem twoRowMatrix_one_one (a : ℝ) : twoRowMatrix a 1 1 = -a := (rfl)

@[simp]
theorem twoRowBox_fst (t : ℝ) (c : Coord 2 2) : (twoRowBox t).1 c = 0 := (rfl)

@[simp]
theorem twoRowBox_snd_inl (t : ℝ) (j : Fin 2) : (twoRowBox t).2 (.inl j) = t := (rfl)

@[simp]
theorem twoRowBox_snd_inr (t : ℝ) (i : Fin 2) : (twoRowBox t).2 (.inr i) = 0 := (rfl)

private theorem zLo_twoRowBox {a t : ℝ} (ha : 0 ≤ a) :
    zLo (twoRowMatrix a) (twoRowBox t) 0 0 = 0 ∧
      zLo (twoRowMatrix a) (twoRowBox t) 0 1 = -t ∧
      zLo (twoRowMatrix a) (twoRowBox t) 1 0 = 0 ∧
      zLo (twoRowMatrix a) (twoRowBox t) 1 1 = -(a * t) := by
  have h00 : 0 ≤ twoRowMatrix a 0 0 := by simpa using ha
  have h01 : twoRowMatrix a 0 1 ≤ 0 := by norm_num
  have h10 : 0 ≤ twoRowMatrix a 1 0 := by norm_num
  have h11 : twoRowMatrix a 1 1 ≤ 0 := by simp [ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [zLo_of_nonneg h00]; simp
  · rw [zLo_of_nonpos h01]; simp
  · rw [zLo_of_nonneg h10]; simp
  · rw [zLo_of_nonpos h11]; simp

private theorem zHi_twoRowBox {a t : ℝ} (ha : 0 ≤ a) :
    zHi (twoRowMatrix a) (twoRowBox t) 0 0 = a * t ∧
      zHi (twoRowMatrix a) (twoRowBox t) 0 1 = 0 ∧
      zHi (twoRowMatrix a) (twoRowBox t) 1 0 = t ∧
      zHi (twoRowMatrix a) (twoRowBox t) 1 1 = 0 := by
  have h00 : 0 ≤ twoRowMatrix a 0 0 := by simpa using ha
  have h01 : twoRowMatrix a 0 1 ≤ 0 := by norm_num
  have h10 : 0 ≤ twoRowMatrix a 1 0 := by norm_num
  have h11 : twoRowMatrix a 1 1 ≤ 0 := by simp [ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [zHi_of_nonneg h00]; simp
  · rw [zHi_of_nonpos h01]; simp
  · rw [zHi_of_nonneg h10]; simp
  · rw [zHi_of_nonpos h11]; simp

private theorem up_twoRowBox {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    up (twoRowMatrix a) (twoRowBox t) = twoRowBox t := by
  obtain ⟨hL00, hL01, hL10, hL11⟩ := zLo_twoRowBox (t := t) ha
  obtain ⟨hU00, hU01, hU10, hU11⟩ := zHi_twoRowBox (t := t) ha
  rw [up_eq_self_iff, Fin.forall_fin_two]
  constructor
  · simp only [imageLo_def, imageHi_def, Fin.sum_univ_two, hL00, hL01, hU00, hU01,
      twoRowBox_fst, twoRowBox_snd_inr]
    exact ⟨by linarith, by nlinarith⟩
  · simp only [imageLo_def, imageHi_def, Fin.sum_univ_two, hL10, hL11, hU10, hU11,
      twoRowBox_fst, twoRowBox_snd_inr]
    exact ⟨by nlinarith, by linarith⟩

private theorem inverseLo_twoRowBox {a t : ℝ} (ha : 0 < a) :
    ∀ i j : Fin 2, inverseLo (twoRowMatrix a) (twoRowBox t) i j = 0 := by
  obtain ⟨hL00, _, hL10, _⟩ := zLo_twoRowBox (t := t) ha.le
  obtain ⟨_, hU01, _, hU11⟩ := zHi_twoRowBox (t := t) ha.le
  have he0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have he1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  have h00 : 0 < twoRowMatrix a 0 0 := by simpa using ha
  have h01 : twoRowMatrix a 0 1 < 0 := by norm_num
  have h10 : 0 < twoRowMatrix a 1 0 := by norm_num
  have h11 : twoRowMatrix a 1 1 < 0 := by simp [ha]
  rw [Fin.forall_fin_two]
  constructor <;> rw [Fin.forall_fin_two] <;> constructor
  · rw [inverseLo_of_pos h00, restHi_def, he0, Finset.sum_singleton, hU01]; simp
  · rw [inverseLo_of_neg h01, restLo_def, he1, Finset.sum_singleton, hL00]; simp
  · rw [inverseLo_of_pos h10, restHi_def, he0, Finset.sum_singleton, hU11]; simp
  · rw [inverseLo_of_neg h11, restLo_def, he1, Finset.sum_singleton, hL10]; simp

private theorem inverseHi_twoRowBox {a t : ℝ} (ha : 0 < a) :
    inverseHi (twoRowMatrix a) (twoRowBox t) 0 0 = t / a ∧
      inverseHi (twoRowMatrix a) (twoRowBox t) 1 0 = a * t ∧
      inverseHi (twoRowMatrix a) (twoRowBox t) 0 1 = a * t ∧
      inverseHi (twoRowMatrix a) (twoRowBox t) 1 1 = t / a := by
  obtain ⟨_, hL01, _, hL11⟩ := zLo_twoRowBox (t := t) ha.le
  obtain ⟨hU00, _, hU10, _⟩ := zHi_twoRowBox (t := t) ha.le
  have he0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have he1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  have h00 : 0 < twoRowMatrix a 0 0 := by simpa using ha
  have h01 : twoRowMatrix a 0 1 < 0 := by norm_num
  have h10 : 0 < twoRowMatrix a 1 0 := by norm_num
  have h11 : twoRowMatrix a 1 1 < 0 := by simp [ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inverseHi_of_pos h00, restLo_def, he0, Finset.sum_singleton, hL01]; simp
  · rw [inverseHi_of_pos h10, restLo_def, he0, Finset.sum_singleton, hL11]; simp
  · rw [inverseHi_of_neg h01, restHi_def, he1, Finset.sum_singleton, hU00]; simp
  · rw [inverseHi_of_neg h11, restHi_def, he1, Finset.sum_singleton, hU10]; simp

/-- One simultaneous tightening step contracts `[0, t]² × [0, 0]²` to `[0, t / a]² × [0, 0]²`
for every `1 ≤ a` and `0 ≤ t ≤ 1`. -/
theorem step_twoRowBox {a t : ℝ} (ha : 1 ≤ a) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    step (twoRowMatrix a) (twoRowBox 1) (twoRowBox t) = twoRowBox (t / a) := by
  have ha0 : 0 < a := by linarith
  have hclip : clip (twoRowBox t) (twoRowBox 1) = twoRowBox t :=
    clip_eq_self_of_within (within_def.mpr ⟨fun _ => le_rfl, fun c => by
      cases c with
      | inl _ => exact ht₁
      | inr _ => exact le_rfl⟩)
  obtain ⟨hinvU00, hinvU10, hinvU01, hinvU11⟩ := inverseHi_twoRowBox (t := t) ha0
  have hdiv_le : t / a ≤ t := div_le_self ht₀ ha
  have hle_mul : t ≤ a * t := le_mul_of_one_le_left ht₀ ha
  rw [step_def, hclip, up_twoRowBox ha0.le ht₀]
  refine raw_ext (fun j => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    (down_fst_inr (twoRowMatrix a) (twoRowBox t)) (down_snd_inr (twoRowMatrix a) (twoRowBox t))
  · rw [twoRowBox_fst]
    exact le_antisymm
      (down_fst_inl_le_iff.mpr ⟨le_rfl, fun i => (inverseLo_twoRowBox ha0 i j).le⟩)
      ((twoRowBox_fst t (.inl j)).symm.le.trans (le_down_fst_inl _ _ j))
  · exact le_antisymm ((down_snd_inl_le_inverseHi _ _ 0 0).trans_eq hinvU00)
      (le_down_snd_inl_iff.mpr ⟨hdiv_le, Fin.forall_fin_two.mpr
        ⟨hinvU00.ge, (hdiv_le.trans hle_mul).trans_eq hinvU10.symm⟩⟩)
  · exact le_antisymm ((down_snd_inl_le_inverseHi _ _ 1 1).trans_eq hinvU11)
      (le_down_snd_inl_iff.mpr ⟨hdiv_le, Fin.forall_fin_two.mpr
        ⟨(hdiv_le.trans hle_mul).trans_eq hinvU01.symm, hinvU11.ge⟩⟩)

/-- For `1 ≤ a`, the `k`-th simultaneous iterate of the two-row recurrence is
`[0, 1 / a ^ k]² × [0, 0]²`. -/
theorem rawRun_twoRow {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    rawRun (twoRowMatrix a) (twoRowBox 1) k = twoRowBox (1 / a ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have ht₀ : 0 ≤ 1 / a ^ k := by positivity
      have ht₁ : 1 / a ^ k ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ ha) (by positivity)
      rw [rawRun_succ, ih, step_twoRowBox ha ht₀ ht₁, div_div, pow_succ]

/-- For `1 ≤ a`, the `k`-th iterate of the two-row recurrence has total width `2 / a ^ k`. -/
theorem width_rawRun_twoRow {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    width (rawRun (twoRowMatrix a) (twoRowBox 1) k) = 2 / a ^ k := by
  rw [rawRun_twoRow ha k, width_eq_sum_var_add_row]
  simp only [Fin.sum_univ_two, twoRowBox_fst, twoRowBox_snd_inl, twoRowBox_snd_inr, sub_zero,
    add_zero]
  ring

/-- For `1 ≤ a`, the `k`-th iterate of the two-row recurrence has strictly positive width. -/
theorem width_rawRun_twoRow_pos {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    0 < width (rawRun (twoRowMatrix a) (twoRowBox 1) k) := by
  rw [width_rawRun_twoRow ha k]
  positivity

/-- For `1 < a`, the total width of the simultaneous two-row iterates tends to `0`. -/
theorem tendsto_width_rawRun_twoRow {a : ℝ} (ha : 1 < a) :
    Tendsto (fun k => width (rawRun (twoRowMatrix a) (twoRowBox 1) k)) atTop (𝓝 0) := by
  simp_rw [width_rawRun_twoRow ha.le, div_eq_mul_inv, ← inv_pow]
  have hpow : Tendsto (fun k : ℕ => a⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ ha)
  simpa using hpow.const_mul (2 : ℝ)

/-- For `1 < a`, the simultaneous two-row iteration never stabilizes in finitely many steps. -/
theorem rawRun_twoRow_succ_ne {a : ℝ} (ha : 1 < a) (k : ℕ) :
    rawRun (twoRowMatrix a) (twoRowBox 1) (k + 1) ≠ rawRun (twoRowMatrix a) (twoRowBox 1) k := by
  intro heq
  have h0 := congrFun (congrArg Prod.snd heq) (.inl 0)
  rw [rawRun_twoRow ha.le (k + 1), rawRun_twoRow ha.le k, twoRowBox_snd_inl,
    twoRowBox_snd_inl] at h0
  have hpow0 : a ^ k ≠ 0 := by positivity
  have hpow1 : a ^ (k + 1) ≠ 0 := by positivity
  rw [div_eq_div_iff hpow1 hpow0] at h0
  have hmul : a ^ k * a = a ^ k * 1 := by
    simpa [pow_succ, mul_comm] using h0.symm
  have ha1 : a = 1 := mul_left_cancel₀ hpow0 hmul
  linarith

/-- The graph point `(0, 0)` belongs to every public iterate of the two-row recurrence. -/
theorem graph_zero_mem_publicRun_twoRow (a : ℝ) (k : ℕ) :
    graph (twoRowMatrix a) 0 ∈
      (publicRun (twoRowMatrix a) (twoRowBox 1) k : Set (Coord 2 2 → ℝ)) := by
  refine graph_survives _ _ 0 ?_ k
  rw [graph_mem_Icc_iff]
  simp

/-- At `a = 2`, updating row `0` and feeding the updated box immediately into row `1` gives the
inverse upper bound `1 / 4` on `x₂`. -/
theorem twoRow_sequential_inverseHi :
    inverseHi (twoRowMatrix 2) (fun _ => 0, Sum.elim ![1 / 2, 1] (fun _ => 0)) 1 1 = 1 / 4 := by
  have hneg : twoRowMatrix 2 1 1 < 0 := by norm_num
  have hpos : 0 ≤ twoRowMatrix 2 1 0 := by norm_num
  have he1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  rw [inverseHi_of_neg hneg, restHi_def, he1, Finset.sum_singleton, zHi_of_nonneg hpos]
  norm_num

/-- At `a = 2`, the sequential row-0-then-row-1 inverse upper bound on `x₂` is strictly tighter
than the simultaneous step upper bound `1 / 2`. -/
theorem twoRow_sequential_inverseHi_lt_simultaneous :
    inverseHi (twoRowMatrix 2) (fun _ => 0, Sum.elim ![1 / 2, 1] (fun _ => 0)) 1 1 <
      (step (twoRowMatrix 2) (twoRowBox 1) (twoRowBox 1)).2 (.inl 1) := by
  rw [twoRow_sequential_inverseHi, step_twoRowBox (by norm_num) (by norm_num) le_rfl,
    twoRowBox_snd_inl]
  norm_num

-- At `a = 2`, `[0, 1 / 2]²` maps to `[0, 1 / 4]²`, contained in the image of `[0, 1]²`.
example :
    step (twoRowMatrix 2) (twoRowBox 1) (twoRowBox (1 / 2)) = twoRowBox (1 / 4) ∧
      Within (step (twoRowMatrix 2) (twoRowBox 1) (twoRowBox (1 / 2)))
        (step (twoRowMatrix 2) (twoRowBox 1) (twoRowBox 1)) := by
  have h1 : step (twoRowMatrix 2) (twoRowBox 1) (twoRowBox 1) = twoRowBox (1 / 2) :=
    step_twoRowBox (by norm_num) (by norm_num) le_rfl
  have h2 : step (twoRowMatrix 2) (twoRowBox 1) (twoRowBox (1 / 2)) = twoRowBox (1 / 4) := by
    have hstep := step_twoRowBox (a := 2) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hstep
    exact hstep
  refine ⟨h2, ?_⟩
  rw [h1, h2]
  exact within_def.mpr ⟨fun _ => le_rfl, fun c => by
    cases c with
    | inl _ => norm_num
    | inr _ => exact le_rfl⟩

end TauCeti.AffineBoundTightening
