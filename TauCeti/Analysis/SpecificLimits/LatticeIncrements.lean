/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Vanishing increments on a lattice grid

For a nondecreasing real-valued function on the nonnegative half-line, vanishing
successive increments on one positive lattice grid imply vanishing increments over
every fixed bounded time window. No continuity or constancy between grid points
is needed. The comparison encloses the window in a fixed number of grid cells.

This allows discrete renewal-increment limits to control excess-life probabilities
at arbitrary real observation times.
-/

public section

open Filter Topology
open scoped NNReal

namespace Monotone

/-- If successive increments of a nondecreasing function vanish on a positive lattice
grid, its increments over every fixed nonnegative window vanish at arbitrary times. -/
theorem tendsto_sub_add_of_tendsto_sub_lattice {f : ℝ≥0 → ℝ} (hf : Monotone f)
    {a : ℝ≥0} (ha : 0 < a)
    (h : Tendsto (fun n : ℕ ↦ f (a * (n + 1)) - f (a * n)) atTop (𝓝 0))
    (x : ℝ≥0) :
    Tendsto (fun t ↦ f (t + x) - f t) atTop (𝓝 0) := by
  -- A fixed finite number of successive grid increments still has limit zero.
  have hsteps (k : ℕ) :
      Tendsto (fun n : ℕ ↦ f (a * (n + k)) - f (a * n)) atTop (𝓝 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := h.comp (tendsto_add_atTop_nat k)
      convert hs.add ih using 1
      · ext n
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_assoc]
        ring
      · simp
  have hfloor : Tendsto (fun t : ℝ≥0 ↦ ⌊t / a⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const ha)
  obtain ⟨k, hk⟩ := exists_nat_gt (x / a)
  have hx : x < a * k := by
    simpa [mul_comm] using (div_lt_iff₀ ha).1 hk
  have hlim := (hsteps (k + 1)).comp hfloor
  apply squeeze_zero (fun t ↦ sub_nonneg.2 (hf le_self_add)) _ hlim
  intro t
  have hlo : a * (⌊t / a⌋₊ : ℝ≥0) ≤ t := by
    simpa [mul_comm] using (le_div_iff₀ ha).1 (Nat.floor_le (by positivity : 0 ≤ t / a))
  have hhi : t < a * ((⌊t / a⌋₊ : ℝ≥0) + 1) := by
    simpa [mul_comm] using (div_lt_iff₀ ha).1 (Nat.lt_floor_add_one (t / a))
  have hwindow : t + x ≤ a * ((⌊t / a⌋₊ : ℝ≥0) + (k + 1 : ℕ)) := by
    calc
      t + x ≤ a * ((⌊t / a⌋₊ : ℝ≥0) + 1) + a * k := (add_lt_add hhi hx).le
      _ = _ := by push_cast; ring
  exact sub_le_sub (hf hwindow) (hf hlo)

end Monotone
