/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Vanishing harmonic sequences

A sequence satisfying the discrete midpoint identity has constant first differences.
If it tends to zero, it must therefore vanish identically. Applied to the singleton
masses of a finite measure on the integers, this rules out a nonzero finite measure
whose masses satisfy the symmetric nearest-neighbor stationarity equations.
-/

public section

open Filter
open scoped Topology

namespace Filter.Tendsto

/-- A sequence tending to zero and satisfying the discrete midpoint identity vanishes
identically. The result holds in any Hausdorff topological abelian group. -/
theorem eq_zero_of_add_add_two {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] {f : ℕ → E} (h : Tendsto f atTop (𝓝 0))
    (hrec : ∀ n, f n + f (n + 2) = f (n + 1) + f (n + 1)) (n : ℕ) : f n = 0 := by
  have hd : ∀ k, f (k + 1) - f k = f 1 - f 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hs : f (k + 2) - f (k + 1) = f (k + 1) - f k :=
        sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using hrec k)
      exact hs.trans ih
  have hlim : Tendsto (fun k => f (k + 1) - f k) atTop (𝓝 0) := by
    simpa using (h.comp (tendsto_add_atTop_nat 1)).sub h
  have hz : f 1 - f 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (by simpa only [hd] using hlim)
  have heq : ∀ k, f k = f 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact (sub_eq_zero.mp ((hd k).trans hz)).trans ih
  have hconst : Tendsto (fun _ : ℕ => f 0) atTop (𝓝 0) :=
    h.congr' (Eventually.of_forall heq)
  exact (heq n).trans (tendsto_nhds_unique tendsto_const_nhds hconst)

end Filter.Tendsto
