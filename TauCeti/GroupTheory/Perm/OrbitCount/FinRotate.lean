/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Orbits of cyclic rotation

Cyclic rotation of a nonempty finite ordinal is a single cycle through every point, including the
singleton case where the rotation is the identity: its full cycle partition has the one part `n`,
so it has one orbit and order `n`. The orbit count includes fixed points. The formula is useful
when a traversal permutation is identified, up to conjugacy, with cyclic rotation: it reduces the
resulting orbit or component count to whether the underlying ordinal is empty.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

/-- The full cycle partition of cyclic rotation of a nonempty finite ordinal has the single
part `n`. -/
theorem parts_partition_finRotate {n : ℕ} (hn : n ≠ 0) : (finRotate n).partition.parts = {n} := by
  rcases n with _ | _ | n
  · exact absurd rfl hn
  -- For `n = 1` the rotation is the identity of `Fin 1`, whose only part is its one fixed point.
  · simp [finRotate_one, ← Equiv.Perm.one_def]
  · rw [parts_partition_of_isCycle isCycle_finRotate, support_finRotate]
    simp

/-- Cyclic rotation of a nonempty finite ordinal of length `n` has order `n`. -/
theorem orderOf_finRotate {n : ℕ} (hn : n ≠ 0) : orderOf (finRotate n) = n := by
  rw [← lcm_parts_partition, parts_partition_finRotate hn, Multiset.lcm_singleton, normalize_eq]

/-- Cyclic rotation has one orbit when the ordinal is nonempty, and none otherwise. -/
@[simp]
theorem orbitCount_finRotate (n : ℕ) : orbitCount (finRotate n) = if n = 0 then 0 else 1 := by
  split_ifs with hn
  · subst hn
    rw [orbitCount_eq_card_parts_partition, parts_partition_of_isEmpty, Multiset.card_zero]
  · rw [orbitCount_eq_card_parts_partition, parts_partition_finRotate hn, Multiset.card_singleton]

end TauCeti
