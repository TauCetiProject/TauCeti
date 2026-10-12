/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# Partitions of the unit interval

`unitInterval.Partition n` is a monotone sequence `0 = t₀ ≤ ⋯ ≤ tₙ = 1` in the unit interval.
It indexes the segments of the tube neighbourhoods of paths in
`TauCeti.Topology.Homotopy.TubeNeighborhood`.
-/

-- Ported from https://github.com/leanprover-community/mathlib4/pull/44183.

public section

namespace unitInterval

/-- A partition `0 = t₀ ≤ ⋯ ≤ tₙ = 1` of the unit interval into `n` segments. -/
structure Partition (n : ℕ) where
  /-- The partition points. -/
  t : Fin (n + 1) → I
  /-- The partition points are monotone. -/
  mono : Monotone t
  /-- The first partition point is `0`. -/
  t_zero : t 0 = 0
  /-- The last partition point is `1`. -/
  t_last : t (Fin.last n) = 1

namespace Partition

attribute [simp] t_zero t_last

/-- There is no partition into zero segments, since `t 0` would be both `0` and `1`. -/
instance : IsEmpty (Partition 0) :=
  ⟨fun p ↦ zero_ne_one (p.t_zero.symm.trans p.t_last)⟩

/-- Consecutive partition points are ordered. -/
theorem t_castSucc_le_succ {n : ℕ} (part : Partition n) (i : Fin n) :
    part.t i.castSucc ≤ part.t i.succ :=
  part.mono i.castSucc_lt_succ.le

end Partition

end unitInterval
