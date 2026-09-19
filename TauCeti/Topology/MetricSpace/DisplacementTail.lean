/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Truncating powers of distances by tails about a basepoint

In a pseudometric space a displacement larger than `2 R` forces one of its two endpoints to lie at
distance at least `R` from a basepoint `x`, and then the displacement is at most twice that
distance. Consequently the `q`-th power of a displacement is at most its truncation at `2 R` plus
`2 ^ q` times the parts, beyond distance `R` from `x`, of the `q`-th powers of the distances of the
two endpoints from `x`. This is the pointwise estimate through which the tails of the moments of
two laws control the transport cost of an unbounded power of the distance.

## Main statements

* `TauCeti.edist_rpow_le_min_add_indicator` — the pointwise truncation estimate.
-/

public section

open Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- A displacement larger than `2 R` is at most twice the distance from the basepoint `x` of an
endpoint lying at distance at least `R` from it. Hence the `q`-th power of the displacement is at
most its truncation at `2 R` plus `2 ^ q` times the tail parts, beyond `R`, of the `q`-th powers of
the distances of the two endpoints from `x`. -/
theorem edist_rpow_le_min_add_indicator {q : ℝ} (hq : 0 < q) (x : X) (R : ℝ≥0) (y z : X) :
    edist y z ^ q ≤ min (edist y z) (2 * R) ^ q +
      2 ^ q * {w | R ≤ nndist x w}.indicator (fun w ↦ edist x w ^ q) y +
      2 ^ q * {w | R ≤ nndist x w}.indicator (fun w ↦ edist x w ^ q) z := by
  by_cases hd : edist y z ≤ 2 * R
  · rw [min_eq_left hd, add_assoc]
    exact le_self_add
  rw [not_le] at hd
  -- An endpoint `w` with `edist y z ≤ 2 * edist x w` lies at distance at least `R` from `x`.
  have hmem {w : X} (hw : edist y z ≤ 2 * edist x w) : w ∈ {w | R ≤ nndist x w} := by
    rw [mem_ofPred_eq, ← ENNReal.coe_le_coe, ← edist_nndist]
    by_contra hlt
    exact (not_le.2 hd) (hw.trans (by gcongr; exact (not_le.1 hlt).le))
  have hbound {w : X} (hw : edist y z ≤ 2 * edist x w) :
      edist y z ^ q ≤ 2 ^ q * {w | R ≤ nndist x w}.indicator (fun w ↦ edist x w ^ q) w := by
    rw [indicator_of_mem (hmem hw), ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    exact ENNReal.rpow_le_rpow hw hq.le
  have htri : edist y z ≤ edist x y + edist x z := edist_triangle_left y z x
  rcases le_total (edist x z) (edist x y) with hle | hle
  · refine (hbound ?_).trans (le_add_right (le_add_left le_rfl))
    exact htri.trans (by rw [two_mul]; gcongr)
  · refine (hbound ?_).trans (le_add_left le_rfl)
    exact htri.trans (by rw [two_mul]; gcongr)

end TauCeti
