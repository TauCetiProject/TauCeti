/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compactness of norm balls in the unitary group of a sesquilinear form

Let `R` be a proper normed commutative ring with continuous star (such as `ℝ` or `ℂ`) and `J` an
invertible square matrix over `R`. Because the coercion
`Matrix.unitaryGroupOf J → Matrix n n R` is a closed embedding
(`Matrix.unitaryGroupOf.isClosedEmbedding_val`), every norm ball
`{g : Matrix.unitaryGroupOf J | ‖((g : GL n R) : Matrix n n R) - A‖ ≤ T}` is compact
(`TauCeti.isCompact_unitaryGroupOf_norm_sub_le`), and in particular `{g | ‖g‖ ≤ T}` is compact
(`TauCeti.isCompact_unitaryGroupOf_norm_le`). Consequently, for any proper homomorphism
`j : S →* Matrix.unitaryGroupOf J` and any measure `ν` finite on compacts, the preimage of every
norm ball has finite `ν`-measure (`TauCeti.measure_unitaryGroupOf_ball_ne_top_of_isProperMap`).

## Main results

* `TauCeti.isCompact_unitaryGroupOf_norm_sub_le`: norm balls centered at `A` in
  `Matrix.unitaryGroupOf J` are compact.
* `TauCeti.isCompact_unitaryGroupOf_norm_le`: norm balls `{g | ‖g‖ ≤ T}` in
  `Matrix.unitaryGroupOf J` are compact.
* `TauCeti.measure_unitaryGroupOf_ball_ne_top_of_isProperMap`: preimages of norm balls under a
  proper map `j : S → Matrix.unitaryGroupOf J` have finite measure.

## Provenance

Adapted from `New.isCompact_U_norm_le` and
`New.DiscreteSeries.measure_ball_ne_top_of_isProperMap` in `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/DiscreteSeries/Haar/TotalMass.lean`).
-/

public section

namespace TauCeti

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

section CompactBalls

variable {n R : Type*} [Fintype n] [DecidableEq n] [NormedCommRing R] [StarRing R]
  [ContinuousStar R] [ProperSpace R]

/-- For an invertible matrix `J` over a proper normed commutative star ring `R`, the norm ball
`{g : unitaryGroupOf J | ‖(g : Matrix n n R) - A‖ ≤ T}` is compact. -/
theorem isCompact_unitaryGroupOf_norm_sub_le {J : Matrix n n R} (hJ : IsUnit J)
    (A : Matrix n n R) (T : ℝ) :
    IsCompact {g : Matrix.unitaryGroupOf J | ‖((g : GL n R) : Matrix n n R) - A‖ ≤ T} := by
  have hcl := Matrix.unitaryGroupOf.isClosedEmbedding_val (A := J) hJ
  have hball : IsCompact (Metric.closedBall A T) := by
    by_cases hT : 0 ≤ T
    · have hsub : Metric.closedBall A T =
          Set.univ.pi fun i ↦ Set.univ.pi fun j ↦ Metric.closedBall (A i j) T := by
        ext M
        simp only [Metric.mem_closedBall, dist_eq_norm, Matrix.norm_le_iff hT, Matrix.sub_apply]
        exact ⟨fun h i _ j _ ↦ mem_closedBall_iff_norm.mpr (h i j),
          fun h i j ↦ mem_closedBall_iff_norm.mp (h i trivial j trivial)⟩
      rw [hsub]
      exact isCompact_univ_pi fun i ↦ isCompact_univ_pi fun j ↦ isCompact_closedBall (A i j) T
    · rw [Metric.closedBall_eq_empty.mpr (not_le.mp hT)]
      exact isCompact_empty
  have heq : {g : Matrix.unitaryGroupOf J | ‖((g : GL n R) : Matrix n n R) - A‖ ≤ T} =
      (fun g : Matrix.unitaryGroupOf J ↦ ((g : GL n R) : Matrix n n R)) ⁻¹'
        Metric.closedBall A T :=
    Set.ext fun g ↦ (mem_closedBall_iff_norm (b := ((g : GL n R) : Matrix n n R))).symm
  rw [heq]
  exact hcl.isCompact_preimage hball

/-- For an invertible matrix `J` over a proper normed commutative star ring `R`, the norm ball
`{g : unitaryGroupOf J | ‖(g : Matrix n n R)‖ ≤ T}` is compact. -/
theorem isCompact_unitaryGroupOf_norm_le {J : Matrix n n R} (hJ : IsUnit J) (T : ℝ) :
    IsCompact {g : Matrix.unitaryGroupOf J | ‖((g : GL n R) : Matrix n n R)‖ ≤ T} := by
  simpa only [sub_zero] using isCompact_unitaryGroupOf_norm_sub_le hJ 0 T

/-- If `j : S → Matrix.unitaryGroupOf J` is a proper map and `ν` is finite on compact sets, then
the preimage `{s : S | ‖(j s : Matrix n n R) - A‖ ≤ T}` has finite `ν`-measure. -/
theorem measure_unitaryGroupOf_ball_ne_top_of_isProperMap {S : Type*} [TopologicalSpace S]
    [MeasurableSpace S] (ν : Measure S) [IsFiniteMeasureOnCompacts ν]
    {J : Matrix n n R} (hJ : IsUnit J) {j : S → Matrix.unitaryGroupOf J} (hj : IsProperMap j)
    (A : Matrix n n R) (T : ℝ) :
    ν {s : S | ‖((j s : GL n R) : Matrix n n R) - A‖ ≤ T} ≠ ⊤ :=
  (hj.isCompact_preimage (isCompact_unitaryGroupOf_norm_sub_le hJ A T)).measure_ne_top

end CompactBalls

end TauCeti
