/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Complex.Basic

/-!
# Closed annuli in proper metric spaces

The closed annulus `{z | a ≤ dist z c ∧ dist z c ≤ b}` about `c` is compact in a proper space
(`Metric.isCompact_annulus`), and likewise when it is written with the norm. In `ℂ`, so is its
closed upper half about `z₀`, the points with `0 ≤ im (z - z₀)` (`TauCeti.isCompact_halfAnnulus`).
-/

public section

open Metric Set

namespace Metric

/-- A closed annulus is compact in a proper space. -/
theorem isCompact_annulus {E : Type*} [PseudoMetricSpace E] [ProperSpace E] (c : E) (a b : ℝ) :
    IsCompact {z : E | a ≤ dist z c ∧ dist z c ≤ b} :=
  (isCompact_closedBall c b).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const))
    fun _ hz ↦ hz.2

end Metric

namespace TauCeti

/-- A closed annulus written with the norm is compact in a proper seminormed group. -/
theorem isCompact_setOf_le_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] [ProperSpace E]
    (c : E) (a b : ℝ) : IsCompact {z : E | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b} := by
  simpa only [dist_eq_norm] using Metric.isCompact_annulus c a b

/-- A closed upper half-annulus, the points `z` with `a ≤ ‖z - z₀‖ ≤ b` and `0 ≤ im (z - z₀)`,
is compact. -/
theorem isCompact_halfAnnulus (z₀ : ℂ) (a b : ℝ) :
    IsCompact {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im} := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ (z - z₀).im} :=
    isClosed_le continuous_const (Complex.continuous_im.comp (continuous_sub_right z₀))
  simpa only [← ofPred_and, and_assoc] using
    (isCompact_setOf_le_norm_sub_le z₀ a b).inter_right hclosed

end TauCeti
