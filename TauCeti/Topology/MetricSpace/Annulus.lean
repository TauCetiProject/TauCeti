/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Closed annuli in proper metric spaces

The closed annulus `{z | a ≤ dist z c ∧ dist z c ≤ b}` about `c` is compact in a proper space
(`Metric.isCompact_annulus`), and likewise when it is written with the norm.
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

end TauCeti
