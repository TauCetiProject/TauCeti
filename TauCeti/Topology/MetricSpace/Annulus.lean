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
(`Metric.isCompact_annulus`), and likewise when it is written with the norm. Shrinking the radii
gives a smaller annulus (`TauCeti.setOf_le_norm_sub_le_subset`), and a closed ball about `z` of
radius `ρ` lies in the annulus about `c` with radii `‖z - c‖ ∓ ρ`
(`TauCeti.closedBall_subset_setOf_le_norm_sub_le`).
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

/-- The closed annulus `r₁ ≤ ‖z - c‖ ≤ r₂` lies in `a ≤ ‖z - c‖ ≤ b` when `a ≤ r₁` and
`r₂ ≤ b`. -/
theorem setOf_le_norm_sub_le_subset {E : Type*} [SeminormedAddCommGroup E] {c : E}
    {a b r₁ r₂ : ℝ} (h₁ : a ≤ r₁) (h₂ : r₂ ≤ b) :
    {z : E | r₁ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r₂} ⊆ {z : E | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b} :=
  fun _ hz ↦ ⟨h₁.trans hz.1, hz.2.trans h₂⟩

/-- The closed ball of radius `ρ` about `z` lies in the closed annulus about `c` with radii
`‖z - c‖ - ρ` and `‖z - c‖ + ρ`. -/
theorem closedBall_subset_setOf_le_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] (c z : E)
    (ρ : ℝ) : closedBall z ρ ⊆ {w : E | ‖z - c‖ - ρ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ ‖z - c‖ + ρ} := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have h₁ := norm_sub_le_norm_sub_add_norm_sub z w c
  have h₂ := norm_sub_le_norm_sub_add_norm_sub w z c
  rw [norm_sub_rev z w] at h₁
  exact ⟨by linarith, by linarith⟩

end TauCeti
