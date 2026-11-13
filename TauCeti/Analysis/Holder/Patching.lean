/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Patching local bounds for the bounded Hölder norm

Let `f` be a bounded `α`-Hölder function on a metric space and `r > 0`. Suppose that around every
point `x` the function `f` agrees, on the ball `ball x r`, with a bounded Hölder function `g` of
norm at most `M`. Then `‖f‖ ≤ 2 (1 + r^(-α)) M`: the supremum of `f` is controlled pointwise by
the local pieces, and the Hölder seminorm of `f` is controlled by the local pieces between points
at distance less than `r`, and by twice the supremum between points farther apart
(`HolderOnWith.of_dist_lt_of_dist_le`).

This is how a global Schauder norm is recovered from norms of localizations: with `g = χₓ f` for
cutoffs `χₓ` equal to one on `ball x r`, a bound on the norms of the localizations that is uniform
in the centre `x` bounds the norm of `f`.

## Main declarations

* `TauCeti.HolderSpace.norm_le_of_forall_eqOn_ball`: the patching estimate.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (passing from local to global Schauder estimates).
-/

public section

noncomputable section

namespace TauCeti.HolderSpace

open Set Metric
open scoped NNReal

variable {α : ℝ≥0} {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Patching local Hölder bounds.** Let `r > 0`. If around every point `x` the bounded Hölder
function `f` agrees on `ball x r` with a bounded Hölder function of norm at most `M`, then
`‖f‖ ≤ 2 (1 + r^(-α)) M`. -/
theorem norm_le_of_forall_eqOn_ball [Nonempty X] {f : HolderSpace α X Y} {r M : ℝ} (hr : 0 < r)
    (h : ∀ x, ∃ g : HolderSpace α X Y, ‖g‖ ≤ M ∧ EqOn f g (ball x r)) :
    ‖f‖ ≤ 2 * (1 + r ^ (-(α : ℝ))) * M := by
  have hM : 0 ≤ M := by
    obtain ⟨g, hg, -⟩ := h (Classical.arbitrary X)
    exact (norm_nonneg g).trans hg
  have hf (x : X) : ‖f x‖ ≤ M := by
    obtain ⟨g, hg, hfg⟩ := h x
    rw [hfg (mem_ball_self hr)]
    exact (norm_apply_le g x).trans hg
  -- Between points at distance less than `r`, `f` is one of the local pieces.
  have hloc : ∀ x ∈ univ, ∀ y ∈ univ, dist x y < (⟨r, hr.le⟩ : ℝ≥0) →
      dist (f x) (f y) ≤ (⟨M, hM⟩ : ℝ≥0) * dist x y ^ (α : ℝ) := by
    intro x _ y _ hxy
    obtain ⟨g, hg, hfg⟩ := h x
    rw [hfg (mem_ball_self hr), hfg (mem_ball'.2 hxy)]
    exact (g.holderWith_nnnorm.dist_le x y).trans (by gcongr; exact hg)
  have hosc : ∀ x ∈ univ, ∀ y ∈ univ, dist (f x) (f y) ≤ (⟨2 * M, by positivity⟩ : ℝ≥0) := by
    intro x _ y _
    exact (dist_le_norm_add_norm _ _).trans (by linarith [hf x, hf y])
  have hH := (holderOnWith_univ.1 (HolderOnWith.of_dist_lt_of_dist_le
    (NNReal.coe_pos.1 hr : (0 : ℝ≥0) < ⟨r, hr.le⟩) hloc hosc)).nnholderNorm_le
  have hsup : ‖f.toBoundedContinuousFunction‖ ≤ M :=
    (BoundedContinuousFunction.norm_le hM).2 fun x ↦ by
      simpa only [toBoundedContinuousFunction_apply] using hf x
  have hH' : (nnHolderNorm α (f.toBoundedContinuousFunction : X → Y) : ℝ) ≤
      M + 2 * M * r ^ (-(α : ℝ)) := by
    rw [coe_toBoundedContinuousFunction]
    exact_mod_cast hH
  rw [norm_def]
  linarith

end TauCeti.HolderSpace
