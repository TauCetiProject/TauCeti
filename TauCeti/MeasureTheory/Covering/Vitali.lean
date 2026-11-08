/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
-- `Mathlib.MeasureTheory.Constructions.BorelSpace.Metric` is imported privately: it supplies only
-- the measurability of balls inside the proof.
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# The Vitali covering estimate for two measures

Mathlib's `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` extracts, from a
family of balls of bounded radii centred at the points of a set `S`, a pairwise disjoint
subfamily whose fourfold enlargements still cover `S`. This file turns that covering lemma into
a measure estimate: if `t` times the `ν`-measure of each fourfold enlarged ball is at most the
`μ`-integral of `g` over the original ball, then `t * ν S ≤ ∫⁻ g ∂μ`.

Taking `ν = μ` an additive Haar measure gives the weak-type `(1, 1)` Hardy–Littlewood maximal
inequality, and a weight `ν = μ.withDensity w` gives its weighted form of Fefferman and Stein.

## Main statements

* `TauCeti.mul_measure_le_lintegral_of_forall_exists_ball`: the Vitali covering estimate.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [TopologicalSpace.SeparableSpace X] [OpensMeasurableSpace X] {μ ν : Measure X} {t : ℝ≥0∞}

/-- **The Vitali covering estimate**, for two measures. If every point of `S` is the centre of a
ball `ball x r` of radius at most `R` such that `t` times the `ν`-measure of the fourfold enlarged
closed ball `closedBall x (4 * r)` is at most `∫⁻ y in ball x r, g y ∂μ`, then
`t * ν S ≤ ∫⁻ g ∂μ`.

Mathlib's `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` extracts a pairwise
disjoint subfamily of those balls whose fourfold enlargements still cover `S`, and disjointness
turns the sum of the integrals over the selected balls into a single integral over their union.
With `ν = μ` an additive Haar measure this is `TauCeti.mul_measure_le_of_forall_exists_ball`; a
weight `ν = μ.withDensity w` gives the weighted maximal inequality. -/
theorem mul_measure_le_lintegral_of_forall_exists_ball {S : Set X} {R : ℝ} {g : X → ℝ≥0∞}
    (hS : ∀ x ∈ S, ∃ r ∈ Ioc 0 R, t * ν (closedBall x (4 * r)) ≤ ∫⁻ y in ball x r, g y ∂μ) :
    t * ν S ≤ ∫⁻ y, g y ∂μ := by
  choose! r hr hle using hS
  obtain ⟨u, hu, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S id r R
      (fun x hx => (hr x hx).2) 4 (by norm_num)
  simp only [id_eq] at hdisj hcov
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun x hx =>
      ⟨x, ball_subset_interior_closedBall (mem_ball_self (hr x (hu hx)).1)⟩
  have : Countable u := hcount.to_subtype
  -- The fourfold enlargements of the selected balls cover `S`.
  have hsub : S ⊆ ⋃ b ∈ u, closedBall b (4 * r b) := fun x hx => by
    obtain ⟨b, hb, hball⟩ := hcov x hx
    exact mem_biUnion hb (hball (mem_closedBall_self (hr x hx).1.le))
  -- The selected balls are pairwise disjoint, so the integrals over them add up to at most `∫⁻ g`.
  have hdisj' : Pairwise (Function.onFun Disjoint fun b : u => ball (b : X) (r b)) :=
    fun b b' hbb' =>
      (hdisj b.2 b'.2 (Subtype.coe_injective.ne hbb')).mono ball_subset_closedBall
        ball_subset_closedBall
  calc t * ν S
      ≤ t * ∑' b : u, ν (closedBall (b : X) (4 * r b)) := by
        gcongr
        exact (measure_mono hsub).trans (measure_biUnion_le ν hcount _)
    _ = ∑' b : u, t * ν (closedBall (b : X) (4 * r b)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, ∫⁻ y in ball (b : X) (r b), g y ∂μ :=
        _root_.tsum_le_tsum fun b => hle b (hu b.2)
    _ = ∫⁻ y in ⋃ b : u, ball (b : X) (r b), g y ∂μ := by
        rw [lintegral_iUnion (fun b => measurableSet_ball) hdisj']
    _ ≤ ∫⁻ y, g y ∂μ := setLIntegral_le_lintegral _ _

end TauCeti
