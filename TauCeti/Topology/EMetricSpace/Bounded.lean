/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.EMetricSpace.Diam

/-!
# Sequences at bounded distance from a point

A sequence at distance at most `R ≠ ⊤` from a point has range of finite diameter, so a compactness
hypothesis for sequences of finite diameter applies to every sublevel set of a function `φ`
intersected with such a ball.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X] {x : X}

/-- A sequence at distance at most `R ≠ ⊤` from a point has range of finite diameter. -/
theorem ediam_range_ne_top_of_edist_le {R : ℝ≥0∞} (hR : R ≠ ⊤) {w : ℕ → X}
    (hw : ∀ n, edist x (w n) ≤ R) : Metric.ediam (range w) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := R + R) (by finiteness) (Metric.ediam_le ?_)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact (edist_triangle_left _ _ x).trans (add_le_add (hw i) (hw j))

/-- A sequence of energy at most `c` at distance at most `R ≠ ⊤` from a point `x` has a
subsequence converging for the auxiliary convergence `l`, if `l` has compactness for sequences of
finite diameter. -/
theorem exists_strictMono_tendsto_of_edist_le {φ : X → EReal} {l : X → Filter X}
    (hcpt : ∀ (c : ℝ) ⦃v : ℕ → X⦄, Metric.ediam (range v) ≠ ⊤ → (∀ n, φ (v n) ≤ c) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (l y))
    {c : ℝ} {R : ℝ≥0∞} (hR : R ≠ ⊤) {w : ℕ → X}
    (hw : ∀ n, φ (w n) ≤ c ∧ edist x (w n) ≤ R) :
    ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (w ∘ ψ) atTop (l y) :=
  hcpt c (ediam_range_ne_top_of_edist_le hR fun n ↦ (hw n).2) fun n ↦ (hw n).1

end TauCeti
