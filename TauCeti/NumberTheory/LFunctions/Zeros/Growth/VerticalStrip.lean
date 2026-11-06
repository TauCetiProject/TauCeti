/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.VerticalStripGrowth
public import TauCeti.NumberTheory.LFunctions.Data.Basic

/-!
# Vertical-strip growth of completed L-functions

An analytic L-function record has vertical-strip growth when its completed function
has polynomial growth above a strip-dependent height threshold. The threshold is
essential: the finite polar divisor may contain poles at nonzero heights.

This property concerns only the completed function, not its presentation by coefficients
and gamma factors. It is invariant under equality of completed functions and under taking
the dual record. The analytic estimates that establish it for a family are separate from
this definition.
-/

public section

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- The completed function has polynomial growth on every closed vertical strip,
above a height threshold that is allowed to depend on the strip. -/
def HasVerticalStripGrowth (d : AnalyticLFunctionData) : Prop :=
  TauCeti.HasVerticalStripGrowth d.completed

variable {d e : AnalyticLFunctionData}

/-- The explicit polynomial bound on the completed function. -/
theorem hasVerticalStripGrowth_def : d.HasVerticalStripGrowth ↔
    ∀ a b : ℝ, a < b → ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ s : ℂ, s.re ∈ Set.Icc a b → T ≤ |s.im| →
        ‖d.completed s‖ ≤ C * (1 + |s.im|) ^ A :=
  TauCeti.hasVerticalStripGrowth_def

/-- Strip growth depends only on the completed function. -/
theorem hasVerticalStripGrowth_iff_of_completed_eq (h : d.completed = e.completed) :
    d.HasVerticalStripGrowth ↔ e.HasVerticalStripGrowth := by
  simp only [HasVerticalStripGrowth, h]

/-- Taking the dual preserves vertical-strip growth. -/
theorem HasVerticalStripGrowth.dual (h : d.HasVerticalStripGrowth) :
    d.dual.HasVerticalStripGrowth :=
  (TauCeti.HasVerticalStripGrowth.conj h).congr
    (fun s ↦ (dual_completed_apply d s).symm)

/-- A record and its dual have the same vertical-strip growth property. -/
@[simp]
theorem hasVerticalStripGrowth_dual_iff :
    d.dual.HasVerticalStripGrowth ↔ d.HasVerticalStripGrowth :=
  ⟨fun h ↦ by simpa using h.dual, HasVerticalStripGrowth.dual⟩

end TauCeti.LFunctions.AnalyticLFunctionData
