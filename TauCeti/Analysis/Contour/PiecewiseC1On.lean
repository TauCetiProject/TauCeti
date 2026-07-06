/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Piecewise `C¹` curves on an interval

The contour-integration roadmap states its objects — the generalized winding number, the contour
integral, and the Hungerbühler--Wasem regularity conditions — for a **piecewise `C¹`** curve
`γ : ℝ → ℂ` on the closed interval `[[a, b]]` between two parameters (in either order): continuous
there, and `C¹` on each piece between finitely many breakpoints. This file introduces
that regularity as a predicate `Contour.IsPiecewiseC1On γ a b` on the raw function `γ` itself —
following the roadmap's function-based design, with no bundled path type — together with its API.

The predicate is the hypothesis a "regularity package" supplies to the raw contour-integral lemmas
(for example the fundamental theorem of calculus along a contour in `Contour.ArcFTC`), and it is a
prerequisite for the homology Cauchy theorem and the generalized residue theorem.

## Main definitions

* `Contour.IsPiecewiseC1On γ a b` — `γ` is continuous on `[[a, b]]` and `C¹` on every closed
  subinterval whose interior avoids a fixed finite breakpoint set in `(min a b, max a b)`.

## Main results

* `Contour.isPiecewiseC1On_iff` — unfold the predicate to its defining clauses.
* `Contour.IsPiecewiseC1On.continuousOn` — the underlying continuity on `[[a, b]]`.
* `Contour.IsPiecewiseC1On.of_contDiffOn` — a `C¹` curve is piecewise `C¹`, with no breakpoints.

## Provenance

Adapted from the regularity fields of the `PiecewiseC1PathOn` structure in the AINTLIB
`LeanModularForms` development, re-expressed as a predicate on a raw function `γ : ℝ → ℂ` per the
roadmap's function-based contour design rather than as a bundled path type.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **Piecewise `C¹` on the interval between `a` and `b`.** The curve `γ : ℝ → ℂ` is continuous on
the closed interval `[[a, b]]` (unordered, hence orientation-robust), and there is a finite set of
breakpoints `p ⊆ (min a b, max a b)` such that `γ` is `C¹` on every closed subinterval of `[[a, b]]`
whose interior avoids `p`. Equivalently `γ` is continuously differentiable on each piece between
consecutive breakpoints, with corners allowed only at the breakpoints; an unbounded-derivative cusp
such as `t ↦ √|t|` is excluded, being not `C¹` up to the breakpoint. This is the raw-function form
of the roadmap's piecewise-`C¹` curve — a `Prop` on `γ` itself, with no bundled path type. -/
def IsPiecewiseC1On (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ContinuousOn γ (uIcc a b) ∧
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d)

/-- `IsPiecewiseC1On` unfolded to its defining clauses: continuity on `[[a, b]]`, and a finite
breakpoint set off which every breakpoint-free closed subinterval carries a `C¹` restriction. -/
theorem isPiecewiseC1On_iff :
    IsPiecewiseC1On γ a b ↔
      ContinuousOn γ (uIcc a b) ∧
        ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
          ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
            ContDiffOn ℝ 1 γ (Icc c d) :=
  Iff.rfl

/-- A piecewise-`C¹` curve is continuous on the parameter interval `[[a, b]]`. -/
theorem IsPiecewiseC1On.continuousOn (h : IsPiecewiseC1On γ a b) :
    ContinuousOn γ (uIcc a b) :=
  h.1

/-- A `C¹` curve on `[[a, b]]` is piecewise `C¹`, with no breakpoints. -/
theorem IsPiecewiseC1On.of_contDiffOn (h : ContDiffOn ℝ 1 γ (uIcc a b)) :
    IsPiecewiseC1On γ a b :=
  ⟨h.continuousOn, ∅, by simp, fun c d hcd _ => h.mono hcd⟩

end TauCeti.Contour
