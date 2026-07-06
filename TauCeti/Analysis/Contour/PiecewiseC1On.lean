/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.Basic

/-!
# Piecewise `C¹` curves on an interval

The contour-integration roadmap states its objects — the generalized winding number, the contour
integral, and the Hungerbühler--Wasem regularity conditions — for a **piecewise `C¹`** curve
`γ : ℝ → ℂ` on the closed interval `[[a, b]]` between two parameters (in either order): continuous
there and continuously differentiable away from a finite set of breakpoints. This file introduces
that regularity as a predicate `Contour.IsPiecewiseC1On γ a b` on the raw function `γ` itself —
following the roadmap's function-based design, with no bundled path type — together with its API.

The predicate is the hypothesis a "regularity package" supplies to the raw contour-integral lemmas
(for example the fundamental theorem of calculus along a contour in `Contour.ArcFTC`), and it is a
prerequisite for the homology Cauchy theorem and the generalized residue theorem.

## Main definitions

* `Contour.IsPiecewiseC1On γ a b` — `γ` is continuous on `[[a, b]]` and continuously differentiable
  at every interior time outside a finite breakpoint set contained in `(min a b, max a b)`.

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
the closed interval `[[a, b]]` (unordered, hence orientation-robust) and continuously
differentiable away from a finite set of breakpoints `p ⊆ (min a b, max a b)`: at every interior
time outside `p` the curve is differentiable and its derivative is continuous there. This is the
raw-function form of the roadmap's piecewise-`C¹` curve — a `Prop` on `γ` itself, with no bundled
path type. The endpoints are never breakpoints. -/
def IsPiecewiseC1On (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ContinuousOn γ (uIcc a b) ∧
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      (∀ t ∈ Ioo (min a b) (max a b), t ∉ p → DifferentiableAt ℝ γ t) ∧
      (∀ t ∈ Ioo (min a b) (max a b), t ∉ p → ContinuousAt (deriv γ) t)

/-- `IsPiecewiseC1On` unfolded to its defining clauses: continuity on `[[a, b]]`, and a finite
breakpoint set off which `γ` is differentiable with continuous derivative. -/
theorem isPiecewiseC1On_iff :
    IsPiecewiseC1On γ a b ↔
      ContinuousOn γ (uIcc a b) ∧
        ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
          (∀ t ∈ Ioo (min a b) (max a b), t ∉ p → DifferentiableAt ℝ γ t) ∧
          (∀ t ∈ Ioo (min a b) (max a b), t ∉ p → ContinuousAt (deriv γ) t) :=
  Iff.rfl

/-- A piecewise-`C¹` curve is continuous on the parameter interval `[[a, b]]`. -/
theorem IsPiecewiseC1On.continuousOn (h : IsPiecewiseC1On γ a b) :
    ContinuousOn γ (uIcc a b) :=
  h.1

/-- A `C¹` curve on `[[a, b]]` is piecewise `C¹`, with no breakpoints. -/
theorem IsPiecewiseC1On.of_contDiffOn (h : ContDiffOn ℝ 1 γ (uIcc a b)) :
    IsPiecewiseC1On γ a b := by
  have hsub : Ioo (min a b) (max a b) ⊆ uIcc a b := by
    rw [← Set.Icc_min_max]; exact Ioo_subset_Icc_self
  have hderiv : ContinuousOn (deriv γ) (Ioo (min a b) (max a b)) :=
    (h.mono hsub).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  refine ⟨h.continuousOn, ∅, by simp, fun t ht _ => ?_, fun t ht _ => ?_⟩
  · have hmem : uIcc a b ∈ nhds t := by rw [← Set.Icc_min_max]; exact Icc_mem_nhds ht.1 ht.2
    exact (h.contDiffAt hmem).differentiableAt_one
  · exact hderiv.continuousAt (Ioo_mem_nhds ht.1 ht.2)

end TauCeti.Contour
