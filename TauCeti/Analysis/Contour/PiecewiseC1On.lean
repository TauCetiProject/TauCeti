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
* `Contour.IsPiecewiseC1On.of_breakpoints`, `Contour.IsPiecewiseC1On.exists_breakpoints` —
  introduce the predicate from, and eliminate it to, a finite breakpoint witness.
* `Contour.IsPiecewiseC1On.mono` — restrict the regularity to a subinterval `[[c, d]] ⊆ [[a, b]]`.
* `Contour.isPiecewiseC1On_comm`, `Contour.IsPiecewiseC1On.symm` — endpoint-swap invariance.

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

/-- Build a piecewise-`C¹` curve from continuity on `[[a, b]]` together with a finite breakpoint set
off which every breakpoint-free closed subinterval carries a `C¹` restriction. -/
theorem IsPiecewiseC1On.of_breakpoints (hcont : ContinuousOn γ (uIcc a b)) (p : Finset ℝ)
    (hp : ↑p ⊆ Ioo (min a b) (max a b))
    (hC1 : ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d)) :
    IsPiecewiseC1On γ a b :=
  ⟨hcont, p, hp, hC1⟩

/-- Extract the finite breakpoint set of a piecewise-`C¹` curve, together with the `C¹` restriction
it induces on every breakpoint-free closed subinterval of `[[a, b]]`. -/
theorem IsPiecewiseC1On.exists_breakpoints (h : IsPiecewiseC1On γ a b) :
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) :=
  h.2

/-- Piecewise-`C¹` regularity restricts to any subinterval: if `γ` is piecewise `C¹` on `[[a, b]]`
and `[[c, d]] ⊆ [[a, b]]`, then `γ` is piecewise `C¹` on `[[c, d]]`, with the breakpoint set cut
down to the smaller interior. -/
theorem IsPiecewiseC1On.mono (h : IsPiecewiseC1On γ a b) {c d : ℝ}
    (hsub : uIcc c d ⊆ uIcc a b) : IsPiecewiseC1On γ c d := by
  obtain ⟨p, _, hC1⟩ := h.exists_breakpoints
  refine ⟨h.continuousOn.mono hsub, p.filter (fun x => x ∈ Ioo (min c d) (max c d)), ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact hx.2
  · intro u v huv hdis
    refine hC1 u v (huv.trans hsub) ?_
    rw [Set.disjoint_left] at hdis ⊢
    intro x hxp hxuv
    rw [← Set.Icc_min_max] at huv
    obtain ⟨hlu, hvu⟩ := (Set.Icc_subset_Icc_iff (hxuv.1.trans hxuv.2).le).1 huv
    refine hdis ?_ hxuv
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hxp, lt_of_le_of_lt hlu hxuv.1, lt_of_lt_of_le hxuv.2 hvu⟩

/-- Piecewise-`C¹` regularity is symmetric in the endpoints, since `[[a, b]] = [[b, a]]`. -/
theorem isPiecewiseC1On_comm : IsPiecewiseC1On γ a b ↔ IsPiecewiseC1On γ b a := by
  simp only [isPiecewiseC1On_iff, Set.uIcc_comm a b, min_comm a b, max_comm a b]

/-- Piecewise-`C¹` regularity is invariant under swapping the endpoints of the interval. -/
theorem IsPiecewiseC1On.symm (h : IsPiecewiseC1On γ a b) : IsPiecewiseC1On γ b a :=
  isPiecewiseC1On_comm.mp h

end TauCeti.Contour
