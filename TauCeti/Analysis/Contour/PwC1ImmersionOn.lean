/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On

/-!
# Piecewise `C¹` immersions on an interval

The on-cycle Layer 4 targets of the contour-integration roadmap — the Hungerbühler–Wasem
generalized residue theorem and its half-residue specialisation — are stated for a **piecewise
`C¹` immersion**: a piecewise-`C¹` curve whose within-piece derivative is non-vanishing on every
closed piece, one-sided at the piece endpoints. This file introduces that regularity as the
predicate `Contour.IsPwC1ImmersionOn γ a b` on the raw function `γ` — the roadmap's pinned
definition, verbatim — together with its basic API.

The non-vanishing tangent is what the on-cycle theory needs and the plain `IsPiecewiseC1On`
cannot supply: Hungerbühler–Wasem represent each on-cycle singularity by model sectors of a
definite opening angle, which requires a well-defined non-zero tangent there. The one-sided
conditions are load-bearing: merely asking `deriv γ ≠ 0` off a finite set would admit zero-speed
turnarounds (`γ t = t ^ 2` on `[-1, 1]`, whose one-sided tangents both vanish at `0`) and
zero-speed seams of a closed curve, which are not immersions. `derivWithin` is used because at a
corner the global `deriv` is `0` by Mathlib convention, which would falsely contradict
non-vanishing; at interior points of a piece it agrees with `deriv`. (The homology Cauchy
theorem, whose singularities lie *off* the curve, needs only `IsPiecewiseC1On`.)

## Main definitions

* `Contour.IsPwC1ImmersionOn γ a b` — over a common finite breakpoint set, every breakpoint-free
  closed subinterval of `[[a, b]]` carries a `C¹` restriction with non-vanishing within-piece
  derivative.

## Main results

* `Contour.isPwC1ImmersionOn_iff` — unfold the predicate to its defining clauses.
* `Contour.IsPwC1ImmersionOn.isPiecewiseC1On` — an immersion is in particular piecewise `C¹`,
  with the same breakpoint witness.
* `Contour.IsPwC1ImmersionOn.continuousOn` — the underlying continuity on `[[a, b]]`.
* `Contour.IsPwC1ImmersionOn.of_breakpoints`, `Contour.IsPwC1ImmersionOn.exists_breakpoints` —
  introduce the predicate from, and eliminate it to, a finite breakpoint witness.
* `Contour.isPwC1ImmersionOn_comm`, `Contour.IsPwC1ImmersionOn.symm` — endpoint-swap invariance.

## Provenance

The raw-function mirror of the `ClosedPwC1Immersion` structure of the AINTLIB `LeanModularForms`
development (`PaperPwC1Immersion.lean`): the pieces clause matches its `contDiffOn_pieces` and
`derivWithin_ne_zero_pieces` fields — Hungerbühler–Wasem's `Λ̇|_{[aₖ,aₖ₊₁]} ≠ 0` (arXiv:1808.00997,
p. 3) — whose closed partition includes the interval endpoints, so the seam of a closed curve is
constrained too. Closedness itself (`γ a = γ b`) stays a separate hypothesis of the theorems. The
definition is pinned in the roadmap (`TauCetiRoadmap/ContourIntegration/Suggested.lean`).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **Piecewise-`C¹` immersion on the interval between `a` and `b`.** The curve `γ : ℝ → ℂ` is
continuous on `[[a, b]]` and, over a common finite breakpoint set
`p ⊆ (min a b, max a b)`, every breakpoint-free closed subinterval `[c, d]` carries a `C¹`
restriction whose within-piece derivative is non-vanishing on **all** of `[c, d]` — one-sided at
the piece endpoints, including at `a` and `b`. This strengthens `IsPiecewiseC1On` by a
non-vanishing tangent on every piece (`IsPwC1ImmersionOn.isPiecewiseC1On`); the `c < d` guard
excludes degenerate pieces, on which `derivWithin` is not meaningful. -/
def IsPwC1ImmersionOn (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ContinuousOn γ (uIcc a b) ∧
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) ∧
          ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0

/-- `IsPwC1ImmersionOn` unfolded to its defining clauses: continuity on `[[a, b]]`, and a finite
breakpoint set off which every breakpoint-free closed subinterval carries a `C¹` restriction with
non-vanishing within-piece derivative. -/
theorem isPwC1ImmersionOn_iff :
    IsPwC1ImmersionOn γ a b ↔
      ContinuousOn γ (uIcc a b) ∧
        ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
          ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
            ContDiffOn ℝ 1 γ (Icc c d) ∧
              ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0 :=
  Iff.rfl

/-- A piecewise-`C¹` immersion is continuous on the parameter interval `[[a, b]]`. -/
theorem IsPwC1ImmersionOn.continuousOn (h : IsPwC1ImmersionOn γ a b) :
    ContinuousOn γ (uIcc a b) :=
  h.1

/-- Build a piecewise-`C¹` immersion from continuity on `[[a, b]]` together with a finite
breakpoint set off which every breakpoint-free closed subinterval carries a `C¹` restriction with
non-vanishing within-piece derivative. -/
theorem IsPwC1ImmersionOn.of_breakpoints (hcont : ContinuousOn γ (uIcc a b)) (p : Finset ℝ)
    (hp : ↑p ⊆ Ioo (min a b) (max a b))
    (hpieces : ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d) ∧ ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0) :
    IsPwC1ImmersionOn γ a b :=
  ⟨hcont, p, hp, hpieces⟩

/-- Extract the finite breakpoint set of a piecewise-`C¹` immersion, together with the `C¹`
restriction and the non-vanishing within-piece derivative it induces on every breakpoint-free
closed subinterval of `[[a, b]]`. -/
theorem IsPwC1ImmersionOn.exists_breakpoints (h : IsPwC1ImmersionOn γ a b) :
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) ∧
          ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0 :=
  h.2

/-- A piecewise-`C¹` immersion is in particular piecewise `C¹`, with the same breakpoint
witness. -/
theorem IsPwC1ImmersionOn.isPiecewiseC1On (h : IsPwC1ImmersionOn γ a b) :
    IsPiecewiseC1On γ a b := by
  obtain ⟨hcont, p, hp, hpieces⟩ := h
  refine IsPiecewiseC1On.of_breakpoints hcont p hp fun c d hsub hdisj => ?_
  rcases lt_trichotomy c d with hlt | rfl | hgt
  · exact (hpieces c d hlt hsub hdisj).1
  · rw [Icc_self]
    exact fun x hx => by rw [mem_singleton_iff] at hx; subst hx; exact contDiffWithinAt_singleton
  · simp [Icc_eq_empty (not_le.mpr hgt)]

/-- Piecewise-`C¹`-immersion regularity is symmetric in the endpoints, since
`[[a, b]] = [[b, a]]`. -/
theorem isPwC1ImmersionOn_comm : IsPwC1ImmersionOn γ a b ↔ IsPwC1ImmersionOn γ b a := by
  simp only [isPwC1ImmersionOn_iff, Set.uIcc_comm a b, min_comm a b, max_comm a b]

/-- Piecewise-`C¹`-immersion regularity is invariant under swapping the endpoints of the
interval. -/
theorem IsPwC1ImmersionOn.symm (h : IsPwC1ImmersionOn γ a b) : IsPwC1ImmersionOn γ b a :=
  isPwC1ImmersionOn_comm.mp h

end TauCeti.Contour

end
