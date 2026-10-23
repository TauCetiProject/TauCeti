/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Continuous
public import TauCeti.Analysis.Convex.Measure

/-!
# Rademacher's theorem for locally Lipschitz and convex functions

Mathlib proves Rademacher's theorem for a function between finite-dimensional real normed spaces
that is Lipschitz on a set (`LipschitzOnWith.ae_differentiableWithinAt_of_mem`). This file
localises it: a function that is only *locally* Lipschitz on a set `s` is differentiable within
`s` at almost every point of `s`, and differentiable at almost every point of `s` when `s` is
open.

A convex function on a convex set `s` of a finite-dimensional real normed space is locally
Lipschitz on the interior of `s` (`ConvexOn.locallyLipschitzOn_interior`), and the frontier of a
convex set is Haar-null (`Convex.addHaar_frontier`). Together these give the classical fact that
a real convex function is differentiable at almost every point of its (convex) domain, with no
assumption that the domain be open or have nonempty interior: when the interior is empty the
domain lies in a proper affine subspace and is itself null.

## Main statements

* `LocallyLipschitzOn.ae_differentiableWithinAt_of_mem` and
  `LocallyLipschitzOn.ae_differentiableAt_of_mem` — Rademacher's theorem for locally Lipschitz
  functions;
* `Convex.ae_mem_interior` — almost every point of a convex set is an interior point;
* `ConvexOn.ae_differentiableAt_of_mem` — a convex function is differentiable at almost every
  point of its domain.

## References

* H. Rademacher, *Über partielle und totale Differenzierbarkeit von Funktionen mehrerer
  Variabeln und über die Transformation der Doppelintegrale*, Math. Ann. 79 (1919), 340--359;
* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 25.5.
-/

public section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ] {s : Set E}

namespace LocallyLipschitzOn

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F}

/-- **Rademacher's theorem** for locally Lipschitz functions: a function between
finite-dimensional real normed spaces which is locally Lipschitz on a set is differentiable
within that set at almost every point of it. -/
theorem ae_differentiableWithinAt_of_mem (hf : LocallyLipschitzOn s f) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  -- Every point of `s` has an open neighbourhood `U` with `f` Lipschitz on `s ∩ U`.
  have hloc : ∀ y ∈ s, ∃ U, IsOpen U ∧ y ∈ U ∧ ∃ K, LipschitzOnWith K f (s ∩ U) := by
    intro y hy
    obtain ⟨K, t, ht, hK⟩ := hf hy
    obtain ⟨U, hU, hyU, hUt⟩ := mem_nhdsWithin.1 ht
    exact ⟨U, hU, hyU, K, hK.mono ((inter_comm s U).subset.trans hUt)⟩
  choose! U hU hyU K hK using hloc
  -- Second countability gives a countable cover of `s` by the relatively open pieces `s ∩ U y`.
  obtain ⟨c, hcs, hc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => s ∩ U y) fun y hy => inter_mem_nhdsWithin s ((hU y hy).mem_nhds (hyU y hy))
  have h := (ae_ball_iff hc).2 fun y hy =>
    (hK y (hcs hy)).ae_differentiableWithinAt_of_mem (μ := μ)
  filter_upwards [h] with x hx hxs
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov hxs)
  exact (hx y hy hxy).mono_of_mem_nhdsWithin
    (inter_mem_nhdsWithin s ((hU y (hcs hy)).mem_nhds hxy.2))

/-- **Rademacher's theorem** for locally Lipschitz functions on an open set: a function between
finite-dimensional real normed spaces which is locally Lipschitz on an open set is differentiable
at almost every point of it. -/
theorem ae_differentiableAt_of_mem (hf : LocallyLipschitzOn s f) (hs : IsOpen s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_differentiableWithinAt_of_mem] with x hx hxs
  exact (hx hxs).differentiableAt (hs.mem_nhds hxs)

end LocallyLipschitzOn

namespace ConvexOn

variable {f : E → ℝ}

/-- A real convex function on a finite-dimensional real normed space is differentiable at almost
every interior point of its domain. -/
theorem ae_differentiableAt_of_mem_interior (hf : ConvexOn ℝ s f) :
    ∀ᵐ x ∂μ, x ∈ interior s → DifferentiableAt ℝ f x :=
  hf.locallyLipschitzOn_interior.ae_differentiableAt_of_mem isOpen_interior

/-- A real convex function on a finite-dimensional real normed space is differentiable at almost
every point of its domain. -/
theorem ae_differentiableAt_of_mem (hf : ConvexOn ℝ s f) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x := by
  filter_upwards [hf.1.ae_mem_interior, hf.ae_differentiableAt_of_mem_interior] with x h₁ h₂ hx
  exact h₂ (h₁ hx)

end ConvexOn
