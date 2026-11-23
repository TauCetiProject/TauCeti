/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Poincaré recurrence for open sets

Let `f` be a conservative self-map of a topological space `α` with a measure `μ` for which open
sets are measurable, for instance a measurable map preserving a finite measure
(`MeasureTheory.MeasurePreserving.conservative`). Mathlib's Poincaré recurrence theorem
`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem` says that almost every point of a
measurable set `s` returns to `s` infinitely often.

When `μ` has full support, that is, every nonempty open set has positive measure
(`MeasureTheory.Measure.IsOpenPosMeasure`), this gives the topological form of the recurrence
theorem: every nonempty open set `U` contains a point whose forward orbit returns to `U`
infinitely often (`MeasureTheory.Conservative.exists_mem_frequently_iterate_mem_of_isOpen`): by
`MeasureTheory.Conservative.frequently_ae_mem_and_frequently_image_mem`, the points of a set of
positive measure that return to it infinitely often form a set of positive measure. In particular
some point of `U` returns to `U` after a positive number of iterates. Together with the
almost-everywhere recurrence to every neighbourhood of the starting point on a second countable
space, `MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds`, this is the form in which the
recurrence theorem is applied to area-preserving maps of surfaces of finite area and to
symplectomorphisms of symplectic manifolds of finite volume.

No symplectic or smooth structure is involved: the statement is about measures alone.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 5.3.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 16.
-/

public section

open Filter Set

namespace MeasureTheory.Conservative

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  {f : α → α} {μ : Measure α} [μ.IsOpenPosMeasure] {U : Set α}

/-- **Poincaré recurrence for open sets.** If `f` is conservative for a measure of full support,
then every nonempty open set `U` contains a point whose forward orbit returns to `U` infinitely
often. -/
theorem exists_mem_frequently_iterate_mem_of_isOpen (hf : Conservative f μ) (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ x ∈ U, ∃ᶠ n in atTop, f^[n] x ∈ U :=
  (hf.frequently_ae_mem_and_frequently_image_mem hU.nullMeasurableSet
    (hU.measure_ne_zero μ hne)).exists

end MeasureTheory.Conservative
