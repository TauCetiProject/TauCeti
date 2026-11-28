/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.Probability.Moments.Variance

/-!
# Partial integrals over finite product measures in `L²`

For a function `T` on a finite product of probability spaces, integrating out every coordinate but
the `i`-th gives the function `a ↦ ∫ y, T (Function.update y i a)`. For integrable `T` it is,
almost everywhere, a version of the conditional expectation of `T` given the `i`-th coordinate.
This file shows that it is square-integrable when `T` is.

## Main results

* `TauCeti.memLp_integral_update`: the partial integral of a square-integrable function, as a
  function of the remaining coordinate, is square-integrable.
-/

public section

open MeasureTheory ProbabilityTheory Function

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- The partial integral `a ↦ ∫ y, T (update y i a)` of a square-integrable function `T` of
independent coordinates, almost everywhere a version of `a ↦ E(T | Xᵢ = a)`, is
square-integrable. -/
theorem memLp_integral_update (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    {T : (∀ i, α i) → ℝ} (hT : MemLp T 2 (Measure.pi P)) (i : ι) :
    MemLp (fun a ↦ ∫ y, T (update y i a) ∂(Measure.pi P)) 2 (P i) := by
  have hmp := (measurePreserving_update_prod_pi P i).comp
    (Measure.measurePreserving_swap (μ := P i) (ν := Measure.pi P))
  have hF : MemLp (fun p : α i × (∀ j, α j) ↦ T (update p.2 i p.1)) 2
      ((P i).prod (Measure.pi P)) := hT.comp_measurePreserving hmp
  have hm : AEStronglyMeasurable (fun a ↦ ∫ y, T (update y i a) ∂(Measure.pi P)) (P i) :=
    hF.aestronglyMeasurable.integral_prod_right'
  refine (evariance_lt_top_iff_memLp hm).mp ?_
  calc evariance (fun a ↦ ∫ y, T (update y i a) ∂(Measure.pi P)) (P i)
      ≤ evariance (fun p : α i × (∀ j, α j) ↦ T (update p.2 i p.1)) ((P i).prod (Measure.pi P)) :=
        by rw [TauCeti.Probability.evariance_prod_eq hF.aestronglyMeasurable]; exact le_add_self
    _ < ⊤ := evariance_lt_top hF

end TauCeti
