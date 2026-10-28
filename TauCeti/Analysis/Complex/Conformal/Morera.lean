/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Morera's theorem

This file states Morera's theorem under its classical name. Mathlib proves the equivalence
between complex differentiability and being continuous and conservative on an open set
(`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`); the theorem here is the
direction of that equivalence going from vanishing rectangle integrals to differentiability.

## Main results

* `TauCeti.morera`: a continuous function on an open set whose rectangle integrals vanish is
  complex differentiable there.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4, Section 6.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IV, Section 5.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Morera's theorem.** A continuous function with values in a complex Banach space, defined on
an open set of `ℂ` and conservative there (its integrals over the boundaries of rectangles in the
set vanish), is complex differentiable on that set. -/
theorem morera {U : Set ℂ} {f : ℂ → E} (hU : IsOpen U) (hcont : ContinuousOn f U)
    (hcons : Complex.IsConservativeOn f U) : DifferentiableOn ℂ f U :=
  (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp ⟨hcons, hcont⟩

end TauCeti
