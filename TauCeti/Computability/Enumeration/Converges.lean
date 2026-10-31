/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Stage
public import TauCeti.Computability.Approximation.Modulus
public import Mathlib.Algebra.Notation.Indicator
import Mathlib.Order.Filter.IndicatorFunction

/-!
# Convergence of finite-stage enumerations

Under monotone stages, the finite stages `A s` of an enumeration approximate its limit in the sense
of limit approximations: any function restricted to the stages converges pointwise to the same
function restricted to the limit. In particular the set-oracle answers of the stages converge to
those of the limit set.

## Main results

* `TauCeti.Enumeration.converges_indicator_stageLimit`: under monotone stages, the indicator
  functions of the stages converge to that of the limit.
-/

public section

open TauCeti.Approximation

namespace TauCeti

namespace Enumeration

/-- Under monotone stages, the indicator functions of the stages converge to the indicator function
of the limit. This is Mathlib's `Monotone.indicator_eventuallyEq_iUnion` for the stages. -/
theorem converges_indicator_stageLimit {M : Type*} [Zero M] {A : ℕ → Finset ℕ} (hA : Monotone A)
    (f : ℕ → M) : Converges (fun s => (A s : Set ℕ).indicator f) ((stageLimit A).indicator f) :=
  converges_iff_eventually.2 fun z => by
    rw [stageLimit_eq_iUnion]
    exact Monotone.indicator_eventuallyEq_iUnion _ (fun _ _ h => Finset.coe_subset.2 (hA h)) f z

end Enumeration

end TauCeti
