/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Period of Boolean negation

Boolean negation has minimal period two at every point. Under a semiconjugacy to negation,
this forces even periods, for example for face traversals of bipartite graphs.
-/

public section

namespace Bool

/-- Every Boolean has minimal period two under negation. -/
@[simp] theorem minimalPeriod_not (b : Bool) : Function.minimalPeriod Bool.not b = 2 :=
  Function.minimalPeriod_eq_prime (by simp [Function.IsPeriodicPt, Function.IsFixedPt])
    (by simp [Function.IsFixedPt])

end Bool
