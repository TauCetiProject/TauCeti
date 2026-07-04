/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Basic

/-!
# Strong continuity API for semigroup orbits

This file exposes the basic orbit-continuity consequences of the existing
`StronglyContinuousSemigroup` structure. The structure only assumes strong continuity at `0`;
`TauCeti.Analysis.Semigroups.Basic` proves strong continuity at every nonnegative real time for
the real-time shim `S.realOperator`. This file packages that theorem in the forms downstream
generator and resolvent arguments use: continuity on the half-line, continuity on compact
nonnegative intervals, and positive-time ordinary continuity.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part A, "API to develop", the
foundational strong-continuity API for strongly continuous semigroups.

## Main declarations

* `TauCeti.Semigroups.StronglyContinuousSemigroup.continuousOn_realOperator_orbit`:
  `t ↦ S.realOperator t x` is continuous on `[0, ∞)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.continuousAt_realOperator_orbit_of_pos`:
  positive-time orbits are ordinarily continuous.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.continuousOn_realOperator_orbit_uIcc`:
  the orbit is continuous on any compact interval whose endpoints are nonnegative.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Proposition I.5.3.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1.
-/

public section

noncomputable section

open scoped Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

/-- The real-time orbit of a strongly continuous semigroup is continuous on the nonnegative
half-line. -/
theorem continuousOn_realOperator_orbit (S : StronglyContinuousSemigroup X) (x : X) :
    ContinuousOn (fun t : ℝ => S.realOperator t x) (Set.Ici 0) :=
  fun t ht => S.realOperator_continuousWithinAt x t ht

/-- At a positive real time, the real-time orbit of a strongly continuous semigroup is ordinarily
continuous. -/
theorem continuousAt_realOperator_orbit_of_pos (S : StronglyContinuousSemigroup X) (x : X)
    {t : ℝ} (ht : 0 < t) : ContinuousAt (fun u : ℝ => S.realOperator u x) t :=
  (S.realOperator_continuousWithinAt x t ht.le).continuousAt (Ici_mem_nhds ht)

/-- The real-time orbit is continuous on every compact interval with nonnegative endpoints. -/
theorem continuousOn_realOperator_orbit_uIcc (S : StronglyContinuousSemigroup X) (x : X)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (fun t : ℝ => S.realOperator t x) (Set.uIcc a b) :=
  (S.continuousOn_realOperator_orbit x).mono fun _ hu =>
    (le_inf ha hb).trans hu.1

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
