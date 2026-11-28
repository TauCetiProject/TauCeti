/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.CayleyChart
public import TauCeti.Topology.Algebra.IsOpenUnits

/-!
# Continuity of Cayley coordinates

In a topological ring with open units, the Cayley coordinate relative to any base
point is continuous wherever its denominator is a unit. This applies to matrix
algebras without requiring a norm, for instance in simultaneous approximation.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [IsOpenUnits A]
  {j J : A}

/-- The Cayley coordinate is continuous at a point where its denominator is a unit. -/
@[fun_prop]
theorem continuousAt_cayleyCoord (hJ : IsUnit (j + J)) :
    ContinuousAt (cayleyCoord j) J := by
  rw [cayleyCoord_eq_fun]
  have hinv : ContinuousAt Ring.inverse (j + J) := by
    simpa only [hJ.unit_spec] using IsOpenUnits.continuousAt_ringInverse hJ.unit
  exact (continuousAt_const.sub continuousAt_id).mul
    (hinv.comp (continuousAt_const.add continuousAt_id))

/-- The Cayley coordinate is continuous where its denominator is a unit. -/
theorem continuousOn_cayleyCoord : ContinuousOn (cayleyCoord j) {J : A | IsUnit (j + J)} :=
  fun _ hJ ↦ (continuousAt_cayleyCoord hJ).continuousWithinAt

end TauCeti
