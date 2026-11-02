/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.PowerBounded
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Canonical reduction of a nonarchimedean topological ring

The canonical reduction is `A° / A°°`, using the native power-bounded subring and its
ideal of topologically nilpotent elements. It is always reduced, even when `A` is not:
topological nilpotence of a positive power implies topological nilpotence of the element.
No completeness, uniformity or noetherianity is required.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.3.1.
-/

public section

namespace TauCeti.Huber

variable (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
    [ContinuousMul A]

/-- The ideal of topologically nilpotent elements in the power-bounded subring is radical. -/
theorem isRadical_topologicallyNilpotentIdeal : (topologicallyNilpotentIdeal A).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro a ha
  rw [mem_topologicallyNilpotentIdeal] at ha ⊢
  exact IsTopologicallyNilpotent.of_pow (by decide : 2 ≠ 0) ha

/-- The canonical reduction `A° / A°°` of a nonarchimedean topological ring. -/
abbrev CanonicalReduction := powerBoundedSubring A ⧸ topologicallyNilpotentIdeal A

instance : IsReduced (CanonicalReduction A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_topologicallyNilpotentIdeal A)

end TauCeti.Huber
