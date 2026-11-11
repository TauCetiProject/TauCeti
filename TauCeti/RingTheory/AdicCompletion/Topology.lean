/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Topology of adically complete rings

Two ideals defining the same topology give the same notion of separated completeness.
Mathlib identifies each with Hausdorff completeness for the additive uniformity. The result
here uses that uniformity only locally, so callers need only specify the ring topology.

In an `I`-adically complete ring carrying the `I`-adic topology, `I` is open and contained in the
Jacobson radical, so the topological nilradical also lies in the Jacobson radical
(`IsAdic.topologicalNilradical_le_jacobson`).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.1.9.
-/

public section

namespace IsAdic

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I J : Ideal R}

/-- Separated adic completeness depends only on the topology defined by the ideal.
There is no finite generation hypothesis on either ideal. -/
theorem isAdicComplete_iff_of_isAdic (hI : IsAdic I) (hJ : IsAdic J) :
    IsAdicComplete I R ↔ IsAdicComplete J R := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  let := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact hI.isAdicComplete_iff.trans hJ.isAdicComplete_iff.symm

/-- In an `I`-adically complete ring whose topology is `I`-adic, the topological nilradical lies in
the Jacobson radical. -/
theorem topologicalNilradical_le_jacobson [IsLinearTopology R R] (hI : IsAdic I)
    [IsAdicComplete I R] : topologicalNilradical R ≤ Ring.jacobson R := by
  rw [← Ideal.jacobson_bot]
  refine topologicalNilradical_le_jacobson_bot (by simpa using hI.isOpen_pow 1) ?_
  rw [Ideal.jacobson_bot]
  exact IsAdicComplete.le_jacobson I

end IsAdic
