/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import TauCeti.Algebra.Algebra.Subalgebra.Operations
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Topology of fixed subrings

For a monoid acting by ring automorphisms on a Hausdorff topological ring, with each element
acting continuously, the fixed subring `FixedPoints.subring A G` is closed: its carrier is the
common fixed set `MulAction.fixedPoints G A`. Consequently the fixed subring of a complete
Hausdorff ring is complete. This parallels `Subalgebra.isClosed_center` and the completeness of
the center (`TauCeti/Topology/Algebra/Algebra/Center.lean`).

## Main results

* `TauCeti.FixedPoints.isClosed_subring`: the fixed subring is closed.
* The fixed subring of a complete Hausdorff ring is complete (an instance).
-/

public section

namespace TauCeti.FixedPoints

variable {A G : Type*} [Ring A] [Monoid G] [MulSemiringAction G A]

variable (A G) in
/-- The fixed subring of a monoid acting continuously on a Hausdorff ring is closed. -/
theorem isClosed_subring [TopologicalSpace A] [T2Space A] [ContinuousConstSMul G A] :
    IsClosed (_root_.FixedPoints.subring A G : Set A) := by
  rw [coe_subring]
  exact isClosed_fixedPoints_of_continuousConstSMul

/-- The fixed subring of a monoid acting continuously on a complete Hausdorff ring is
complete. -/
instance [UniformSpace A] [CompleteSpace A] [T2Space A] [ContinuousConstSMul G A] :
    CompleteSpace (_root_.FixedPoints.subring A G) :=
  (isClosed_subring A G).completeSpace_coe

end TauCeti.FixedPoints
