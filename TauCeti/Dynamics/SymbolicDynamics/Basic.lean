/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions

/-!
# Cylinder sets of the full shift form a basis

For a discrete alphabet `A`, Mathlib's cylinder sets `SymbolicDynamics.FullShift.cylinder U x`,
for finite `U`, are clopen (`SymbolicDynamics.FullShift.isOpen_cylinder`,
`SymbolicDynamics.FullShift.isClosed_cylinder`). This file records that they form a basis of the
product topology on `G → A` (`SymbolicDynamics.FullShift.isTopologicalBasis_cylinders`).
-/

public section

open TopologicalSpace

namespace SymbolicDynamics.FullShift

/-- For a discrete alphabet, the cylinder sets form a basis of the product topology. -/
theorem isTopologicalBasis_cylinders {G A : Type*} [TopologicalSpace A] [DiscreteTopology A] :
    IsTopologicalBasis (Set.range fun p : Finset G × (G → A) => cylinder p.1 p.2) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x u hx hu => ?_
  · rintro _ ⟨⟨U, x⟩, rfl⟩
    exact isOpen_cylinder U x
  · obtain ⟨U, v, hv, hsub⟩ := isOpen_pi_iff.1 hu x hx
    refine ⟨cylinder U x, ⟨(U, x), rfl⟩, mem_cylinder.2 fun _ _ => rfl,
      fun y hy => hsub fun i hi => ?_⟩
    rw [mem_cylinder.1 hy i hi]
    exact (hv i hi).2

end SymbolicDynamics.FullShift
