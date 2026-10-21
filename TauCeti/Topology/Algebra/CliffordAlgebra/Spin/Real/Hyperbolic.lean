/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Hyperbolic
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Hyperbolic

/-!
# The identity component of the real hyperbolic-plane orthogonal group

The proper isometry group of the real hyperbolic plane is the topological unit group
through the hyperbolic torus. Its identity component is therefore the positive-unit
subgroup. The real Spin image is exactly this component: the general spinor-norm
calculation identifies it with the square-unit parameters, and a real unit is a square
exactly when it is positive.
-/

public section

open Set
open TauCeti.QuadraticMap

namespace TauCeti

/-- The real Spin image of the hyperbolic plane is the identity component of its proper
orthogonal group. -/
theorem range_spinToSpecialOrthogonal_hyperbolicPlane_real :
    (CliffordAlgebra.spinToSpecialOrthogonal (hyperbolicPlane ℝ)).range =
      Subgroup.connectedComponentOfOne (specialOrthogonalGroup (hyperbolicPlane ℝ)) := by
  rw [CliffordAlgebra.range_spinToSpecialOrthogonal_hyperbolicPlane,
    connectedComponentOfOne_specialOrthogonalGroup_hyperbolicPlane]
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg ⊢
    obtain ⟨t, ht, rfl⟩ := hg
    exact ⟨t, (Units.isSquare_iff_pos t).mp ht, rfl⟩
  · intro hg
    rw [Subgroup.mem_map] at hg ⊢
    obtain ⟨t, ht, rfl⟩ := hg
    exact ⟨t, (Units.isSquare_iff_pos t).mpr ht, rfl⟩

end TauCeti
