/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Compact unitary groups in proper C⋆-rings

`Unitary.compactSpace_of_properSpace` equips the unitary group of a proper C⋆-ring with
`CompactSpace`, including for the trivial ring. The unitary elements form a closed
multiplicative submonoid of the ring. This supplies compactness for finite-dimensional
operator and matrix algebras.
-/

public section

/-- The unitary group of a proper C⋆-ring is compact. -/
instance Unitary.compactSpace_of_properSpace
    {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] [ProperSpace E] :
    CompactSpace (unitary E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E) ‖(1 : E)‖).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [mem_closedBall_zero_iff]
  have hnorm : ‖u‖ = ‖(1 : E)‖ := by
    simpa using CStarRing.norm_coe_unitary_mul (⟨u, hu⟩ : unitary E) 1
  exact hnorm.le
