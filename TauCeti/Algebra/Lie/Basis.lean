/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Coordinates of Lie brackets in a finite basis
-/

public section

namespace Module.Basis

/-- A bracket coordinate is the sum of the bracket columns weighted by the first argument's
basis coordinates. -/
theorem repr_lie_eq_sum {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [Fintype ι] (b : Basis ι R L) (X Y : L) (k : ι) :
    b.repr ⁅X, Y⁆ k = ∑ i : ι, b.repr X i * b.repr ⁅b i, Y⁆ k := by
  classical
  conv_lhs => rw [← b.sum_repr X]
  rw [sum_lie]
  simp [smul_lie, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul]

end Module.Basis
