/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Geometry.Lie.Exponential.Matrix.Basic

/-!
# The linear Lie algebra of a matrix subgroup

For a subgroup `G` of `GL(n, ℝ)`, `Subgroup.linearLieAlgebra G` is the set of matrices whose
whole exponential line stays in `G`. For closed `G` the coordinate equivalence
`TauCeti.Lie.unitsLieAlgebraLieEquiv` identifies this set with the abstract subgroup Lie algebra.
The identification shows that the set is closed under addition and matrix commutators.

Inverse-transpose stability of `G` implies transpose stability of its linear Lie algebra, without
a closedness hypothesis.
-/

public section

open scoped Matrix Matrix.Norms.Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Subgroup

variable {G : Subgroup (Matrix.GeneralLinearGroup n ℝ)} {X : Matrix n n ℝ}

/-- Inverse-transpose stability of a matrix subgroup implies transpose stability of its linear
Lie algebra. This implication needs no closedness assumption. -/
theorem transpose_mem_linearLieAlgebra
    (hG : ∀ g ∈ G, Matrix.GeneralLinearGroup.inverseTranspose g ∈ G)
    (hX : X ∈ G.linearLieAlgebra) : Xᵀ ∈ G.linearLieAlgebra := by
  rw [mem_linearLieAlgebra_iff] at hX ⊢
  intro t
  have h := hG _ (hX (-t))
  rw [Matrix.inverseTranspose_expUnit, Matrix.transpose_smul] at h
  simpa only [neg_smul, neg_neg] using h

end Subgroup
