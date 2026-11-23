/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

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

open Manifold
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] TauCeti.normedAlgebraRatOfReal
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℚ R] [CompleteSpace R]

/-- Inverse transpose carries the exponential of `X` to the exponential of `-Xᵀ`. -/
@[simp]
theorem inverseTranspose_expUnit (X : Matrix n n R) :
    inverseTranspose (TauCeti.expUnit X) = TauCeti.expUnit (-Xᵀ) := by
  apply Units.ext
  rw [coe_inverseTranspose, ← TauCeti.expUnit_neg, TauCeti.expUnit_coe,
    TauCeti.expUnit_coe]
  -- The entrywise topology in `Matrix.exp_transpose` agrees definitionally with the
  -- operator-norm topology used in `TauCeti.expUnit`.
  convert (Matrix.exp_transpose (-X)).symm using 1 <;> rfl

end Matrix.GeneralLinearGroup

namespace Subgroup

/-- The matrices whose entire exponential line is contained in a real matrix subgroup. -/
def linearLieAlgebra (G : Subgroup (Matrix.GeneralLinearGroup n ℝ)) : Set (Matrix n n ℝ) :=
  {X | ∀ t : ℝ, TauCeti.expUnit (t • X) ∈ G}

variable {G : Subgroup (Matrix.GeneralLinearGroup n ℝ)} {X Y : Matrix n n ℝ}

/-- Membership in the linear Lie algebra means containment of the whole exponential line. -/
theorem mem_linearLieAlgebra_iff :
    X ∈ G.linearLieAlgebra ↔ ∀ t : ℝ, TauCeti.expUnit (t • X) ∈ G :=
  Iff.rfl

/-- In matrix coordinates, the exponential line consists of matrices underlying elements of the
subgroup. -/
theorem mem_linearLieAlgebra_iff_forall_exp :
    X ∈ G.linearLieAlgebra ↔
      ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n ℝ) = NormedSpace.exp (t • X) := by
  constructor
  · intro hX t
    exact ⟨TauCeti.expUnit (t • X), hX t, TauCeti.expUnit_coe _⟩
  · intro hX t
    obtain ⟨g, hg, h⟩ := hX t
    have hg' : g = TauCeti.expUnit (t • X) := Units.ext (h.trans (TauCeti.expUnit_coe _).symm)
    exact hg' ▸ hg

/-- The zero matrix lies in every linear Lie algebra. -/
@[simp]
theorem zero_mem_linearLieAlgebra : (0 : Matrix n n ℝ) ∈ G.linearLieAlgebra := by
  intro t
  simpa only [smul_zero, TauCeti.expUnit_zero] using G.one_mem

/-- Scalar multiplication preserves the exponential-line condition for any subgroup. -/
theorem smul_mem_linearLieAlgebra (c : ℝ) (hX : X ∈ G.linearLieAlgebra) :
    c • X ∈ G.linearLieAlgebra := by
  intro t
  simpa only [smul_smul] using hX (t * c)

/-- Negation preserves the linear Lie algebra of any subgroup. -/
theorem neg_mem_linearLieAlgebra (hX : X ∈ G.linearLieAlgebra) :
    -X ∈ G.linearLieAlgebra := by
  simpa only [neg_one_smul] using smul_mem_linearLieAlgebra (-1) hX

/-- For a closed matrix subgroup, the exponential-line set is the underlying set of the
matrix-coordinate image of the abstract subgroup Lie algebra. -/
theorem linearLieAlgebra_eq_map_lieSubalgebraOfSubgroup
    (hG : IsClosed (G : Set (Matrix.GeneralLinearGroup n ℝ))) :
    G.linearLieAlgebra =
      (((TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℝ)) G).toSubmodule.map
        (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix n n ℝ)).toLinearEquiv.toLinearMap) :
        Set _) := by
  ext X
  rw [mem_linearLieAlgebra_iff, SetLike.mem_coe, Submodule.mem_map_equiv,
    LieSubalgebra.mem_toSubmodule]
  exact (TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hG X).symm

/-- The linear Lie algebra of a closed matrix subgroup is a closed set of matrices. -/
theorem isClosed_linearLieAlgebra
    (hG : IsClosed (G : Set (Matrix.GeneralLinearGroup n ℝ))) :
    IsClosed G.linearLieAlgebra := by
  rw [linearLieAlgebra_eq_map_lieSubalgebraOfSubgroup hG]
  exact Submodule.isClosed_of_finiteDimensional _

/-- Addition preserves the linear Lie algebra of a closed matrix subgroup. -/
theorem add_mem_linearLieAlgebra
    (hG : IsClosed (G : Set (Matrix.GeneralLinearGroup n ℝ)))
    (hX : X ∈ G.linearLieAlgebra) (hY : Y ∈ G.linearLieAlgebra) :
    X + Y ∈ G.linearLieAlgebra := by
  rw [linearLieAlgebra_eq_map_lieSubalgebraOfSubgroup hG] at hX hY ⊢
  exact add_mem hX hY

/-- The matrix commutator preserves the linear Lie algebra of a closed matrix subgroup. -/
theorem commutator_mem_linearLieAlgebra
    (hG : IsClosed (G : Set (Matrix.GeneralLinearGroup n ℝ)))
    (hX : X ∈ G.linearLieAlgebra) (hY : Y ∈ G.linearLieAlgebra) :
    X * Y - Y * X ∈ G.linearLieAlgebra := by
  rw [linearLieAlgebra_eq_map_lieSubalgebraOfSubgroup hG] at hX hY ⊢
  rcases hX with ⟨X, hX, rfl⟩
  rcases hY with ⟨Y, hY, rfl⟩
  exact ⟨⁅X, Y⁆, LieSubalgebra.lie_mem _ hX hY,
    (TauCeti.Lie.unitsLieAlgebraLieEquiv.map_lie X Y)⟩

/-- Inverse-transpose stability of a matrix subgroup implies transpose stability of its linear
Lie algebra. This implication needs no closedness assumption. -/
theorem transpose_mem_linearLieAlgebra
    (hG : ∀ g ∈ G, Matrix.GeneralLinearGroup.inverseTranspose g ∈ G)
    (hX : X ∈ G.linearLieAlgebra) : Xᵀ ∈ G.linearLieAlgebra := by
  intro t
  have h := hG _ (hX (-t))
  rw [Matrix.GeneralLinearGroup.inverseTranspose_expUnit, Matrix.transpose_smul] at h
  simpa only [neg_smul, neg_neg] using h

end Subgroup
