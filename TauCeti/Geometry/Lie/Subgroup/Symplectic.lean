/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Topology.Algebra.SymplecticGroup

/-!
# The Lie algebra of the symplectic group, and its exponential

The symplectic group sits inside the general linear group as `TauCeti.GLSymplectic`, a subgroup of
`GL (l ⊕ l) 𝕜 = (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ`, which over `𝕜 = ℝ` or `ℂ` (any `RCLike` field) is a
real Lie group. This file computes the Lie algebra that `TauCeti.Lie.lieSubalgebraOfSubgroup`
assigns to it: in the canonical matrix coordinates of the general linear Lie algebra it is
Mathlib's symplectic Lie algebra `LieAlgebra.Symplectic.sp l 𝕜`, the matrices that are
skew-adjoint for the canonical skew-symmetric matrix `J`. Over `ℝ` this is the Lie algebra of the
real symplectic group `Sp(2n, ℝ)`; over `ℂ` it is the complex symplectic Lie algebra, viewed as a
real Lie algebra.

Two inputs meet here: the matrix-level characterization of the exponential lines that stay inside
the symplectic group, `Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp`, and the
algebra-coordinate form of the Lie algebra of a closed subgroup of units,
`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff`, whose closedness
hypothesis is supplied by `TauCeti.isClosed_GLSymplectic`.

The exponential of an element `X` of `sp l 𝕜` is symplectic, so it is an element
`TauCeti.GLSymplectic.expOfMemSp X` of the symplectic subgroup, and its one-parameter subgroup
`t ↦ exp (t X)` restricts to a path of symplectic matrices.

## Main definitions

* `TauCeti.GLSymplectic.expOfMemSp`: the exponential of an element of the symplectic Lie algebra,
  as a symplectic matrix.
* `TauCeti.GLSymplectic.expPath`: the path `t ↦ exp (t X)`, `t ∈ [0, 1]`, of symplectic matrices
  from the identity to `exp X`.

## Main results

* `TauCeti.Lie.forall_lieExp_mem_GLSymplectic_iff_mem_sp`: in canonical matrix coordinates, the
  abstract exponential line of `A` stays inside the symplectic subgroup exactly when `A` is
  skew-adjoint for `J`.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp`: **the Lie
  algebra of the symplectic group is `sp`.**
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_mem_sp_of_mem_lieSubalgebraOfSubgroup`: the same statement
  read from an element of the Lie algebra of the symplectic group.
* `TauCeti.Lie.isEmbeddedLieSubgroup_GLSymplectic`: the symplectic group is an embedded Lie
  subgroup of the general linear group, so a Lie group in its own right.
* `TauCeti.GLSymplectic.continuous_expOfMemSp`: the exponential of a continuous family of
  elements of `sp` is continuous in the symplectic group.
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm used for the general linear Lie group.
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {l : Type*} [DecidableEq l] [Fintype l] {𝕜 : Type*} [RCLike 𝕜]

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup inside the symplectic group exactly when it is skew-adjoint for the
canonical skew-symmetric matrix. -/
-- Normalize the whole exponential-line predicate before subgroup membership expands.
@[simp↓]
theorem forall_lieExp_mem_GLSymplectic_iff_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv
        (R := Matrix (l ⊕ l) (l ⊕ l) 𝕜)).symm (t • A)) ∈ GLSymplectic l 𝕜) ↔
      A ∈ LieAlgebra.Symplectic.sp l 𝕜 := by
  rw [forall_lieExp_unitsLieAlgebraLieEquiv_symm_smul_mem_iff,
    ← Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp]
  simp only [GLSymplectic.mem_iff_mem_symplecticGroup, TauCeti.expUnit_coe]
  -- Both sides are now the same condition; only the `GL (l ⊕ l) 𝕜` abbreviation for the matrix
  -- units still has to be unfolded.
  exact Iff.rfl

/-- **The Lie algebra of the symplectic group is `sp`.** A matrix belongs to Mathlib's
symplectic Lie algebra exactly when its inverse image under the canonical units Lie equivalence
belongs to the Lie subalgebra of the symplectic subgroup of the general linear group. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp
    (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) :
    (unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) 𝕜)).symm A ∈
        lieSubalgebraOfSubgroup (GLSymplectic l 𝕜 : Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ) ↔
      A ∈ LieAlgebra.Symplectic.sp l 𝕜 := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff (isClosed_GLSymplectic l 𝕜),
    ← Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp]
  simp only [GLSymplectic.mem_iff_mem_symplecticGroup, TauCeti.expUnit_coe]
  -- Both sides are now the same condition; only the `GL (l ⊕ l) 𝕜` abbreviation for the matrix
  -- units still has to be unfolded.
  exact Iff.rfl

/-- The matrix coordinates of an element of the Lie algebra of the symplectic group lie in `sp`. -/
theorem unitsLieAlgebraLieEquiv_mem_sp_of_mem_lieSubalgebraOfSubgroup
    {X : LeftInvariantDerivation 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜) (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ}
    (hX : X ∈ lieSubalgebraOfSubgroup (GLSymplectic l 𝕜 : Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ)) :
    unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) 𝕜) X ∈ LieAlgebra.Symplectic.sp l 𝕜 := by
  rwa [← unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp,
    LieEquiv.symm_apply_apply]

/-- **The symplectic group is an embedded Lie subgroup of the general linear group.** Being a
closed subgroup of the Lie group of units, the closed-subgroup theorem makes it a Lie group for its
subspace topology. Over `𝕜 = ℝ` this is `Sp(2n, ℝ)`. -/
theorem isEmbeddedLieSubgroup_GLSymplectic :
    IsEmbeddedLieSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
      (GLSymplectic l 𝕜 : Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ) :=
  isEmbeddedLieSubgroup_of_isClosed (isClosed_GLSymplectic l 𝕜)

end TauCeti.Lie

namespace TauCeti.GLSymplectic

open scoped unitInterval

attribute [local instance 100] LieRing.ofAssociativeRing

-- `TauCeti.expUnit` is stated for normed `ℚ`-algebras; the operator norm gives a normed
-- `ℝ`-algebra, whose scalars this instance restricts.
attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {l : Type*} [DecidableEq l] [Fintype l] {𝕜 : Type*} [RCLike 𝕜]

/-- The exponential of an element of the symplectic Lie algebra, as a symplectic matrix. -/
def expOfMemSp (X : Matrix (l ⊕ l) (l ⊕ l) 𝕜) (hX : X ∈ LieAlgebra.Symplectic.sp l 𝕜) :
    GLSymplectic l 𝕜 :=
  ⟨expUnit X, mem_iff_mem_symplecticGroup.2 <| by
    rw [expUnit_coe]
    exact Matrix.exp_mem_symplecticGroup_of_mem_sp X hX⟩

@[simp]
theorem coe_expOfMemSp (X : Matrix (l ⊕ l) (l ⊕ l) 𝕜) (hX : X ∈ LieAlgebra.Symplectic.sp l 𝕜) :
    ((expOfMemSp X hX : GL (l ⊕ l) 𝕜) : Matrix (l ⊕ l) (l ⊕ l) 𝕜) = exp X :=
  expUnit_coe X

/-- Along a continuous family of elements of the symplectic Lie algebra, the exponential is
continuous as a family of symplectic matrices. -/
theorem continuous_expOfMemSp {α : Type*} [TopologicalSpace α] {f : α → Matrix (l ⊕ l) (l ⊕ l) 𝕜}
    (hf : Continuous f) (hfX : ∀ a, f a ∈ LieAlgebra.Symplectic.sp l 𝕜) :
    Continuous fun a ↦ expOfMemSp (f a) (hfX a) :=
  (continuous_expUnit.comp hf).subtype_mk _

/-- The one-parameter subgroup `t ↦ exp (t X)`, `t ∈ [0, 1]`, generated by an element `X` of the
symplectic Lie algebra, as a path of symplectic matrices from the identity to `exp X`. -/
def expPath (X : Matrix (l ⊕ l) (l ⊕ l) 𝕜) (hX : X ∈ LieAlgebra.Symplectic.sp l 𝕜) :
    Path (1 : GLSymplectic l 𝕜) (expOfMemSp X hX) where
  toFun t := expOfMemSp ((t : ℝ) • X) ((LieAlgebra.Symplectic.sp l 𝕜).toSubmodule.smul_of_tower_mem
    (t : ℝ) hX)
  continuous_toFun := continuous_expOfMemSp (continuous_subtypeVal.smul continuous_const) _
  source' := by
    refine Subtype.ext (Units.ext ?_)
    simp
  target' := by
    refine Subtype.ext (Units.ext ?_)
    simp

@[simp]
theorem coe_expPath_apply (X : Matrix (l ⊕ l) (l ⊕ l) 𝕜) (hX : X ∈ LieAlgebra.Symplectic.sp l 𝕜)
    (t : I) : ((expPath X hX t : GL (l ⊕ l) 𝕜) : Matrix (l ⊕ l) (l ⊕ l) 𝕜) = exp ((t : ℝ) • X) :=
  expUnit_coe _

end TauCeti.GLSymplectic
