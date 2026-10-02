/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Subgroup.SpecialLinear
public import TauCeti.Geometry.Lie.Subgroup.Unitary
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The Lie algebra of the special unitary group

The special unitary group sits inside the general linear group as `TauCeti.GLSpecialUnitary`, a
subgroup of `GL n 𝕜 = (Matrix n n 𝕜)ˣ`, which over `ℝ` or `ℂ` (any `RCLike` field) is a real Lie
group.  This file computes the Lie algebra that `TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to
it: in the canonical matrix coordinates of the general linear Lie algebra it is `𝔰𝔲`, the
**skew-Hermitian matrices of trace zero**, `Aᴴ = -A` and `trace A = 0`.

Nothing analytic is new here.  `TauCeti.GLSpecialUnitary` is by construction the intersection of
the unitary subgroup with the kernel of the determinant, and the Lie algebra of an intersection of
closed subgroups is the intersection of the Lie algebras
(`TauCeti.Lie.lieSubalgebraOfSubgroup_inf`), so the two conditions are read off one at a time from
statements already available: the unitary factor contributes `Aᴴ = -A`
(`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg`)
and the determinant factor contributes `trace A = 0`
(`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sl`, the kernel of
the determinant being the image of the special linear group).  Closedness of both factors is what
makes the decomposition an equality rather than only an inclusion.

Unlike the orthogonal, symplectic and special linear cases, the answer is **not** the membership
condition of a Mathlib Lie subalgebra: Mathlib has `LieAlgebra.Orthogonal.so`,
`LieAlgebra.Symplectic.sp` and `LieAlgebra.SpecialLinear.sl`, but no special unitary counterpart —
`𝔰𝔲` is only a *real* subalgebra of `Matrix n n ℂ`, not a complex one — so the statement is the
explicit conjunction.

The trace condition is not redundant over `ℂ`: a skew-Hermitian matrix has purely imaginary
trace, and for a nonempty index type `i • 1` is skew-Hermitian without being trace-free.  Over
`ℝ` it *is* redundant, since a skew-symmetric matrix has trace equal to its own negative, and
there the special unitary group is Mathlib's special orthogonal group; that degeneration is
recorded below.

## Main results

* `TauCeti.Lie.lieSubalgebraOfSubgroup_GLSpecialUnitary`: the Lie algebra of the special unitary
  group is the intersection of the Lie algebras of the unitary and special linear groups.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff`: **the Lie
  algebra of the special unitary group is the trace-zero skew-Hermitian matrices.**
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff_mem_so`: over
  `ℝ` it is Mathlib's orthogonal Lie algebra, the trace condition being automatic there.
* `TauCeti.Lie.isEmbeddedLieSubgroup_GLSpecialUnitary`: **the special unitary group is an embedded
  Lie subgroup** of the general linear group, hence a Lie group in its own right.
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm used for the general linear Lie group,
-- together with continuity of the conjugate transpose for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **The Lie algebra of the special unitary group splits.**  It is the intersection of the Lie
algebra of the unitary group with the Lie algebra of the special linear group, because the special
unitary group is the intersection of those two subgroups and both of them are closed. -/
theorem lieSubalgebraOfSubgroup_GLSpecialUnitary :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
        (GLSpecialUnitary n 𝕜 : Subgroup (Matrix n n 𝕜)ˣ) =
      lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) (unitarySubgroup (Matrix n n 𝕜)ˣ) ⊓
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
          ((Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup n 𝕜 →* GL n 𝕜).range : Subgroup (Matrix n n 𝕜)ˣ) := by
  rw [GLSpecialUnitary.eq_unitarySubgroup_inf_ker_det,
    ← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
  exact lieSubalgebraOfSubgroup_inf (isClosed_unitarySubgroup_units (Matrix n n 𝕜))
    isClosed_range_toGL

/-- **The Lie algebra of the special unitary group is `𝔰𝔲`.**  A matrix is skew-Hermitian with
vanishing trace exactly when its inverse image under the canonical units Lie equivalence belongs
to the Lie subalgebra of the special unitary subgroup of the general linear group.

Over `ℂ` both conditions are needed: for a nonempty index type `i • 1` is skew-Hermitian, yet its
exponential line consists of unitary matrices whose determinant is not identically `1`. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff (A : Matrix n n 𝕜) :
    (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm A ∈
        lieSubalgebraOfSubgroup (GLSpecialUnitary n 𝕜 : Subgroup (Matrix n n 𝕜)ˣ) ↔
      Aᴴ = -A ∧ A.trace = 0 := by
  rw [lieSubalgebraOfSubgroup_GLSpecialUnitary, LieSubalgebra.mem_inf,
    unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg,
    unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sl,
    LieAlgebra.SpecialLinear.mem_sl_iff]

/-- Over `ℝ` the special unitary group is Mathlib's special orthogonal group, and its Lie algebra
is the orthogonal Lie algebra `LieAlgebra.Orthogonal.so n ℝ`: the trace of a skew-symmetric matrix
is its own negative, so the determinant condition contributed nothing. -/
theorem unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff_mem_so
    (A : Matrix n n ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix n n ℝ)).symm A ∈
        lieSubalgebraOfSubgroup (GLSpecialUnitary n ℝ : Subgroup (Matrix n n ℝ)ˣ) ↔
      A ∈ LieAlgebra.Orthogonal.so n ℝ := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff,
    LieAlgebra.Orthogonal.mem_so, Matrix.conjTranspose_eq_transpose_of_trivial,
    and_iff_left_iff_imp]
  intro hA
  -- Taking traces in `Aᵀ = -A` gives `trace A = -trace A`.
  have h := congrArg Matrix.trace hA
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h
  linarith

/-- **The special unitary group is an embedded Lie subgroup of the general linear group.**  Being
a closed subgroup of the Lie group of units, the closed-subgroup theorem makes it a Lie group for
its subspace topology, with smooth inclusion of everywhere split differential. -/
theorem isEmbeddedLieSubgroup_GLSpecialUnitary :
    IsEmbeddedLieSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      (GLSpecialUnitary n 𝕜 : Subgroup (Matrix n n 𝕜)ˣ) :=
  isEmbeddedLieSubgroup_of_isClosed (isClosed_GLSpecialUnitary n 𝕜)

end TauCeti.Lie
