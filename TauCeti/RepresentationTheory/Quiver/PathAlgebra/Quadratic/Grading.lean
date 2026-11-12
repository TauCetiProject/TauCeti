/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Quadratic.Dual
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# Path length on a quadratic dual

The orthogonal relations defining a quadratic dual have path length two in the ordinary
opposite path algebra. Their two-sided ideal is homogeneous, so the quotient itself inherits
the path-length grading. These are the images of the original opposite-path pieces, rather
than a separately graded copy of the algebra. This grading makes comparisons with quadratic
duals usable in graded resolutions and Hilbert-series calculations.

Quadratic duality and its handedness follow Polishchuk--Positselski, *Quadratic algebras*,
Chapter 1, Section 2. The grading descends using
`TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece`.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver MulOpposite

universe u v w

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Finite Q]
  [∀ a b : Q, Finite (a ⟶ b)] (R : Submodule k (pathAlgebra k Q))

/-- The quadratic dual relation ideal is homogeneous for opposite path length. -/
theorem isHomogeneous_quadraticDualIdeal :
    (quadraticDualIdeal k Q R).asIdeal.IsHomogeneous (opGrade k Q) := by
  rw [quadraticDualIdeal_eq_span]
  refine TwoSidedIdeal.homogeneous_span _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨2, (mem_opGrade_iff k Q).2 (quadraticOrthogonal_le_grade_two R hx)⟩

/-- The degree-`n` submodule of the actual quadratic dual quotient. -/
noncomputable def quadraticDualGrade (n : ℕ) : Submodule k (quadraticDual k Q R) :=
  TauCeti.GradedAlgebra.quotientPiece (opGrade k Q) (quadraticDualIdeal k Q R).asIdeal n

/-- A degree-`n` class has a representative of opposite path length `n`. -/
@[simp]
theorem mem_quadraticDualGrade_iff {n : ℕ} {x : quadraticDual k Q R} :
    x ∈ quadraticDualGrade k Q R n ↔
      ∃ y ∈ opGrade k Q n, quadraticDualMk k Q R y = x := by
  simp only [quadraticDualGrade, TauCeti.GradedAlgebra.mem_quotientPiece_iff,
    quadraticDualMk_apply]

/-- The quotient map preserves path length. -/
theorem quadraticDualMk_mem_grade {n : ℕ} {x : (pathAlgebra k Q)ᵐᵒᵖ}
    (hx : x ∈ opGrade k Q n) : quadraticDualMk k Q R x ∈ quadraticDualGrade k Q R n :=
  (mem_quadraticDualGrade_iff k Q R).2 ⟨x, hx, rfl⟩

/-- The quadratic dual is the internal direct sum of its induced path-length pieces. -/
theorem isInternal_quadraticDualGrade : DirectSum.IsInternal (quadraticDualGrade k Q R) :=
  TauCeti.GradedAlgebra.isInternal_quotientPiece _ _ (isHomogeneous_quadraticDualIdeal k Q R)

/-- Multiplication in the quadratic dual adds path lengths. -/
theorem mul_mem_quadraticDualGrade {m n : ℕ} {x y : quadraticDual k Q R}
    (hx : x ∈ quadraticDualGrade k Q R m) (hy : y ∈ quadraticDualGrade k Q R n) :
    x * y ∈ quadraticDualGrade k Q R (m + n) :=
  TauCeti.GradedAlgebra.mul_mem_quotientPiece _ _ hx hy

/-- The induced path-length graded algebra structure on the quadratic dual. -/
@[instance_reducible]
noncomputable def quadraticDualGradedAlgebra : GradedAlgebra (quadraticDualGrade k Q R) :=
  TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece _ _
    (isHomogeneous_quadraticDualIdeal k Q R)

end TauCeti.PathAlgebra
