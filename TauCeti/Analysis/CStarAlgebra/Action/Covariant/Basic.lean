/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Covariant representations of C⋆-actions

A covariant representation consists of a possibly degenerate coefficient representation and a
strongly continuous unitary group representation, satisfying `U g (π a v) = π (α g a) (U g v)`.
Strong continuity is imposed separately from `ContRepresentation`, which only makes each
individual operator continuous. These data admit vector-valued integrated forms without assuming
operator-norm continuity of the group representation.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

namespace TauCeti.CStarAction

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A covariant pair for a point-norm continuous action on a possibly nonunital C⋆-algebra.
The coefficient representation is not required to be nondegenerate. -/
structure CovariantRepresentation (α : CStarAction G A) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The coefficient representation. -/
  coefficient : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  /-- The group representation by bounded operators. -/
  group : ContRepresentation ℂ G H
  /-- Each group operator preserves the inner product. -/
  isUnitary : group.IsUnitary
  /-- Every group orbit is continuous in the Hilbert-space norm. -/
  continuous_orbit : ∀ v, Continuous fun g => group g v
  /-- Covariance of the coefficient and group representations. -/
  covariance (g : G) (a : A) (v : H) :
    group g (coefficient a v) = coefficient (α g a) (group g v)

namespace CovariantRepresentation

variable {α : CStarAction G A}

/-- The coefficient and group representations determine a covariant pair. -/
@[ext]
theorem ext {P Q : CovariantRepresentation α H}
    (hπ : P.coefficient = Q.coefficient) (hU : P.group = Q.group) : P = Q := by
  cases P
  cases Q
  cases hπ
  cases hU
  rfl

/-- Covariance as an equality of bounded operators. -/
@[simp]
theorem group_mul_coefficient (P : CovariantRepresentation α H) (g : G) (a : A) :
    P.group g * P.coefficient a = P.coefficient (α g a) * P.group g := by
  ext v
  exact P.covariance g a v

/-- The coefficient at a transformed element is obtained by unitary conjugation. -/
theorem coefficient_action (P : CovariantRepresentation α H) (g : G) (a : A) :
    P.coefficient (α g a) = P.group g * P.coefficient a * P.group g⁻¹ := by
  rw [P.group_mul_coefficient, mul_assoc, ← map_mul]
  simp

/-- Every coefficient representation gives a covariant pair for the trivial action, with
trivial group representation. -/
def trivial (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    CovariantRepresentation (CStarAction.trivial (G := G) (A := A)) H where
  coefficient := π
  group := ContRepresentation.trivial ℂ G H
  isUnitary := ContRepresentation.isUnitary_trivial
  continuous_orbit _ := by simpa using continuous_const
  covariance _ _ _ := by simp

@[simp]
theorem trivial_coefficient (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (trivial (G := G) π).coefficient = π :=
  (rfl)

@[simp]
theorem trivial_group (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (trivial (G := G) π).group = ContRepresentation.trivial ℂ G H :=
  (rfl)

end CovariantRepresentation

end TauCeti.CStarAction
