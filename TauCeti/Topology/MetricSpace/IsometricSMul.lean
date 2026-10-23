/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Isometric actions of submonoids and subgroups

A submonoid or subgroup of a monoid acting by isometries acts by isometries through the
restricted action. Mathlib registers the restricted action itself, but not this property of it;
these instances let theorems about isometric actions apply directly to a subgroup, for example to
a discrete subgroup of `PSL(2, ℝ)` acting on the upper half-plane.
-/

public section

variable {M X : Type*} [PseudoEMetricSpace X]

/-- A submonoid of a monoid acting by isometries acts by isometries. -/
@[to_additive /-- An additive submonoid of an additive monoid acting by isometries acts by
isometries. -/]
instance Submonoid.isIsometricSMul [MulOneClass M] [SMul M X] [IsIsometricSMul M X]
    (S : Submonoid M) : IsIsometricSMul S X :=
  ⟨fun s ↦ isometry_smul X (s : M)⟩

/-- A subgroup of a group acting by isometries acts by isometries. -/
@[to_additive /-- An additive subgroup of an additive group acting by isometries acts by
isometries. -/]
instance Subgroup.isIsometricSMul [Group M] [SMul M X] [IsIsometricSMul M X]
    (S : Subgroup M) : IsIsometricSMul S X :=
  ⟨fun s ↦ isometry_smul X (s : M)⟩
