/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Continuity for restricted actions

This file records generic transfer instances for actions whose pointwise orbit maps are
continuous. A submonoid, and hence a subgroup, inherits `ContinuousConstSMul` from an ambient
monoid action.
-/

public section

namespace TauCeti

namespace Submonoid

/-- A submonoid inherits continuity in the point from an ambient continuous action. -/
instance continuousConstSMul {M X : Type*} [Monoid M] [TopologicalSpace X] [MulAction M X]
    [ContinuousConstSMul M X] (S : Submonoid M) : ContinuousConstSMul S X :=
  ⟨fun g => by
    simpa only [Submonoid.smul_def] using continuous_const_smul (g : M)⟩

end Submonoid

namespace Subgroup

/-- A subgroup inherits continuity in the point from an ambient continuous action. -/
instance continuousConstSMul {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (S : Subgroup G) : ContinuousConstSMul S X :=
  Submonoid.continuousConstSMul S.toSubmonoid

end Subgroup

end TauCeti
