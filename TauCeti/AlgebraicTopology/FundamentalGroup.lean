/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Fundamental groups of simply connected spaces

This file records basic consequences of simple connectedness for maps on fundamental groups.

## Main declarations

* `TauCeti.FundamentalGroup.map_range_le_mapOfEq_range_of_simplyConnectedSpace`: a simply
  connected domain satisfies the fundamental-group range condition against any `mapOfEq` range.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {A : Type*} [TopologicalSpace A]

/-- A simply connected domain satisfies the fundamental-group range condition against any
basepoint-adjusted map range. -/
theorem FundamentalGroup.map_range_le_mapOfEq_range_of_simplyConnectedSpace
    [SimplyConnectedSpace A] (p : C(E, X)) (f : C(A, X)) (a₀ : A) (e₀ : E)
    (he : p e₀ = f a₀) :
    (_root_.FundamentalGroup.map f a₀).range ≤
      (_root_.FundamentalGroup.mapOfEq p he).range := by
  rw [show (_root_.FundamentalGroup.map f a₀).range = ⊥ by
    have : Subsingleton ((_root_.FundamentalGroup.map f a₀).range) :=
      (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.map f a₀).subsingleton_coe_range)
    exact Subgroup.eq_bot_of_subsingleton _]
  exact bot_le

end TauCeti
