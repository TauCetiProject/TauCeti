/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Fundamental groups with trivial source

This file records basic consequences of triviality of a source fundamental group for induced
maps on fundamental groups.

## Main declarations

* `TauCeti.FundamentalGroup.map_range_eq_bot_of_subsingleton`: if the source fundamental group
  is subsingleton, the range of any induced map from it is trivial.
* `TauCeti.FundamentalGroup.map_range_le_of_subsingleton`: if the source fundamental group is
  subsingleton, any induced-map range lies in any target subgroup.
* `TauCeti.FundamentalGroup.map_range_le_mapOfEq_range_of_subsingleton`: the corresponding
  basepoint-adjusted `mapOfEq` range specialization.
* `TauCeti.FundamentalGroup.map_range_le_mapOfEq_range_of_simplyConnectedSpace`: a simply
  connected domain satisfies the fundamental-group range condition against any `mapOfEq` range.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {A : Type*} [TopologicalSpace A]

/-- If the source fundamental group is subsingleton, the range of any induced map from it is
trivial. -/
@[simp]
theorem FundamentalGroup.map_range_eq_bot_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X)) :
    (_root_.FundamentalGroup.map f a₀).range = ⊥ := by
  have : Subsingleton ((_root_.FundamentalGroup.map f a₀).range) :=
    (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.map f a₀).subsingleton_coe_range)
  exact Subgroup.eq_bot_of_subsingleton _

/-- A simply connected domain has trivial induced fundamental-group range. -/
theorem FundamentalGroup.map_range_eq_bot_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) :
    (_root_.FundamentalGroup.map f a₀).range = ⊥ :=
  FundamentalGroup.map_range_eq_bot_of_subsingleton f

/-- If the source fundamental group is subsingleton, its induced-map range lies in any target
subgroup. -/
theorem FundamentalGroup.map_range_le_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X))
    (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H := by
  rw [FundamentalGroup.map_range_eq_bot_of_subsingleton f]
  exact bot_le

/-- A simply connected domain has induced fundamental-group range contained in any target
subgroup. -/
theorem FundamentalGroup.map_range_le_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H :=
  FundamentalGroup.map_range_le_of_subsingleton f H

/-- If the source fundamental group is subsingleton, its induced-map range lies in any
basepoint-adjusted map range. -/
theorem FundamentalGroup.map_range_le_mapOfEq_range_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (p : C(E, X)) (f : C(A, X)) (e₀ : E)
    (he : p e₀ = f a₀) :
    (_root_.FundamentalGroup.map f a₀).range ≤
      (_root_.FundamentalGroup.mapOfEq p he).range :=
  FundamentalGroup.map_range_le_of_subsingleton f
    (_root_.FundamentalGroup.mapOfEq p he).range

/-- A simply connected domain satisfies the fundamental-group range condition against any
basepoint-adjusted map range. -/
theorem FundamentalGroup.map_range_le_mapOfEq_range_of_simplyConnectedSpace
    [SimplyConnectedSpace A] (p : C(E, X)) (f : C(A, X)) (a₀ : A) (e₀ : E)
    (he : p e₀ = f a₀) :
    (_root_.FundamentalGroup.map f a₀).range ≤
      (_root_.FundamentalGroup.mapOfEq p he).range :=
  FundamentalGroup.map_range_le_of_simplyConnectedSpace f a₀
    (_root_.FundamentalGroup.mapOfEq p he).range

end TauCeti
