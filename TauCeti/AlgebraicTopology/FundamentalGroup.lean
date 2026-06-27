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

* `TauCeti.FundamentalGroup.map_range_eq_bot_of_simplyConnected`: maps out of a simply
  connected space have trivial fundamental-group range.
* `TauCeti.FundamentalGroup.map_range_le_mapOfEq_range_of_simplyConnected`: a simply connected
  domain satisfies the fundamental-group range condition against any `mapOfEq` range.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {A : Type*} [TopologicalSpace A]

/-- A map out of a space whose fundamental group at the chosen basepoint is trivial has
trivial range on fundamental groups. -/
@[simp]
private theorem FundamentalGroup.map_range_eq_bot_of_subsingleton
    (f : C(A, X)) (a₀ : A) [Subsingleton (_root_.FundamentalGroup A a₀)] :
    (_root_.FundamentalGroup.map f a₀).range = ⊥ := by
  apply le_antisymm
  · rintro _ ⟨γ, rfl⟩
    rw [Subgroup.mem_bot]
    rw [Subsingleton.elim γ 1]
    exact map_one (_root_.FundamentalGroup.map f a₀)
  · exact bot_le

/-- A map out of a simply connected space has trivial range on fundamental groups. -/
@[simp]
theorem FundamentalGroup.map_range_eq_bot_of_simplyConnected [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) :
    (_root_.FundamentalGroup.map f a₀).range = ⊥ :=
  FundamentalGroup.map_range_eq_bot_of_subsingleton f a₀

/-- A domain whose fundamental group at the chosen basepoint is trivial satisfies the
fundamental-group range condition against any basepoint-adjusted map range. -/
private theorem FundamentalGroup.map_range_le_mapOfEq_range_of_subsingleton
    (p : C(E, X)) (f : C(A, X)) (a₀ : A)
    [Subsingleton (_root_.FundamentalGroup A a₀)] (e₀ : E) (he : p e₀ = f a₀) :
    (_root_.FundamentalGroup.map f a₀).range ≤
      (_root_.FundamentalGroup.mapOfEq p he).range := by
  rw [FundamentalGroup.map_range_eq_bot_of_subsingleton f a₀]
  exact bot_le

/-- A simply connected domain satisfies the fundamental-group range condition against any
basepoint-adjusted map range. -/
theorem FundamentalGroup.map_range_le_mapOfEq_range_of_simplyConnected [SimplyConnectedSpace A]
    (p : C(E, X)) (f : C(A, X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀) :
    (_root_.FundamentalGroup.map f a₀).range ≤
      (_root_.FundamentalGroup.mapOfEq p he).range :=
  FundamentalGroup.map_range_le_mapOfEq_range_of_subsingleton p f a₀ e₀ he

end TauCeti
