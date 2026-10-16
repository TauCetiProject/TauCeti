/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
# Decomposing a simple function along its fibres

A simple function `u : SimpleFunc α β` is the finite sum, over the values `c` in its range, of the
constant `c` restricted to the fibre `u ⁻¹' {c}`. More generally, for any `ψ : β → M` into an
additive commutative monoid, `u.map ψ` is the sum of the constants `ψ c` restricted to the same
fibres. This is the form in which an operator defined on simple functions is evaluated by
linearity, as in the Riesz–Thorin theorem.
-/

public section

namespace MeasureTheory.SimpleFunc

variable {α β M : Type*} [MeasurableSpace α] [AddCommMonoid M]

/-- The value of `u.map ψ` at `x` is the sum, over the range of `u`, of the constants `ψ c`
restricted to the fibres `u ⁻¹' {c}` and evaluated at `x`. -/
theorem map_apply_eq_sum_restrict_const (u : SimpleFunc α β) (ψ : β → M) (x : α) :
    u.map ψ x = ∑ c ∈ u.range, (const α (ψ c)).restrict (u ⁻¹' {c}) x := by
  rw [Finset.sum_eq_single (u x)]
  · simp [restrict_apply _ (u.measurableSet_fiber _)]
  · intro c _ hc
    simp [restrict_apply _ (u.measurableSet_fiber c), Ne.symm hc]
  · exact fun h => absurd (u.mem_range_self x) h

/-- A simple function mapped by `ψ` is the sum, over its range, of the constants `ψ c`
restricted to the fibres `u ⁻¹' {c}`. -/
theorem map_eq_sum_restrict_const (u : SimpleFunc α β) (ψ : β → M) :
    u.map ψ = ∑ c ∈ u.range, (const α (ψ c)).restrict (u ⁻¹' {c}) := by
  ext x
  rw [map_apply_eq_sum_restrict_const, ← Finset.sum_apply]
  exact congrFun (map_sum (⟨⟨_, coe_zero⟩, coe_add⟩ : SimpleFunc α M →+ α → M) _ _).symm x

/-- A simple function is the sum, over its range, of its values `c` restricted to the fibres
`u ⁻¹' {c}`. -/
theorem eq_sum_restrict_const [AddCommMonoid β] (u : SimpleFunc α β) :
    u = ∑ c ∈ u.range, (const α c).restrict (u ⁻¹' {c}) := by
  exact map_eq_sum_restrict_const u id

end MeasureTheory.SimpleFunc
