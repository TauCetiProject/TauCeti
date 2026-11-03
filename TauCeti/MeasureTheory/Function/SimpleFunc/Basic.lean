/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
# Decomposing a simple function along its fibres

This file also records how products and stars act on simple functions that are constant on a
measurable set and zero off it.

A simple function `u : SimpleFunc α β` is the finite sum, over the values `c` in its range, of the
constant `c` restricted to the fibre `u ⁻¹' {c}`. More generally, for any `ψ : β → M` into an
additive commutative monoid, `u.map ψ` is the sum of the constants `ψ c` restricted to the same
fibres. This is the form in which an operator defined on simple functions is evaluated by
linearity, as in the Riesz–Thorin theorem.

A finite family of simple functions is one simple function into the product,
`MeasureTheory.SimpleFunc.pi`.
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
  exact congrFun
    (map_sum (⟨⟨_, FunLike.coe_zero⟩, FunLike.coe_add⟩ : SimpleFunc α M →+ α → M) _ _).symm x

/-- A simple function is the sum, over its range, of its values `c` restricted to the fibres
`u ⁻¹' {c}`. -/
theorem eq_sum_restrict_const [AddCommMonoid β] (u : SimpleFunc α β) :
    u = ∑ c ∈ u.range, (const α c).restrict (u ⁻¹' {c}) := by
  exact map_eq_sum_restrict_const u id

/-- The product of two simple functions constant on measurable sets `A` and `B` and zero
elsewhere is constant on `A ∩ B` and zero elsewhere. -/
theorem piecewise_const_mul_piecewise_const [MulZeroClass β] (c d : β) {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    piecewise A hA (const α c) (const α 0) * piecewise B hB (const α d) (const α 0) =
      piecewise (A ∩ B) (hA.inter hB) (const α (c * d)) (const α 0) := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [piecewise_apply, hxA, hxB]

/-- The star of a simple function constant on a measurable set `A` and zero elsewhere is
constant with the starred value on `A` and zero elsewhere. -/
theorem star_piecewise_const [AddMonoid β] [StarAddMonoid β] (c : β) {A : Set α}
    (hA : MeasurableSet A) :
    star (piecewise A hA (const α c) (const α 0)) =
      piecewise A hA (const α (star c)) (const α 0) := by
  ext x
  by_cases hxA : x ∈ A <;> simp [piecewise_apply, hxA]

/-- A finite family of simple functions `f i : α →ₛ β i`, as one simple function into the
product `∀ i, β i`. Its fibres are the intersections of the fibres of the `f i`. -/
def pi {ι : Type*} [Finite ι] {β : ι → Type*} (f : ∀ i, SimpleFunc α (β i)) :
    SimpleFunc α (∀ i, β i) where
  toFun a i := f i a
  measurableSet_fiber' w := by
    have h : (fun a i ↦ f i a) ⁻¹' {w} = ⋂ i, f i ⁻¹' {w i} := by
      ext a
      simp [funext_iff]
    rw [h]
    exact MeasurableSet.iInter fun i ↦ (f i).measurableSet_fiber _
  finite_range' := (Set.Finite.pi fun i ↦ (f i).finite_range).subset <| by
    rintro _ ⟨a, rfl⟩
    simp

/-- The simple function `pi f` is the function `a ↦ (i ↦ f i a)`. -/
@[simp]
theorem coe_pi {ι : Type*} [Finite ι] {β : ι → Type*} (f : ∀ i, SimpleFunc α (β i)) :
    ⇑(pi f) = fun a i ↦ f i a :=
  (rfl)

/-- The value of `pi f` at `a` is the family of the values `f i a`. -/
theorem pi_apply {ι : Type*} [Finite ι] {β : ι → Type*} (f : ∀ i, SimpleFunc α (β i)) (a : α) :
    pi f a = fun i ↦ f i a :=
  (rfl)

end MeasureTheory.SimpleFunc
