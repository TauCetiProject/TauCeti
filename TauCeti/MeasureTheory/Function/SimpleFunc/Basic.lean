/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Decomposing a simple function along its fibres

A simple function `u : SimpleFunc α β` is the finite sum, over the values `c` in its range, of the
constant `c` restricted to the fibre `u ⁻¹' {c}`. More generally, for any `ψ : β → M` into an
additive commutative monoid, `u.map ψ` is the sum of the constants `ψ c` restricted to the same
fibres. This is the form in which an operator defined on simple functions is evaluated by
linearity, as in the Riesz–Thorin theorem. Weighting the fibre pieces by coefficients `a c`
gives `x ↦ a (u x) • u x` (`MeasureTheory.SimpleFunc.sum_smul_restrict_const_apply`).

If `u` lies in `Lᵖ` for some `0 < p < ∞`, each of these restricted constants lies in every `L^q`
(`MeasureTheory.SimpleFunc.memLp_restrict_const_fiber`).

The file also records how products and stars act on simple functions defined piecewise on a
measurable set (`MeasureTheory.SimpleFunc.piecewise_const_zero_mul_piecewise_const_zero`,
`MeasureTheory.SimpleFunc.star_piecewise`).

A finite family of simple functions is one simple function into the product,
`MeasureTheory.SimpleFunc.pi`.
-/

public section

open scoped ENNReal

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
  rw [map_apply_eq_sum_restrict_const, sum_apply]

/-- A simple function is the sum, over its range, of its values `c` restricted to the fibres
`u ⁻¹' {c}`. -/
theorem eq_sum_restrict_const [AddCommMonoid β] (u : SimpleFunc α β) :
    u = ∑ c ∈ u.range, (const α c).restrict (u ⁻¹' {c}) :=
  -- `u.map id` is `u` by definition of `SimpleFunc.map`.
  map_eq_sum_restrict_const u id

/-- If a simple function `u` lies in `Lᵖ` for some `0 < p < ∞`, the constant `c` restricted to the
fibre `u ⁻¹' {c}` lies in every `L^q`: the fibres over nonzero values have finite measure. -/
theorem memLp_restrict_const_fiber {E : Type*} [NormedAddCommGroup E] {μ : Measure α}
    {u : SimpleFunc α E} {p : ℝ≥0∞} (hu : MemLp u p μ) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (q : ℝ≥0∞) (c : E) : MemLp ((const α c).restrict (u ⁻¹' {c})) q μ := by
  rw [coe_restrict _ (u.measurableSet_fiber c), coe_const]
  refine memLp_indicator_const q (u.measurableSet_fiber c).nullMeasurableSet c ?_
  exact (eq_or_ne c 0).imp_right fun hc ↦ (u.measure_preimage_lt_top_of_memLp hp0 hp hu c hc).ne

/-- Weighting each fibre piece of `u` by a coefficient depending on its value gives, at `x`, the
value `u x` weighted by the coefficient of `u x`. -/
theorem sum_smul_restrict_const_apply {R : Type*} [AddCommMonoid β] [SMulZeroClass R β]
    (u : SimpleFunc α β) (a : β → R) (x : α) :
    ∑ c ∈ u.range, a c • (const α c).restrict (u ⁻¹' {c}) x = a (u x) • u x := by
  rw [← map_apply (fun c => a c • c) u x, map_apply_eq_sum_restrict_const]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [restrict_apply _ (u.measurableSet_fiber c), coe_const]
  by_cases hx : x ∈ u ⁻¹' {c} <;> simp [hx]

/-- The product of a simple function `f` on a measurable set `A`, extended by zero, and a simple
function `g` on a measurable set `B`, extended by zero, is `f * g` on `A ∩ B`, extended by zero. -/
theorem piecewise_const_zero_mul_piecewise_const_zero [MulZeroClass β] (f g : SimpleFunc α β)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    piecewise A hA f (const α 0) * piecewise B hB g (const α 0) =
      piecewise (A ∩ B) (hA.inter hB) (f * g) (const α 0) := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [piecewise_apply, hxA, hxB]

/-- The star of a constant simple function is the constant star. -/
@[simp]
theorem star_const [Star β] (b : β) : star (const α b) = const α (star b) :=
  (rfl)

/-- The star of a simple function defined piecewise on a measurable set `A` is defined piecewise
on `A` by the stars of the two pieces. -/
theorem star_piecewise [Star β] (f g : SimpleFunc α β) {A : Set α} (hA : MeasurableSet A) :
    star (piecewise A hA f g) = piecewise A hA (star f) (star g) := by
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
