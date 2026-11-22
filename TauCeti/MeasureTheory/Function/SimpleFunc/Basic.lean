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
(`MeasureTheory.SimpleFunc.memLp_restrict_const_fiber`), for `u` with values in any extended
seminormed additive monoid.

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
fibre `u ⁻¹' {c}` lies in every `L^q`: by Markov's inequality, either `‖c‖ₑ = 0`, or the fibre
is null, or `‖c‖ₑ < ∞` and the fibre has finite measure. -/
theorem memLp_restrict_const_fiber {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {μ : Measure α} {u : SimpleFunc α ε} {p : ℝ≥0∞} (hu : MemLp u p μ) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (q : ℝ≥0∞) (c : ε) : MemLp ((const α c).restrict (u ⁻¹' {c})) q μ := by
  have hs := (u.measurableSet_fiber c).nullMeasurableSet (μ := μ)
  rw [coe_restrict _ (u.measurableSet_fiber c), coe_const]
  have hp' : 0 < 1 / p.toReal := one_div_pos.2 (ENNReal.toReal_pos hp0 hp)
  -- Markov's inequality: on the fibre `u` is `c`, so `‖c‖ₑ * μ (u ⁻¹' {c}) ^ (1 / p)` is bounded
  -- by the `p`-seminorm of `u`.
  have hfin : ‖c‖ₑ * μ (u ⁻¹' {c}) ^ (1 / p.toReal) < ∞ := by
    have hind : (u ⁻¹' {c}).indicator (fun _ ↦ c) = (u ⁻¹' {c}).indicator u :=
      Set.indicator_congr fun _ hx ↦ (Set.mem_singleton_iff.1 hx).symm
    rw [← eLpNorm_indicator_const hs hp0 hp, hind]
    exact (eLpNorm_indicator_le _ hs).trans_lt hu.eLpNorm_lt_top
  rw [ENNReal.mul_lt_top_iff, ENNReal.rpow_lt_top_iff_of_pos hp',
    ENNReal.rpow_eq_zero_iff_of_pos hp'] at hfin
  rw [MeasureTheory.memLp_iff]
  rcases hfin with ⟨hc, hμ⟩ | hc | hμ
  · exact (eLpNorm_indicator_const_le c q hs).trans_lt
      (ENNReal.mul_lt_top hc (ENNReal.rpow_lt_top_of_nonneg (by positivity) hμ.ne))
  · exact (eLpNorm_indicator_const_le c q hs).trans_lt (by simp [hc])
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, Measure.restrict_eq_zero.2 hμ,
      eLpNorm_measure_zero]
    exact ENNReal.zero_lt_top

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
