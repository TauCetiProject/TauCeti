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

If `u` lies in `Lᵖ` for some `0 < p < ∞`, then for each `c` the constant `c` restricted to
`u ⁻¹' {c}` lies in every `L^q` (`MeasureTheory.SimpleFunc.memLp_restrict_const_fiber`), for `u`
with values in any topological space with a zero of extended norm `0`.

The file also records that restricting a simple function to a measurable set agrees with
`SimpleFunc.piecewise` (`MeasureTheory.SimpleFunc.restrict_eq_piecewise`), how products act on
simple functions supported on a measurable set (extended by zero outside it,
`MeasureTheory.SimpleFunc.piecewise_zero_mul_piecewise_zero`), how stars act on
simple functions defined piecewise on a measurable set (`MeasureTheory.SimpleFunc.star_piecewise`),
and how products and stars act on constant simple functions
(`MeasureTheory.SimpleFunc.const_mul_const`, `MeasureTheory.SimpleFunc.star_const`).

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
fibre `u ⁻¹' {c}` lies in every `L^q`. The codomain only needs a zero of extended norm `0`. -/
theorem memLp_restrict_const_fiber {ε : Type*} [TopologicalSpace ε] [Zero ε] [ENorm ε]
    (h0 : ‖(0 : ε)‖ₑ = 0) {μ : Measure α} {u : SimpleFunc α ε} {p : ℝ≥0∞} (hu : MemLp u p μ)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (q : ℝ≥0∞) (c : ε) :
    MemLp ((const α c).restrict (u ⁻¹' {c})) q μ := by
  have hsm := u.measurableSet_fiber c
  have hs := hsm.nullMeasurableSet (μ := μ)
  -- The fibre piece has the extended norm of the `ℝ≥0∞`-valued indicator of `‖c‖ₑ` on the fibre,
  -- so both have the same `eLpNorm` for every exponent `r`.
  have heLp (r : ℝ≥0∞) : eLpNorm ((const α c).restrict (u ⁻¹' {c})) r μ =
      eLpNorm ((u ⁻¹' {c}).indicator fun _ ↦ ‖c‖ₑ) r μ := by
    refine eLpNorm_congr_eNorm_ae (SimpleFunc.aestronglyMeasurable _)
      (aestronglyMeasurable_const.indicator hsm) (.of_forall fun x ↦ ?_)
    by_cases hx : u x = c <;> simp [restrict_apply _ hsm, hx, h0]
  -- Markov's inequality: on the fibre `u` is `c`, so `‖c‖ₑ * μ (u ⁻¹' {c}) ^ (1 / p)` is bounded
  -- by the `p`-seminorm of `u`.
  have hfin : ‖c‖ₑ * μ (u ⁻¹' {c}) ^ (1 / p.toReal) < ∞ := by
    have hle : eLpNorm ((const α c).restrict (u ⁻¹' {c})) p μ ≤ eLpNorm u p μ := by
      refine eLpNorm_mono_eNorm (SimpleFunc.aestronglyMeasurable _) fun x ↦ ?_
      by_cases hx : u x = c <;> simp [restrict_apply _ hsm, hx, h0]
    have h := hle.trans_lt hu.eLpNorm_lt_top
    rwa [heLp p, eLpNorm_indicator_const hs hp0 hp, eNorm_eq_self] at h
  have hp' : 0 < 1 / p.toReal := one_div_pos.2 (ENNReal.toReal_pos hp0 hp)
  rw [ENNReal.mul_lt_top_iff, ENNReal.rpow_lt_top_iff_of_pos hp',
    ENNReal.rpow_eq_zero_iff_of_pos hp'] at hfin
  rw [MeasureTheory.memLp_iff, heLp q]
  rcases hfin with ⟨hc, hμ⟩ | hc | hμ
  · exact (eLpNorm_indicator_const_le _ q hs).trans_lt
      (ENNReal.mul_lt_top (by simpa using hc)
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hμ.ne))
  · exact (eLpNorm_indicator_const_le _ q hs).trans_lt (by simp [hc])
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

/-- Restricting a simple function `f` to a measurable set `s` agrees with the piecewise function
equal to `f` on `s` and `0` outside `s`. -/
theorem restrict_eq_piecewise [Zero β] (f : SimpleFunc α β) {s : Set α}
    (hs : MeasurableSet s) : f.restrict s = piecewise s hs f 0 := by
  rw [restrict, dite_eq_left hs]

/-- The product of a simple function `f` on a measurable set `A`, extended by zero, and a simple
function `g` on a measurable set `B`, extended by zero, is `f * g` on `A ∩ B`, extended by zero. -/
theorem piecewise_zero_mul_piecewise_zero [MulZeroClass β] (f g : SimpleFunc α β)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    piecewise A hA f 0 * piecewise B hB g 0 =
      piecewise (A ∩ B) (hA.inter hB) (f * g) 0 := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [piecewise_apply, hxA, hxB]

/-- The product of two constant simple functions is the constant product. -/
@[to_additive (attr := simp) /-- The sum of two constant simple functions is the constant
sum. -/]
theorem const_mul_const [Mul β] (a b : β) : const α a * const α b = const α (a * b) :=
  (rfl)

/-- The star of a constant simple function is the constant star. -/
@[simp]
theorem star_const [Star β] (b : β) : star (const α b) = const α (star b) :=
  (rfl)

/-- The star of a simple function defined piecewise on a measurable set `A` is defined piecewise
on `A` by the stars of the two pieces. -/
@[simp]
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
