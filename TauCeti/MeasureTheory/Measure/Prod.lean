/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Marginal masses and sections of product measures

For a measure `π` on `α × β` with measurable singletons, the mass that the first marginal
`π.map Prod.fst` gives to a point `x` is the sum of the masses of the points `(x, y)` of the row
over `x`, when `β` is finite, and symmetrically for the second marginal. Mathlib records this for
the extended masses (`MeasureTheory.measure_preimage_fst_singleton_eq_sum`); this file states it
for the real masses `Measure.real`. A set of zero first-marginal mass carries no mass in any
rectangle over it (`MeasureTheory.Measure.measure_prod_eq_zero_of_fst_eq_zero`). Weighting by a
function of the first coordinate commutes with taking the first marginal (`fst_withDensity`).

It also records that almost every section of an almost-everywhere measurable function on a
product `μ.prod ν` is almost-everywhere measurable (`AEMeasurable.prodMk_left`), the counterpart of
Mathlib's `MeasureTheory.AEStronglyMeasurable.prodMk_left`.

Finally, for a measurable map `f` into an additive group, the law of `f z.1 - f z.2` under
`μ.prod μ` is symmetric (`MeasureTheory.Measure.map_neg_map_sub_prod_self`): swapping the two
identical factors negates the difference.

For real-valued coordinates, if one factor has a reflection-invariant law, reflecting the other
coordinate according to the sign of the first preserves the product measure
(`MeasureTheory.Measure.measurePreserving_prod_skew_neg`), and the quotient `z.1 / z.2` has the
same law as `z.1 / |z.2|` when the numerator's law is reflection invariant
(`MeasureTheory.Measure.map_div_prod_eq_map_div_abs`).
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

/-- Weighting a joint measure by a function of its first coordinate weights its first marginal
by the same function. No finiteness assumption is needed. -/
@[simp]
theorem fst_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ρ.withDensity (fun p ↦ f p.1)).fst = ρ.fst.withDensity f := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [Measure.fst, lintegral_map hg measurable_fst,
    lintegral_withDensity_eq_lintegral_mul ρ (f := fun p ↦ f p.1)
      (by fun_prop) (by fun_prop), lintegral_withDensity_eq_lintegral_mul _ hf hg,
    Measure.fst, lintegral_map (hf.mul hg) measurable_fst]
  simp only [Pi.mul_apply]

/-- An integrable nonnegative weight on the first marginal makes the weighted joint measure
finite. -/
theorem isFiniteMeasure_withDensity_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hint : ∫⁻ x, f x ∂ρ.fst < ∞) :
    IsFiniteMeasure (ρ.withDensity (fun p ↦ f p.1)) := by
  apply isFiniteMeasure_withDensity
  rw [Measure.fst, lintegral_map hf measurable_fst] at hint
  exact hint.ne

/-- A set of zero first-marginal mass carries no mass in any rectangle over it: if
`σ.fst t = 0`, then `σ (t ×ˢ s) = 0` for every `s`. Neither set needs to be measurable. -/
theorem measure_prod_eq_zero_of_fst_eq_zero {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (σ : Measure (α × β)) {t : Set α} (ht : σ.fst t = 0) (s : Set β) :
    σ (t ×ˢ s) = 0 :=
  measure_mono_null (Set.prod_subset_preimage_fst t s)
    (preimage_null_of_map_null measurable_fst.aemeasurable ht)

variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] {π : Measure (α × β)}

/-- The real mass of a point under the first marginal of a measure on `α × β`, with `β` finite, is
the sum of the real masses of the points of its row. -/
theorem map_fst_real_singleton [Fintype β] (x : α)
    (h : ∀ y, π {(x, y)} ≠ ∞ := by finiteness) :
    (π.map Prod.fst).real {x} = ∑ y, π.real {(x, y)} := by
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton x), measureReal_def,
    measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum fun y _ ↦ h y]
  rfl

/-- The real mass of a point under the second marginal of a measure on `α × β`, with `α` finite,
is the sum of the real masses of the points of its column. -/
theorem map_snd_real_singleton [Fintype α] (y : β)
    (h : ∀ x, π {(x, y)} ≠ ∞ := by finiteness) :
    (π.map Prod.snd).real {y} = ∑ x, π.real {(x, y)} := by
  rw [map_measureReal_apply measurable_snd (measurableSet_singleton y), measureReal_def,
    measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum fun x _ ↦ h x]
  rfl

/-- The law of the difference `f z.1 - f z.2` of two coordinates of a product measure `μ.prod μ`
is symmetric: swapping the two identical factors negates the difference. -/
theorem map_neg_map_sub_prod_self {γ G : Type*} [MeasurableSpace γ] [MeasurableSpace G]
    [AddGroup G] [MeasurableNeg G] [MeasurableSub₂ G] (μ : Measure γ) [SFinite μ] {f : γ → G}
    (hf : Measurable f) :
    ((μ.prod μ).map fun z => f z.1 - f z.2).map Neg.neg =
      (μ.prod μ).map fun z => f z.1 - f z.2 := by
  rw [map_map measurable_neg (by fun_prop)]
  conv_lhs => rw [← prod_swap]
  rw [map_map (measurable_neg.comp (by fun_prop)) measurable_swap]
  congr 1
  funext z
  simp

/-- Reflecting the second coordinate according to the sign of the first preserves the product of
a measure with a reflection-invariant measure, because every fibre transformation preserves the
second measure. -/
theorem measurePreserving_prod_skew_neg {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (hν : ν.map (fun x : ℝ ↦ -x) = ν) :
    MeasurePreserving (fun z : ℝ × ℝ ↦ (z.1, if z.1 < 0 then -z.2 else z.2))
      (μ.prod ν) (μ.prod ν) := by
  refine (MeasurePreserving.id μ).skew_product
    (g := fun y x : ℝ ↦ if y < 0 then -x else x) ?_ ?_
  · exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
      measurable_snd.neg measurable_snd
  · refine ae_of_all _ fun y ↦ ?_
    by_cases hy : y < 0
    · simpa only [hy, ↓reduceIte] using hν
    · simpa only [hy, ↓reduceIte] using (Measure.map_id' (μ := ν))

/-- The quotient of independent coordinates, the numerator having a reflection-invariant law, has
the same law as the quotient by the absolute value of the denominator. -/
theorem map_div_prod_eq_map_div_abs {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (hμ : μ.map (fun x : ℝ ↦ -x) = μ) :
    ((μ.prod ν).map fun z : ℝ × ℝ ↦ z.1 / z.2) =
      (μ.prod ν).map fun z : ℝ × ℝ ↦ z.1 / |z.2| := by
  let skew : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1, if z.1 < 0 then -z.2 else z.2)
  let twist : ℝ × ℝ → ℝ × ℝ := fun z ↦ (if z.2 < 0 then -z.1 else z.1, z.2)
  have hskew : MeasurePreserving skew (ν.prod μ) (ν.prod μ) :=
    measurePreserving_prod_skew_neg hμ
  -- Conjugating the skew map by coordinate swaps reflects the numerator exactly when the
  -- denominator is negative.
  have htwist : MeasurePreserving twist (μ.prod ν) (μ.prod ν) := by
    have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) (μ.prod ν) (ν.prod μ) :=
      Measure.measurePreserving_swap
    have hswap' : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) (ν.prod μ) (μ.prod ν) :=
      Measure.measurePreserving_swap
    have htwist_eq : twist = (Prod.swap : ℝ × ℝ → ℝ × ℝ) ∘ skew ∘ Prod.swap := by
      funext z
      rfl
    rw [htwist_eq]
    exact hswap'.comp (hskew.comp hswap)
  calc
    (μ.prod ν).map (fun z : ℝ × ℝ ↦ z.1 / z.2)
        = ((μ.prod ν).map twist).map (fun z : ℝ × ℝ ↦ z.1 / z.2) := by rw [htwist.map_eq]
    _ = (μ.prod ν).map ((fun z : ℝ × ℝ ↦ z.1 / z.2) ∘ twist) := by
      rw [Measure.map_map (by fun_prop) htwist.measurable]
    _ = (μ.prod ν).map fun z : ℝ × ℝ ↦ z.1 / |z.2| := by
      apply Measure.map_congr
      refine ae_of_all _ fun z ↦ ?_
      by_cases hz : z.2 < 0
      · simp only [twist, hz, ↓reduceIte, Function.comp_apply, abs_of_neg hz]
        ring
      · simp only [twist, hz, ↓reduceIte, Function.comp_apply,
          abs_of_nonneg (le_of_not_gt hz)]

end MeasureTheory.Measure

/-- Almost every section of an almost-everywhere measurable function on `μ.prod ν` is
almost-everywhere measurable. This is the counterpart for `AEMeasurable` of
`MeasureTheory.AEStronglyMeasurable.prodMk_left`. -/
theorem AEMeasurable.prodMk_left {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite ν] {f : α × β → γ} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEMeasurable (fun y ↦ f (x, y)) ν := by
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨_, hf.measurable_mk.comp measurable_prodMk_left, hx⟩
