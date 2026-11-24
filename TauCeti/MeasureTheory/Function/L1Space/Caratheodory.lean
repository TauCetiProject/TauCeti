/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory

/-!
# Integrability of Carathéodory compositions

Let `F : α → X → G` be a family of maps such that `F t` is Lipschitz with constant `L t` for
`μ`-almost every `t`, where `L : α → ℝ≥0` is integrable. On an interval, `F : ℝ → E → G` is a
time-dependent map on `[a, b]`.

## Main results

* `TauCeti.integrable_apply_of_integrable_apply`: if every section `t ↦ F t x` is almost
  everywhere strongly measurable, integrability of one section `t ↦ F t x₀` gives integrability
  of every section.
* `TauCeti.integrableOn_apply_of_lipschitzWith`: if every section is integrable on `[a, b]`, then
  along every curve `x` continuous on `[a, b]` the composite `s ↦ F s (x s)` is integrable on
  `[a, b]`; its measurability is Tau Ceti's
  `MeasureTheory.AEStronglyMeasurable.apply_of_forall_of_continuousAt`.
* `TauCeti.intervalIntegrable_apply_of_lipschitzWith`: the same composite is interval integrable
  on `a..b` when `a ≤ b`.

These are the integrability hypotheses of the nonlinear Carathéodory theorem
`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti

/-- **Integrability of the sections.** If `t ↦ F t x` is almost everywhere strongly measurable
for every `x`, one section `t ↦ F t x₀` is integrable, and `F t` is Lipschitz with an integrable
constant `L t` for almost every `t`, then every section is integrable. -/
theorem integrable_apply_of_integrable_apply {α X G : Type*} [MeasurableSpace α] {μ : Measure α}
    [PseudoMetricSpace X] [NormedAddCommGroup G] {F : α → X → G} {L : α → ℝ≥0} {x₀ : X}
    (hF : ∀ x, AEStronglyMeasurable (fun t ↦ F t x) μ) (hF₀ : Integrable (fun t ↦ F t x₀) μ)
    (hL : Integrable (fun t ↦ (L t : ℝ)) μ) (hLip : ∀ᵐ t ∂μ, LipschitzWith (L t) (F t)) (x : X) :
    Integrable (fun t ↦ F t x) μ := by
  refine Integrable.mono' (hF₀.norm.add (hL.mul_const (dist x x₀))) (hF x) ?_
  filter_upwards [hLip] with t ht
  exact norm_le_norm_add_const_of_dist_le (ht.dist_le_mul x x₀)

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G] {F : ℝ → E → G}
  {L : ℝ → ℝ≥0} {a b : ℝ}

/-- **Integrability along a curve.** If every section `t ↦ F t x` is integrable on `[a, b]` and
`F t` is Lipschitz with an integrable constant `L t` for almost every `t ∈ [a, b]`, then
`s ↦ F s (x s)` is integrable on `[a, b]` for every curve `x` continuous on `[a, b]`. -/
theorem integrableOn_apply_of_lipschitzWith (hF : ∀ x, IntegrableOn (fun t ↦ F t x) (Icc a b))
    (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc a b))
    (hLip : ∀ᵐ t ∂volume.restrict (Icc a b), LipschitzWith (L t) (F t)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b)) :
    IntegrableOn (fun s ↦ F s (x s)) (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  have hmeas : AEStronglyMeasurable (fun s ↦ F s (x s)) (volume.restrict (Icc a b)) :=
    (hx.aestronglyMeasurable measurableSet_Icc).apply_of_forall_of_continuousAt
      (fun y ↦ (hF y).aestronglyMeasurable) (hLip.mono fun _ ht ↦ ht.continuous.continuousAt)
  refine Integrable.mono' ((hF 0).norm.add (hL.mul_const C)) hmeas ?_
  filter_upwards [hLip, ae_restrict_mem measurableSet_Icc] with s hs hsI
  refine (norm_le_norm_add_const_of_dist_le (hs.dist_le_mul (x s) 0)).trans
    (add_le_add_right ?_ _)
  rw [dist_zero_right]
  exact mul_le_mul_of_nonneg_left (hC s hsI) (L s).coe_nonneg

/-- **Interval integrability along a curve.** Under the hypotheses of
`TauCeti.integrableOn_apply_of_lipschitzWith`, with `a ≤ b`, the composite `s ↦ F s (x s)` is
interval integrable on `a..b` for every curve `x` continuous on `[a, b]`. -/
theorem intervalIntegrable_apply_of_lipschitzWith (hab : a ≤ b)
    (hF : ∀ x, IntegrableOn (fun t ↦ F t x) (Icc a b))
    (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc a b))
    (hLip : ∀ᵐ t ∂volume.restrict (Icc a b), LipschitzWith (L t) (F t)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b)) :
    IntervalIntegrable (fun s ↦ F s (x s)) volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    (integrableOn_apply_of_lipschitzWith hF hL hLip hx)

end TauCeti
