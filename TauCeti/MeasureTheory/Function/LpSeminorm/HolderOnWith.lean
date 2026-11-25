/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder functions on a bounded set are in every `Lᵖ`

Let `G` be `α`-Hölder with constant `K` on a ball `B(x₀, ρ)` of a proper metric space, with
`α > 0`, and let `μ` be finite on compact sets. Then `G` is continuous on the ball and stays within
`K ρ^α` of its value at the centre, so `G - G x₀` is a bounded measurable function on a set of
finite measure. More generally, `G` is bounded on any bounded set on which it is Hölder.

## Main declarations

* `TauCeti.MeasureTheory.memLp_sub_of_holderOnWith`: `G - G x₀` lies in every `Lᵖ(B)`, for every
  measurable `B ⊆ B(x₀, ρ)`.
* `TauCeti.MeasureTheory.memLp_of_holderOnWith`: if `G` is Hölder on a bounded set `S`, then `G`
  lies in every `Lᵖ(B)`, for every measurable `B ⊆ S`.
* `TauCeti.MeasureTheory.setIntegral_ball_norm_sub_sq_le_of_holderOnWith`:
  `∫_{B(x₀, ρ)} ‖G x₀ - G‖² ≤ μ(B(x₀, ρ)) (K ρ^α)²`.
-/

public section

open Metric Set
open scoped ENNReal NNReal

namespace TauCeti

namespace MeasureTheory

open _root_.MeasureTheory

variable {X E : Type*} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup E]

/-- On a measurable set `B` inside a ball `B(x₀, ρ)` on which `G` is `α`-Hölder with constant
`K`, with `α > 0`, `G - G x₀` is bounded by `K ρ^α`, so it lies in every `Lᵖ(B)`. -/
theorem memLp_sub_of_holderOnWith {B : Set X} (hB : MeasurableSet B) {x₀ : X} {ρ : ℝ}
    (hBρ : B ⊆ ball x₀ ρ) {α K : ℝ≥0} (hα : 0 < α) {G : X → E}
    (hGK : HolderOnWith K α G (ball x₀ ρ)) {p : ℝ≥0∞} :
    MemLp (fun x => G x - G x₀) p (μ.restrict B) := by
  have : IsFiniteMeasure (μ.restrict B) :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hBρ))
  refine MemLp.of_bound ((((hGK.continuousOn hα).mono hBρ).aestronglyMeasurable hB).sub
    aestronglyMeasurable_const) (K * ρ ^ (α : ℝ)) ((ae_restrict_iff' hB).2 (ae_of_all _ ?_))
  intro x hx
  rw [← dist_eq_norm]
  exact hGK.dist_le_mul_rpow_of_mem_ball (hBρ hx)

/-- On a measurable set `B` inside a bounded set `S` on which `G` is `α`-Hölder, with `α > 0`,
`G` is bounded, so it lies in every `Lᵖ(B)`. -/
theorem memLp_of_holderOnWith {B S : Set X} (hB : MeasurableSet B) (hBS : B ⊆ S)
    (hS : Bornology.IsBounded S) {α K : ℝ≥0} (hα : 0 < α) {G : X → E}
    (hGK : HolderOnWith K α G S) {p : ℝ≥0∞} : MemLp G p (μ.restrict B) := by
  have : IsFiniteMeasure (μ.restrict B) :=
    isFiniteMeasure_restrict.2 (hS.subset hBS).measure_lt_top.ne
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hGK.isBounded_image hS)
  exact MemLp.of_bound (((hGK.continuousOn hα).mono hBS).aestronglyMeasurable hB) M
    ((ae_restrict_iff' hB).2 (ae_of_all _ fun x hx => hM _ (mem_image_of_mem _ (hBS hx))))

/-- A function `G` that is `α`-Hölder with constant `K` on `B(x₀, ρ)`, with `α > 0`, stays within
`K ρ^α` of `G x₀`, so `∫_{B(x₀, ρ)} ‖G x₀ - G‖² ≤ μ(B(x₀, ρ)) (K ρ^α)²`. -/
theorem setIntegral_ball_norm_sub_sq_le_of_holderOnWith {x₀ : X} {ρ : ℝ} {α K : ℝ≥0}
    (hα : 0 < α) {G : X → E} (hGK : HolderOnWith K α G (ball x₀ ρ)) :
    ∫ x in ball x₀ ρ, ‖G x₀ - G x‖ ^ 2 ∂μ ≤ μ.real (ball x₀ ρ) * (K * ρ ^ (α : ℝ)) ^ 2 := by
  have hGc : MemLp (fun x => G x - G x₀) 2 (μ.restrict (ball x₀ ρ)) :=
    memLp_sub_of_holderOnWith measurableSet_ball subset_rfl hα hGK
  have hGi : IntegrableOn (fun x => ‖G x - G x₀‖ ^ 2) (ball x₀ ρ) μ :=
    hGc.norm.integrable_sq
  calc _ ≤ ∫ _ in ball x₀ ρ, (K * ρ ^ (α : ℝ)) ^ 2 ∂μ :=
        setIntegral_mono_on (by simpa only [norm_sub_rev] using hGi)
          (integrableOn_const measure_ball_lt_top.ne) measurableSet_ball fun x hx => by
            rw [norm_sub_rev, ← dist_eq_norm]
            exact pow_le_pow_left₀ dist_nonneg (hGK.dist_le_mul_rpow_of_mem_ball hx) 2
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

end MeasureTheory

end TauCeti
