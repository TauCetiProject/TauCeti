/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.Topology.Algebra.Order.Field

/-!
# The deviation of an `Lᵖ` function from a constant

On a finite measure space the `Lᵖ` seminorm of `fun x => f x - a`, for a constant `a`, is the
`Lᵖ` distance from `f` to the constant class `MeasureTheory.Lp.const`.  The identity holds for
every exponent `p`.  It is the bridge between the seminorm form of an estimate on the deviation
from a constant and its norm form; for `1 ≤ p`, where `Lᵖ` is a normed group, both sides of the
norm form are continuous functions of the `Lᵖ` class and so pass to limits.

Fatou's lemma bounds the deviation from a constant along an exhaustion: the `Lᵖ` seminorm of
`f - b` on `Ω` is at most the `liminf` of the seminorms of `f - aₙ` on measurable sets `Vₙ ↑ Ω`,
when `aₙ → b`.

It also records that the constant class `t / (1 - t)` has `Lᵖ` norm tending to infinity as
`t → 1⁻`, for every finite nonzero measure. This is the check that the family of real
Cauchy–Riemann operators `\bar∂ + t / (1 - t)` has unbounded zeroth-order term, so it does not
extend continuously to `t = 1`.

## Main declarations

* `TauCeti.eLpNorm_sub_const_eq_enorm`: the deviation from a constant as a distance in `Lᵖ`.
* `TauCeti.eLpNorm_sub_const_restrict_le_liminf`: Fatou along an exhaustion for the deviation from
  a constant.
* `MeasureTheory.Measure.tendsto_norm_lpConst_div_one_sub`: the constant class `t / (1 - t)` is
  unbounded in `Lᵖ` as `t → 1⁻`.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
  [IsFiniteMeasure μ] {p : ℝ≥0∞}

/-- **The deviation from a constant, as a distance in `Lᵖ`.**  The `Lᵖ` seminorm of
`fun x => f x - a` is the distance from `f` to the constant class `a`. -/
theorem eLpNorm_sub_const_eq_enorm (a : F) (f : Lp F p μ) :
    eLpNorm (fun x => f x - a) p μ = ‖f - Lp.const p μ a‖ₑ := by
  rw [Lp.eNorm_def]
  exact eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (.sub .rfl (Lp.coeFn_const p μ a))).symm

omit [IsFiniteMeasure μ] in
/-- The `Lᵖ` seminorm of `f - b` on `Ω` is at most the `liminf` of the `Lᵖ` seminorms of `f - aₙ`
on an exhaustion `Vₙ ↑ Ω` by measurable sets, when `aₙ → b` (Fatou). -/
theorem eLpNorm_sub_const_restrict_le_liminf {Ω : Set α} {f : α → F}
    (hf : AEStronglyMeasurable f (μ.restrict Ω))
    {V : ℕ → Set α} (hV : ∀ n, MeasurableSet (V n))
    (hVmono : Monotone V) (hVunion : ⋃ n, V n = Ω) {a : ℕ → F} {b : F}
    (ha : Tendsto a atTop (𝓝 b)) :
    eLpNorm (fun x ↦ f x - b) p (μ.restrict Ω) ≤
      atTop.liminf fun n ↦ eLpNorm (fun x ↦ f x - a n) p (μ.restrict (V n)) := by
  have hΩ : MeasurableSet Ω := hVunion ▸ MeasurableSet.iUnion hV
  set g : ℕ → α → F := fun n ↦ (V n).indicator fun x ↦ f x - a n with hgdef
  have hVsub : ∀ n, V n ⊆ Ω := fun n ↦ hVunion ▸ Set.subset_iUnion V n
  have hgmeas : ∀ n, AEStronglyMeasurable (g n) μ := fun n ↦
    (aestronglyMeasurable_indicator_iff (hV n)).2
      ((hf.mono_measure (Measure.restrict_mono (hVsub n) le_rfl)).sub aestronglyMeasurable_const)
  have hgval : ∀ n x, x ∈ V n → g n x = f x - a n := fun n x hx ↦ by
    simp only [hgdef]
    exact Set.indicator_of_mem hx _
  have hgzero : ∀ n x, x ∉ V n → g n x = 0 := fun n x hx ↦ by
    simp only [hgdef]
    exact Set.indicator_of_notMem hx _
  have hptw : ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (Ω.indicator (fun x ↦ f x - b) x)) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨n₀, hn₀⟩ := Set.mem_iUnion.1 (hVunion ▸ hx)
      rw [Set.indicator_of_mem hx]
      refine Tendsto.congr' (Filter.eventually_atTop.2 ⟨n₀, fun n hn ↦ ?_⟩)
        (tendsto_const_nhds.sub ha)
      exact (hgval n x (hVmono hn hn₀)).symm
    · rw [Set.indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun n ↦
        (hgzero n x fun hmem ↦ hx (hVunion ▸ Set.mem_iUnion.2 ⟨n, hmem⟩)).symm
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩ.nullMeasurableSet]
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hgmeas (Ω.indicator fun x ↦ f x - b)
    ((aestronglyMeasurable_indicator_iff hΩ).2 (hf.sub aestronglyMeasurable_const))
    (ae_of_all _ hptw)).trans_eq ?_
  simp only [hgdef, eLpNorm_indicator_eq_eLpNorm_restrict (hV _).nullMeasurableSet]

end TauCeti

namespace MeasureTheory.Measure

open Filter Set Topology
open scoped ENNReal

/-- **Check: the family `\bar∂ + t / (1 - t)` is not continuous at `t = 1`.** For a finite nonzero
measure `μ` and `p ≠ 0`, the `L^p(μ)` norm of the constant zeroth-order term `t / (1 - t)` tends
to infinity as `t → 1⁻`; applied to Lebesgue measure on the unit disc, the multiplication
operators have unbounded norm, so the deformation invariance of the index does not apply. -/
theorem tendsto_norm_lpConst_div_one_sub {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [NeZero μ] {p : ℝ≥0∞} (hp : p ≠ 0) :
    Tendsto (fun t : ℝ ↦ ‖Lp.const p μ (((t / (1 - t) : ℝ)) : ℂ)‖) (𝓝[<] 1) atTop := by
  simp only [Lp.norm_const _ _ _ hp, Complex.norm_real, Real.norm_eq_abs]
  have hμ : 0 < μ.real univ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureReal_univ_pos) _
  exact (tendsto_abs_atTop_atTop.comp TauCeti.tendsto_div_one_sub_nhdsLT_one).atTop_mul_const hμ

end MeasureTheory.Measure
