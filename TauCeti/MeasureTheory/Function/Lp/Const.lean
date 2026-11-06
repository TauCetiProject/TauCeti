/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete

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

## Main declarations

* `TauCeti.eLpNorm_sub_const_eq_enorm`: the deviation from a constant as a distance in `Lᵖ`.
* `TauCeti.eLpNorm_sub_const_restrict_le_liminf`: Fatou along an exhaustion for the deviation from
  a constant.
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
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (.sub .rfl (Lp.coeFn_const p μ a))).symm

omit [IsFiniteMeasure μ] in
/-- The `Lᵖ` seminorm of `f - b` on `Ω` is at most the `liminf` of the `Lᵖ` seminorms of `f - aₙ`
on an exhaustion `Vₙ ↑ Ω` by measurable sets, when `aₙ → b` (Fatou). -/
theorem eLpNorm_sub_const_restrict_le_liminf {f : α → F} (hf : AEStronglyMeasurable f μ)
    {Ω : Set α} {V : ℕ → Set α} (hV : ∀ n, MeasurableSet (V n))
    (hVmono : Monotone V) (hVunion : ⋃ n, V n = Ω) {a : ℕ → F} {b : F}
    (ha : Tendsto a atTop (𝓝 b)) :
    eLpNorm (fun x ↦ f x - b) p (μ.restrict Ω) ≤
      atTop.liminf fun n ↦ eLpNorm (fun x ↦ f x - a n) p (μ.restrict (V n)) := by
  have hΩ : MeasurableSet Ω := hVunion ▸ MeasurableSet.iUnion hV
  set g : ℕ → α → F := fun n ↦ (V n).indicator fun x ↦ f x - a n with hgdef
  have hgmeas : ∀ n, AEStronglyMeasurable (g n) μ := fun n ↦
    (hf.sub aestronglyMeasurable_const).indicator (hV n)
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
    ((hf.sub aestronglyMeasurable_const).indicator hΩ)
    (ae_of_all _ hptw)).trans_eq ?_
  simp only [hgdef, eLpNorm_indicator_eq_eLpNorm_restrict (hV _).nullMeasurableSet]

end TauCeti
