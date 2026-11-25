/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Order.Compact
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Finiteness, trimming and fixed points of measure-preserving maps

## Main results

* `MeasureTheory.MeasurePreserving.isFiniteMeasure` — a finite source measure makes the target of
  a measure-preserving map finite.
* `MeasureTheory.MeasurePreserving.trim_comap` — a measure-preserving map preserves the measures
  trimmed to a target sub-σ-algebra and its pullback on the source.
* `MeasureTheory.MeasurePreserving.map_eq_self_of_strictMono` — a strictly increasing map of a
  densely ordered space preserving a locally finite measure of full support fixes every point
  between two of its fixed points.
-/

public section

namespace MeasureTheory.MeasurePreserving

variable {α β : Type*} {m : MeasurableSpace β}
  [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {f g : α → β}

/-- A finite source measure makes the target of a measure-preserving map finite. -/
theorem isFiniteMeasure [IsFiniteMeasure μ] (hf : MeasurePreserving f μ ν) : IsFiniteMeasure ν :=
  hf.map_eq ▸ Measure.isFiniteMeasure_map μ f

/-- A measure-preserving map also preserves the measures trimmed to a sub-σ-algebra of the target
and its pullback on the source. -/
theorem trim_comap (hg : MeasurePreserving g μ ν) (hm : m ≤ mβ) :
    @MeasurePreserving α β (m.comap g) m g
      (μ.trim ((MeasurableSpace.comap_mono hm).trans hg.measurable.comap_le)) (ν.trim hm) := by
  have hmeas : Measurable[m.comap g, m] g := measurable_iff_comap_le.mpr le_rfl
  refine @MeasurePreserving.mk α β (m.comap g) m g _ _ hmeas ?_
  refine @Measure.ext β m _ _ fun s hs ↦ ?_
  have hmg : m.comap g ≤ mα := (MeasurableSpace.comap_mono hm).trans hg.measurable.comap_le
  have hs' : MeasurableSet[m.comap g] (g ⁻¹' s) := ⟨s, hs, rfl⟩
  rw [Measure.map_apply hmeas hs, trim_measurableSet_eq hmg hs', trim_measurableSet_eq hm hs]
  exact hg.measure_preimage (hm s hs).nullMeasurableSet

section StrictMono

open Set Function

variable {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [CompactIccSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] {h : α → α}

/-- A strictly increasing map of a densely ordered space preserving a locally finite measure of
full support does not move a point `x` up when it fixes a point `y ≥ x`: otherwise the intervals
`[hⁿ(x), hⁿ⁺¹(x))` would be disjoint subsets of `[x, y]` of equal positive measure. -/
theorem map_le_self_of_strictMono (hμ : MeasurePreserving h μ μ) (hh : StrictMono h) {x y : α}
    (hxy : x ≤ y) (hy : h y = y) : h x ≤ x := by
  by_contra! hx
  set u : ℕ → α := fun n => h^[n] x
  have hu (n : ℕ) : u (n + 1) = h (u n) := iterate_succ_apply' h n x
  have hmono : Monotone u := (hh.strictMono_iterate_of_lt_map hx).monotone
  have hle (n : ℕ) : u n ≤ y := iterate_fixed hy n ▸ hh.monotone.iterate n hxy
  have hpre (n : ℕ) : h ⁻¹' Ico (u (n + 1)) (u (n + 2)) = Ico (u n) (u (n + 1)) := by
    ext z
    simp only [mem_preimage, mem_Ico, hu (n + 1), hu n, hh.le_iff_le, hh.lt_iff_lt]
  have hmeas (n : ℕ) : μ (Ico (u n) (u (n + 1))) = μ (Ico x (h x)) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← hpre n, hμ.measure_preimage measurableSet_Ico.nullMeasurableSet]
  have hpos : μ (Ico x (h x)) ≠ 0 :=
    ((isOpen_Ioo.measure_pos μ (nonempty_Ioo.2 hx)).trans_le
      (measure_mono Ioo_subset_Ico_self)).ne'
  have hsub : (⋃ n, Ico (u n) (u (n + 1))) ⊆ Icc x y := iUnion_subset fun n z hz =>
    ⟨(hmono (Nat.zero_le n)).trans hz.1, (hz.2.trans_le (hle (n + 1))).le⟩
  have hunion := measure_iUnion (μ := μ) hmono.pairwise_disjoint_on_Ico_succ
    fun _ => measurableSet_Ico
  simp only [Order.succ_eq_add_one, hmeas, ENNReal.tsum_const_eq_top_of_ne_zero hpos] at hunion
  exact (isCompact_Icc.measure_lt_top (μ := μ)).ne (top_le_iff.1 (hunion ▸ measure_mono hsub))

/-- A strictly increasing map of a densely ordered space preserving a locally finite measure of
full support fixes every point lying between two of its fixed points. -/
theorem map_eq_self_of_strictMono (hμ : MeasurePreserving h μ μ) (hh : StrictMono h)
    {x y₁ y₂ : α} (h₁ : h y₁ = y₁) (h₂ : h y₂ = y₂) (hx₁ : y₁ ≤ x) (hx₂ : x ≤ y₂) : h x = x := by
  -- The mirror inequality is the first one in the order dual.
  have : IsLocallyFiniteMeasure (α := αᵒᵈ) μ := ‹IsLocallyFiniteMeasure μ›
  have : Measure.IsOpenPosMeasure (X := αᵒᵈ) μ := ‹μ.IsOpenPosMeasure›
  exact (hμ.map_le_self_of_strictMono hh hx₂ h₂).antisymm <|
    map_le_self_of_strictMono (α := αᵒᵈ) (μ := μ) (h := OrderDual.toDual ∘ h ∘ OrderDual.ofDual)
      hμ hh.dual hx₁ h₁

end StrictMono

end MeasureTheory.MeasurePreserving
