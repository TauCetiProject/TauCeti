/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Absolute continuity: domination by point-charging measures, transfer along maps, and `ε`–`δ`

If a measure gives positive mass to every singleton, every null set is empty. It
therefore dominates any other measure, without a countability or finiteness
assumption. This is useful when a full-support discrete reference is used for
relative entropy.

If `f` pushes `μ` forward to a measure absolutely continuous with respect to `ν`, then every
property holding `ν`-almost everywhere holds at `f x` for `μ`-almost every `x`. Mathlib's
`MeasureTheory.ae_eq_comp'` records the special case of an almost-everywhere equality.

If a finite measure `ν` is absolutely continuous with respect to `μ`, then `ν s` is uniformly
small whenever `μ s` is small. This quantitative form of `ν ≪ μ` holds for an arbitrary
reference measure `μ`, with no σ-finiteness and hence no Radon–Nikodym derivative. It is what
transfers approximation properties, such as regularity, from `μ` to `ν`.

## Main declarations

* `TauCeti.absolutelyContinuous_of_forall_singleton_ne_zero`: a measure positive on every
  singleton dominates every measure.
* `MeasureTheory.ae_comp_of_map_absolutelyContinuous`: a `ν`-almost-everywhere property holds
  along `f` `μ`-almost everywhere.
* `MeasureTheory.Measure.AbsolutelyContinuous.exists_pos_measure_lt_of_measure_lt`: the `ε`–`δ`
  form of absolute continuity of a finite measure.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley
  (1999), Theorem 3.5.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A measure positive on every singleton dominates every measure: a null set cannot contain
any point. No finiteness or countability assumption is needed. -/
theorem absolutelyContinuous_of_forall_singleton_ne_zero
    (hν : ∀ x : α, ν {x} ≠ 0) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  have hempty : s = ∅ := by
    apply Set.Subset.antisymm _ (Set.empty_subset s)
    intro y hy
    have hzero : ν {y} = 0 :=
      le_zero_iff.mp ((measure_mono (Set.singleton_subset_iff.mpr hy)).trans_eq hs)
    exact hν y hzero
  simp [hempty]

end TauCeti

namespace MeasureTheory

/-- If `μ.map f ≪ ν`, a property holding `ν`-almost everywhere holds at `f x` for `μ`-almost
every `x`. This generalizes `MeasureTheory.ae_eq_comp'` from equalities to arbitrary
properties. -/
theorem ae_comp_of_map_absolutelyContinuous {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : AEMeasurable f μ) (hmap : μ.map f ≪ ν)
    {P : β → Prop} (h : ∀ᵐ y ∂ν, P y) : ∀ᵐ x ∂μ, P (f x) :=
  ae_of_ae_map hf (hmap.ae_le h)

end MeasureTheory

namespace MeasureTheory.Measure.AbsolutelyContinuous

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- **`ε`–`δ` absolute continuity.** If a finite measure `ν` is absolutely continuous with respect
to `μ`, then for every `ε ≠ 0` there is `δ > 0` such that `μ s < δ` implies `ν s < ε`, for every
set `s`. No finiteness or σ-finiteness assumption on `μ` is needed. -/
theorem exists_pos_measure_lt_of_measure_lt [IsFiniteMeasure ν] (h : ν ≪ μ) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ δ > 0, ∀ s, μ s < δ → ν s < ε := by
  by_contra! H
  -- Otherwise there are sets of `μ`-measure below `2⁻ⁿ` and `ν`-measure at least `ε`.
  choose s hμs hνs using fun n : ℕ ↦ H ((2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.pow_pos (by simp) n)
  set t := fun n ↦ toMeasurable μ (s n)
  have hsum : ∑' n, μ (t n) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) (by simp)
      (ENNReal.tsum_le_tsum fun n ↦ ?_)
    simpa [t, measure_toMeasurable] using (hμs n).le
  -- By Borel–Cantelli their `limsup` is `μ`-null, hence `ν`-null.
  have hzero : ν (limsup t atTop) = 0 := h (measure_limsup_atTop_eq_zero hsum)
  have hanti : Antitone fun n ↦ ⋃ i ≥ n, t i :=
    fun _ _ hmn ↦ iUnion₂_mono' fun i hi ↦ ⟨i, hmn.trans hi, subset_rfl⟩
  rw [limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter] at hzero
  simp only [iSup_eq_iUnion] at hzero
  -- Continuity from above of the finite measure `ν` gives the contradiction `ε ≤ 0`.
  rw [hanti.measure_iInter
    (fun _ ↦ (MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_toMeasurable μ (s i)).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩] at hzero
  refine hε (le_zero_iff.mp (hzero ▸ le_iInf fun n ↦ (hνs n).trans (measure_mono ?_)))
  exact (subset_toMeasurable μ (s n)).trans (subset_iUnion₂_of_subset n le_rfl subset_rfl)

end MeasureTheory.Measure.AbsolutelyContinuous
