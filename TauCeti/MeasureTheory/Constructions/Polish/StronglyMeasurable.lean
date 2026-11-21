/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Topology.Order.Basic
import TauCeti.Topology.Order.LeftRight

/-!
# Strong measurability of right-hand limits of eventually right-continuous families

Mathlib's `MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto` and
`MeasureTheory.StronglyMeasurable.limUnder` apply to limits along filters on a countable index type.
For an uncountable parameter `r > a` in a second-countable linear order `ι` with the order topology
(such as `ℝ`), the right-hand limit `lim_{r → a⁺} f r x` need not be measurable from individual
strong measurability of `f r` alone. When `f r` is eventually strongly measurable as `r → a⁺` and
each trajectory `r ↦ f r x` is eventually right-continuous as `r → a⁺` (with a threshold that may
depend on `x`), convergence and the limit along `𝓝[>] a` coincide with those along a single
countable subset near `a⁺` (`TopologicalSpace.exists_countable_subset_tendsto_nhdsGT_iff`),
reducing both results to the countable-index case.

## Main statements

* `MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto_nhdsGT`: measurability of
  `{x | ∃ c, Tendsto (f · x) (𝓝[>] a) (𝓝 c)}` for families `f` with `f r` eventually strongly
  measurable and `r ↦ f r x` eventually right-continuous along `𝓝[>] a`.
* `MeasureTheory.StronglyMeasurable.limUnder_nhdsGT`: strong measurability of
  `x ↦ limUnder (𝓝[>] a) (f · x)` under the same hypotheses.
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace MeasureTheory.StronglyMeasurable

variable {ι X E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [MeasurableSpace X] [TopologicalSpace E]
  {a : ι} {f : ι → X → E}

/-- If `f r : X → E` into a completely pseudo-metrizable space is eventually strongly measurable as
`r → a⁺`, and for each `x` the trajectory `r ↦ f r x` is eventually right-continuous as `r → a⁺`,
then the set of points `x` where `lim_{r → a⁺} f r x` exists is measurable. -/
theorem measurableSet_exists_tendsto_nhdsGT [IsCompletelyPseudoMetrizableSpace E]
    (hf : ∀ᶠ r in 𝓝[>] a, StronglyMeasurable (f r))
    (hrc : ∀ x, ∀ᶠ r in 𝓝[>] a, ContinuousWithinAt (f · x) (Ioi r) r) :
    MeasurableSet {x | ∃ c, Tendsto (f · x) (𝓝[>] a) (𝓝 c)} := by
  let := upgradeIsCompletelyPseudoMetrizable E
  obtain ⟨S, hSc, hSs, _, hiff⟩ :=
    TopologicalSpace.exists_countable_subset_tendsto_nhdsGT_iff (E := E) hf
  have := hSc.to_subtype
  convert StronglyMeasurable.measurableSet_exists_tendsto
    (l := comap (Subtype.val : S → ι) (𝓝 a)) (fun s : S ↦ (hSs s.property).1) using 1
  ext x
  refine exists_congr fun c ↦ ?_
  rw [hiff (hrc x), nhdsWithin, ← subtypeVal_map_comap, tendsto_map'_iff]
  rfl

/-- If `f r : X → E` into a nonempty completely metrizable space is eventually strongly measurable
as `r → a⁺`, and for each `x` the trajectory `r ↦ f r x` is eventually right-continuous as `r → a⁺`,
then the right-hand limit `x ↦ limUnder (𝓝[>] a) (f · x)` is strongly measurable. -/
protected theorem limUnder_nhdsGT [Nonempty E] [IsCompletelyMetrizableSpace E]
    (hf : ∀ᶠ r in 𝓝[>] a, StronglyMeasurable (f r))
    (hrc : ∀ x, ∀ᶠ r in 𝓝[>] a, ContinuousWithinAt (f · x) (Ioi r) r) :
    StronglyMeasurable (fun x ↦ limUnder (𝓝[>] a) (f · x)) := by
  obtain hbot | hne := eq_or_neBot (𝓝[>] a)
  · simpa only [hbot, limUnder, Filter.map_bot] using stronglyMeasurable_const
  let := upgradeIsCompletelyMetrizable E
  obtain ⟨S, hSc, hSs, hSne, hiff⟩ :=
    TopologicalSpace.exists_countable_subset_tendsto_nhdsGT_iff (E := E) hf
  have := hSc.to_subtype
  let l : Filter S := comap Subtype.val (𝓝 a)
  have : l.NeBot := (Filter.map_neBot_iff _).1 (by rwa [subtypeVal_map_comap, ← nhdsWithin, hSne])
  convert StronglyMeasurable.limUnder (l := l) (fun s : S ↦ (hSs s.property).1) using 1
  ext x
  have hiff' (c : E) : Tendsto (f · x) (𝓝[>] a) (𝓝 c) ↔
      Tendsto (fun s : S ↦ f s.val x) l (𝓝 c) := by
    rw [hiff (hrc x), nhdsWithin, ← subtypeVal_map_comap, tendsto_map'_iff]
    rfl
  by_cases hconv : ∃ c, Tendsto (f · x) (𝓝[>] a) (𝓝 c)
  · obtain ⟨c, hc⟩ := hconv
    rw [hc.limUnder_eq, ((hiff' c).1 hc).limUnder_eq]
  · have hconv' : ¬ ∃ c, Tendsto (fun s : S ↦ f s.val x) l (𝓝 c) :=
      fun ⟨c, hc⟩ ↦ hconv ⟨c, (hiff' c).2 hc⟩
    rw [limUnder_of_not_tendsto hconv, limUnder_of_not_tendsto hconv']

end MeasureTheory.StronglyMeasurable
