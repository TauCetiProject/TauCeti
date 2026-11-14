/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Strong measurability of right-hand limits of eventually right-continuous families

Mathlib's `MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto` and
`MeasureTheory.StronglyMeasurable.limUnder` apply to limits along filters on a countable index type.
For an uncountable parameter `r > a` in a second-countable, densely ordered linear order `ι` (such
as `ℝ`), the right-hand limit `lim_{r → a⁺} f r x` need not be measurable from individual strong
measurability of `f r` alone. When `f r` is eventually strongly measurable as `r → a⁺` and each
trajectory `r ↦ f r x` is eventually right-continuous as `r → a⁺` (with a threshold that may depend
on `x`), convergence and the limit along `𝓝[>] a` coincide with those along a single countable dense
subset near `a⁺`, reducing both results to the countable-index case.

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

section Helper

variable {ι E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]

/-- If `g : ι → E` into a regular space is right-continuous on `Ioo a b` (`a < b`) and `D` is dense
in `ι`, convergence of `g` along `𝓝[>] a` is equivalent to convergence along `D ∩ Ioo a r₀` for any
`r₀ > a`. -/
private theorem tendsto_nhdsGT_iff_comap [TopologicalSpace E] [RegularSpace E]
    {D : Set ι} (hD : Dense D) {a r₀ b : ι} (hr₀ : a < r₀) (hb : a < b) {g : ι → E}
    (hrc : ∀ r ∈ Ioo a b, ContinuousWithinAt g (Ioi r) r) (c : E) :
    Tendsto g (𝓝[>] a) (𝓝 c) ↔
      Tendsto (fun s : (D ∩ Ioo a r₀ : Set ι) ↦ g s.1) (comap Subtype.val (𝓝[>] a)) (𝓝 c) := by
  refine ⟨fun h ↦ h.comp tendsto_comap, fun h ↦ (closed_nhds_basis c).tendsto_right_iff.2 ?_⟩
  rintro V ⟨hVc, hVclosed⟩
  obtain ⟨W, hW, hWV⟩ := mem_comap.1 (h hVc)
  obtain ⟨u, hu, huW⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb).1 hW
  set m : ι := min (min u b) r₀
  have hm : a < m := lt_min (lt_min hu hb) hr₀
  refine mem_of_superset (Ioo_mem_nhdsGT hm) fun r hr ↦ ?_
  by_contra hrV
  have hr_rc : ContinuousWithinAt g (Ioi r) r :=
    hrc r ⟨hr.1, hr.2.trans_le ((min_le_left _ _).trans (min_le_right u b))⟩
  obtain ⟨v, hv, hvV⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hr.2).1
    (hr_rc.preimage_mem_nhdsWithin (hVclosed.isOpen_compl.mem_nhds hrV))
  obtain ⟨d, hd, hdD⟩ := hD.inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.2 (lt_min hv hr.2))
  have hd_m : d < m := hd.2.trans_le (min_le_right v m)
  have hd_u : d ∈ Ioo a u :=
    ⟨hr.1.trans hd.1, hd_m.trans_le ((min_le_left _ _).trans (min_le_left u b))⟩
  have hd_r₀ : d ∈ Ioo a r₀ := ⟨hr.1.trans hd.1, hd_m.trans_le (min_le_right _ r₀)⟩
  exact hvV ⟨hd.1, hd.2.trans_le (min_le_left v m)⟩ (hWV (a := ⟨d, hdD, hd_r₀⟩) (huW hd_u))

end Helper

variable {ι X E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι] [SecondCountableTopology ι] [MeasurableSpace X] [TopologicalSpace E]
  {a : ι} {f : ι → X → E}

/-- If `f r : X → E` into a completely pseudo-metrizable space is eventually strongly measurable as
`r → a⁺`, and for each `x` the trajectory `r ↦ f r x` is eventually right-continuous as `r → a⁺`,
then the set of points `x` where `lim_{r → a⁺} f r x` exists is measurable. -/
theorem measurableSet_exists_tendsto_nhdsGT [IsCompletelyPseudoMetrizableSpace E]
    (hf : ∀ᶠ r in 𝓝[>] a, StronglyMeasurable (f r))
    (hrc : ∀ x, ∀ᶠ r in 𝓝[>] a, ContinuousWithinAt (f · x) (Ioi r) r) :
    MeasurableSet {x | ∃ c, Tendsto (f · x) (𝓝[>] a) (𝓝 c)} := by
  obtain hbot | hne := eq_or_neBot (𝓝[>] a)
  · rcases isEmpty_or_nonempty E with _ | ⟨c₀⟩
    · simp [hbot]
    · convert MeasurableSet.univ using 1
      ext x
      simp only [mem_ofPred_eq, hbot, tendsto_bot, exists_const, mem_univ]
  let := upgradeIsCompletelyPseudoMetrizable E
  obtain ⟨b₀, hb₀⟩ := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a) (s := Ioi a))
  obtain ⟨r₀, hr₀, hfr₀⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb₀).1 hf
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense ι
  let S : Set ι := D ∩ Ioo a r₀
  have : Countable S := (hDc.mono inter_subset_left).to_subtype
  convert StronglyMeasurable.measurableSet_exists_tendsto
    (l := comap (Subtype.val : S → ι) (𝓝[>] a)) (fun s : S ↦ hfr₀ s.2.2) using 1
  ext x
  obtain ⟨b, hb, hrcx⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb₀).1 (hrc x)
  exact exists_congr (tendsto_nhdsGT_iff_comap hD hr₀ hb hrcx)

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
  obtain ⟨b₀, hb₀⟩ := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a) (s := Ioi a))
  obtain ⟨r₀, hr₀, hfr₀⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb₀).1 hf
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense ι
  let S : Set ι := D ∩ Ioo a r₀
  have : Countable S := (hDc.mono inter_subset_left).to_subtype
  let l : Filter S := comap Subtype.val (𝓝[>] a)
  have hl_ne : l.NeBot := comap_neBot fun t ht ↦ by
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hr₀).1 ht
    obtain ⟨d, hd, hdD⟩ := hD.inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.2 (lt_min hu hr₀))
    exact ⟨⟨d, hdD, hd.1, hd.2.trans_le (min_le_right u r₀)⟩,
      hsub ⟨hd.1, hd.2.trans_le (min_le_left u r₀)⟩⟩
  convert StronglyMeasurable.limUnder (l := l) (fun s : S ↦ hfr₀ s.2.2) using 1
  ext x
  obtain ⟨b, hb, hrcx⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb₀).1 (hrc x)
  have hiff := tendsto_nhdsGT_iff_comap hD hr₀ hb hrcx
  by_cases hconv : ∃ c, Tendsto (f · x) (𝓝[>] a) (𝓝 c)
  · obtain ⟨c, hc⟩ := hconv
    rw [hc.limUnder_eq, ((hiff c).1 hc).limUnder_eq]
  · have hconv' : ¬ ∃ c, Tendsto (fun s : S ↦ f s.1 x) l (𝓝 c) :=
      fun ⟨c, hc⟩ ↦ hconv ⟨c, (hiff c).2 hc⟩
    rw [limUnder_of_not_tendsto hconv, limUnder_of_not_tendsto hconv']

end MeasureTheory.StronglyMeasurable
