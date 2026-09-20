/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the statements compare the `map_values` witness with another directing measure.
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
-- Public: the conclusions are consequences of almost-sure uniqueness of directing measures.
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Unique
-- Non-public: used to replace the mapped process by an a.e.-equal process.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Congr

/-!
# Compatibility of directing measures with measurable maps

A directing measure is functorial in the state space. If `X` is conditionally i.i.d. with
directing measure `ν`, then applying a measurable map `g` to every coordinate gives the
pushforward directing measure `ν.map g`. If the mapped process is also presented with another
directing measure `ξ`, uniqueness forces `ν.map g = ξ` almost surely.

The same conclusion holds when the mapped coordinates are first selected along an injection and
then changed almost surely. This form compares directing measures attached to two different
presentations of one conditionally i.i.d. family. Countable families of such comparisons can be
put on one common almost-sure set with `ae_all_iff`.

## Main results

* `ConditionallyIIDWith.ae_map_directing_eq_of_comp_injective` compares directing measures after
  a measurable value map, an injective coordinate selection, and an a.e. change of the process.
-/

public section

noncomputable section

open Filter MeasurableSpace MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure Ω} {ν : Ω → ProbabilityMeasure α} {ξ : Ω → ProbabilityMeasure β}

/-- **Directing measures commute almost surely with a measurable value map and an injective
coordinate selection.**

Suppose `ν` directs `X`, while `ξ` directs `Y`. If, after selecting the coordinates of `X` along
an injection `k`, applying `g` gives `Y` coordinatewise almost surely, then `ξ` is almost surely
the pushforward of `ν` by `g`.

The theorem assumes that the base measure is a probability measure and that the target measurable
space is countably generated. -/
theorem ConditionallyIIDWith.ae_map_directing_eq_of_comp_injective
    [IsProbabilityMeasure μ] [CountablyGenerated β]
    {X : ι → Ω → α} {Y : ℕ → Ω → β}
    (hX : ConditionallyIIDWith μ X ν) (hY : ConditionallyIIDWith μ Y ξ)
    {g : α → β} (hg : Measurable g) {k : ℕ → ι} (hk : Function.Injective k)
    (hXY : ∀ i, (fun ω => g (X (k i) ω)) =ᵐ[μ] Y i) :
    (fun ω => (ν ω).map g) =ᵐ[μ] ξ := by
  have hmap : ConditionallyIIDWith μ (fun i ω => g (X (k i) ω))
      (fun ω => (ν ω).map g) :=
    (hX.comp_injective hk).map_values hg
  exact conditionallyIID_ae_unique (hmap.congr_process hXY) hY

end Probability

end TauCeti

end

end
