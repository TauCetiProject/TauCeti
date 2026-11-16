/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Locally almost everywhere constant functions on preconnected sets

A function that is almost everywhere constant near each point of a preconnected set is almost
everywhere equal to a single constant on the whole set, provided the measure charges every
nonempty open set and the set is Lindelöf (for instance, any set in a second-countable or, more
generally, hereditarily Lindelöf space). This is the measure-theoretic analogue of
`IsPreconnected.constant` for locally constant functions. It turns local constancy statements,
such as the constancy on every ball of a Sobolev function with vanishing weak gradient, into
global ones on a connected domain.

The positivity of the measure on open sets makes the local constant at each point unique, so
sharing a local constant is an equivalence relation on the set whose classes are relatively open.
Connectedness then forces a single constant, and since the set is Lindelöf, countably many of the
local neighbourhoods cover it.

## Main results

* `IsPreconnected.exists_ae_eq_const_of_forall_nhds`: a locally almost everywhere constant
  function on a preconnected Lindelöf set is almost everywhere constant on it.
-/

public section

open MeasureTheory Set
open scoped Topology

namespace IsPreconnected

/-- **A locally almost everywhere constant function on a preconnected Lindelöf set is almost
everywhere constant.** Let `μ` be positive on nonempty open sets, and let `s` be a preconnected
Lindelöf set (every set is Lindelöf in a hereditarily Lindelöf space, for instance a
second-countable one, see `HereditarilyLindelofSpace.isLindelof`). If every point of `s` has a
neighbourhood on which `f` is `μ`-almost everywhere equal to a constant, then `f` is `μ`-almost
everywhere equal to a single constant on `s`. -/
theorem exists_ae_eq_const_of_forall_nhds {X β : Type*}
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure] [Nonempty β]
    {s : Set X} (hs : IsPreconnected s) (hsL : IsLindelof s) {f : X → β}
    (hf : ∀ x ∈ s, ∃ c, ∃ U ∈ 𝓝 x, ∀ᵐ y ∂μ.restrict U, f y = c) :
    ∃ c, ∀ᵐ y ∂μ.restrict s, f y = c := by
  -- `P c x`: near `x`, the function `f` is almost everywhere equal to `c`.
  let P (c : β) (x : X) : Prop := ∃ U ∈ 𝓝 x, ∀ᵐ y ∂μ.restrict U, f y = c
  -- Since `μ` charges every neighbourhood, the local constant at a point is unique.
  have hunique {c d : β} {x : X} (hc : P c x) (hd : P d x) : c = d := by
    obtain ⟨U, hU, hcU⟩ := hc
    obtain ⟨V, hV, hdV⟩ := hd
    have : (ae (μ.restrict (U ∩ V))).NeBot :=
      ae_restrict_neBot.2 (Measure.measure_pos_of_mem_nhds μ (Filter.inter_mem hU hV)).ne'
    obtain ⟨y, hyc, hyd⟩ := ((ae_restrict_of_ae_restrict_of_subset inter_subset_left hcU).and
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right hdV)).exists
    rw [← hyc, hyd]
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨Classical.arbitrary β, by simp⟩
  obtain ⟨c₀, hc₀⟩ := hf x₀ hx₀
  -- By connectedness, `f` is almost everywhere equal to `c₀` near every point of `s`: sharing a
  -- local constant is symmetric, transitive by `hunique`, and holds near each point of `s`.
  have hall (x : X) (hx : x ∈ s) : P c₀ x := by
    obtain ⟨d, hd₀, hdx⟩ := hs.induction₂ (fun x y => ∃ c, P c x ∧ P c y)
      (fun x hx => by
        obtain ⟨c, U, hU, hcU⟩ := hf x hx
        filter_upwards [nhdsWithin_le_nhds (eventually_mem_nhds_iff.2 hU)] with y hy
        exact ⟨c, ⟨U, hU, hcU⟩, U, hy, hcU⟩)
      (fun _ _ _ _ _ _ ⟨c, hcx, hcy⟩ ⟨d, hdy, hdz⟩ => ⟨c, hcx, hunique hcy hdy ▸ hdz⟩)
      (fun _ _ _ _ ⟨c, hcx, hcy⟩ => ⟨c, hcy, hcx⟩) hx₀ hx
    exact hunique hd₀ hc₀ ▸ hdx
  -- `s` is Lindelöf, so countably many of these neighbourhoods cover it.
  choose! U hU hUc using hall
  obtain ⟨T, hTc, hTs, hcover⟩ := hsL.elim_nhds_subcover U hU
  exact ⟨c₀, ae_restrict_of_ae_restrict_of_subset hcover <|
    (ae_restrict_biUnion_iff _ hTc _).2 fun x hx => hUc x (hTs x hx)⟩

end IsPreconnected

end
