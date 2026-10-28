/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Bases

/-!
# Locally almost everywhere constant functions on preconnected sets

A function that is almost everywhere constant near each point of a preconnected set is almost
everywhere equal to a single constant on the whole set, provided the measure charges every
nonempty open set and the space is second countable. This is the measure-theoretic analogue of
`IsPreconnected.constant` for locally constant functions. It turns local constancy statements,
such as the constancy on every ball of a Sobolev function with vanishing weak gradient, into
global ones on a connected domain.

The positivity of the measure on open sets makes the local constant at each point unique, so the
points near which `f` equals a given constant form an open set. Connectedness then forces a single
constant, and second countability reduces the union of the local neighbourhoods to a countable
one.

## Main results

* `IsPreconnected.exists_ae_eq_const_of_forall_nhds`: a locally almost everywhere constant
  function on a preconnected set is almost everywhere constant on it.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Topology

namespace TauCeti

/-- **A locally almost everywhere constant function on a preconnected set is almost everywhere
constant.** Let `μ` be positive on nonempty open sets of a second-countable space. If every point
of a preconnected set `s` has a neighbourhood on which `f` is `μ`-almost everywhere equal to a
constant, then `f` is `μ`-almost everywhere equal to a single constant on `s`. -/
theorem _root_.IsPreconnected.exists_ae_eq_const_of_forall_nhds {X β : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] {μ : Measure X}
    [μ.IsOpenPosMeasure] [Nonempty β] {s : Set X} (hs : IsPreconnected s) {f : X → β}
    (hf : ∀ x ∈ s, ∃ c, ∃ U ∈ 𝓝 x, ∀ᵐ y ∂μ.restrict U, f y = c) :
    ∃ c, ∀ᵐ y ∂μ.restrict s, f y = c := by
  -- `P c x`: near `x`, the function `f` is almost everywhere equal to `c`.
  let P (c : β) (x : X) : Prop := ∃ U ∈ 𝓝 x, ∀ᵐ y ∂μ.restrict U, f y = c
  have hopen (c : β) : IsOpen {x | P c x} := by
    refine isOpen_iff_mem_nhds.2 fun x ⟨U, hU, hc⟩ => ?_
    filter_upwards [eventually_mem_nhds_iff.2 hU] with y hy using ⟨U, hy, hc⟩
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
  -- By connectedness, `f` is almost everywhere equal to `c₀` near every point of `s`.
  have hall : ∀ x ∈ s, P c₀ x := by
    by_contra! hbad
    obtain ⟨x₁, hx₁, hx₁c⟩ := hbad
    obtain ⟨y, -, hyc, d, hd, hyd⟩ := hs {x | P c₀ x} {x | ∃ d ≠ c₀, P d x} (hopen c₀)
      (isOpen_iff_forall_mem_open.2 fun x ⟨d, hd, hdx⟩ =>
        ⟨{x | P d x}, fun y hy => ⟨d, hd, hy⟩, hopen d, hdx⟩)
      (fun x hx => by
        obtain ⟨d, hdx⟩ := hf x hx
        by_cases hdc : d = c₀
        · exact Or.inl (hdc ▸ hdx)
        · exact Or.inr ⟨d, hdc, hdx⟩)
      ⟨x₀, hx₀, hc₀⟩
      (by
        obtain ⟨d, hdx⟩ := hf x₁ hx₁
        exact ⟨x₁, hx₁, d, fun hdc => hx₁c (hdc ▸ hdx), hdx⟩)
    exact hd (hunique hyd hyc)
  -- Countably many of these neighbourhoods cover `s`.
  choose! U hU hUc using hall
  obtain ⟨T, hTs, hTc, hT⟩ := isOpen_biUnion_countable s (fun x => interior (U x))
    (fun _ _ => isOpen_interior)
  have hcover : s ⊆ ⋃ x ∈ T, interior (U x) := by
    rw [hT]
    exact fun x hx => mem_biUnion hx (mem_interior_iff_mem_nhds.2 (hU x hx))
  refine ⟨c₀, ae_restrict_of_ae_restrict_of_subset hcover ?_⟩
  exact (ae_restrict_biUnion_iff _ hTc _).2 fun x hx =>
    ae_restrict_of_ae_restrict_of_subset interior_subset (hUc x (hTs hx))

end TauCeti

end
