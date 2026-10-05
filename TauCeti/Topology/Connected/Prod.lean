/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Preconnected sets in a product with preconnected fibres

A subset of `X × Y` over a preconnected base need not be preconnected even when every vertical
fibre is: the fibres may fail to be linked to one another. They are linked as soon as the set
contains the graph of a continuous map `X → Y`, since that graph is preconnected and meets every
fibre. This is how one shows that the regions between continuous graphs over a connected base,
such as the sectors of a cylindrical stack, are connected.

## Main declarations

* `TauCeti.isPreconnected_of_isPreconnected_preimage_prodMk`: a set with preconnected fibres
  containing the graph of a continuous map over a preconnected base is preconnected.
-/

public section

open Set

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Over a preconnected base, a set `s ⊆ X × Y` is preconnected if each of its fibres
`{y | (x, y) ∈ s}` is preconnected and it contains the graph of a continuous map `f : X → Y`. -/
theorem isPreconnected_of_isPreconnected_preimage_prodMk [PreconnectedSpace X]
    {s : Set (X × Y)} {f : X → Y} (hf : Continuous f) (hfs : ∀ x, (x, f x) ∈ s)
    (hs : ∀ x, IsPreconnected (Prod.mk x ⁻¹' s)) : IsPreconnected s := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · rw [eq_empty_of_isEmpty s]
    exact isPreconnected_empty
  -- Every point is joined to `(x₀, f x₀)` through its fibre followed by the graph of `f`.
  refine isPreconnected_of_forall (x₀, f x₀) fun z hz ↦
    ⟨Prod.mk z.1 '' (Prod.mk z.1 ⁻¹' s) ∪ range fun x ↦ (x, f x), ?_, Or.inr ⟨x₀, rfl⟩,
      Or.inl ⟨z.2, hz, rfl⟩, ?_⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, rfl⟩)
    exacts [hy, hfs x]
  · exact ((hs z.1).image _ (Continuous.prodMk_right z.1).continuousOn).union (z.1, f z.1)
      ⟨f z.1, hfs z.1, rfl⟩ ⟨z.1, rfl⟩ (isPreconnected_range (by fun_prop))

end TauCeti
