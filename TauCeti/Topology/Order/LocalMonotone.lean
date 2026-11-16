/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue

/-!
# Strict monotonicity near a point

A function `f` between orders is *strictly monotone at `a`* (`TauCeti.StrictMonoAt f a`) when it
is strictly monotone on a neighbourhood of `a`, and *strictly antitone at `a`*
(`TauCeti.StrictAntiAt f a`) when it is strictly antitone on one.

A function cannot be both on a set with two points, so it cannot be both at a point of a densely
ordered space without maximum. On a densely ordered conditionally complete linear order, a
function continuous and injective near `a` is one of the two at `a`, by
`ContinuousOn.strictMonoOn_of_injOn_Icc'`. If `g = h ∘ τ` near `a`, and each of `τ` at `a` and
`h` at `τ a` is strictly monotone or strictly antitone, then `g` is strictly monotone at `a`
exactly when `h` and `τ` go in the same direction.

## Main results

* `Set.Nontrivial.not_strictMonoOn_and_strictAntiOn`: no function is both strictly monotone and
  strictly antitone on a set with two points.
* `TauCeti.strictMonoAt_or_strictAntiAt`: a function continuous and injective on a neighbourhood
  of `a` is strictly monotone or strictly antitone at `a`.
* `TauCeti.not_strictMonoAt_and_strictAntiAt`: no function is both at a point.
* `TauCeti.strictMonoAt_iff_of_eventuallyEq_comp`: the direction of a composite.
-/

public section

open Filter Set Topology

/-- A function is not both strictly monotone and strictly antitone on a set with two points. -/
theorem Set.Nontrivial.not_strictMonoOn_and_strictAntiOn {α β : Type*} [LinearOrder α]
    [Preorder β] {f : α → β} {s : Set α} (hs : s.Nontrivial) :
    ¬(StrictMonoOn f s ∧ StrictAntiOn f s) := by
  rintro ⟨hm, ha⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  rcases hxy.lt_or_gt with h | h
  · exact lt_asymm (hm hx hy h) (ha hx hy h)
  · exact lt_asymm (hm hy hx h) (ha hy hx h)

namespace TauCeti

variable {α β γ : Type*}

section Defs

variable [TopologicalSpace α] [Preorder α] [Preorder β]

/-- `f` is strictly monotone at `a`: it is strictly monotone on some neighbourhood of `a`. -/
@[expose] def StrictMonoAt (f : α → β) (a : α) : Prop := ∃ s ∈ 𝓝 a, StrictMonoOn f s

/-- `f` is strictly antitone at `a`: it is strictly antitone on some neighbourhood of `a`. -/
@[expose] def StrictAntiAt (f : α → β) (a : α) : Prop := ∃ s ∈ 𝓝 a, StrictAntiOn f s

end Defs

/-- A function continuous and injective on a neighbourhood of `a` is strictly monotone or
strictly antitone at `a`. -/
theorem strictMonoAt_or_strictAntiAt [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] [LinearOrder β] [TopologicalSpace β]
    [OrderClosedTopology β] {f : α → β} {a : α} {s : Set α} (hs : s ∈ 𝓝 a)
    (hc : ContinuousOn f s) (hi : InjOn f s) : StrictMonoAt f a ∨ StrictAntiAt f a := by
  obtain ⟨b, c, hbc, hI, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hs
  exact ((hc.mono hsub).strictMonoOn_of_injOn_Icc' (hbc.1.trans hbc.2) (hi.mono hsub)).imp
    (fun h ↦ ⟨_, hI, h⟩) fun h ↦ ⟨_, hI, h⟩

/-- A function is not both strictly monotone and strictly antitone at a point of a densely
ordered space without maximum. -/
theorem not_strictMonoAt_and_strictAntiAt [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] [Preorder β] {f : α → β} {a : α} :
    ¬(StrictMonoAt f a ∧ StrictAntiAt f a) := by
  rintro ⟨⟨s, hs, hm⟩, t, ht, ha⟩
  obtain ⟨u, hau, hsub⟩ := exists_Ico_subset_of_mem_nhds (inter_mem hs ht) (exists_gt a)
  obtain ⟨x, hax, hxu⟩ := exists_between hau
  have hst : (s ∩ t).Nontrivial :=
    ⟨a, hsub ⟨le_rfl, hau⟩, x, hsub ⟨hax.le, hxu⟩, hax.ne⟩
  exact hst.not_strictMonoOn_and_strictAntiOn
    ⟨hm.mono inter_subset_left, ha.mono inter_subset_right⟩

/-- **The direction of a composite.** If `g = h ∘ τ` near `a`, and `τ` at `a` and `h` at `τ a`
are each strictly monotone or strictly antitone, then `g` is strictly monotone at `a` exactly when
`h` and `τ` have the same direction. -/
theorem strictMonoAt_iff_of_eventuallyEq_comp [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [DenselyOrdered β] [NoMaxOrder β] [Preorder γ] {g : α → γ} {h : β → γ}
    {τ : α → β} {a : α} (hg : g =ᶠ[𝓝 a] h ∘ τ) (hτc : ContinuousAt τ a)
    (hτ : StrictMonoAt τ a ∨ StrictAntiAt τ a) (hh : StrictMonoAt h (τ a) ∨ StrictAntiAt h (τ a)) :
    StrictMonoAt g a ↔ (StrictMonoAt h (τ a) ↔ StrictMonoAt τ a) := by
  -- Shrink the neighbourhood of `a` so that `τ` maps it into that of `τ a` and `g = h ∘ τ` on it.
  have key : ∀ {V W}, V ∈ 𝓝 (τ a) → W ∈ 𝓝 a →
      ∃ W' ∈ 𝓝 a, W' ⊆ W ∧ MapsTo τ W' V ∧ EqOn (h ∘ τ) g W' := fun hV hW ↦
    ⟨_, inter_mem (inter_mem hW (hτc.preimage_mem_nhds hV)) hg, fun _ hx ↦ hx.1.1,
      fun _ hx ↦ hx.1.2, fun _ hx ↦ hx.2.symm⟩
  have hgτ := not_strictMonoAt_and_strictAntiAt (f := τ) (a := a)
  have hgh := not_strictMonoAt_and_strictAntiAt (f := h) (a := τ a)
  have hgg := not_strictMonoAt_and_strictAntiAt (f := g) (a := a)
  rcases hh with ⟨V, hV, hhV⟩ | ⟨V, hV, hhV⟩ <;> rcases hτ with ⟨W, hW, hτW⟩ | ⟨W, hW, hτW⟩ <;>
    obtain ⟨W', hW', hW'W, hmaps, heq⟩ := key hV hW
  · have : StrictMonoAt g a := ⟨W', hW', (hhV.comp (hτW.mono hW'W) hmaps).congr heq⟩
    have : StrictMonoAt h (τ a) := ⟨V, hV, hhV⟩
    have : StrictMonoAt τ a := ⟨W, hW, hτW⟩
    tauto
  · have : StrictAntiAt g a :=
      ⟨W', hW', (hhV.comp_strictAntiOn (hτW.mono hW'W) hmaps).congr heq⟩
    have : StrictMonoAt h (τ a) := ⟨V, hV, hhV⟩
    have : StrictAntiAt τ a := ⟨W, hW, hτW⟩
    tauto
  · have : StrictAntiAt g a :=
      ⟨W', hW', (hhV.comp_strictMonoOn (hτW.mono hW'W) hmaps).congr heq⟩
    have : StrictAntiAt h (τ a) := ⟨V, hV, hhV⟩
    have : StrictMonoAt τ a := ⟨W, hW, hτW⟩
    tauto
  · have : StrictMonoAt g a := ⟨W', hW', (hhV.comp (hτW.mono hW'W) hmaps).congr heq⟩
    have : StrictAntiAt h (τ a) := ⟨V, hV, hhV⟩
    have : StrictAntiAt τ a := ⟨W, hW, hτW⟩
    tauto

end TauCeti
