/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Order.Monotone.Basic

/-!
# Strict monotonicity near a point

A function `f` between orders is *strictly monotone at `a`* (`TauCeti.StrictMonoAt f a`) when it
is strictly monotone on a neighbourhood of `a`, and *strictly antitone at `a`*
(`TauCeti.StrictAntiAt f a`) when it is strictly antitone on one.

A function cannot be both on a set with two points
(`Set.Nontrivial.not_strictMonoOn_and_strictAntiOn`), so it cannot be both at a point that is not
isolated. On a densely ordered conditionally complete linear order, a
function continuous and injective near `a` is one of the two at `a`, by
`ContinuousOn.strictMonoOn_of_injOn_Icc'`. If `g = h ∘ τ` near `a`, and each of `τ` at `a` and
`h` at `τ a` is strictly monotone or strictly antitone, then `g` is strictly monotone at `a`
exactly when `h` and `τ` go in the same direction.

## Main results

* `TauCeti.strictMonoAt_iff`, `StrictMonoOn.strictMonoAt`: the definition, and how to obtain the
  predicate from monotonicity on a neighbourhood; likewise for `StrictAntiAt`.
* `TauCeti.strictMonoAt_toDual_comp_iff`, `TauCeti.strictAntiAt_toDual_comp_iff`: reversing the
  order of the codomain swaps the two predicates.
* `Filter.EventuallyEq.strictMonoAt_iff`: functions equal near `a` have the same direction at `a`.
* `TauCeti.StrictMonoAt.comp`: the composite of functions strictly monotone at the right points
  is strictly monotone; similarly with one or both strictly antitone.
* `TauCeti.strictMonoAt_or_strictAntiAt`: a function continuous and injective on a neighbourhood
  of `a` is strictly monotone or strictly antitone at `a`.
* `TauCeti.not_strictMonoAt_and_strictAntiAt`: no function is both at a point that is not
  isolated.
* `TauCeti.strictMonoAt_iff_of_eventuallyEq_comp`: the direction of a composite.
-/

public section

open Filter OrderDual Set Topology

namespace TauCeti

variable {α β γ : Type*}

section Defs

variable [TopologicalSpace α] [Preorder α] [Preorder β]

/-- `f` is strictly monotone at `a`: it is strictly monotone on some neighbourhood of `a`. -/
def StrictMonoAt (f : α → β) (a : α) : Prop := ∃ s ∈ 𝓝 a, StrictMonoOn f s

/-- `f` is strictly antitone at `a`: it is strictly antitone on some neighbourhood of `a`. -/
def StrictAntiAt (f : α → β) (a : α) : Prop := ∃ s ∈ 𝓝 a, StrictAntiOn f s

/-- Unfolds `StrictMonoAt`. -/
theorem strictMonoAt_iff {f : α → β} {a : α} : StrictMonoAt f a ↔ ∃ s ∈ 𝓝 a, StrictMonoOn f s :=
  Iff.rfl

/-- Unfolds `StrictAntiAt`. -/
theorem strictAntiAt_iff {f : α → β} {a : α} : StrictAntiAt f a ↔ ∃ s ∈ 𝓝 a, StrictAntiOn f s :=
  Iff.rfl

/-- `toDual ∘ f` is strictly monotone at `a` if and only if `f` is strictly antitone at `a`. -/
@[simp]
theorem strictMonoAt_toDual_comp_iff {f : α → β} {a : α} :
    StrictMonoAt (toDual ∘ f : α → βᵒᵈ) a ↔ StrictAntiAt f a :=
  Iff.rfl

/-- `toDual ∘ f` is strictly antitone at `a` if and only if `f` is strictly monotone at `a`. -/
@[simp]
theorem strictAntiAt_toDual_comp_iff {f : α → β} {a : α} :
    StrictAntiAt (toDual ∘ f : α → βᵒᵈ) a ↔ StrictMonoAt f a :=
  Iff.rfl

/-- A function equal near `a` to one strictly monotone at `a` is strictly monotone at `a`. -/
theorem StrictMonoAt.congr_of_eventuallyEq {f g : α → β} {a : α} (hf : StrictMonoAt f a)
    (hfg : f =ᶠ[𝓝 a] g) : StrictMonoAt g a := by
  obtain ⟨t, ht, hf⟩ := hf
  exact ⟨t ∩ {x | f x = g x}, inter_mem ht hfg, (hf.mono inter_subset_left).congr fun _ hx ↦ hx.2⟩

/-- A function equal near `a` to one strictly antitone at `a` is strictly antitone at `a`. -/
theorem StrictAntiAt.congr_of_eventuallyEq {f g : α → β} {a : α} (hf : StrictAntiAt f a)
    (hfg : f =ᶠ[𝓝 a] g) : StrictAntiAt g a := by
  obtain ⟨t, ht, hf⟩ := hf
  exact ⟨t ∩ {x | f x = g x}, inter_mem ht hfg, (hf.mono inter_subset_left).congr fun _ hx ↦ hx.2⟩

end Defs

end TauCeti

section Intro

variable {α β : Type*} [TopologicalSpace α] [Preorder α] [Preorder β] {f : α → β} {s : Set α}
  {a : α}

/-- A function strictly monotone on a neighbourhood of `a` is strictly monotone at `a`. -/
theorem StrictMonoOn.strictMonoAt (hf : StrictMonoOn f s) (hs : s ∈ 𝓝 a) :
    TauCeti.StrictMonoAt f a :=
  ⟨s, hs, hf⟩

/-- A function strictly antitone on a neighbourhood of `a` is strictly antitone at `a`. -/
theorem StrictAntiOn.strictAntiAt (hf : StrictAntiOn f s) (hs : s ∈ 𝓝 a) :
    TauCeti.StrictAntiAt f a :=
  ⟨s, hs, hf⟩

/-- A strictly monotone function is strictly monotone at every point. -/
theorem StrictMono.strictMonoAt (hf : StrictMono f) (a : α) : TauCeti.StrictMonoAt f a :=
  hf.strictMonoOn univ |>.strictMonoAt univ_mem

/-- A strictly antitone function is strictly antitone at every point. -/
theorem StrictAnti.strictAntiAt (hf : StrictAnti f) (a : α) : TauCeti.StrictAntiAt f a :=
  hf.strictAntiOn univ |>.strictAntiAt univ_mem

/-- Functions equal near `a` are both or neither strictly monotone at `a`. -/
theorem Filter.EventuallyEq.strictMonoAt_iff {g : α → β} (hfg : f =ᶠ[𝓝 a] g) :
    TauCeti.StrictMonoAt f a ↔ TauCeti.StrictMonoAt g a :=
  ⟨(·.congr_of_eventuallyEq hfg), (·.congr_of_eventuallyEq hfg.symm)⟩

/-- Functions equal near `a` are both or neither strictly antitone at `a`. -/
theorem Filter.EventuallyEq.strictAntiAt_iff {g : α → β} (hfg : f =ᶠ[𝓝 a] g) :
    TauCeti.StrictAntiAt f a ↔ TauCeti.StrictAntiAt g a :=
  ⟨(·.congr_of_eventuallyEq hfg), (·.congr_of_eventuallyEq hfg.symm)⟩

end Intro

namespace TauCeti

variable {α β γ : Type*}

section Comp

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β] [Preorder γ]
  {h : β → γ} {τ : α → β} {a : α}

/-- The composite of a function strictly monotone at `τ a` with a function `τ` continuous and
strictly monotone at `a` is strictly monotone at `a`. -/
theorem StrictMonoAt.comp (hh : StrictMonoAt h (τ a)) (hτ : StrictMonoAt τ a)
    (hτc : ContinuousAt τ a) : StrictMonoAt (h ∘ τ) a := by
  obtain ⟨⟨V, hV, hhV⟩, ⟨W, hW, hτW⟩⟩ := And.intro hh hτ
  exact (hhV.comp (hτW.mono inter_subset_left) fun _ hx ↦ hx.2).strictMonoAt
    (inter_mem hW (hτc.preimage_mem_nhds hV))

/-- The composite of a function strictly monotone at `τ a` with a function `τ` continuous and
strictly antitone at `a` is strictly antitone at `a`. -/
theorem StrictMonoAt.comp_strictAntiAt (hh : StrictMonoAt h (τ a)) (hτ : StrictAntiAt τ a)
    (hτc : ContinuousAt τ a) : StrictAntiAt (h ∘ τ) a := by
  obtain ⟨⟨V, hV, hhV⟩, ⟨W, hW, hτW⟩⟩ := And.intro hh hτ
  exact (hhV.comp_strictAntiOn (hτW.mono inter_subset_left) fun _ hx ↦ hx.2).strictAntiAt
    (inter_mem hW (hτc.preimage_mem_nhds hV))

/-- The composite of a function strictly antitone at `τ a` with a function `τ` continuous and
strictly monotone at `a` is strictly antitone at `a`. -/
theorem StrictAntiAt.comp_strictMonoAt (hh : StrictAntiAt h (τ a)) (hτ : StrictMonoAt τ a)
    (hτc : ContinuousAt τ a) : StrictAntiAt (h ∘ τ) a := by
  obtain ⟨⟨V, hV, hhV⟩, ⟨W, hW, hτW⟩⟩ := And.intro hh hτ
  exact (hhV.comp_strictMonoOn (hτW.mono inter_subset_left) fun _ hx ↦ hx.2).strictAntiAt
    (inter_mem hW (hτc.preimage_mem_nhds hV))

/-- The composite of a function strictly antitone at `τ a` with a function `τ` continuous and
strictly antitone at `a` is strictly monotone at `a`. -/
theorem StrictAntiAt.comp (hh : StrictAntiAt h (τ a)) (hτ : StrictAntiAt τ a)
    (hτc : ContinuousAt τ a) : StrictMonoAt (h ∘ τ) a := by
  obtain ⟨⟨V, hV, hhV⟩, ⟨W, hW, hτW⟩⟩ := And.intro hh hτ
  exact (hhV.comp (hτW.mono inter_subset_left) fun _ hx ↦ hx.2).strictMonoAt
    (inter_mem hW (hτc.preimage_mem_nhds hV))

end Comp

/-- A function continuous and injective on a neighbourhood of `a` is strictly monotone or
strictly antitone at `a`. -/
theorem strictMonoAt_or_strictAntiAt [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] [LinearOrder β] [TopologicalSpace β]
    [OrderClosedTopology β] {f : α → β} {a : α} {s : Set α} (hs : s ∈ 𝓝 a)
    (hc : ContinuousOn f s) (hi : InjOn f s) : StrictMonoAt f a ∨ StrictAntiAt f a := by
  obtain ⟨b, c, hbc, hI, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hs
  exact ((hc.mono hsub).strictMonoOn_of_injOn_Icc' (hbc.1.trans hbc.2) (hi.mono hsub)).imp
    (·.strictMonoAt hI) (·.strictAntiAt hI)

/-- A function is not both strictly monotone and strictly antitone at a point that is not
isolated. -/
theorem not_strictMonoAt_and_strictAntiAt [LinearOrder α] [TopologicalSpace α] [Preorder β]
    {f : α → β} {a : α} [(𝓝[≠] a).NeBot] : ¬(StrictMonoAt f a ∧ StrictAntiAt f a) := by
  rintro ⟨hm, ha⟩
  obtain ⟨s, hs, hm⟩ := strictMonoAt_iff.1 hm
  obtain ⟨t, ht, ha⟩ := strictAntiAt_iff.1 ha
  -- A point of `s ∩ t` other than `a` makes `s ∩ t` nontrivial.
  have hst' : s ∩ t ∩ {a}ᶜ ∈ 𝓝[≠] a :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (inter_mem hs ht)) self_mem_nhdsWithin
  obtain ⟨x, hx, hxa⟩ := Filter.nonempty_of_mem hst'
  have hst : (s ∩ t).Nontrivial := ⟨a, mem_of_mem_nhds (inter_mem hs ht), x, hx, Ne.symm hxa⟩
  exact hst.not_strictMonoOn_and_strictAntiOn
    ⟨hm.mono inter_subset_left, ha.mono inter_subset_right⟩

/-- **The direction of a composite.** If `g = h ∘ τ` near `a`, and `τ` at `a` and `h` at `τ a`
are each strictly monotone or strictly antitone, then `g` is strictly monotone at `a` exactly when
`h` and `τ` have the same direction. -/
theorem strictMonoAt_iff_of_eventuallyEq_comp [LinearOrder α] [TopologicalSpace α]
    [LinearOrder β] [TopologicalSpace β] [Preorder γ] {g : α → γ} {h : β → γ} {τ : α → β} {a : α}
    [(𝓝[≠] a).NeBot] [(𝓝[≠] τ a).NeBot] (hg : g =ᶠ[𝓝 a] h ∘ τ) (hτc : ContinuousAt τ a)
    (hτ : StrictMonoAt τ a ∨ StrictAntiAt τ a) (hh : StrictMonoAt h (τ a) ∨ StrictAntiAt h (τ a)) :
    StrictMonoAt g a ↔ (StrictMonoAt h (τ a) ↔ StrictMonoAt τ a) := by
  rw [hg.strictMonoAt_iff]
  have hgτ := not_strictMonoAt_and_strictAntiAt (f := τ) (a := a)
  have hgh := not_strictMonoAt_and_strictAntiAt (f := h) (a := τ a)
  have hgg := not_strictMonoAt_and_strictAntiAt (f := h ∘ τ) (a := a)
  rcases hh with hh | hh <;> rcases hτ with hτ | hτ
  · have := hh.comp hτ hτc
    tauto
  · have := hh.comp_strictAntiAt hτ hτc
    tauto
  · have := hh.comp_strictMonoAt hτ hτc
    tauto
  · have := hh.comp hτ hτc
    tauto

end TauCeti
