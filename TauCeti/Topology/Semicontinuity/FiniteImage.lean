/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Semicontinuity for maps with finite image on a neighbourhood

For a product-valued function `f : α → ∀ i, β i` into linearly ordered codomains that takes
finitely many distinct product values on a neighbourhood of `x` (or on a relative neighbourhood of
`x` within `s`), coordinatewise upper semicontinuity forces `f x' ≤ f x` eventually near `x`
without any ordering on the index type `ι`
(`TauCeti.eventually_le_of_upperSemicontinuousWithinAt_of_finite_image_on_nhdsWithin`,
`TauCeti.eventually_le_of_upperSemicontinuousAt_of_finite_image_on_nhds`), and dually for lower
semicontinuity
(`TauCeti.eventually_ge_of_lowerSemicontinuousWithinAt_of_finite_image_on_nhdsWithin`,
`TauCeti.eventually_ge_of_lowerSemicontinuousAt_of_finite_image_on_nhds`). Consequently,
post-composing such a map with any monotone map into a preorder preserves upper and lower
semicontinuity at all four scopes
(`Monotone.upperSemicontinuousWithinAt_comp_of_finite_image_on_nhdsWithin`,
`Monotone.upperSemicontinuousAt_comp_of_finite_image_on_nhds`,
`Monotone.upperSemicontinuousOn_comp_of_finite_image_on_nhdsWithin`,
`Monotone.upperSemicontinuous_comp_of_finite_image_on_nhds`,
`Monotone.lowerSemicontinuousWithinAt_comp_of_finite_image_on_nhdsWithin`,
`Monotone.lowerSemicontinuousAt_comp_of_finite_image_on_nhds`,
`Monotone.lowerSemicontinuousOn_comp_of_finite_image_on_nhdsWithin`,
`Monotone.lowerSemicontinuous_comp_of_finite_image_on_nhds`). In particular, for a well-ordered
index type `ι` (with `Mathlib.Order.PiLex`), composing with `toLex` yields semicontinuity into
`Lex (∀ i, β i)` directly via
`Pi.toLex_monotone.<scope>_comp_of_finite_image_on_nhds<Within> hf hfin`.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *$\mathbb{Q}$-universal
  desingularization*, Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

open Filter Set Topology

namespace TauCeti

section Eventually

variable {α ι : Type*} {β : ι → Type*} [TopologicalSpace α] [∀ i, LinearOrder (β i)]

/-- If each coordinate of `f` is upper semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `f x' ≤ f x` eventually in `𝓝[s] x`. -/
theorem eventually_le_of_upperSemicontinuousWithinAt_of_finite_image_on_nhdsWithin
    {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝[s] x, f x' ≤ f x := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  obtain ⟨u, hu, hufin⟩ := hfin
  have hV : {v ∈ f '' u | ¬ v ≤ f x}.Finite := hufin.subset (sep_subset _ _)
  have hex : ∃ᶠ x' in 𝓝[s] x, ∃ v ∈ {v ∈ f '' u | ¬ v ≤ f x}, f x' = v :=
    (hnot.and_eventually hu).mono fun x' ⟨hnotle, hx'⟩ ↦ ⟨f x', ⟨⟨x', hx', rfl⟩, hnotle⟩, rfl⟩
  obtain ⟨v, ⟨-, hnotle⟩, hvfreq⟩ := hV.frequently_exists.mp hex
  exact hnotle fun i ↦
    (hf i).frequently (v i) (hvfreq.mono fun _ hx' ↦ (congr_fun hx' i).symm.le)

/-- If each coordinate of `f` is upper semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `f x' ≤ f x` eventually in `𝓝 x`. -/
theorem eventually_le_of_upperSemicontinuousAt_of_finite_image_on_nhds
    {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, UpperSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝 x, f x' ≤ f x := by
  rw [← nhdsWithin_univ]
  refine eventually_le_of_upperSemicontinuousWithinAt_of_finite_image_on_nhdsWithin
    (fun i ↦ (hf i).upperSemicontinuousWithinAt univ) ?_
  rwa [nhdsWithin_univ]

/-- If each coordinate of `f` is lower semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `f x ≤ f x'` eventually in `𝓝[s] x`. -/
theorem eventually_ge_of_lowerSemicontinuousWithinAt_of_finite_image_on_nhdsWithin
    {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝[s] x, f x ≤ f x' :=
  eventually_le_of_upperSemicontinuousWithinAt_of_finite_image_on_nhdsWithin
    (β := fun i ↦ (β i)ᵒᵈ) hf hfin

/-- If each coordinate of `f` is lower semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `f x ≤ f x'` eventually in `𝓝 x`. -/
theorem eventually_ge_of_lowerSemicontinuousAt_of_finite_image_on_nhds
    {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, LowerSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    ∀ᶠ x' in 𝓝 x, f x ≤ f x' :=
  eventually_le_of_upperSemicontinuousAt_of_finite_image_on_nhds
    (β := fun i ↦ (β i)ᵒᵈ) hf hfin

end Eventually

end TauCeti

section MonotoneComp

variable {α ι γ : Type*} {β : ι → Type*} [TopologicalSpace α] [∀ i, LinearOrder (β i)]
  [Preorder γ]

/-- Post-composing a coordinatewise upper semicontinuous map `f` taking finitely many distinct
product values on a neighbourhood of `x` within `s` with a monotone map preserves
`UpperSemicontinuousWithinAt`. -/
theorem Monotone.upperSemicontinuousWithinAt_comp_of_finite_image_on_nhdsWithin
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousWithinAt (fun x' ↦ g (f x')) s x := fun _ hy ↦
  (TauCeti.eventually_le_of_upperSemicontinuousWithinAt_of_finite_image_on_nhdsWithin
    hf hfin).mono fun _ hx' ↦ (hg hx').trans_lt hy

/-- Post-composing a coordinatewise upper semicontinuous map `f` taking finitely many distinct
product values on a neighbourhood of `x` with a monotone map preserves
`UpperSemicontinuousAt`. -/
theorem Monotone.upperSemicontinuousAt_comp_of_finite_image_on_nhds
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, UpperSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuousAt (fun x' ↦ g (f x')) x := fun _ hy ↦
  (TauCeti.eventually_le_of_upperSemicontinuousAt_of_finite_image_on_nhds hf hfin).mono
    fun _ hx' ↦ (hg hx').trans_lt hy

/-- Post-composing a coordinatewise upper semicontinuous map `f` taking finitely many distinct
product values on a relative neighbourhood within `s` of each point of `s` with a monotone map
preserves `UpperSemicontinuousOn`. -/
theorem Monotone.upperSemicontinuousOn_comp_of_finite_image_on_nhdsWithin
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, UpperSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousOn (fun x' ↦ g (f x')) s :=
  fun x hx ↦
    hg.upperSemicontinuousWithinAt_comp_of_finite_image_on_nhdsWithin
      (fun i ↦ hf i x hx) (hfin x hx)

/-- Post-composing a coordinatewise upper semicontinuous map `f` taking finitely many distinct
product values on a neighbourhood of each point with a monotone map preserves
`UpperSemicontinuous`. -/
theorem Monotone.upperSemicontinuous_comp_of_finite_image_on_nhds
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i}
    (hf : ∀ i, UpperSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuous (fun x' ↦ g (f x')) :=
  fun x ↦ hg.upperSemicontinuousAt_comp_of_finite_image_on_nhds (fun i ↦ hf i x) (hfin x)

/-- Post-composing a coordinatewise lower semicontinuous map `f` taking finitely many distinct
product values on a neighbourhood of `x` within `s` with a monotone map preserves
`LowerSemicontinuousWithinAt`. -/
theorem Monotone.lowerSemicontinuousWithinAt_comp_of_finite_image_on_nhdsWithin
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousWithinAt (fun x' ↦ g (f x')) s x :=
  Monotone.upperSemicontinuousWithinAt_comp_of_finite_image_on_nhdsWithin
    (β := fun i ↦ (β i)ᵒᵈ) (γ := γᵒᵈ) hg.dual hf hfin

/-- Post-composing a coordinatewise lower semicontinuous map `f` taking finitely many distinct
product values on a neighbourhood of `x` with a monotone map preserves
`LowerSemicontinuousAt`. -/
theorem Monotone.lowerSemicontinuousAt_comp_of_finite_image_on_nhds
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, LowerSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuousAt (fun x' ↦ g (f x')) x :=
  Monotone.upperSemicontinuousAt_comp_of_finite_image_on_nhds
    (β := fun i ↦ (β i)ᵒᵈ) (γ := γᵒᵈ) hg.dual hf hfin

/-- Post-composing a coordinatewise lower semicontinuous map `f` taking finitely many distinct
product values on a relative neighbourhood within `s` of each point of `s` with a monotone map
preserves `LowerSemicontinuousOn`. -/
theorem Monotone.lowerSemicontinuousOn_comp_of_finite_image_on_nhdsWithin
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, LowerSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousOn (fun x' ↦ g (f x')) s :=
  Monotone.upperSemicontinuousOn_comp_of_finite_image_on_nhdsWithin
    (β := fun i ↦ (β i)ᵒᵈ) (γ := γᵒᵈ) hg.dual hf hfin

/-- Post-composing a coordinatewise lower semicontinuous map `f` taking finitely many distinct
product values on a neighbourhood of each point with a monotone map preserves
`LowerSemicontinuous`. -/
theorem Monotone.lowerSemicontinuous_comp_of_finite_image_on_nhds
    {g : (∀ i, β i) → γ} (hg : Monotone g) {f : α → ∀ i, β i}
    (hf : ∀ i, LowerSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuous (fun x' ↦ g (f x')) :=
  Monotone.upperSemicontinuous_comp_of_finite_image_on_nhds
    (β := fun i ↦ (β i)ᵒᵈ) (γ := γᵒᵈ) hg.dual hf hfin

end MonotoneComp
