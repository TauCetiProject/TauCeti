/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Basic properties and composition identities for hitting times

General order-theoretic and set-theoretic properties of Mathlib's `MeasureTheory.hittingAfter` for
arbitrary processes, without measurability, filtration, or topological assumptions.

Postcomposing a process `u` with a state-space map `f` pulls back the target set in
`MeasureTheory.hittingAfter` along `f` (`MeasureTheory.hittingAfter_comp`), and whenever `f` maps
`s` into `t`, the postcomposed process hits `t` no later than the original process hits `s`
(`Set.MapsTo.hittingAfter_comp_le`). Applying an injective map (such as `Subtype.val`) to the
state space preserves the hitting time of a singleton.

## Main statements

* `MeasureTheory.hittingAfter_comp`: postcomposing the process pulls back the target set.
* `Set.MapsTo.hittingAfter_comp_le`: monotonicity under `Set.MapsTo`.
* `Function.Injective.hittingAfter_singleton`: singleton hitting times under injective state
  maps.
-/

public section

namespace MeasureTheory

section Composition

variable {ι Ω α β : Type*} [Preorder ι] [InfSet ι]

/-- Hitting a set `t` after time `n` along a post-composed process `i ↦ f (u i ·)` is the same
as hitting the preimage `f ⁻¹' t` after time `n` along `u`. -/
theorem hittingAfter_comp (u : ι → Ω → α) (f : α → β) (t : Set β) (n : ι) :
    hittingAfter (fun i ω => f (u i ω)) t n = hittingAfter u (f ⁻¹' t) n :=
  rfl

/-- Applying an injective map to the values of a process preserves the hitting time of the image
singleton. -/
theorem _root_.Function.Injective.hittingAfter_singleton {f : α → β} (hf : Function.Injective f)
    (u : ι → Ω → α) (x : α) (n : ι) :
    hittingAfter (fun i ω => f (u i ω)) {f x} n = hittingAfter u {x} n := by
  rw [hittingAfter_comp, ← Set.image_singleton, hf.preimage_image]

end Composition

end MeasureTheory

/-- If `f` maps `s` into `t`, then the post-composed process `i ↦ f (u i ·)` hits `t` after time
`n` no later than `u` hits `s` after time `n`. -/
theorem Set.MapsTo.hittingAfter_comp_le {ι Ω α β : Type*} [ConditionallyCompleteLinearOrder ι]
    {f : α → β} {s : Set α} {t : Set β} (hf : Set.MapsTo f s t) (u : ι → Ω → α) (n : ι) :
    MeasureTheory.hittingAfter (fun i ω => f (u i ω)) t n ≤
      MeasureTheory.hittingAfter u s n := by
  rw [MeasureTheory.hittingAfter_comp]
  exact MeasureTheory.hittingAfter_anti u n hf.subset_preimage
