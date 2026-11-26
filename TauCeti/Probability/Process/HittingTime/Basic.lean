/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Basic properties of hitting times

General order-theoretic and set-theoretic properties of Mathlib's `MeasureTheory.hittingAfter` for
arbitrary processes, without measurability, filtration, or topological assumptions.

In particular, post-composing a process with a state-space map `f` pulls back the target set in
`hittingAfter` (`MeasureTheory.hittingAfter_comp`), and whenever `f` maps `s` into `t`, the
post-composed process hits `t` no later than the original process hits `s`
(`Set.MapsTo.hittingAfter_comp_le`).
-/

public section

namespace MeasureTheory

/-- Hitting a set `t` after time `n` along a post-composed process `i ↦ f (u i ·)` is the same
as hitting the preimage `f ⁻¹' t` after time `n` along `u`. -/
theorem hittingAfter_comp {ι Ω α β : Type*} [Preorder ι] [InfSet ι] (u : ι → Ω → α)
    (f : α → β) (t : Set β) (n : ι) :
    hittingAfter (fun i ω => f (u i ω)) t n = hittingAfter u (f ⁻¹' t) n :=
  rfl

end MeasureTheory

/-- If `f` maps `s` into `t`, then the post-composed process `i ↦ f (u i ·)` hits `t` after time
`n` no later than `u` hits `s` after time `n`. -/
theorem Set.MapsTo.hittingAfter_comp_le {ι Ω α β : Type*} [ConditionallyCompleteLinearOrder ι]
    {f : α → β} {s : Set α} {t : Set β} (hf : Set.MapsTo f s t) (u : ι → Ω → α) (n : ι) :
    MeasureTheory.hittingAfter (fun i ω => f (u i ω)) t n ≤
      MeasureTheory.hittingAfter u s n := by
  rw [MeasureTheory.hittingAfter_comp]
  exact MeasureTheory.hittingAfter_anti u n hf.subset_preimage
