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
(`Set.MapsTo.hittingAfter_comp_le`). Precomposing the sample space pulls back `hittingAfter` along
the sample-space map (`MeasureTheory.hittingAfter_comp_right`), and applying an injective map
(such as `Subtype.val`) to the state space preserves the hitting time of a singleton.

## Main statements

* `MeasureTheory.hittingAfter_comp`: postcomposing the process pulls back the target set.
* `Set.MapsTo.hittingAfter_comp_le`: monotonicity under `Set.MapsTo`.
* `MeasureTheory.hittingAfter_comp_right`: precomposing the sample space precomposes
  `hittingAfter`.
* `Function.Injective.hittingAfter_singleton` and
  `MeasureTheory.hittingAfter_subtype_coe_singleton`: singleton hitting times under injective state
  maps and subtype inclusion.
* `MeasureTheory.hittingAfter_eval_comp` and
  `MeasureTheory.hittingAfter_eval_subtype_coe_singleton`: specialization to the coordinate process
  on trajectories.
-/

public section

namespace MeasureTheory

section Composition

variable {ι Ω Ω' α β : Type*} [Preorder ι] [InfSet ι]

/-- Hitting a set `t` after time `n` along a post-composed process `i ↦ f (u i ·)` is the same
as hitting the preimage `f ⁻¹' t` after time `n` along `u`. -/
theorem hittingAfter_comp (u : ι → Ω → α) (f : α → β) (t : Set β) (n : ι) :
    hittingAfter (fun i ω => f (u i ω)) t n = hittingAfter u (f ⁻¹' t) n :=
  rfl

/-- Precomposing the sample space with `g` precomposes `hittingAfter` with `g`. -/
theorem hittingAfter_comp_right (u : ι → Ω → α) (g : Ω' → Ω) (s : Set α) (n : ι) :
    hittingAfter (fun i ω' => u i (g ω')) s n = hittingAfter u s n ∘ g := by
  classical
  ext ω'
  simp only [hittingAfter_def, Function.comp_apply]

/-- Applying an injective map to the values of a process preserves the hitting time of the image
singleton. -/
theorem _root_.Function.Injective.hittingAfter_singleton {f : α → β} (hf : Function.Injective f)
    (u : ι → Ω → α) (x : α) (n : ι) :
    hittingAfter (fun i ω => f (u i ω)) {f x} n = hittingAfter u {x} n := by
  rw [hittingAfter_comp, ← Set.image_singleton, hf.preimage_image]

/-- Including a subtype-valued process into the ambient type preserves singleton hitting times. -/
theorem hittingAfter_subtype_coe_singleton {s : Set α} (u : ι → Ω → s) (x : s) (n : ι) :
    hittingAfter (fun i ω => (u i ω).val) {x.val} n = hittingAfter u {x} n :=
  Subtype.coe_injective.hittingAfter_singleton u x n

/-- Evaluating coordinate-process `hittingAfter` on a postcomposed trajectory `i ↦ f (ω i)` pulls
back the target set along `f`. -/
theorem hittingAfter_eval_comp (f : α → β) (t : Set β) (n : ι) (ω : ι → α) :
    hittingAfter (fun i w => w i) t n (fun i => f (ω i)) =
      hittingAfter (fun i w => w i) (f ⁻¹' t) n ω :=
  (congrFun (hittingAfter_comp_right (fun i (w : ι → β) => w i)
    (fun (w : ι → α) i => f (w i)) t n) ω).symm.trans
    (congrFun (hittingAfter_comp (fun i (w : ι → α) => w i) f t n) ω)

/-- Evaluating coordinate-process `hittingAfter` on an included subtype trajectory preserves
singleton hitting times. -/
theorem hittingAfter_eval_subtype_coe_singleton {s : Set α} (x : s) (n : ι) (ω : ι → s) :
    hittingAfter (fun i (w : ι → α) => w i) {x.val} n (fun i => (ω i).val) =
      hittingAfter (fun i w => w i) {x} n ω :=
  (congrFun (hittingAfter_comp_right (fun i (w : ι → α) => w i)
    (fun (w : ι → s) i => (w i).val) {x.val} n) ω).symm.trans
    (congrFun (hittingAfter_subtype_coe_singleton (fun i (w : ι → s) => w i) x n) ω)

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
