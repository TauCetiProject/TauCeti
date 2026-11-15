/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Composition identities for hitting times

Postcomposing a process `u` with a map `f` pulls back the target set in `MeasureTheory.hittingAfter`
along `f`, and precomposing the sample space pulls back `MeasureTheory.hittingAfter` along the
sample-space map. In particular, applying an injective map (such as `Subtype.val`) to the state
space preserves the hitting time of a singleton. No measurability, topology, or linear order is
required.

## Main statements

* `MeasureTheory.hittingAfter_comp`: postcomposing the process pulls back the target set.
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

variable {ι Ω Ω' α β : Type*} [Preorder ι] [InfSet ι]

/-- Postcomposing the values of a process with `f` pulls back the target set in `hittingAfter`. -/
theorem hittingAfter_comp (u : ι → Ω → α) (f : α → β) (t : Set β) (n : ι) :
    hittingAfter (fun i ω => f (u i ω)) t n = hittingAfter u (f ⁻¹' t) n := by
  classical
  ext ω
  simp only [hittingAfter_def, Set.mem_preimage]

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
      hittingAfter (fun i w => w i) {x} n ω := by
  rw [hittingAfter_eval_comp, ← Set.image_singleton, Subtype.coe_injective.preimage_image]

end MeasureTheory
