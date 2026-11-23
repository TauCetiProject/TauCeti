/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Sets preconnected at infinity inside a set

A set `E` is preconnected at infinity inside a set `S` if, outside each bounded set, `S`
contains a preconnected set containing every point of `E` far enough out.  This is the
connectedness of an end of a domain that a crosscut argument needs: a preconnected set avoiding
a bounded crosscut lies on one side of it.

## Main definitions

* `TauCeti.IsPreconnectedAtInfinityIn`: `E` is preconnected at infinity inside `S`.

## Main results

* `TauCeti.IsPreconnectedAtInfinityIn.image`: the notion is preserved by images under continuous
  maps that tend to infinity at infinity and map bounded sets to bounded sets.
* `TauCeti.IsPreconnectedAtInfinityIn.preimage_div_sub`: in a normed division ring, the notion is
  invariant under the affine change of coordinates `w ↦ (w - c) / b`.
-/

public section

open Bornology Filter Function Set

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [Bornology α] {S T E E' : Set α}

/-- A set `E` is *preconnected at infinity inside* `S` if, for every bounded set `B`, some
preconnected subset of `S` disjoint from `B` contains every point of `E` far enough out. -/
def IsPreconnectedAtInfinityIn (S E : Set α) : Prop :=
  ∀ B : Set α, IsBounded B → ∃ C ⊆ S, IsPreconnected C ∧ Disjoint C B ∧
    ∀ᶠ w in cobounded α, w ∈ E → w ∈ C

/-- Unfolding `TauCeti.IsPreconnectedAtInfinityIn`. -/
theorem isPreconnectedAtInfinityIn_iff :
    IsPreconnectedAtInfinityIn S E ↔ ∀ B : Set α, IsBounded B → ∃ C ⊆ S, IsPreconnected C ∧
      Disjoint C B ∧ ∀ᶠ w in cobounded α, w ∈ E → w ∈ C :=
  Iff.rfl

/-- Being preconnected at infinity inside `S` is inherited by every superset of `S`. -/
theorem IsPreconnectedAtInfinityIn.mono (hE : IsPreconnectedAtInfinityIn S E) (hST : S ⊆ T) :
    IsPreconnectedAtInfinityIn T E := fun B hB =>
  let ⟨C, hCS, hC⟩ := hE B hB
  ⟨C, hCS.trans hST, hC⟩

/-- Being preconnected at infinity inside `S` is inherited by every subset of `E`. -/
theorem IsPreconnectedAtInfinityIn.subset (hE : IsPreconnectedAtInfinityIn S E) (h : E' ⊆ E) :
    IsPreconnectedAtInfinityIn S E' := fun B hB => by
  obtain ⟨C, hCS, hCc, hCB, hEC⟩ := hE B hB
  exact ⟨C, hCS, hCc, hCB, hEC.mono fun w hw hw' => hw (h hw')⟩

/-- Being preconnected at infinity is preserved by images under a map `f` that is continuous on
`S`, tends to infinity at infinity, and maps bounded sets to bounded sets
(`comap f (cobounded β) ≤ cobounded α`). -/
theorem IsPreconnectedAtInfinityIn.image {β : Type*} [TopologicalSpace β] [Bornology β]
    (hE : IsPreconnectedAtInfinityIn S E) {f : α → β} (hf : ContinuousOn f S)
    (hf_tendsto : Tendsto f (cobounded α) (cobounded β))
    (hf_bdd : comap f (cobounded β) ≤ cobounded α) :
    IsPreconnectedAtInfinityIn (f '' S) (f '' E) := fun B hB => by
  have hB' : IsBounded (f ⁻¹' B) := by
    rw [isBounded_def, ← preimage_compl]
    exact hf_tendsto (isBounded_def.1 hB)
  obtain ⟨C, hCS, hCc, hCB, hEC⟩ := hE _ hB'
  -- far out in `β`, every preimage point lies far out in `α`, hence in `C` once it is in `E`
  obtain ⟨A, hA, hAEC⟩ := mem_comap.1 (hf_bdd hEC)
  refine ⟨f '' C, image_mono hCS, hCc.image f (hf.mono hCS), disjoint_image_left.2 hCB, ?_⟩
  filter_upwards [hA] with w hw
  rintro ⟨x, hxE, rfl⟩
  exact mem_image_of_mem f (hAEC hw hxE)

/-- In a normed division ring, being preconnected at infinity is invariant under the affine change
of coordinates `w ↦ (w - c) / b`. -/
theorem IsPreconnectedAtInfinityIn.preimage_div_sub {𝕜 : Type*} [NormedDivisionRing 𝕜]
    {S E : Set 𝕜} (hE : IsPreconnectedAtInfinityIn S E) {c b : 𝕜} (hb : b ≠ 0) :
    IsPreconnectedAtInfinityIn ((fun w => (w - c) / b) ⁻¹' S) ((fun w => (w - c) / b) ⁻¹' E) := by
  -- the preimages are the images under the inverse affine map `z ↦ z * b + c`
  have hl : LeftInverse (fun w => (w - c) / b) fun z => z * b + c := fun z => by
    simp [mul_div_cancel_right₀ _ hb]
  have hr : RightInverse (fun w => (w - c) / b) fun z => z * b + c := fun w => by
    simp [div_mul_cancel₀ _ hb]
  rw [← image_eq_preimage_of_inverse hl hr]
  refine hE.image (by fun_prop) ?_ ?_
  · simpa [Function.comp_def] using
      (tendsto_add_const_cobounded c).comp (tendsto_mul_right_cobounded hb)
  · -- `comap (· * b + c)` is `map ((· - c) / b)`, and `(· - c) / b` tends to infinity
    have hg : Tendsto (fun w => (w - c) / b) (cobounded 𝕜) (cobounded 𝕜) := by
      simpa [div_eq_mul_inv, Function.comp_def] using
        (tendsto_mul_right_cobounded (inv_ne_zero hb)).comp (tendsto_sub_const_cobounded c)
    exact (map_eq_comap_of_inverse hl.comp_eq_id hr.comp_eq_id).ge.trans hg

end TauCeti
