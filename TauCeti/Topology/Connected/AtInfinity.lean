/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

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

* `TauCeti.IsPreconnectedAtInfinityIn.preimage_homeomorph`: the notion is invariant under
  homeomorphisms that, together with their inverses, tend to infinity at infinity.
* `TauCeti.IsPreconnectedAtInfinityIn.preimage_div_sub`: in a normed division ring, the notion is
  invariant under the affine change of coordinates `w ↦ (w - c) / b`.
-/

public section

open Bornology Filter Set

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

/-- Being preconnected at infinity is preserved by preimages under a homeomorphism `φ` such that
both `φ` and its inverse tend to infinity at infinity. -/
theorem IsPreconnectedAtInfinityIn.preimage_homeomorph {β : Type*} [TopologicalSpace β]
    [Bornology β] {S E : Set β} (hE : IsPreconnectedAtInfinityIn S E) (φ : α ≃ₜ β)
    (hφ : Tendsto φ (cobounded α) (cobounded β))
    (hφ' : Tendsto φ.symm (cobounded β) (cobounded α)) :
    IsPreconnectedAtInfinityIn (φ ⁻¹' S) (φ ⁻¹' E) := fun B hB => by
  have hB' : IsBounded (φ.symm ⁻¹' B) := by
    rw [isBounded_def, ← preimage_compl]
    exact hφ' (isBounded_def.1 hB)
  obtain ⟨C, hCS, hCc, hCB, hEC⟩ := hE _ hB'
  refine ⟨φ ⁻¹' C, preimage_mono hCS, φ.isPreconnected_preimage.2 hCc, ?_, hφ.eventually hEC⟩
  exact disjoint_left.2 fun x hxC hxB => disjoint_left.1 hCB hxC (by simpa using hxB)

/-- In a normed division ring, being preconnected at infinity is invariant under the affine change
of coordinates `w ↦ (w - c) / b`. -/
theorem IsPreconnectedAtInfinityIn.preimage_div_sub {𝕜 : Type*} [NormedDivisionRing 𝕜]
    {S E : Set 𝕜} (hE : IsPreconnectedAtInfinityIn S E) {c b : 𝕜} (hb : b ≠ 0) :
    IsPreconnectedAtInfinityIn ((fun w => (w - c) / b) ⁻¹' S) ((fun w => (w - c) / b) ⁻¹' E) := by
  let ψ : 𝕜 ≃ₜ 𝕜 :=
    { toFun := fun w => (w - c) / b
      invFun := fun z => z * b + c
      left_inv := fun w => by simp [div_mul_cancel₀ _ hb]
      right_inv := fun z => by simp [mul_div_cancel_right₀ _ hb]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hψ : Tendsto ψ (cobounded 𝕜) (cobounded 𝕜) := by
    simpa [ψ, div_eq_mul_inv, Function.comp_def] using
      (tendsto_mul_right_cobounded (inv_ne_zero hb)).comp (tendsto_sub_const_cobounded c)
  have hψ' : Tendsto ψ.symm (cobounded 𝕜) (cobounded 𝕜) := by
    simpa [ψ, Function.comp_def] using
      (tendsto_add_const_cobounded c).comp (tendsto_mul_right_cobounded hb)
  exact hE.preimage_homeomorph ψ hψ hψ'

end TauCeti
