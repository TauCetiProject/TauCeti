/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# Sets preconnected at infinity inside a set

A set `E` is preconnected at infinity inside a set `S` if, outside each bounded set, `S`
contains a preconnected set containing every point of `E` far enough out.  This is the
connectedness of an end of a domain that a crosscut argument needs: a preconnected set avoiding
a bounded crosscut lies on one side of it.

## Main definitions

* `TauCeti.IsPreconnectedAtInfinityIn`: `E` is preconnected at infinity inside `S`.
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

end TauCeti
