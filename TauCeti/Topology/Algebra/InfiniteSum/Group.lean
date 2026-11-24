/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Tail restriction of infinite products and sums in uniform groups

In a complete commutative uniform group, a family that is multipliable (or summable) outside a
finite index set `S` remains multipliable (or summable) outside any larger finite set `T ⊇ S`.

## Main results

* `TauCeti.multipliable_notMem_of_subset`, `TauCeti.summable_notMem_of_subset`: restricting a
  multipliable or summable family from `{i // i ∉ S}` to `{i // i ∉ T}` for `S ⊆ T`.
-/

public section

namespace TauCeti

/-- Multipliability outside a finite set `S` implies multipliability outside any larger finite set
`T ⊇ S`. -/
@[to_additive /-- Summability outside a finite set `S` implies summability outside any larger
finite set `T ⊇ S`. -/]
theorem multipliable_notMem_of_subset {ι α : Type*} [CommGroup α] [UniformSpace α]
    [IsUniformGroup α] [CompleteSpace α] {S T : Finset ι} (hST : S ⊆ T) (g : ι → α)
    (hconv : Multipliable fun i : {i // i ∉ S} ↦ g i.val) :
    Multipliable fun i : {i // i ∉ T} ↦ g i.val :=
  let incl : {i // i ∉ T} → {i // i ∉ S} := fun i ↦ ⟨i.val, fun h ↦ i.property (hST h)⟩
  hconv.comp_injective (i := incl) fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)

end TauCeti
