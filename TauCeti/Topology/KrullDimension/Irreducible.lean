/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.KrullDimension
public import TauCeti.Order.KrullDimension

/-!
# Proper closed subsets of irreducible spaces have smaller Krull dimension

If `Y` is an irreducible topological space and `Z ⊆ Y` is a closed subset different from `Y`,
then `topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y`. Every chain of irreducible closed
subsets of `Z` is a chain of irreducible closed subsets of `Y` whose members lie in `Z`, and the
whole space `Y`, which is irreducible and closed, strictly contains all of them, so it extends
the chain by one. When the Krull dimension of `Z` is finite this is the strict inequality
`topologicalKrullDim Z < topologicalKrullDim Y`; this holds in particular when the Krull
dimension of `Y` is finite.

The argument only uses that the closure of the image of `Z` is not all of `Y`, so it is stated
for an inducing map `f : X → Y` with non-dense range. The set-level form concerns a closed subset
`Z` of an ambient space strictly contained in an irreducible subset `Y`. Irreducibility of `Y` is
not needed either: for an arbitrary space `Y`, it is enough that the closure of the range of `f`
contain no irreducible component of `Y`, since the closure of the image of the last member of a
chain lies in some irreducible component, which then extends the chain. This is the form that
applies to a nowhere dense closed subset of a reducible scheme, such as the centre of a
modification.

In the other extreme, an irreducible `T₀` space has Krull dimension zero exactly when it has at
most one point: in dimension zero the closure of every point is a maximal irreducible closed
subset, hence the whole space, and in a `T₀` space two points with the same closure coincide.

## Main declarations

* `Topology.IsInducing.topologicalKrullDim_add_one_le_of_forall_not_subset`: if `f : X → Y` is
  inducing and no irreducible component of `Y` lies in the closure of its range, then
  `topologicalKrullDim X + 1 ≤ topologicalKrullDim Y`.
* `Topology.IsInducing.topologicalKrullDim_add_one_le`: if `f : X → Y` is inducing with
  non-dense range and `Y` is irreducible, then `topologicalKrullDim X + 1 ≤ topologicalKrullDim Y`.
* `Topology.IsInducing.topologicalKrullDim_lt`: the strict inequality for such a map, when the
  Krull dimension of the source is finite.
* `IsClosed.topologicalKrullDim_add_one_le`: a proper closed subset `Z` of an
  irreducible space `Y` satisfies `topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y`.
* `IsClosed.topologicalKrullDim_lt`: the strict inequality, when the Krull dimension
  of `Z` is finite.
* `IsIrreducible.topologicalKrullDim_add_one_le`, `IsIrreducible.topologicalKrullDim_lt`: the
  same statements for a closed subset strictly contained in an irreducible subset of an ambient
  space.
* `TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton`: an irreducible `T₀` space has Krull
  dimension zero if and only if it is a subsingleton.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter I, Exercise 1.10(d).
-/

public section

open Order Set Topology TopologicalSpace

namespace Topology.IsInducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `f : X → Y` is inducing and the closure of its range contains no irreducible component of
`Y`, then `topologicalKrullDim X + 1 ≤ topologicalKrullDim Y`: the closure of the image of an
irreducible closed subset of `X` lies in an irreducible component of `Y`, which is strictly
larger. -/
theorem topologicalKrullDim_add_one_le_of_forall_not_subset {f : X → Y} (hf : IsInducing f)
    (hf' : ∀ C ∈ irreducibleComponents Y, ¬C ⊆ closure (range f)) :
    topologicalKrullDim X + 1 ≤ topologicalKrullDim Y := by
  refine Order.krullDim_add_one_le_of_strictMono _
    (IrreducibleCloseds.map_strictMono_of_isInducing hf) fun T hT ↦ ?_
  obtain ⟨C, hC, hTC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (T.map f hf.continuous).isIrreducible
  have hle : T.map f hf.continuous ≤ ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩ := hTC
  have hCT : C ⊆ closure (f '' T) := hT hle
  exact hf' C hC (hCT.trans (closure_mono (image_subset_range f T)))

/-- If `f : X → Y` is inducing with non-dense range and `Y` is irreducible, then
`topologicalKrullDim X + 1 ≤ topologicalKrullDim Y`. -/
theorem topologicalKrullDim_add_one_le [IrreducibleSpace Y] {f : X → Y} (hf : IsInducing f)
    (hf' : ¬DenseRange f) : topologicalKrullDim X + 1 ≤ topologicalKrullDim Y := by
  refine hf.topologicalKrullDim_add_one_le_of_forall_not_subset fun C hC hCf ↦ hf' ?_
  rw [irreducibleComponents_eq_singleton, mem_singleton_iff] at hC
  rw [DenseRange, dense_iff_closure_eq, ← univ_subset_iff, ← hC]
  exact hCf

/-- If `f : X → Y` is inducing with non-dense range, `Y` is irreducible and `X` has finite
Krull dimension, then `topologicalKrullDim X < topologicalKrullDim Y`. -/
theorem topologicalKrullDim_lt [IrreducibleSpace Y] {f : X → Y} (hf : IsInducing f)
    (hf' : ¬DenseRange f) (hX : topologicalKrullDim X ≠ ⊤) :
    topologicalKrullDim X < topologicalKrullDim Y := by
  have h := hf.topologicalKrullDim_add_one_le hf'
  cases hX' : topologicalKrullDim X with
  | bot =>
    exact bot_lt_krullDim_iff.mpr
      ⟨⟨univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩⟩
  | coe n =>
    cases n with
    | top => simp_all
    | coe n => exact ENat.WithBot.add_one_le_iff.mp (by simpa [hX'] using h)

end Topology.IsInducing

namespace IsClosed

variable {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y] {Z : Set Y}

/-- A proper closed subset `Z` of an irreducible space `Y` satisfies
`topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y`. -/
theorem topologicalKrullDim_add_one_le (hZ : IsClosed Z) (hZY : Z ≠ univ) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y :=
  IsInducing.subtypeVal.topologicalKrullDim_add_one_le fun h ↦
    hZY <| hZ.closure_eq ▸ dense_iff_closure_eq.mp (denseRange_subtypeVal.mp h)

/-- A proper closed subset `Z` of an irreducible space `Y` has strictly smaller Krull dimension
than `Y`, provided the Krull dimension of `Z` is finite. -/
theorem topologicalKrullDim_lt (hZ : IsClosed Z) (hZY : Z ≠ univ)
    (hZd : topologicalKrullDim Z ≠ ⊤) : topologicalKrullDim Z < topologicalKrullDim Y :=
  IsInducing.subtypeVal.topologicalKrullDim_lt (fun h ↦
    hZY <| hZ.closure_eq ▸ dense_iff_closure_eq.mp (denseRange_subtypeVal.mp h)) hZd

end IsClosed

namespace IsIrreducible

variable {X : Type*} [TopologicalSpace X] {Y Z : Set X}

/-- A closed subset `Z` of a topological space strictly contained in an irreducible subset `Y`
satisfies `topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y`. The set `Y` need not be closed. -/
theorem topologicalKrullDim_add_one_le (hY : IsIrreducible Y) (hZ : IsClosed Z) (hZY : Z ⊂ Y) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y :=
  haveI := Subtype.irreducibleSpace hY
  (IsEmbedding.inclusion hZY.subset).isInducing.topologicalKrullDim_add_one_le fun h ↦
    hZY.not_subset <| hZ.closure_eq ▸ (denseRange_inclusion_iff _).mp h

/-- A closed subset `Z` of a topological space strictly contained in an irreducible subset `Y`
has strictly smaller Krull dimension than `Y`, provided the Krull dimension of `Z` is finite. The
set `Y` need not be closed. -/
theorem topologicalKrullDim_lt (hY : IsIrreducible Y) (hZ : IsClosed Z) (hZY : Z ⊂ Y)
    (hZd : topologicalKrullDim Z ≠ ⊤) : topologicalKrullDim Z < topologicalKrullDim Y :=
  haveI := Subtype.irreducibleSpace hY
  (IsEmbedding.inclusion hZY.subset).isInducing.topologicalKrullDim_lt (fun h ↦
    hZY.not_subset <| hZ.closure_eq ▸ (denseRange_inclusion_iff _).mp h) hZd

end IsIrreducible

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]

/-- An irreducible `T₀` space has Krull dimension zero if and only if it has at most one point. -/
theorem topologicalKrullDim_eq_zero_iff_subsingleton [T0Space X] :
    topologicalKrullDim X = 0 ↔ Subsingleton X := by
  let top : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  constructor
  · intro h
    have hmax := krullDim_nonpos_iff_forall_isMax.mp h.le
    have hclosure (x : X) : closure {x} = univ := by
      let Z : IrreducibleCloseds X :=
        ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      exact univ_subset_iff.mp (hmax Z (b := top) (subset_univ _))
    exact ⟨fun x y ↦ (inseparable_iff_closure_eq.mpr ((hclosure x).trans (hclosure y).symm)).eq⟩
  · intro _
    have : Nonempty (IrreducibleCloseds X) := ⟨top⟩
    -- A subsingleton space is discrete, so its Krull dimension is at most zero.
    exact (topologicalKrullDim_zero_of_discreteTopology X).antisymm krullDim_nonneg

end TauCeti
