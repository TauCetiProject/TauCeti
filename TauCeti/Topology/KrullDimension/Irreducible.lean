/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Proper closed subsets of irreducible spaces have smaller Krull dimension

If `Y` is an irreducible topological space and `Z ⊆ Y` is a closed subset different from `Y`,
then `topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y`. Every chain of irreducible closed
subsets of `Z` is a chain of irreducible closed subsets of `Y` whose members lie in `Z`, and the
whole space `Y`, which is irreducible and closed, strictly contains all of them, so it extends
the chain by one. When the Krull dimension of `Y` is finite this is the strict inequality
`topologicalKrullDim Z < topologicalKrullDim Y`.

The argument only uses that the closure of the image of `Z` is not all of `Y`, so it is stated
for an inducing map `f : X → Y` with non-dense range. The set-level form concerns a closed subset
`Z` of an ambient space strictly contained in an irreducible subset `Y`.

In the other extreme, an irreducible `T₀` space has Krull dimension zero exactly when it has at
most one point: in dimension zero the closure of every point is a maximal irreducible closed
subset, hence the whole space, and in a `T₀` space two points with the same closure coincide.

## Main declarations

* `Topology.IsInducing.topologicalKrullDim_add_one_le`: if `f : X → Y` is inducing with
  non-dense range and `Y` is irreducible, then `topologicalKrullDim X + 1 ≤ topologicalKrullDim Y`.
* `Topology.IsInducing.topologicalKrullDim_lt`: the strict inequality for such a map, when the
  Krull dimension of the target is finite.
* `IsClosed.topologicalKrullDim_add_one_le`: a proper closed subset `Z` of an
  irreducible space `Y` satisfies `topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y`.
* `IsClosed.topologicalKrullDim_lt`: the strict inequality, when the Krull dimension
  of `Y` is finite.
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

/-- If `f : X → Y` is inducing with non-dense range and `Y` is irreducible, then
`topologicalKrullDim X + 1 ≤ topologicalKrullDim Y`: the irreducible closed subsets of `X` map
strictly monotonically to irreducible closed subsets of `Y` contained in the closure of the
range, and `Y` itself lies strictly above all of them. -/
theorem topologicalKrullDim_add_one_le [IrreducibleSpace Y] {f : X → Y} (hf : IsInducing f)
    (hf' : ¬DenseRange f) : topologicalKrullDim X + 1 ≤ topologicalKrullDim Y := by
  cases isEmpty_or_nonempty (IrreducibleCloseds X)
  · simp [topologicalKrullDim, krullDim_eq_bot]
  let top : IrreducibleCloseds Y := ⟨univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hlt (T : IrreducibleCloseds X) : T.map f hf.continuous < top := by
    refine lt_of_le_of_ne (subset_univ _) fun h ↦ hf' ?_
    rw [DenseRange, dense_iff_closure_eq, ← univ_subset_iff]
    exact (congrArg SetLike.coe h).symm.subset.trans (closure_mono (image_subset_range f T))
  rw [topologicalKrullDim, ← krullDim_WithTop]
  refine krullDim_le_of_strictMono
    (fun T ↦ (T.map (IrreducibleCloseds.map f hf.continuous)).untopD top) ?_
  exact WithTop.strictMono_iff.mpr
    ⟨by simpa using IrreducibleCloseds.map_strictMono_of_isInducing hf, by simpa using hlt⟩

/-- If `f : X → Y` is inducing with non-dense range and `Y` is irreducible of finite Krull
dimension, then `topologicalKrullDim X < topologicalKrullDim Y`. -/
theorem topologicalKrullDim_lt [IrreducibleSpace Y] {f : X → Y} (hf : IsInducing f)
    (hf' : ¬DenseRange f) (hY : topologicalKrullDim Y ≠ ⊤) :
    topologicalKrullDim X < topologicalKrullDim Y := by
  have h := hf.topologicalKrullDim_add_one_le hf'
  cases hX : topologicalKrullDim X with
  | bot =>
    exact bot_lt_krullDim_iff.mpr
      ⟨⟨univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩⟩
  | coe n =>
    cases n with
    | top => simp_all
    | coe n => exact ENat.WithBot.add_one_le_iff.mp (by simpa [hX] using h)

end Topology.IsInducing

namespace IsClosed

variable {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y] {Z : Set Y}

/-- A proper closed subset `Z` of an irreducible space `Y` satisfies
`topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y`. -/
theorem topologicalKrullDim_add_one_le (hZ : IsClosed Z) (hZY : Z ≠ univ) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y :=
  IsInducing.subtypeVal.topologicalKrullDim_add_one_le fun h ↦
    hZY <| hZ.closure_eq ▸ dense_iff_closure_eq.mp (denseRange_subtype_val.mp h)

/-- A proper closed subset `Z` of an irreducible space `Y` of finite Krull dimension has
strictly smaller Krull dimension than `Y`. -/
theorem topologicalKrullDim_lt (hZ : IsClosed Z) (hZY : Z ≠ univ)
    (hY : topologicalKrullDim Y ≠ ⊤) : topologicalKrullDim Z < topologicalKrullDim Y :=
  IsInducing.subtypeVal.topologicalKrullDim_lt (fun h ↦
    hZY <| hZ.closure_eq ▸ dense_iff_closure_eq.mp (denseRange_subtype_val.mp h)) hY

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
of finite Krull dimension has strictly smaller Krull dimension than `Y`. The set `Y` need not be
closed. -/
theorem topologicalKrullDim_lt (hY : IsIrreducible Y) (hZ : IsClosed Z) (hZY : Z ⊂ Y)
    (hYd : topologicalKrullDim Y ≠ ⊤) : topologicalKrullDim Z < topologicalKrullDim Y :=
  haveI := Subtype.irreducibleSpace hY
  (IsEmbedding.inclusion hZY.subset).isInducing.topologicalKrullDim_lt (fun h ↦
    hZY.not_subset <| hZ.closure_eq ▸ (denseRange_inclusion_iff _).mp h) hYd

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
    have : Subsingleton (IrreducibleCloseds X) := ⟨fun Z W ↦ IrreducibleCloseds.ext <|
      (Z.isIrreducible.nonempty.eq_univ).trans W.isIrreducible.nonempty.eq_univ.symm⟩
    have : Nonempty (IrreducibleCloseds X) := ⟨top⟩
    exact krullDim_eq_zero

end TauCeti
