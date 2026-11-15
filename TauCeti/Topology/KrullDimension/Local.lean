/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.KrullDimension.Basic

/-!
# Local Krull dimension of topological spaces

The local Krull dimension of a topological space at a point is the infimum of the Krull
dimensions of its open neighbourhoods. It is unchanged by passing through an open embedding,
and the dimension of the whole space is the supremum of its local dimensions.

This topological invariant is the local side of dimension theory for schemes. For a scheme
locally of finite type over a field, it is computed from the dimension of the local ring and
the transcendence degree of the residue field.

## Main declarations

* `TauCeti.topologicalKrullDimAt`: the local Krull dimension at a point.
* `TauCeti.iSup_topologicalKrullDimAt`: the global dimension is the supremum of the local
  dimensions.
* `Topology.IsOpenEmbedding.topologicalKrullDimAt_eq`: local dimension is invariant under open
  embeddings.
* `TauCeti.topologicalKrullDimAt_of_isHomeomorph`: local dimension is invariant under
  homeomorphisms.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
-/

public section

open Order Set Topology TopologicalSpace

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The local Krull dimension of `X` at `x` is the infimum of the dimensions of the open
neighbourhoods of `x`. -/
noncomputable def topologicalKrullDimAt (X : Type*) [TopologicalSpace X] (x : X) : WithBot ℕ∞ :=
  ⨅ U : {U : Set X // IsOpen U ∧ x ∈ U}, topologicalKrullDim U.1

/-- The local Krull dimension written as the infimum over open neighbourhoods. -/
theorem topologicalKrullDimAt_eq_iInf (x : X) :
    topologicalKrullDimAt X x =
      ⨅ U : {U : Set X // IsOpen U ∧ x ∈ U}, topologicalKrullDim U.1 :=
  (rfl)

/-- Local dimension is at most the dimension of any open neighbourhood. -/
theorem topologicalKrullDimAt_le_of_isOpen {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    topologicalKrullDimAt X x ≤ topologicalKrullDim U :=
  iInf_le _ (⟨U, hU, hx⟩ : {U : Set X // IsOpen U ∧ x ∈ U})

/-- Local dimension is at most global dimension. -/
theorem topologicalKrullDimAt_le (x : X) :
    topologicalKrullDimAt X x ≤ topologicalKrullDim X := by
  refine (topologicalKrullDimAt_le_of_isOpen isOpen_univ (mem_univ x)).trans_eq ?_
  exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq

/-- The local dimension at a point is nonnegative. -/
@[simp]
theorem topologicalKrullDimAt_nonneg (x : X) : 0 ≤ topologicalKrullDimAt X x := by
  refine le_iInf fun U ↦ ?_
  rw [topologicalKrullDim]
  exact krullDim_nonneg_iff.mpr
    ⟨⟨closure {⟨x, U.2.2⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

/-- The Krull dimension of a space is the supremum of its local Krull dimensions. -/
theorem iSup_topologicalKrullDimAt (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt X x := by
  refine le_antisymm (iSup_le fun p ↦ ?_) (iSup_le topologicalKrullDimAt_le)
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  refine le_iSup_of_le x (le_iInf fun U ↦ ?_)
  let f : U.1 → X := Subtype.val
  let q : LTSeries {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty} :=
    ⟨p.length, fun j ↦ ⟨p j, ⟨⟨x, U.2.2⟩, p.monotone (Fin.zero_le j) hx⟩⟩,
      fun j ↦ p.step j⟩
  exact (q.map _ (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f
    U.2.1.isOpenEmbedding_subtypeVal).symm.strictMono).length_le_krullDim

end TauCeti

namespace Topology.IsOpenEmbedding

open TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open embedding preserves local Krull dimension. -/
theorem topologicalKrullDimAt_eq {f : X → Y} (hf : IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (f x) := by
  apply le_antisymm
  · refine le_iInf fun V ↦ ?_
    let U : {U : Set X // IsOpen U ∧ x ∈ U} :=
      ⟨f ⁻¹' V.1, V.2.1.preimage hf.continuous, V.2.2⟩
    have hdim : topologicalKrullDim U.1 ≤ topologicalKrullDim V.1 :=
      ((hf.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict V.1 fun z ↦
        z.2).isInducing.topologicalKrullDim_le
    exact (iInf_le _ U).trans hdim
  · refine le_iInf fun U ↦ ?_
    let V : {V : Set Y // IsOpen V ∧ f x ∈ V} :=
      ⟨f '' U.1, hf.isOpenMap U.1 U.2.1, mem_image_of_mem f U.2.2⟩
    refine (iInf_le _ V).trans_eq ?_
    exact (hf.isEmbedding.homeomorphImage U.1).symm.isHomeomorph.topologicalKrullDim_eq

end Topology.IsOpenEmbedding

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism preserves local Krull dimension. -/
theorem topologicalKrullDimAt_of_isHomeomorph (f : X → Y) (hf : IsHomeomorph f) (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (f x) :=
  hf.isOpenEmbedding.topologicalKrullDimAt_eq x

/-- An isolated point has local Krull dimension zero. -/
@[simp]
theorem topologicalKrullDimAt_eq_zero_of_isOpen_singleton {x : X} (hx : IsOpen ({x} : Set X)) :
    topologicalKrullDimAt X x = 0 := by
  apply le_antisymm
  · exact (topologicalKrullDimAt_le_of_isOpen hx (mem_singleton x)).trans
      (topologicalKrullDim_zero_of_discreteTopology ↑({x} : Set X))
  · exact topologicalKrullDimAt_nonneg x

end TauCeti
