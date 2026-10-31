/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Integral points over a nonarchimedean local field are compact and open

Let `E` be a nonarchimedean local field with valuation ring `𝒪[E]`, and let `A` be an
`𝒪[E]`-algebra, the coordinate ring of an affine `𝒪[E]`-scheme `𝒳 = Spec A`. Its integral points
`𝒳(𝒪[E]) = Hom(A, 𝒪[E])` map to the points `Hom(A, E)` of its generic fibre by composing with the
inclusion `𝒪[E] → E`. For the point topologies this map is a closed embedding whose image is the
set of points with integral values, and its source is compact because `𝒪[E]` is compact
(`TauCeti.PointTopology.instCompactSpace`). When `A` is of finite type it is also an open
embedding, because `𝒪[E]` is open in `E` and integrality need only be checked on finitely many
generators.

For an affine group `𝒢 = Spec H` of finite type over `𝒪[E]` the map is the group homomorphism
`AlgHom.mapValue (Algebra.ofId 𝒪[E] E)`, so the integral points `𝒢(𝒪[E])` form a compact open
subgroup of the topological group `G(E)` of points of the generic fibre. These are the compact open
subgroups, such as the congruence subgroups and the parahoric subgroups of integral models, on which
the local representation theory of `G(E)` is built.

Only the compactness statements use that `E` is a local field; the others hold for every ring
whose topology is defined by its valuation.

## Main declarations

* `TauCeti.PointTopology.range_integralPoints`: the image of the integral points consists of the
  points whose values are all integral.
* `TauCeti.PointTopology.isClosedEmbedding_integralPoints` and
  `TauCeti.PointTopology.isOpenEmbedding_integralPoints`: the integral points form a closed
  subspace, and an open one for a coordinate algebra of finite type.
* `TauCeti.PointTopology.isClosedEmbedding_mapValue_integer`,
  `TauCeti.PointTopology.isOpenEmbedding_mapValue_integer` and
  `TauCeti.PointTopology.isCompact_range_mapValue_integer`: the integral points of an affine group
  of finite type over `𝒪[E]` form a compact open subgroup of its points over `E`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2, and Ex. 2.3, p. 3.
-/

public section

open Topology ValuativeRel

namespace TauCeti.PointTopology

section Valuative

variable {E A : Type*} [CommRing E] [ValuativeRel E] [CommRing A] [Algebra 𝒪[E] A]

/-- A point of `A` with values in `E` comes from an integral point exactly when all its values
are integral. -/
theorem range_integralPoints :
    Set.range (fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x) =
      {x | ∀ a, x a ∈ 𝒪[E]} := by
  have hv := Valuation.integer.integers (valuation E)
  rw [AlgHom.range_comp_left_of_injective _ hv.hom_inj]
  ext x
  refine forall_congr' fun a ↦ ?_
  simp only [Set.mem_range, Algebra.ofId_apply]
  exact ⟨by rintro ⟨r, hr⟩; exact hr ▸ hv.map_le_one r, fun h ↦ hv.exists_of_le_one h⟩

variable [TopologicalSpace E] [IsValuativeTopology E]

/- The proofs below pass embedding facts about `Subtype.val : 𝒪[E] → E` for the structure map
`Algebra.ofId 𝒪[E] E`: the algebra structure of the subring `𝒪[E]` is defined by its inclusion,
and Mathlib states no separate lemma identifying the two. -/

/-- The integral points form a closed subspace of the points over `E`. -/
theorem isClosedEmbedding_integralPoints :
    IsClosedEmbedding fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x :=
  isClosedEmbedding_map_codomain _ Valuation.isClosed_integer.isClosedEmbedding_subtypeVal

/-- The integral points of a finite type algebra form an open subspace of the points over `E`. -/
theorem isOpenEmbedding_integralPoints [Algebra.FiniteType 𝒪[E] A] :
    IsOpenEmbedding fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x :=
  isOpenEmbedding_map_codomain _ Valuation.isOpen_integer.isOpenEmbedding_subtypeVal

variable {H : Type*} [Semiring H] [Bialgebra 𝒪[E] H]

/-- The integral points of a bialgebra over `𝒪[E]` form a closed subspace of its points over
`E`. -/
theorem isClosedEmbedding_mapValue_integer :
    IsClosedEmbedding (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] E)) :=
  AlgHom.isClosedEmbedding_mapValue Valuation.isClosed_integer.isClosedEmbedding_subtypeVal

/-- The integral points of a bialgebra of finite type over `𝒪[E]` form an open subspace of its
points over `E`. -/
theorem isOpenEmbedding_mapValue_integer [Algebra.FiniteType 𝒪[E] H] :
    IsOpenEmbedding (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] E)) :=
  AlgHom.isOpenEmbedding_mapValue Valuation.isOpen_integer.isOpenEmbedding_subtypeVal

end Valuative

section LocalField

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/-- The integral points of a commutative bialgebra over the valuation ring of a nonarchimedean
local field form a compact subset of its points over the field. When the bialgebra is of finite
type, this subset is also open by `isOpenEmbedding_mapValue_integer`; for the coordinate ring of an
affine group it is then a compact open subgroup. -/
theorem isCompact_range_mapValue_integer {H : Type*} [CommRing H] [Bialgebra 𝒪[E] H] :
    IsCompact (Set.range (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] E))) :=
  isCompact_range (AlgHom.continuous_mapValue continuous_subtype_val)

end LocalField

end TauCeti.PointTopology
