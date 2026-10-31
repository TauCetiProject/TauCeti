/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.Topology.Algebra.PointTopology.Functoriality
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Integral points over a nonarchimedean local field

Let `E` be a field whose topology comes from its valuation, with valuation ring `O = 𝒪[E]`, and
let `A` be an `O`-algebra, the coordinate ring of an affine `O`-scheme `𝒳 = Spec A`. Its integral
points `𝒳(O) = Hom_O(A, O)` map to the points `X(E) = Hom_O(A, E)` of the generic fibre by
composition with the inclusion `O → E`. The image consists of the points all of whose values are
integral, and it suffices to test this on a generating family of `A`. Since `O` is open in `E`, the
map is an open embedding when `A` is of finite type over `O`. When `E` is a nonarchimedean local
field, `O` is compact, so `𝒳(O)` is compact (`TauCeti.PointTopology.instCompactSpace`, which needs
no finiteness), and the map is also a closed embedding, `X(E)` being Hausdorff.

For an affine group scheme `𝒢 = Spec H` over `O`, the map is the group homomorphism
`AlgHom.mapValue (Algebra.ofId O E)` from `𝒢(O)` to `G(E)`. When `H` is of finite type, its image
`TauCeti.PointTopology.integralPointsSubgroup H` is therefore a compact open subgroup of `G(E)`. In
particular `G(E)` has a compact open subgroup; the congruence subgroups of `𝒢(O)` are open
subgroups of it, and so of `G(E)`.

## Main declarations

* `TauCeti.PointTopology.range_integralPoints` and
  `TauCeti.PointTopology.range_integralPoints_of_adjoin_eq_top`: the image of `𝒳(O)` in `X(E)` is
  the set of points with integral values, tested on all of `A` or on a generating family.
* `TauCeti.PointTopology.isOpenEmbedding_integralPoints`: for `A` of finite type, `𝒳(O) → X(E)` is
  an open embedding.
* `TauCeti.PointTopology.isClosedEmbedding_integralPoints`: over a nonarchimedean local field,
  `𝒳(O) → X(E)` is a closed embedding.
* `TauCeti.PointTopology.isOpenEmbedding_mapValue_integralPoints`: the homomorphism `𝒢(O) → G(E)`
  is an open embedding.
* `TauCeti.PointTopology.integralPointsSubgroup`: `𝒢(O)` as an open subgroup of `G(E)`, with
  `TauCeti.PointTopology.mem_integralPointsSubgroup_iff` and
  `TauCeti.PointTopology.isCompact_integralPointsSubgroup`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2, and Ex. 2.3, p. 3.
-/

public section

open Topology ValuativeRel WithConv

namespace TauCeti.PointTopology

section Range

variable {E A : Type*} [Field E] [ValuativeRel E] [Semiring A] [Algebra 𝒪[E] A]

/-- The integral points of `Spec A` are the points over `E` all of whose values lie in `𝒪[E]`. -/
theorem range_integralPoints :
    Set.range (fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x) =
      {x | ∀ a, x a ∈ 𝒪[E]} := by
  rw [AlgHom.range_comp_left_of_injective _ Subtype.val_injective]
  -- The algebra map `𝒪[E] → E` is the subtype inclusion.
  simp_rw [show Set.range (Algebra.ofId 𝒪[E] E) = 𝒪[E] from Subtype.range_coe, SetLike.mem_coe]

/-- Integrality of a point over `E` can be tested on any generating family of `A`. -/
theorem range_integralPoints_of_adjoin_eq_top {ι : Type*} {a : ι → A}
    (ha : Algebra.adjoin 𝒪[E] (Set.range a) = ⊤) :
    Set.range (fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x) =
      {x | ∀ i, x (a i) ∈ 𝒪[E]} := by
  rw [AlgHom.range_comp_left_eq_of_adjoin_eq_top _ Subtype.val_injective ha]
  -- The algebra map `𝒪[E] → E` is the subtype inclusion.
  simp_rw [show Set.range (Algebra.ofId 𝒪[E] E) = 𝒪[E] from Subtype.range_coe, SetLike.mem_coe]

end Range

section Topology

variable {E A : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]

/-- For `A` of finite type over `𝒪[E]`, the integral points of `Spec A` form an open subspace of
its points over `E`: the inclusion `𝒪[E] → E` is an open embedding. -/
theorem isOpenEmbedding_integralPoints [IsValuativeTopology E] [Semiring A] [Algebra 𝒪[E] A]
    [Algebra.FiniteType 𝒪[E] A] :
    IsOpenEmbedding fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x :=
  isOpenEmbedding_map_codomain _ Valuation.isOpen_integer.isOpenEmbedding_subtypeVal

/-- Over a nonarchimedean local field `E`, the integral points of `Spec A` form a closed subspace of
its points over `E`, for every `𝒪[E]`-algebra `A`: they are compact, and the points over `E` are
Hausdorff. -/
theorem isClosedEmbedding_integralPoints [IsNonarchimedeanLocalField E] [CommRing A]
    [Algebra 𝒪[E] A] :
    IsClosedEmbedding fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x :=
  (continuous_map_codomain _ continuous_subtype_val).isClosedEmbedding
    fun _ _ h ↦ (AlgHom.cancel_left Subtype.val_injective).1 h

end Topology

section Group

variable {E H : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [Semiring H]
  [HopfAlgebra 𝒪[E] H] [Algebra.FiniteType 𝒪[E] H]

/-- For a Hopf algebra `H` of finite type over `𝒪[E]`, the homomorphism from the integral points
`𝒢(O)` of `𝒢 = Spec H` to its points `G(E)` over `E` is an open embedding. -/
theorem isOpenEmbedding_mapValue_integralPoints [IsValuativeTopology E] :
    IsOpenEmbedding (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] E)) := by
  rw [← isHomeomorph_ofConv.isOpenEmbedding.of_comp_iff]
  have h : ofConv ∘ AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] E) =
      (fun x : H →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] E).comp x) ∘ ofConv := by
    ext x : 1
    simp [AlgHom.mapValue_apply]
  rw [h]
  exact isOpenEmbedding_integralPoints.comp isHomeomorph_ofConv.isOpenEmbedding

variable (H) in
/-- The integral points `𝒢(O)` of the affine group scheme `𝒢 = Spec H` over `O = 𝒪[E]`, for `H` of
finite type, as an open subgroup of the points `G(E)` over `E`: the range of
`AlgHom.mapValue (Algebra.ofId 𝒪[E] E)`. Over a nonarchimedean local field it is compact
(`isCompact_integralPointsSubgroup`). -/
noncomputable def integralPointsSubgroup [IsValuativeTopology E] :
    OpenSubgroup (WithConv (H →ₐ[𝒪[E]] E)) where
  toSubgroup := (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] E)).range
  isOpen' := isOpenEmbedding_mapValue_integralPoints.isOpen_range

/-- As a subgroup, `integralPointsSubgroup H` is the range of the homomorphism from the integral
points. -/
@[simp]
theorem toSubgroup_integralPointsSubgroup [IsValuativeTopology E] :
    (integralPointsSubgroup (E := E) H).toSubgroup =
      (AlgHom.mapValue (H := H) (Algebra.ofId 𝒪[E] E)).range :=
  (rfl)

/-- A point of `G(E)` is integral exactly when all its values lie in `𝒪[E]`. -/
@[simp]
theorem mem_integralPointsSubgroup_iff [IsValuativeTopology E] {x : WithConv (H →ₐ[𝒪[E]] E)} :
    x ∈ integralPointsSubgroup H ↔ ∀ h, x.ofConv h ∈ 𝒪[E] := by
  rw [← OpenSubgroup.mem_toSubgroup, toSubgroup_integralPointsSubgroup, MonoidHom.mem_range,
    ← MonoidHom.mem_mrange, AlgHom.mem_mrange_mapValue_iff Subtype.val_injective]
  exact forall_congr' fun h ↦ ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩

end Group

section CompactGroup

variable {E H : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [CommRing H]
  [HopfAlgebra 𝒪[E] H] [Algebra.FiniteType 𝒪[E] H]

/-- Over a nonarchimedean local field, the integral points `𝒢(O)` form a compact open subgroup of
`G(E)`. -/
theorem isCompact_integralPointsSubgroup [IsNonarchimedeanLocalField E] :
    IsCompact (integralPointsSubgroup (E := E) H : Set (WithConv (H →ₐ[𝒪[E]] E))) := by
  rw [← OpenSubgroup.coe_toSubgroup, toSubgroup_integralPointsSubgroup, MonoidHom.coe_range]
  exact isCompact_range isOpenEmbedding_mapValue_integralPoints.continuous

end CompactGroup

end TauCeti.PointTopology
