/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Compact open subgroups of topological groups

In a group `G` with separately continuous multiplication, every open subgroup `U : OpenSubgroup G`
is also closed (`OpenSubgroup.isClosed`). This file develops the consequences of that closedness for
compactness, directedness, relative index, and profinite structure:

* Any open subgroup contained in a compact set is itself compact
  (`OpenSubgroup.isCompact_of_subset`), so the intersection of a compact open subgroup with an
  arbitrary open subgroup is again compact (`OpenSubgroup.isCompact_inf_left`,
  `OpenSubgroup.isCompact_inf_right`).
* Consequently, the compact open subgroups — and the compact open subgroups contained in a fixed
  open subgroup `U₀` — form downward-directed families under inclusion
  (`TauCeti.directedOn_isCompact_openSubgroup`, `OpenSubgroup.directedOn_isCompact_and_le`), and
  when `U₀` is compact they are cofinal below every open subgroup
  (`OpenSubgroup.exists_isCompact_le_and_le`).
* The trace of any open subgroup on a compact open subgroup has finite index
  (`OpenSubgroup.finiteIndex_subgroupOf_of_isCompact`).
* When `G` is a totally disconnected topological group, every compact open subgroup bundles as an
  object of `ProfiniteGrp` (`OpenSubgroup.toProfiniteGrp`), with functorial transition morphisms
  `OpenSubgroup.toProfiniteGrpMap` in `ProfiniteGrp` along subgroup inclusions `U ≤ V`.

These properties organize the level filtrations of smooth representations and Hecke algebras on
locally profinite groups.

## Main definitions

* `OpenSubgroup.toProfiniteGrp`, `OpenAddSubgroup.toProfiniteAddGrp`: bundles a compact open
  subgroup of a totally disconnected topological group as an object of `ProfiniteGrp`.
* `OpenSubgroup.toProfiniteGrpMap`, `OpenAddSubgroup.toProfiniteAddGrpMap`: functorial transition
  morphism `U.toProfiniteGrp hU ⟶ V.toProfiniteGrp hV` induced by `U ≤ V`.

## Main results

* `OpenSubgroup.isCompact_of_subset`: an open subgroup lying inside a compact set is compact.
* `OpenSubgroup.isCompact_inf_left`, `OpenSubgroup.isCompact_inf_right`: intersecting with a compact
  open subgroup produces a compact open subgroup.
* `OpenSubgroup.directedOn_isCompact_and_le`, `TauCeti.directedOn_isCompact_openSubgroup`,
  `OpenSubgroup.exists_isCompact_le_and_le`: downward directedness and cofinality of compact open
  subgroups.
* `OpenSubgroup.finiteIndex_subgroupOf_of_isCompact`: an open subgroup has finite index in any
  compact open subgroup.

## References

* J. Bernstein, *Representations of `p`-adic Groups*, Harvard lecture notes (1992), Ch. I, §1.1.
* L. Kramer, *Locally Profinite Groups and Bruhat–Tits Buildings*, Proposition 1.43 and
  Theorem 1.44.
-/

public section

open CategoryTheory

universe u

namespace OpenSubgroup

section SeparatelyContinuousMul

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- An open subgroup contained in a compact subset is compact, since it is closed. -/
@[to_additive /-- An open additive subgroup contained in a compact subset is compact, since it is
closed. -/]
theorem isCompact_of_subset (U : OpenSubgroup G) {K : Set G} (hK : IsCompact K)
    (hUK : (U : Set G) ⊆ K) : IsCompact (U : Set G) :=
  hK.of_isClosed_subset U.isClosed hUK

/-- The intersection of a compact open subgroup with any open subgroup is compact. -/
@[to_additive /-- The intersection of a compact open additive subgroup with any open additive
subgroup is compact. -/]
theorem isCompact_inf_left (U V : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    IsCompact ((U ⊓ V : OpenSubgroup G) : Set G) :=
  (U ⊓ V).isCompact_of_subset hU Set.inter_subset_left

/-- The intersection of any open subgroup with a compact open subgroup is compact. -/
@[to_additive /-- The intersection of any open additive subgroup with a compact open additive
subgroup is compact. -/]
theorem isCompact_inf_right (U V : OpenSubgroup G) (hV : IsCompact (V : Set G)) :
    IsCompact ((U ⊓ V : OpenSubgroup G) : Set G) :=
  (U ⊓ V).isCompact_of_subset hV Set.inter_subset_right

/-- Given a compact open subgroup `U₀` and any open subgroup `V`, their intersection `U₀ ⊓ V` is a
compact open subgroup contained in both `U₀` and `V`. Thus the compact open subgroups contained in
`U₀` are cofinal among all open subgroups under reverse inclusion. -/
@[to_additive /-- Given a compact open additive subgroup `U₀` and any open additive subgroup `V`,
their intersection `U₀ ⊓ V` is a compact open additive subgroup contained in both `U₀` and `V`. -/]
theorem exists_isCompact_le_and_le (U₀ V : OpenSubgroup G) (hU₀ : IsCompact (U₀ : Set G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ H ≤ U₀ ∧ H ≤ V :=
  ⟨U₀ ⊓ V, U₀.isCompact_inf_left V hU₀, inf_le_left, inf_le_right⟩

/-- The compact open subgroups contained in a fixed open subgroup `U₀` form a directed family under
reverse inclusion `≥` (`U₀` itself need not be compact). -/
@[to_additive /-- The compact open additive subgroups contained in a fixed open additive subgroup
`U₀` form a directed family under reverse inclusion `≥` (`U₀` itself need not be compact). -/]
theorem directedOn_isCompact_and_le (U₀ : OpenSubgroup G) :
    DirectedOn (· ≥ ·) {H : OpenSubgroup G | IsCompact (H : Set G) ∧ H ≤ U₀} :=
  fun H₁ hH₁ H₂ _ ↦ ⟨H₁ ⊓ H₂, ⟨H₁.isCompact_inf_left H₂ hH₁.1, inf_le_of_left_le hH₁.2⟩,
    inf_le_left, inf_le_right⟩

/-- Every open subgroup `V` has finite relative index `[U : U ∩ V]` inside a compact open subgroup
`U`. -/
@[to_additive /-- Every open additive subgroup `V` has finite relative index `[U : U ∩ V]` inside a
compact open additive subgroup `U`. -/]
theorem finiteIndex_subgroupOf_of_isCompact (U V : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    (V.toSubgroup.subgroupOf U.toSubgroup).FiniteIndex := by
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp hU
  have : SeparatelyContinuousMul U.toSubgroup := U.toSubgroup.toSubmonoid.separatelyContinuousMul
  exact (V.comap U.toSubgroup.subtype continuous_subtype_val).finiteIndex_toSubgroup

end SeparatelyContinuousMul

section Profinite

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TotallyDisconnectedSpace G]

/-- A compact open subgroup of a totally disconnected topological group, bundled as an object of
`ProfiniteGrp`. -/
@[to_additive /-- A compact open additive subgroup of a totally disconnected topological additive
group, bundled as an object of `ProfiniteAddGrp`. -/]
abbrev toProfiniteGrp (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) : ProfiniteGrp.{u} :=
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  ProfiniteGrp.of U

/-- The underlying type of `U.toProfiniteGrp hU` is `U`. -/
@[to_additive /-- The underlying type of `U.toProfiniteAddGrp hU` is `U`. -/]
theorem coe_toProfiniteGrp (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    (U.toProfiniteGrp hU : Type u) = U :=
  (rfl)

/-- An inclusion `U ≤ V` between compact open subgroups induces a morphism
`U.toProfiniteGrp hU ⟶ V.toProfiniteGrp hV` in `ProfiniteGrp`. -/
@[to_additive /-- An inclusion `U ≤ V` between compact open additive subgroups induces a morphism
`U.toProfiniteAddGrp hU ⟶ V.toProfiniteAddGrp hV` in `ProfiniteAddGrp`. -/]
def toProfiniteGrpMap {U V : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (hV : IsCompact (V : Set G)) (hUV : U ≤ V) :
    U.toProfiniteGrp hU ⟶ V.toProfiniteGrp hV :=
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV
  ProfiniteGrp.ofHom ⟨Subgroup.inclusion hUV, continuous_inclusion hUV⟩

/-- The underlying `ContinuousMonoidHom` of `toProfiniteGrpMap hU hV hUV` is
`Subgroup.inclusion hUV`. -/
@[to_additive (attr := simp) /-- The underlying `ContinuousAddMonoidHom` of
`toProfiniteAddGrpMap hU hV hUV` is `AddSubgroup.inclusion hUV`. -/]
theorem hom_toProfiniteGrpMap {U V : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (hV : IsCompact (V : Set G)) (hUV : U ≤ V) :
    (toProfiniteGrpMap hU hV hUV).hom = ⟨Subgroup.inclusion hUV, continuous_inclusion hUV⟩ :=
  (rfl)

/-- Evaluating `toProfiniteGrpMap hU hV hUV` computes `Subgroup.inclusion hUV`. -/
@[to_additive /-- Evaluating `toProfiniteAddGrpMap hU hV hUV` computes
`AddSubgroup.inclusion hUV`. -/]
theorem toProfiniteGrpMap_apply {U V : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (hV : IsCompact (V : Set G)) (hUV : U ≤ V) (x : U) :
    toProfiniteGrpMap hU hV hUV x = Subgroup.inclusion hUV x :=
  (rfl)

/-- `toProfiniteGrpMap` sends the identity inclusion `U ≤ U` to the identity morphism. -/
@[to_additive (attr := simp) /-- `toProfiniteAddGrpMap` sends the identity inclusion `U ≤ U` to the
identity morphism. -/]
theorem toProfiniteGrpMap_refl (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    toProfiniteGrpMap hU hU le_rfl = 𝟙 (U.toProfiniteGrp hU) :=
  (rfl)

/-- `toProfiniteGrpMap` is functorial with respect to composition of inclusions `U ≤ V ≤ W`. -/
@[to_additive (attr := simp) /-- `toProfiniteAddGrpMap` is functorial with respect to composition of
inclusions `U ≤ V ≤ W`. -/]
theorem toProfiniteGrpMap_trans {U V W : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (hV : IsCompact (V : Set G)) (hW : IsCompact (W : Set G)) (hUV : U ≤ V) (hVW : V ≤ W) :
    toProfiniteGrpMap hU hV hUV ≫ toProfiniteGrpMap hV hW hVW =
      toProfiniteGrpMap hU hW (hUV.trans hVW) :=
  (rfl)

end Profinite

end OpenSubgroup

namespace TauCeti

/-- The compact open subgroups of a group with separately continuous multiplication form a directed
family under reverse inclusion `≥`. -/
@[to_additive /-- The compact open additive subgroups of an additive group with separately
continuous addition form a directed family under reverse inclusion `≥`. -/]
theorem directedOn_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] :
    DirectedOn (· ≥ ·) {H : OpenSubgroup G | IsCompact (H : Set G)} := by
  simpa only [le_top, and_true] using (⊤ : OpenSubgroup G).directedOn_isCompact_and_le

end TauCeti
