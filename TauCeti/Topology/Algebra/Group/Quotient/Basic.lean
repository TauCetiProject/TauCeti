/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.QuotientGroup.Index
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# Quotients of topological groups by normal subgroups

Generic facts about the quotient of a topological group by a normal subgroup, phrased for the
unbundled classes `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`: neither compactness
nor total disconnectedness is needed, so the results apply in particular to profinite groups.

## Main definitions

* `TauCeti.quotientOpenSubgroup`: the image of an open subgroup of `G` in `G ⧸ N`, as an open
  subgroup.
* `TauCeti.quotientOpenSubgroupMap`: the quotient homomorphism restricted to an open subgroup.

## Main results

* `QuotientGroup.instDiscreteTopology`: the quotient of a discrete group by any subgroup is
  discrete.
* `QuotientGroup.isClopen_image_mk`: the image of an open subgroup of `G` under the
  quotient map `G → G ⧸ N` is clopen.
* `QuotientGroup.comapMk'OpenNormalOrderIso`: open normal subgroups of `G ⧸ N` correspond,
  as lattices, to the open normal subgroups of `G` containing `N`.
* `TauCeti.quotientOpenSubgroup_index`: quotienting by a subgroup of `U` preserves the index
  of `U`.
-/

public section

namespace TauCeti

namespace QuotientGroup

section Discrete

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- The quotient of a discrete group by any subgroup is discrete. This is Mathlib's
`QuotientGroup.discreteTopology` read as an instance: in a discrete group every subgroup is open. -/
@[to_additive TauCeti.QuotientAddGroup.instDiscreteTopology /-- The quotient of a discrete
additive group by any additive subgroup is discrete. This is Mathlib's
`QuotientAddGroup.discreteTopology` read as an instance: in a discrete additive group every
additive subgroup is open. -/]
instance instDiscreteTopology (H : Subgroup G) : DiscreteTopology (G ⧸ H) :=
  haveI : ContinuousMul G := ⟨continuous_of_discreteTopology⟩
  QuotientGroup.discreteTopology (isOpen_discrete _)

end Discrete

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}
  [N.Normal]

/-- The image of an open subgroup of `G` in the quotient by a normal subgroup `N` is
clopen: it is open because the quotient map is open, and closed because it is an open
subgroup of the topological group `G ⧸ N`. -/
theorem isClopen_image_mk (U : OpenSubgroup G) :
    IsClopen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) := by
  have hopen : IsOpen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) :=
    QuotientGroup.isOpenMap_coe _ U.isOpen'
  have heq : (QuotientGroup.mk : G → G ⧸ N) '' (U : Set G) =
      (Subgroup.map (QuotientGroup.mk' N) U.toSubgroup : Set (G ⧸ N)) := by
    -- `(U : Set G)` coerces through the `OpenSubgroup` `SetLike` instance, while
    -- `Subgroup.coe_map` is stated for the `Set G` coercion of the underlying `Subgroup`.
    -- The two coercions are definitionally equal and Mathlib provides no lemma bridging
    -- them, so the normalization below can only go through `rfl`.
    rw [show (U : Set G) = ((↑U : Subgroup G) : Set G) from rfl]
    exact (Subgroup.coe_map (QuotientGroup.mk' N) U.toSubgroup).symm
  rw [heq]
  exact ⟨Subgroup.isClosed_of_isOpen _ hopen, hopen⟩

/-- The correspondence theorem for open normal subgroups: the open normal subgroups of
`G ⧸ N` correspond, as lattices, to the open normal subgroups of `G` containing `N`. -/
def comapMk'OpenNormalOrderIso (N : Subgroup G) [N.Normal] :
    OpenNormalSubgroup (G ⧸ N) ≃o
      { U : OpenNormalSubgroup G // (N : Subgroup G) ≤ U.toSubgroup } :=
  -- `QuotientGroup.continuous_mk` is stated for `QuotientGroup.mk`, and binding it at the
  -- coerced type `⇑(QuotientGroup.mk' N)` keeps the `comap` terms below reducibly
  -- type-correct, so that `OpenNormalSubgroup.toSubgroup_comap` rewrites in them.
  have hmk : Continuous ⇑(QuotientGroup.mk' N) := QuotientGroup.continuous_mk
  { toFun U := ⟨OpenNormalSubgroup.comap U (QuotientGroup.mk' N) hmk,
      le_of_le_of_eq (QuotientGroup.le_comap_mk' N U.toSubgroup)
        (OpenNormalSubgroup.toSubgroup_comap U _ _).symm⟩
    invFun U :=
      { toOpenSubgroup :=
          ⟨Subgroup.map (QuotientGroup.mk' N) U.1.toSubgroup,
            QuotientGroup.isOpenMap_coe _ U.1.toOpenSubgroup.isOpen'⟩
        isNormal' :=
          Subgroup.Normal.map inferInstance (QuotientGroup.mk' N)
            (QuotientGroup.mk'_surjective N) }
    left_inv U := OpenNormalSubgroup.toSubgroup_injective <|
      (congrArg (Subgroup.map (QuotientGroup.mk' N))
          (OpenNormalSubgroup.toSubgroup_comap U _ _)).trans
        (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _)
    right_inv U := Subtype.ext <| OpenNormalSubgroup.toSubgroup_injective <|
      (OpenNormalSubgroup.toSubgroup_comap _ _ _).trans <|
        (QuotientGroup.comap_map_mk' N U.1.toSubgroup).trans (sup_eq_right.mpr U.2)
    map_rel_iff' {U V} := by
      simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, SetLike.le_def,
        OpenNormalSubgroup.mem_comap]
      refine ⟨fun h x hx => ?_, fun h _ hg => h hg⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
      exact h hx }

@[simp]
theorem comapMk'OpenNormalOrderIso_apply_toSubgroup (U : OpenNormalSubgroup (G ⧸ N)) :
    (comapMk'OpenNormalOrderIso N U : OpenNormalSubgroup G).toSubgroup =
      Subgroup.comap (QuotientGroup.mk' N) U.toSubgroup :=
  OpenNormalSubgroup.toSubgroup_comap U _ _

@[simp]
theorem comapMk'OpenNormalOrderIso_symm_apply_toSubgroup
    (U : { V : OpenNormalSubgroup G // (N : Subgroup G) ≤ V.toSubgroup }) :
    ((comapMk'OpenNormalOrderIso N).symm U : OpenNormalSubgroup (G ⧸ N)).toSubgroup =
      Subgroup.map (QuotientGroup.mk' N) U.1.toSubgroup :=
  (rfl)

end QuotientGroup

section OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
  [N.Normal]

/-- The image of an open subgroup `U` in `G / N`, as an open subgroup. -/
def quotientOpenSubgroup (U : OpenSubgroup G) : OpenSubgroup (G ⧸ N) where
  toSubgroup := U.toSubgroup.map (QuotientGroup.mk' N)
  isOpen' := QuotientGroup.isOpenMap_coe _ U.isOpen'

/-- The subgroup underlying `quotientOpenSubgroup` is the image subgroup. -/
theorem toSubgroup_quotientOpenSubgroup (U : OpenSubgroup G) :
    (quotientOpenSubgroup N U).toSubgroup = U.toSubgroup.map (QuotientGroup.mk' N) :=
  (rfl)

/-- Membership in `U / N` pulls back to membership in `U` when `N ≤ U`. -/
@[simp]
theorem mem_quotientOpenSubgroup_mk_iff (U : OpenSubgroup G) (hNU : N ≤ U) (g : G) :
    (g : G ⧸ N) ∈ quotientOpenSubgroup N U ↔ g ∈ U := by
  -- `QuotientGroup.mk'_apply` rewrites the coercion `(g : G ⧸ N)` as an application of the
  -- homomorphism `QuotientGroup.mk' N`, which is the shape `Subgroup.mem_comap` matches.
  rw [← OpenSubgroup.mem_toSubgroup, toSubgroup_quotientOpenSubgroup, ← QuotientGroup.mk'_apply,
    ← Subgroup.mem_comap, QuotientGroup.comap_map_mk', sup_eq_right.mpr hNU,
    OpenSubgroup.mem_toSubgroup]

/-- Passing from `U` to its image in `G / N` preserves the index when `N ≤ U`. -/
@[simp]
theorem quotientOpenSubgroup_index (U : OpenSubgroup G) (hNU : N ≤ U) :
    (quotientOpenSubgroup N U).toSubgroup.index = U.toSubgroup.index := by
  rw [toSubgroup_quotientOpenSubgroup, Subgroup.index_map_mk'_eq_index_sup, sup_eq_left.mpr hNU]

/-- The quotient homomorphism restricted from `U` to its image `U / N`. -/
def quotientOpenSubgroupMap (U : OpenSubgroup G) :
    U.toSubgroup →* (quotientOpenSubgroup N U).toSubgroup :=
  MonoidHom.codRestrict ((QuotientGroup.mk' N).comp U.toSubgroup.subtype)
    (quotientOpenSubgroup N U).toSubgroup fun u => ⟨u, u.2, rfl⟩

/-- The restricted quotient homomorphism has the expected value in `G / N`. -/
@[simp]
theorem coe_quotientOpenSubgroupMap (U : OpenSubgroup G) (u : U.toSubgroup) :
    ((quotientOpenSubgroupMap N U u : (quotientOpenSubgroup N U).toSubgroup) : G ⧸ N) =
      (u : G) :=
  (rfl)

/-- The restricted quotient homomorphism is surjective: every element of `U / N` is the image
of an element of `U`. -/
theorem quotientOpenSubgroupMap_surjective (U : OpenSubgroup G) :
    Function.Surjective (quotientOpenSubgroupMap N U) := by
  rintro ⟨-, u, hu, rfl⟩
  exact ⟨⟨u, hu⟩, rfl⟩

/-- The restricted quotient homomorphism is continuous. -/
theorem continuous_quotientOpenSubgroupMap (U : OpenSubgroup G) :
    Continuous (quotientOpenSubgroupMap N U) :=
  continuous_induced_rng.2 (QuotientGroup.continuous_mk.comp continuous_subtype_val)

end OpenSubgroup

end TauCeti
