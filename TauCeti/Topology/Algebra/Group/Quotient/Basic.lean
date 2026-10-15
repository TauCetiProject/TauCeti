/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup
public import TauCeti.Topology.Discrete

/-!
# Quotients of topological groups by subgroups

Generic facts about quotients of groups equipped with a topology. The image of an open subgroup,
its restricted quotient map, and the isomorphism for an open normal subgroup restricted to a
subgroup need only `[SeparatelyContinuousMul G]`. The open normal subgroup correspondence
holds for an arbitrary topology on `G`.
Multiplication on a normal quotient needs `[ContinuousMul G]`. The third isomorphism theorem
holds for arbitrary quotient topologies, without continuity assumptions on the group operations.
The inverse-translation results additionally require `[DiscreteTopology (G ⧸ U)]`.
Neither compactness nor total disconnectedness is needed.

## Main definitions

* `Subgroup.quotientOpenSubgroup`: the image of an open subgroup of `G` in `G ⧸ N`, as an open
  subgroup.
* `Subgroup.quotientOpenSubgroupMap`: the quotient homomorphism restricted to an open subgroup.
* `Subgroup.quotientSubgroupOfEquivMap`: for an open normal subgroup `V`, the quotient
  `W ⧸ V.subgroupOf W` is isomorphic, as a topological group, to the image of `W` in `G ⧸ V`.
* `Subgroup.quotientQuotientContinuousMulEquiv`: for normal subgroups `V ≤ W`, the third
  isomorphism theorem `(G ⧸ V) ⧸ W.map (mk' V) ≃ₜ* G ⧸ W`.

## Main results

* `QuotientGroup.instContinuousMul`: jointly continuous multiplication descends to a normal
  quotient without requiring continuous inversion, with an additive counterpart.
* `Subgroup.continuous_smul_const`: translation of a fixed coset is continuous.
* `Subgroup.continuous_inv_smul_const`: inverse translation of a fixed coset is
  continuous when the quotient is discrete.
* `Subgroup.continuous_inv_smul`: inverse translation is jointly continuous when
  the quotient is discrete.
* `TauCeti.QuotientGroup.instDiscreteTopology`: the quotient of a discrete group by any subgroup is
  discrete.
* `TauCeti.QuotientGroup.continuous_mapOfLE`: the quotient homomorphism `G ⧸ V →* G ⧸ U` for normal
  subgroups `V ≤ U` is continuous.
* `OpenSubgroup.isClopen_image_mk`: the image of an open subgroup of `G` under the
  quotient map `G → G ⧸ N` is clopen.
* `Subgroup.comapMk'OpenNormalOrderIso`: open normal subgroups of `G ⧸ N` correspond
  to the open normal subgroups of `G` containing `N`.
-/

public section

namespace QuotientGroup

/-- A normal quotient inherits jointly continuous multiplication without requiring continuous
inversion. The proof is adapted from the multiplication component of Mathlib's
`QuotientGroup.instIsTopologicalGroup`. -/
@[to_additive /-- An additive quotient inherits jointly continuous addition without requiring
continuous negation. The proof is adapted from the addition component of Mathlib's
`QuotientAddGroup.instIsTopologicalAddGroup`. -/]
instance instContinuousMul {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (N : Subgroup G) [N.Normal] : ContinuousMul (G ⧸ N) where
  continuous_mul := by
    rw [← (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul

end QuotientGroup

namespace Subgroup

open TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Translation of a fixed left coset is continuous under separate continuity of multiplication. -/
theorem continuous_smul_const (U : Subgroup G) (u : G ⧸ U) :
    Continuous (fun γ : G => γ • u) := by
  convert QuotientGroup.continuous_mk.comp (continuous_mul_const u.out) using 1
  ext γ
  exact (MulAction.Quotient.mk_smul_out U γ u).symm

/-- Inverse translation of a fixed coset is continuous when the coset quotient is discrete. -/
theorem continuous_inv_smul_const (U : Subgroup G) [DiscreteTopology (G ⧸ U)]
    (u : G ⧸ U) : Continuous (fun γ : G => γ⁻¹ • u) := by
  simpa only [MulAction.toPerm_symm_apply] using continuous_equiv_symm_apply
    (f := fun γ : G => (MulAction.toPerm γ : G ⧸ U ≃ G ⧸ U))
    (fun v => continuous_smul_const U v) u

/-- Inverse translation on a discrete coset quotient is jointly continuous. -/
theorem continuous_inv_smul (U : Subgroup G) [DiscreteTopology (G ⧸ U)] :
    Continuous (fun p : G × (G ⧸ U) => p.1⁻¹ • p.2) :=
  continuous_prod_of_discrete_right.mpr fun u => by
    simpa using continuous_inv_smul_const U u

end Subgroup

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

section MapOfLE

variable {G : Type*} [Group G] [TopologicalSpace G] {U V : Subgroup G} [U.Normal] [V.Normal]

/-- The quotient homomorphism `G ⧸ V →* G ⧸ U` for normal subgroups `V ≤ U` of a topological
group is continuous: composed with the quotient map of `G` modulo `V` it is the quotient map
modulo `U`, and `G ⧸ V` carries the quotient topology. -/
theorem continuous_mapOfLE (hVU : V ≤ U) : Continuous (mapOfLE hVU) :=
  (_root_.QuotientGroup.isQuotientMap_mk V).continuous_iff.mpr <| by
    rw [← _root_.QuotientGroup.coe_mk' V, ← MonoidHom.coe_comp, mapOfLE_comp_mk',
      _root_.QuotientGroup.coe_mk']
    exact _root_.QuotientGroup.continuous_mk

end MapOfLE

end QuotientGroup

end TauCeti

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] {N : Subgroup G}
  [N.Normal]

/-- The image of an open subgroup of `G` in the quotient by a normal subgroup `N` is
clopen under separate continuity of multiplication. -/
theorem isClopen_image_mk (U : OpenSubgroup G) :
    IsClopen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) := by
  have hopen : IsOpen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) :=
    QuotientGroup.isOpenMap_coe _ U.isOpen'
  refine ⟨(QuotientGroup.isQuotientMap_mk N).isClosed_preimage.mp ?_, hopen⟩
  have hpreimage :
      IsOpen ((U.toSubgroup.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) : Set G) := by
    simpa only [Subgroup.coe_comap, Subgroup.coe_map, QuotientGroup.coe_mk',
      OpenSubgroup.coe_toSubgroup] using hopen.preimage QuotientGroup.continuous_mk
  simpa only [Subgroup.coe_comap, Subgroup.coe_map, QuotientGroup.coe_mk',
    OpenSubgroup.coe_toSubgroup] using Subgroup.isClosed_of_isOpen _ hpreimage

end OpenSubgroup

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] {N : Subgroup G}
  [N.Normal]

/-- The correspondence theorem for open normal subgroups: the open normal subgroups of
`G ⧸ N` correspond to the open normal subgroups of `G` containing `N`, for any topology on `G`. -/
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
            (QuotientGroup.isQuotientMap_mk N).isOpen_preimage.mp <| by
              have hopen : IsOpen ((U.1.toSubgroup.map (QuotientGroup.mk' N)).comap
                  (QuotientGroup.mk' N) : Set G) := by
                rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr U.2]
                exact U.1.toOpenSubgroup.isOpen'
              simpa only [Subgroup.coe_comap, QuotientGroup.coe_mk', Set.preimage,
                Subgroup.mem_carrier, SetLike.mem_coe] using hopen⟩
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
      simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, IsConcreteLE.le_iff,
        OpenNormalSubgroup.mem_comap]
      refine ⟨fun h x hx => ?_, fun h _ hg => h hg⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
      exact h hx }

end Subgroup

namespace OpenNormalSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] {N : Subgroup G}
  [N.Normal]

/-- The open normal subgroup correspondence takes the preimage under the quotient map. -/
@[simp]
theorem comapMk'OpenNormalOrderIso_apply_toSubgroup (U : OpenNormalSubgroup (G ⧸ N)) :
    (Subgroup.comapMk'OpenNormalOrderIso N U : OpenNormalSubgroup G).toSubgroup =
      Subgroup.comap (QuotientGroup.mk' N) U.toSubgroup :=
  OpenNormalSubgroup.toSubgroup_comap U _ _

/-- The inverse open normal subgroup correspondence takes the image under the quotient map. -/
@[simp]
theorem comapMk'OpenNormalOrderIso_symm_apply_toSubgroup
    (U : { V : OpenNormalSubgroup G // (N : Subgroup G) ≤ V.toSubgroup }) :
    ((Subgroup.comapMk'OpenNormalOrderIso N).symm U : OpenNormalSubgroup (G ⧸ N)).toSubgroup =
      Subgroup.map (QuotientGroup.mk' N) U.1.toSubgroup :=
  (rfl)

end OpenNormalSubgroup

namespace Subgroup

section OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] (N : Subgroup G)
  [N.Normal]

/-- The image of an open subgroup `U` in `G / N`, as an open subgroup. -/
def quotientOpenSubgroup (U : OpenSubgroup G) : OpenSubgroup (G ⧸ N) where
  toSubgroup := U.toSubgroup.map (QuotientGroup.mk' N)
  isOpen' := QuotientGroup.isOpenMap_coe _ U.isOpen'

/-- The subgroup underlying `quotientOpenSubgroup` is the image subgroup. -/
@[simp]
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

/-- The quotient homomorphism restricted from `U` to its image in `G / N`. -/
def quotientOpenSubgroupMap (U : OpenSubgroup G) :
    U.toSubgroup →* (quotientOpenSubgroup N U).toSubgroup :=
  (QuotientGroup.mk' N).subgroupMap U.toSubgroup

/-- The restricted quotient homomorphism has the expected value in `G / N`. -/
@[simp]
theorem coe_quotientOpenSubgroupMap (U : OpenSubgroup G) (u : U.toSubgroup) :
    ((quotientOpenSubgroupMap N U u : (quotientOpenSubgroup N U).toSubgroup) : G ⧸ N) =
      (u : G) :=
  (rfl)

/-- The restricted quotient homomorphism is continuous. -/
theorem continuous_quotientOpenSubgroupMap (U : OpenSubgroup G) :
    Continuous (quotientOpenSubgroupMap N U) :=
  continuous_induced_rng.2 (QuotientGroup.continuous_mk.comp continuous_subtype_val)

end OpenSubgroup

section SubgroupOf

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- For an open normal subgroup `V` and any subgroup `W` of `G`, the quotient `W ⧸ V.subgroupOf W`
is isomorphic, as a topological group, to the image `W.map (mk' V)` of `W` in `G ⧸ V`. This is
Noether's first isomorphism theorem for the composite `W → G → G ⧸ V`, whose kernel is
`V.subgroupOf W`; both groups are discrete because `V` is open. -/
noncomputable def quotientSubgroupOfEquivMap (V W : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) : W ⧸ V.subgroupOf W ≃ₜ* W.map (QuotientGroup.mk' V) :=
  haveI : SeparatelyContinuousMul W := separatelyContinuousMul_induced W.subtype
  haveI : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  haveI : DiscreteTopology (W ⧸ V.subgroupOf W) :=
    QuotientGroup.discreteTopology (W.subgroupOf_isOpen V hV)
  { QuotientGroup.liftEquiv (V.subgroupOf W) ((QuotientGroup.mk' V).subgroupMap_surjective W)
      (by rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']) with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- `quotientSubgroupOfEquivMap` sends the class of `w : W` to the class of `w` in `G ⧸ V`. -/
@[simp]
theorem coe_quotientSubgroupOfEquivMap_mk (V W : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) (w : W) :
    ((quotientSubgroupOfEquivMap V W hV (w : W ⧸ V.subgroupOf W) : W.map (QuotientGroup.mk' V)) :
      G ⧸ V) = ((w : G) : G ⧸ V) :=
  (rfl)

end SubgroupOf

section ThirdIso

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Noether's third isomorphism theorem is a topological isomorphism for the quotient topologies.
No openness of the normal subgroups or continuity of the group operations is required. -/
noncomputable def quotientQuotientContinuousMulEquiv (V W : Subgroup G) [V.Normal] [W.Normal]
    (hVW : V ≤ W) :
    (G ⧸ V) ⧸ W.map (QuotientGroup.mk' V) ≃ₜ* G ⧸ W :=
  { QuotientGroup.quotientQuotientEquivQuotient V W hVW with
    continuous_toFun :=
      ((QuotientGroup.isQuotientMap_mk (W.map (QuotientGroup.mk' V))).comp
        (QuotientGroup.isQuotientMap_mk V)).continuous_iff.mpr <| by
          exact QuotientGroup.continuous_mk.congr fun g ↦
            (QuotientGroup.quotientQuotientEquivQuotient_apply_mk V W hVW g).symm
    continuous_invFun := (QuotientGroup.isQuotientMap_mk W).continuous_iff.mpr <| by
      exact (QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk).congr fun g ↦
        (QuotientGroup.quotientQuotientEquivQuotient_symm_mk V W hVW g).symm }

/-- `quotientQuotientContinuousMulEquiv` sends the class of the class of `g` to the class of
`g`. -/
@[simp]
theorem quotientQuotientContinuousMulEquiv_mk (V W : Subgroup G) [V.Normal] [W.Normal]
    (hVW : V ≤ W) (g : G) :
    quotientQuotientContinuousMulEquiv V W hVW
        ((g : G ⧸ V) : (G ⧸ V) ⧸ W.map (QuotientGroup.mk' V)) = (g : G ⧸ W) :=
  QuotientGroup.quotientQuotientEquivQuotient_apply_mk V W hVW g

end ThirdIso

end Subgroup
