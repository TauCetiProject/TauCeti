/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Constructions of open normal subgroups

Bundled constructions of `OpenNormalSubgroup` that Mathlib provides for `OpenSubgroup` but not
for its normal variant: the preimage under a continuous group homomorphism, the product of two
open normal subgroups, the trivial subgroup of a group with the discrete topology, and the whole
group. All are stated for an arbitrary topological space structure on a group; no continuity of
the group operations is required.

Two continuity criteria for maps into the discrete quotients by open normal subgroups are recorded
as well: a map into the quotient by an intersection is continuous when its composites with the two
quotient maps are, and a map into the quotient by a preimage is continuous when its composite with
the homomorphism followed by the quotient map is. Separate continuity of multiplication makes
the relevant quotients discrete; the preimage criterion needs it only on the target group.

## Main definitions

* `OpenNormalSubgroup.comap`: the preimage of an open normal subgroup under a continuous
  group homomorphism.
* `OpenNormalSubgroup.prod`: the product of two open normal subgroups, as an open normal subgroup
  of the product group.
* `TauCeti.openNormalSubgroupBot`: the trivial subgroup of a group with the discrete
  topology, as an open normal subgroup.
* `TauCeti.openNormalSubgroupTop`: the whole group, as an open normal subgroup.

## Main results

* `OpenNormalSubgroup.toSubgroup_inf`, `OpenNormalSubgroup.toSubgroup_sup`: the lattice operations
  on open normal subgroups are those of the underlying subgroups.
* `OpenNormalSubgroup.continuous_mk_inf`, `OpenNormalSubgroup.continuous_mk_comap`: continuity of
  a map into the quotient by an intersection, and by a preimage, of open normal subgroups.
* `TauCeti.mem_openNormalSubgroupBot`: the trivial open normal subgroup contains only the
  identity.
* `TauCeti.openNormalSubgroupBot_le`: the trivial open normal subgroup lies below every open
  normal subgroup.
-/

public section

namespace OpenNormalSubgroup

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- Open normal subgroups compare through their underlying subgroups. -/
theorem toSubgroup_le {U V : OpenNormalSubgroup G} : U.toSubgroup ≤ V.toSubgroup ↔ U ≤ V :=
  Iff.rfl

/-- The underlying subgroup of the intersection of two open normal subgroups is the intersection
of the underlying subgroups. -/
@[simp]
theorem toSubgroup_inf (U V : OpenNormalSubgroup G) :
    (U ⊓ V).toSubgroup = U.toSubgroup ⊓ V.toSubgroup :=
  (rfl)

/-- The underlying subgroup of the join of two open normal subgroups is the join of the underlying
subgroups. -/
@[simp]
theorem toSubgroup_sup [SeparatelyContinuousMul G] (U V : OpenNormalSubgroup G) :
    (U ⊔ V).toSubgroup = U.toSubgroup ⊔ V.toSubgroup :=
  (rfl)

/-- The preimage of an open normal subgroup under a continuous group homomorphism. -/
def comap (U : OpenNormalSubgroup H) (f : G →* H) (hf : Continuous f) :
    OpenNormalSubgroup G where
  toOpenSubgroup := U.toOpenSubgroup.comap f hf
  isNormal' := U.isNormal'.comap f

/-- The preimage of an open normal subgroup as a set. -/
@[simp, norm_cast]
theorem coe_comap (U : OpenNormalSubgroup H) (f : G →* H) (hf : Continuous f) :
    (comap U f hf : Set G) = f ⁻¹' U :=
  (rfl)

/-- The underlying subgroup of the preimage of an open normal subgroup. -/
@[simp]
theorem toSubgroup_comap (U : OpenNormalSubgroup H) (f : G →* H)
    (hf : Continuous f) : (comap U f hf).toSubgroup = U.toSubgroup.comap f :=
  (rfl)

/-- Membership in the preimage of an open normal subgroup. -/
@[simp]
theorem mem_comap {U : OpenNormalSubgroup H} {f : G →* H} {hf : Continuous f} {g : G} :
    g ∈ comap U f hf ↔ f g ∈ U :=
  Iff.rfl

/-- Taking the preimage of an open normal subgroup twice is the preimage under the composite. -/
theorem comap_comap {K : Type*} [Group K] [TopologicalSpace K] (U : OpenNormalSubgroup K)
    (f₂ : H →* K) (hf₂ : Continuous f₂) (f₁ : G →* H) (hf₁ : Continuous f₁) :
    comap (comap U f₂ hf₂) f₁ hf₁ = comap U (f₂.comp f₁) (hf₂.comp hf₁) :=
  (rfl)

/-- The product of two open normal subgroups, as an open normal subgroup of the product group. -/
def prod (U : OpenNormalSubgroup G) (V : OpenNormalSubgroup H) : OpenNormalSubgroup (G × H) where
  toOpenSubgroup := U.toOpenSubgroup.prod V.toOpenSubgroup
  isNormal' := Subgroup.prod_normal U.toSubgroup V.toSubgroup

/-- The product of two open normal subgroups as a set. -/
@[simp, norm_cast]
theorem coe_prod (U : OpenNormalSubgroup G) (V : OpenNormalSubgroup H) :
    (U.prod V : Set (G × H)) = (U : Set G) ×ˢ (V : Set H) :=
  (rfl)

/-- The underlying subgroup of the product of two open normal subgroups. -/
@[simp]
theorem toSubgroup_prod (U : OpenNormalSubgroup G) (V : OpenNormalSubgroup H) :
    (U.prod V).toSubgroup = U.toSubgroup.prod V.toSubgroup :=
  (rfl)

/-- Membership in the product of two open normal subgroups. -/
@[simp]
theorem mem_prod {U : OpenNormalSubgroup G} {V : OpenNormalSubgroup H} {x : G × H} :
    x ∈ U.prod V ↔ x.1 ∈ U ∧ x.2 ∈ V :=
  Iff.rfl

/-- A map into the quotient by the intersection of two open normal subgroups is continuous as
soon as its composites with the two quotient maps are. -/
theorem continuous_mk_inf [SeparatelyContinuousMul G] {X : Type*} [TopologicalSpace X]
    {U V : OpenNormalSubgroup G} {g : X → G}
    (hU : Continuous fun x ↦ (g x : G ⧸ U.toSubgroup))
    (hV : Continuous fun x ↦ (g x : G ⧸ V.toSubgroup)) :
    Continuous fun x ↦ (g x : G ⧸ (U ⊓ V).toSubgroup) := by
  rw [continuous_discrete_rng]
  intro d
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective d
  have : (fun x ↦ (g x : G ⧸ (U ⊓ V).toSubgroup)) ⁻¹' {(y : G ⧸ (U ⊓ V).toSubgroup)} =
      (fun x ↦ (g x : G ⧸ U.toSubgroup)) ⁻¹' {(y : G ⧸ U.toSubgroup)} ∩
        (fun x ↦ (g x : G ⧸ V.toSubgroup)) ⁻¹' {(y : G ⧸ V.toSubgroup)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, QuotientGroup.eq]
    exact Subgroup.mem_inf
  rw [this]
  exact (hU.isOpen_preimage _ (isOpen_discrete _)).inter (hV.isOpen_preimage _ (isOpen_discrete _))

/-- A map into the quotient by the preimage of an open normal subgroup under a continuous
homomorphism is continuous as soon as its composite with the homomorphism followed by the
quotient map is. No continuity of the group operations on the source group is required. -/
theorem continuous_mk_comap [SeparatelyContinuousMul H] {X : Type*} [TopologicalSpace X]
    (U : OpenNormalSubgroup H) (f : G →* H) (hf : Continuous f) {g : X → G}
    (hg : Continuous fun x ↦ (f (g x) : H ⧸ U.toSubgroup)) :
    Continuous fun x ↦ (g x : G ⧸ (U.comap f hf).toSubgroup) := by
  let φ := QuotientGroup.map (U.comap f hf).toSubgroup U.toSubgroup f
    (toSubgroup_comap U f hf).le
  have hφ : Function.Injective φ := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    simp only [φ, QuotientGroup.map_mk, QuotientGroup.eq, toSubgroup_comap,
      Subgroup.mem_comap, map_mul, map_inv]
    exact id
  exact (IsLocallyConstant.desc _ φ
    ((IsLocallyConstant.iff_continuous _).2 hg) hφ).continuous

end OpenNormalSubgroup

namespace TauCeti

/-- The trivial subgroup of a group with the discrete topology, as an open normal subgroup. -/
def openNormalSubgroupBot (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    OpenNormalSubgroup G where
  toOpenSubgroup := ⟨⊥, isOpen_discrete _⟩
  isNormal' := inferInstance

/-- The underlying subgroup of `openNormalSubgroupBot` is `⊥`. -/
@[simp]
theorem openNormalSubgroupBot_toSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : (openNormalSubgroupBot G).toSubgroup = ⊥ :=
  (rfl)

/-- The trivial open normal subgroup contains only the identity. -/
@[simp]
theorem mem_openNormalSubgroupBot {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    {x : G} : x ∈ openNormalSubgroupBot G ↔ x = 1 :=
  Subgroup.mem_bot

/-- The trivial open normal subgroup of a discrete group lies below every open normal subgroup. -/
theorem openNormalSubgroupBot_le {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    {U : OpenNormalSubgroup G} : openNormalSubgroupBot G ≤ U := by
  rw [← OpenNormalSubgroup.toSubgroup_le, openNormalSubgroupBot_toSubgroup]
  exact bot_le

/-- The whole group, as an open normal subgroup. It is the greatest element of
`OpenNormalSubgroup G`, and in particular witnesses that this type is nonempty. -/
def openNormalSubgroupTop (G : Type*) [Group G] [TopologicalSpace G] : OpenNormalSubgroup G where
  toOpenSubgroup := ⊤
  isNormal' := Subgroup.normal_top

/-- The underlying subgroup of `openNormalSubgroupTop` is `⊤`. -/
@[simp]
theorem openNormalSubgroupTop_toSubgroup (G : Type*) [Group G] [TopologicalSpace G] :
    (openNormalSubgroupTop G).toSubgroup = ⊤ :=
  (rfl)

end TauCeti
