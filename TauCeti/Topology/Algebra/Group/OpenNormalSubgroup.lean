/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Constructions of open normal subgroups

Bundled constructions of `OpenNormalSubgroup` that Mathlib provides for `OpenSubgroup` but not
for its normal variant: the preimage under a continuous group homomorphism, the product of two
open normal subgroups, the trivial subgroup of a group with the discrete topology, and the whole
group. All are stated for an arbitrary topological space structure on a group; no continuity of
the group operations is required.

## Main definitions

* `OpenNormalSubgroup.comap`: the preimage of an open normal subgroup under a continuous
  group homomorphism.
* `OpenNormalSubgroup.prod`: the product of two open normal subgroups, as an open normal subgroup
  of the product group.

## Main instances

* `OrderTop (OpenNormalSubgroup G)`: the whole group is the greatest open normal subgroup; in
  particular `OpenNormalSubgroup G` is inhabited.
* `BoundedOrder (OpenNormalSubgroup G)` for `G` with the discrete topology: the trivial subgroup
  is the least open normal subgroup.

## Main results

* `OpenNormalSubgroup.toSubgroup_inf`, `OpenNormalSubgroup.toSubgroup_sup`: the lattice operations
  on open normal subgroups are those of the underlying subgroups.
* `OpenNormalSubgroup.mem_top`, `OpenNormalSubgroup.mem_bot`: the top open normal subgroup
  contains every element, and the bottom one only the identity.
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

/-- The whole group, as an open normal subgroup. -/
instance instTopOpenNormalSubgroup : Top (OpenNormalSubgroup G) :=
  ⟨⟨⊤, Subgroup.normal_top⟩⟩

/-- The top open normal subgroup as a set is the whole group. -/
@[simp, norm_cast]
theorem coe_top : ((⊤ : OpenNormalSubgroup G) : Set G) = Set.univ :=
  (rfl)

/-- The underlying subgroup of the top open normal subgroup is `⊤`. -/
@[simp]
theorem toSubgroup_top : (⊤ : OpenNormalSubgroup G).toSubgroup = ⊤ :=
  (rfl)

/-- Every element lies in the top open normal subgroup. -/
@[simp]
theorem mem_top (x : G) : x ∈ (⊤ : OpenNormalSubgroup G) :=
  Set.mem_univ x

instance instOrderTopOpenNormalSubgroup : OrderTop (OpenNormalSubgroup G) where
  le_top _ := Set.subset_univ _

instance instInhabitedOpenNormalSubgroup : Inhabited (OpenNormalSubgroup G) :=
  ⟨⊤⟩

section DiscreteTopology

variable [DiscreteTopology G]

/-- The trivial subgroup of a group with the discrete topology, as an open normal subgroup. -/
instance instBotOpenNormalSubgroup : Bot (OpenNormalSubgroup G) :=
  ⟨⟨⟨⊥, isOpen_discrete _⟩, Subgroup.normal_bot⟩⟩

/-- The bottom open normal subgroup of a discrete group as a set is `{1}`. -/
@[simp, norm_cast]
theorem coe_bot : ((⊥ : OpenNormalSubgroup G) : Set G) = {1} :=
  (rfl)

/-- The underlying subgroup of the bottom open normal subgroup is `⊥`. -/
@[simp]
theorem toSubgroup_bot : (⊥ : OpenNormalSubgroup G).toSubgroup = ⊥ :=
  (rfl)

/-- The bottom open normal subgroup of a discrete group contains only the identity. -/
@[simp]
theorem mem_bot {x : G} : x ∈ (⊥ : OpenNormalSubgroup G) ↔ x = 1 :=
  Subgroup.mem_bot

instance instOrderBotOpenNormalSubgroup : OrderBot (OpenNormalSubgroup G) where
  bot_le U _ hx := Subgroup.mem_bot.1 hx ▸ one_mem U

/-- `OpenNormalSubgroup G` is a bounded order for discrete `G`. This is not synthesized from the
`OrderTop` and `OrderBot` instances. -/
instance instBoundedOrderOpenNormalSubgroup : BoundedOrder (OpenNormalSubgroup G) where

end DiscreteTopology

/-- The preimage of an open normal subgroup under a continuous group homomorphism.
Its underlying subgroup is definitionally `U.toSubgroup.comap f`. -/
@[expose] def comap (U : OpenNormalSubgroup H) (f : G →* H) (hf : Continuous f) :
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

end OpenNormalSubgroup
