/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti AI contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Compactness.Compact

/-!
# Profinite groups: the finite-quotient limit description

The unbundled workhorse of profinite group theory, phrased for the type-class stack
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`
(with `TotallyDisconnectedSpace G` only where needed) so that consumers outside the
`ProfiniteGrp` category can use them directly.

* The limit description: a family of cosets of the open normal subgroups of a compact totally
  disconnected group, compatible along the canonical quotient maps, is realized by a unique
  element of `G` (`existsUnique_forall_mk_eq`; Ribes and Zalesskii, *Profinite Groups*,
  Proposition 1.1.4). This is the unbundled counterpart of `ProfiniteGrp.toLimit_surjective`
  and `ProfiniteGrp.toLimit_injective`, which describe the same identification for the
  `ProfiniteGrp` category. The compactness input is
  `TauCeti.nonempty_iInter_of_directed_nonempty_isClosed`.
* The same for subgroups: a family `H` of subgroups of the quotients `G ⧸ U` cuts out the closed
  subgroup `limitSubgroup H` of `G` (`isClosed_limitSubgroup`), and when `H` is compatible along
  the quotient maps and `G` is compact, its image in every `G ⧸ U` is exactly `H U`
  (`map_mk'_limitSubgroup`).
-/

public section

namespace TauCeti

section LimitDescription

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Limit description of a profinite group** (unbundled). A family `x` of cosets of the open
normal subgroups of a compact totally disconnected group `G` that is compatible along the
canonical quotient maps is realized by a unique element of `G`: the natural map from `G` to
the inverse limit of the quotients `G ⧸ U` over the open normal subgroups `U` is bijective.
The bundled counterpart for the `ProfiniteGrp` category is
`ProfiniteGrp.toLimit_surjective` together with `ProfiniteGrp.toLimit_injective`. -/
theorem existsUnique_forall_mk_eq (x : ∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G))
    (hcompat : ∀ (U V : OpenNormalSubgroup G) (_hle : (U : Subgroup G) ≤ V) (g : G),
      QuotientGroup.mk' (U : Subgroup G) g = x U → QuotientGroup.mk' (V : Subgroup G) g = x V) :
    ∃! g : G, ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g = x U := by
  have hneIdx : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⟨⊤, isOpen_univ⟩ }⟩
  have hne : ∀ U : OpenNormalSubgroup G,
      ((QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}).Nonempty := fun U =>
    QuotientGroup.mk'_surjective (U : Subgroup G) (x U)
  have hcl : ∀ U : OpenNormalSubgroup G,
      IsClosed ((QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}) := fun U =>
    isClosed_singleton.preimage (QuotientGroup.continuous_mk (N := (U : Subgroup G)))
  have hdir : Directed (· ⊇ ·) fun U : OpenNormalSubgroup G =>
      (QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U} := by
    rintro U V
    refine ⟨U ⊓ V, fun g hgU => ?_, fun g hgV => ?_⟩
    · rw [Set.mem_preimage, Set.mem_singleton_iff] at hgU ⊢
      exact hcompat (U ⊓ V) U inf_le_left g hgU
    · rw [Set.mem_preimage, Set.mem_singleton_iff] at hgV ⊢
      exact hcompat (U ⊓ V) V inf_le_right g hgV
  obtain ⟨g, hg⟩ := nonempty_iInter_of_directed_nonempty_isClosed
    (fun U : OpenNormalSubgroup G => (QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}) hdir hne hcl
  refine ⟨g, fun U => Set.mem_iInter.mp hg U, fun g' hg' => ?_⟩
  have hgg : ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g = x U :=
    fun U => Set.mem_iInter.mp hg U
  have hgg' : ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g' = x U :=
    fun U => hg' U
  refine (inv_mul_eq_one.mp ?_).symm
  refine Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U => ?_
  exact QuotientGroup.eq.mp ((hgg U).trans (hgg' U).symm)

end LimitDescription

section LimitSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]
  {H : ∀ U : OpenNormalSubgroup G, Subgroup (G ⧸ U.toSubgroup)}

/-- The subgroup of `G` cut out by a family `H` of subgroups of its quotients `G ⧸ U` by open
normal subgroups: the elements whose class modulo every `U` lies in `H U`. It is closed
(`isClosed_limitSubgroup`), and when `H` is compatible along the quotient maps and `G` is
compact, its image in every `G ⧸ U` is `H U` (`map_mk'_limitSubgroup`). -/
def limitSubgroup (H : ∀ U : OpenNormalSubgroup G, Subgroup (G ⧸ U.toSubgroup)) : Subgroup G :=
  ⨅ U, (H U).comap (QuotientGroup.mk' U.toSubgroup)

/-- An element lies in `limitSubgroup H` exactly when its class modulo every `U` lies in
`H U`. -/
theorem mem_limitSubgroup {g : G} :
    g ∈ limitSubgroup H ↔ ∀ U : OpenNormalSubgroup G, (g : G ⧸ U.toSubgroup) ∈ H U :=
  Subgroup.mem_iInf

variable [IsTopologicalGroup G]

/-- The subgroup cut out by a family of subgroups of the quotients by open normal subgroups is
closed. -/
theorem isClosed_limitSubgroup (H : ∀ U : OpenNormalSubgroup G, Subgroup (G ⧸ U.toSubgroup)) :
    IsClosed (limitSubgroup H : Set G) := by
  rw [limitSubgroup, Subgroup.coe_iInf]
  exact isClosed_iInter fun U ↦ (isClosed_discrete _).preimage QuotientGroup.continuous_mk

/-- A family of subgroups of the quotients of a compact group by its open normal subgroups that
is compatible along the quotient maps is the family of images of the subgroup it cuts out. -/
theorem map_mk'_limitSubgroup [CompactSpace G]
    (hH : ∀ ⦃U V : OpenNormalSubgroup G⦄ (hUV : U ≤ V),
      (H U).map (QuotientGroup.mapOfLE hUV) = H V)
    (U : OpenNormalSubgroup G) :
    (limitSubgroup H).map (QuotientGroup.mk' U.toSubgroup) = H U := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact fun g hg ↦ mem_limitSubgroup.mp hg U
  · intro y hy
    -- Find a preimage of `y` that lies in the inverse image of every `H V`, by compactness.
    let t : OpenNormalSubgroup G → Set G := fun V ↦
      (QuotientGroup.mk' U.toSubgroup) ⁻¹' {y} ∩
        (QuotientGroup.mk' V.toSubgroup) ⁻¹' (H V : Set (G ⧸ V.toSubgroup))
    have ht_nonempty (V : OpenNormalSubgroup G) : (t V).Nonempty := by
      have hyW : y ∈ (H (U ⊓ V)).map (QuotientGroup.mapOfLE inf_le_left) := by
        rwa [hH inf_le_left]
      obtain ⟨z, hz, hzy⟩ := hyW
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (U ⊓ V).toSubgroup z
      refine ⟨g, ?_, ?_⟩
      · simpa using hzy
      · have hzV : (QuotientGroup.mk g : G ⧸ V.toSubgroup) ∈
            (H (U ⊓ V)).map (QuotientGroup.mapOfLE inf_le_right) :=
          ⟨QuotientGroup.mk g, hz, QuotientGroup.mapOfLE_mk _ g⟩
        rwa [hH inf_le_right] at hzV
    have ht_closed (V : OpenNormalSubgroup G) : IsClosed (t V) :=
      (isClosed_singleton.preimage QuotientGroup.continuous_mk).inter
        ((isClosed_discrete _).preimage QuotientGroup.continuous_mk)
    have ht_directed : Directed (· ⊇ ·) t := by
      intro V W
      refine ⟨V ⊓ W, ?_, ?_⟩
      · rintro g ⟨hgy, hg⟩
        refine ⟨hgy, ?_⟩
        have : (QuotientGroup.mk g : G ⧸ V.toSubgroup) ∈
            (H (V ⊓ W)).map (QuotientGroup.mapOfLE inf_le_left) :=
          ⟨QuotientGroup.mk g, hg, QuotientGroup.mapOfLE_mk _ g⟩
        rwa [hH inf_le_left] at this
      · rintro g ⟨hgy, hg⟩
        refine ⟨hgy, ?_⟩
        have : (QuotientGroup.mk g : G ⧸ W.toSubgroup) ∈
            (H (V ⊓ W)).map (QuotientGroup.mapOfLE inf_le_right) :=
          ⟨QuotientGroup.mk g, hg, QuotientGroup.mapOfLE_mk _ g⟩
        rwa [hH inf_le_right] at this
    let _ : Nonempty (OpenNormalSubgroup G) :=
      ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
    obtain ⟨g, hg⟩ := nonempty_iInter_of_directed_nonempty_isClosed t ht_directed
      ht_nonempty ht_closed
    exact ⟨g, mem_limitSubgroup.mpr fun V ↦ (Set.mem_iInter.mp hg V).2,
      (Set.mem_iInter.mp hg U).1⟩

end LimitSubgroup

end TauCeti
