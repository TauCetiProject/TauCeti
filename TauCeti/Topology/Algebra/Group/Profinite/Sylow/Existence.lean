/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic

/-!
# Existence of Sylow subgroups in profinite groups

Every profinite group has a Sylow pro-`p` subgroup. The construction takes the inverse limit
of the finite sets of Sylow `p`-subgroups of its finite continuous quotients. The transition
map sends a Sylow subgroup to its image under the quotient map; Mathlib's finite Sylow theory
says that these transition maps are surjective. Compactness, in the form of nonemptiness of a
cofiltered limit of nonempty finite types, then supplies a compatible family.

The subgroup upstairs is the intersection of the inverse images of that family. Compatibility
shows that its image in every finite quotient is exactly the chosen Sylow subgroup, which gives
both the pro-`p` property and the prime-to-`p` index condition.

## Main results

* `exists_isProPSylow`: every profinite group has a Sylow pro-`p` subgroup.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 2.3.6.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace ProfiniteSylow

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
/-- The transition map of the finite-quotient system is surjective: every class modulo the
larger subgroup is already the image of a class modulo the smaller one. -/
private theorem finiteQuotientMap_surjective {U V : Subgroup G} [U.Normal] [V.Normal]
    (hVU : V ≤ U) : Function.Surjective (finiteQuotientMap hVU) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U x
  exact ⟨(g : G ⧸ V), finiteQuotientMap_mk hVU g⟩

/-- The cofiltered system of Sylow `p`-subgroups of the finite quotients of `G`. -/
private noncomputable def system : OpenNormalSubgroup G ⥤ Type u where
  obj U := Sylow p (G ⧸ U.toSubgroup)
  map {U V} f := ↾fun P ↦
    P.mapSurjective (finiteQuotientMap_surjective (leOfHom f))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro P
    apply Sylow.ext
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro P
    apply Sylow.ext
    dsimp
    rw [Subgroup.map_map, finiteQuotientMap_comp]

private instance system_obj_finite (U : OpenNormalSubgroup G) :
    Finite ((system (p := p) (G := G)).obj U) := by
  dsimp [system]
  infer_instance

private instance system_obj_nonempty (U : OpenNormalSubgroup G) :
    Nonempty ((system (p := p) (G := G)).obj U) := by
  dsimp [system]
  infer_instance

end ProfiniteSylow

/-- Every profinite group has a Sylow pro-`p` subgroup. -/
theorem exists_isProPSylow (p : ℕ) [Fact p.Prime] (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] : ∃ P : Subgroup G, IsProPSylow p P := by
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system
    (ProfiniteSylow.system (p := p) (G := G))
  let S : ∀ U : OpenNormalSubgroup G, Sylow p (G ⧸ U.toSubgroup) := s
  -- Regard the section equation as compatibility of the underlying Sylow subgroups.
  have hcompat {U V : OpenNormalSubgroup G} (hUV : U ≤ V) :
      (S U : Subgroup (G ⧸ U.toSubgroup)).map (finiteQuotientMap hUV) =
        (S V : Subgroup (G ⧸ V.toSubgroup)) := by
    have h := hs (homOfLE hUV)
    have h' : (S U).mapSurjective (ProfiniteSylow.finiteQuotientMap_surjective hUV) = S V := by
      -- A morphism in `Type` is a bundled function, so expose its application before using
      -- the section equation.
      change (S U).mapSurjective (ProfiniteSylow.finiteQuotientMap_surjective hUV) = S V at h
      exact h
    exact congrArg (fun Q : Sylow p (G ⧸ V.toSubgroup) ↦ Q.1) h'
  -- Pull the compatible family back to `G` and intersect all its members.
  let P : Subgroup G :=
    ⨅ U : OpenNormalSubgroup G,
      (S U : Subgroup (G ⧸ U.toSubgroup)).comap (QuotientGroup.mk' U.toSubgroup)
  -- Compactness upgrades the evident inclusion to equality in every finite quotient.
  have hPmap (U : OpenNormalSubgroup G) :
      P.map (QuotientGroup.mk' U.toSubgroup) = (S U : Subgroup (G ⧸ U.toSubgroup)) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact iInf_le _ U
    · intro y hy
      let t : OpenNormalSubgroup G → Set G := fun V ↦
        (QuotientGroup.mk' U.toSubgroup) ⁻¹' {y} ∩
          (QuotientGroup.mk' V.toSubgroup) ⁻¹' (S V : Set (G ⧸ V.toSubgroup))
      have ht_nonempty (V : OpenNormalSubgroup G) : (t V).Nonempty := by
        let W := U ⊓ V
        have hyW : y ∈ (S W : Subgroup (G ⧸ W.toSubgroup)).map
            (finiteQuotientMap (show W ≤ U from inf_le_left)) := by
          rwa [hcompat inf_le_left]
        obtain ⟨z, hz, hzy⟩ := hyW
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W.toSubgroup z
        refine ⟨g, ?_, ?_⟩
        · simpa using hzy
        · have hzV : (QuotientGroup.mk g : G ⧸ V.toSubgroup) ∈
              (S W : Subgroup (G ⧸ W.toSubgroup)).map
                (finiteQuotientMap (show W ≤ V from inf_le_right)) :=
            ⟨QuotientGroup.mk g, hz, finiteQuotientMap_mk _ g⟩
          rwa [hcompat inf_le_right] at hzV
      have ht_closed (V : OpenNormalSubgroup G) : IsClosed (t V) :=
        (isClosed_singleton.preimage QuotientGroup.continuous_mk).inter
          ((isClosed_discrete _).preimage QuotientGroup.continuous_mk)
      have ht_directed : Directed (· ⊇ ·) t := by
        intro V W
        refine ⟨V ⊓ W, ?_, ?_⟩
        · rintro g ⟨hgy, hg⟩
          refine ⟨hgy, ?_⟩
          have : (QuotientGroup.mk g : G ⧸ V.toSubgroup) ∈
              (S (V ⊓ W) : Subgroup (G ⧸ (V ⊓ W).toSubgroup)).map
                (finiteQuotientMap inf_le_left) :=
            ⟨QuotientGroup.mk g, hg, finiteQuotientMap_mk _ g⟩
          rwa [hcompat inf_le_left] at this
        · rintro g ⟨hgy, hg⟩
          refine ⟨hgy, ?_⟩
          have : (QuotientGroup.mk g : G ⧸ W.toSubgroup) ∈
              (S (V ⊓ W) : Subgroup (G ⧸ (V ⊓ W).toSubgroup)).map
                (finiteQuotientMap inf_le_right) :=
            ⟨QuotientGroup.mk g, hg, finiteQuotientMap_mk _ g⟩
          rwa [hcompat inf_le_right] at this
      let _ : Nonempty (OpenNormalSubgroup G) :=
        ⟨{ toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }⟩
      obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
        ht_directed ht_nonempty (fun V ↦ (ht_closed V).isCompact) ht_closed
      refine ⟨g, ?_, ?_⟩
      · refine Subgroup.mem_iInf.mpr fun V ↦ ?_
        exact (Set.mem_iInter.mp hg V).2
      · exact (Set.mem_iInter.mp hg U).1
  -- The construction is an intersection of closed inverse images.
  have hPclosed : IsClosed (P : Set G) := by
    dsimp [P]
    rw [Subgroup.coe_iInf]
    exact isClosed_iInter fun U ↦
      (isClosed_discrete _).preimage QuotientGroup.continuous_mk
  -- Every finite quotient of `P` factors through one of its Sylow finite images.
  have hPpro : IsProP p P := by
    rw [isProP_iff]
    intro V
    obtain ⟨U, hUV⟩ := Subgroup.exists_openNormalSubgroup_comap_le P V
    let f : P →* G ⧸ U.toSubgroup :=
      (QuotientGroup.mk' U.toSubgroup).domRestrict P
    have hfP : IsPGroup p f.range := by
      dsimp [f]
      rw [MonoidHom.domRestrict_range, hPmap U]
      exact (S U).isPGroup'
    let q : P →* P ⧸ V.toSubgroup := QuotientGroup.mk' V.toSubgroup
    have hker : f.ker ≤ q.ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      apply (QuotientGroup.eq_one_iff x).mpr
      apply hUV
      exact (QuotientGroup.eq_one_iff (x : G)).mp hx
    have hker' : f.rangeRestrict.ker ≤ q.ker := by
      rwa [MonoidHom.ker_rangeRestrict]
    let q' : f.range →* P ⧸ V.toSubgroup :=
      f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q, hker'⟩
    apply hfP.of_surjective q'
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup z
    exact ⟨f.rangeRestrict x, by simp [q', q]⟩
  refine ⟨P, isProPSylow_iff.mpr ⟨hPclosed, hPpro, fun U ↦ ?_⟩⟩
  rw [hPmap U]
  exact (S U).not_dvd_index

end TauCeti
