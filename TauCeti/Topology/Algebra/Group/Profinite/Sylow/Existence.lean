/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import TauCeti.Topology.Algebra.Group.Profinite.Limit
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic

/-!
# Existence of Sylow subgroups in profinite groups

Every profinite group has a Sylow pro-`p` subgroup. The construction takes the inverse limit
of the finite sets of Sylow `p`-subgroups of its finite continuous quotients. The transition
map sends a Sylow subgroup to its image under the quotient map; Mathlib's finite Sylow theory
says that these transition maps are surjective. Compactness, in the form of nonemptiness of a
cofiltered limit of nonempty finite types, then supplies a compatible family.

The subgroup upstairs is `limitSubgroup` of that family, the intersection of its inverse images.
Compatibility shows that its image in every finite quotient is exactly the chosen Sylow subgroup
(`map_mk'_limitSubgroup`), which gives both the pro-`p` property and the prime-to-`p` index
condition.

## Main results

* `isProPSylow_limitSubgroup`: a compatible family of Sylow `p`-subgroups of the finite
  quotients cuts out a Sylow pro-`p` subgroup.
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

/-- **Sylow subgroups from a compatible family.** A family `S` of Sylow `p`-subgroups of the
finite continuous quotients of a profinite group, compatible along the quotient maps, cuts out a
Sylow pro-`p` subgroup, whose image in each `G ⧸ U` is `S U` (`map_mk'_limitSubgroup`). -/
theorem isProPSylow_limitSubgroup (S : ∀ U : OpenNormalSubgroup G, Sylow p (G ⧸ U.toSubgroup))
    (hS : ∀ ⦃U V : OpenNormalSubgroup G⦄ (hUV : U ≤ V),
      (S U : Subgroup (G ⧸ U.toSubgroup)).map (QuotientGroup.mapOfLE hUV) = S V) :
    IsProPSylow p (limitSubgroup fun U ↦ (S U : Subgroup (G ⧸ U.toSubgroup))) := by
  have hPmap := map_mk'_limitSubgroup hS
  have hPclosed := isClosed_limitSubgroup fun U ↦ (S U : Subgroup (G ⧸ U.toSubgroup))
  generalize limitSubgroup (fun U ↦ (S U : Subgroup (G ⧸ U.toSubgroup))) = P at hPmap hPclosed ⊢
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
  refine isProPSylow_iff.mpr ⟨hPclosed, hPpro, fun U ↦ ?_⟩
  rw [hPmap U]
  exact (S U).not_dvd_index

namespace ProfiniteSylow

/-- The cofiltered system of Sylow `p`-subgroups of the finite quotients of `G`. -/
private noncomputable def system : OpenNormalSubgroup G ⥤ Type u where
  obj U := Sylow p (G ⧸ U.toSubgroup)
  map {U V} f := ↾fun P ↦
    P.mapSurjective (QuotientGroup.mapOfLE_surjective (leOfHom f))
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
    rw [Subgroup.map_map, QuotientGroup.mapOfLE_comp]

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
  refine ⟨_, isProPSylow_limitSubgroup S fun U V hUV ↦ ?_⟩
  -- Regard the section equation as compatibility of the underlying Sylow subgroups.
  have h := hs (homOfLE hUV)
  have h' : (S U).mapSurjective (QuotientGroup.mapOfLE_surjective hUV) = S V := by
    -- A morphism in `Type` is a bundled function, so expose its application before using
    -- the section equation.
    change (S U).mapSurjective (QuotientGroup.mapOfLE_surjective hUV) = S V at h
    exact h
  exact congrArg (fun Q : Sylow p (G ⧸ V.toSubgroup) ↦ Q.1) h'

end TauCeti
