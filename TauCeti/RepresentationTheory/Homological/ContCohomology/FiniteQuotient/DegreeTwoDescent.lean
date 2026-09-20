/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Algebra.GroupAction.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Descent of continuous two-cocycles to finite quotients

For a profinite group `G` and a discrete continuous `G`-module `M`, every continuous
`2`-cocycle on `G` is inflated from a finite quotient. The descent is strict: no coboundary is
subtracted from the cocycle.

Strict descent supplies the representative-level surjectivity needed to describe continuous
degree-two cohomology as a colimit of cohomology groups over finite quotients.

## Main statement

* `TauCeti.ContCohomology.exists_openNormalSubgroup_descendZ2`: every continuous `2`-cocycle
  itself descends to a finite quotient, with equality on representatives.
* `TauCeti.ContCohomology.exists_explicitInfl2_eq`: consequently every class in `H²(G, M)` is
  in the image of a finite-level inflation map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.2.5).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Cor. 6.5.6(a).
-/

-- Provenance: the statements follow the human-authored roadmap
-- `TauCetiRoadmap/ProfiniteCohomology/README.md`, which specifies strict degree-two descent by
-- uniform local constancy and finite-image stabilization.

public section

namespace TauCeti.ContCohomology

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {N : Subgroup G} [N.Normal]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

variable [CompactSpace G] [TotallyDisconnectedSpace G] [DiscreteTopology M]

/-- Find one open normal subgroup which simultaneously makes a continuous `2`-cocycle constant
on right cosets in both variables and fixes every value of the cocycle. -/
private theorem exists_openNormalSubgroup_descent_data (z : Z2 G M) :
    ∃ U : OpenNormalSubgroup G,
      (∀ (g h : G) (n n' : U),
        (z : G × G → M) (g * n, h * n') = (z : G × G → M) (g, h)) ∧
      ∀ (n : U) (g h : G),
        n • (z : G × G → M) (g, h) = (z : G × G → M) (g, h) := by
  let W := rightTranslationStabilizer (z : G × G → M)
  have hzloc : IsLocallyConstant (z : G × G → M) :=
    (IsLocallyConstant.iff_continuous _).2 (mem_Z2_iff.1 z.2).1
  have hWopen : IsOpen (W : Set (G × G)) := isOpen_rightTranslationStabilizer hzloc
  have hopen₁ : IsOpen {g : G | (g, 1) ∈ W} :=
    hWopen.preimage (continuous_id.prodMk continuous_const)
  have hopen₂ : IsOpen {g : G | (1, g) ∈ W} :=
    hWopen.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨U₁, hU₁⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hopen₁ W.one_mem
  obtain ⟨U₂, hU₂⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hopen₂ W.one_mem
  obtain ⟨V, hV⟩ := hzloc.range_finite.exists_openNormalSubgroup_smul_eq_self (G := G)
  let U := (U₁ ⊓ U₂) ⊓ V
  refine ⟨U, ?_, ?_⟩
  · intro g h n n'
    -- Coerce the two elements of `U` to `G` so that their pair can be tested for membership in
    -- the right-translation stabilizer `W ≤ G × G`.
    apply mem_rightTranslationStabilizer.mp
      (show ((n : G), (n' : G)) ∈ W from ?_) (g, h)
    have hn₁ : (n : G) ∈ U₁ :=
      (inf_le_left : U₁ ⊓ U₂ ≤ U₁) <|
        (inf_le_left : U ≤ U₁ ⊓ U₂) n.2
    have hn₂ : (n' : G) ∈ U₂ :=
      (inf_le_right : U₁ ⊓ U₂ ≤ U₂) <|
        (inf_le_left : U ≤ U₁ ⊓ U₂) n'.2
    simpa using W.mul_mem (hU₁ hn₁) (hU₂ hn₂)
  · intro n g h
    have hnV : (n : G) ∈ V := (inf_le_right : U ≤ V) n.2
    exact hV (n : G) hnV ((z : G × G → M) (g, h)) ⟨(g, h), rfl⟩

/-- **Strict finite-level descent in degree two.** Every continuous `2`-cocycle on a profinite
group with discrete coefficients is itself the pullback of a `2`-cocycle on `G ⧸ U` with values
in `M ^ U`, for some open normal subgroup `U`. The equality is on cochain representatives, not
only on their classes. -/
theorem exists_openNormalSubgroup_descendZ2 (z : Z2 G M) :
    ∃ (U : OpenNormalSubgroup G)
      (c : Z2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)),
      ∀ g h : G,
        ((c : (G ⧸ U.toSubgroup) × (G ⧸ U.toSubgroup) →
          FixedPoints.addSubgroup U.toSubgroup M) (g, h) : M) =
            (z : G × G → M) (g, h) := by
  obtain ⟨U, hright, hfixed⟩ := exists_openNormalSubgroup_descent_data z
  exact ⟨U, descendZ2 z hright hfixed, coe_descendZ2_apply_mk z hright hfixed⟩

/-- **Surjectivity of the degree-two finite-quotient comparison maps.** Every class in
`H²(G, M)` is inflated from `H²(G ⧸ U, M ^ U)` for some open normal subgroup `U`. -/
theorem exists_explicitInfl2_eq (x : H2 G M) :
    ∃ (U : OpenNormalSubgroup G)
      (y : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)),
      explicitInfl2 G M U.toSubgroup y = x := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    -- The chosen representative itself descends, so no coboundary is subtracted here.
    obtain ⟨U, hright, hfixed⟩ := exists_openNormalSubgroup_descent_data z
    exact ⟨U, descendZ2 z hright hfixed, explicitInfl2_descendZ2 z hright hfixed⟩

end TauCeti.ContCohomology
