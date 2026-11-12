/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Extension
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.MaximalProP

/-!
# Quotients of a pro-`p` class-module extension

Let `V` be a subgroup of a topological group `G`. A continuous homomorphism from `G` to a profinite
group kills the kernel of `V → Vᵃᵇ(p)` as soon as it maps `V` into a closed abelian pro-`p`
subgroup (`TauCeti.abelianizationProPExtensionKernel_le_ker`). When `V` is normal, the
homomorphism therefore factors through the class-module extension `G / ker(V → Vᵃᵇ(p))`.

The two instances used are a profinite extension whose kernel is an abelian pro-`p` group, into
which a free presentation maps its relation subgroup, and a discrete quotient `G/U` (for instance
a finite one) in which the image of `V` is an abelian `p`-group
(`TauCeti.abelianizationProPExtensionKernel_le_of_isPGroup_map`). The latter permits a generating
family of the class-module extension to be read in that quotient.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public section

namespace TauCeti

open scoped IsMulCommutative

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous homomorphism to a profinite group which maps `V` into a closed abelian pro-`p`
subgroup `A` kills the kernel of `V → Vᵃᵇ(p)`. -/
theorem abelianizationProPExtensionKernel_le_ker (p : ℕ) (V : Subgroup G) {E : Type*} [Group E]
    [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E]
    (φ : G →ₜ* E) (A : Subgroup E) [IsMulCommutative A] (hA : IsClosed (A : Set E))
    (hpro : IsProP p A) (hVA : V ≤ A.comap φ) :
    abelianizationProPExtensionKernel p G V ≤ (φ : G →* E).ker := by
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let f : V →ₜ* A :=
    ⟨((φ : G →* E).comp V.subtype).codRestrict A fun v ↦ hVA v.2,
      ((map_continuous φ).comp continuous_subtype_val).subtype_mk _⟩
  intro x hx
  obtain ⟨hv, hzero⟩ := (mem_abelianizationProPExtensionKernel_iff p G V x).mp hx
  rw [abelianizationProPMk_apply] at hzero
  exact congrArg Subtype.val (eq_one_of_maximalProPQuotient_mk_eq_one hpro f hzero)


/-- A discrete quotient in which the image of `V` is an abelian `p`-group kills the kernel
of `V → Vᵃᵇ(p)`. For normal `V`, this is the inclusion needed by `QuotientGroup.mapOfLE`
to factor the quotient through the pro-`p` class-module extension. -/
theorem abelianizationProPExtensionKernel_le_of_isPGroup_map (p : ℕ)
    (V : Subgroup G) (U : OpenNormalSubgroup G)
    (hpro : IsPGroup p (V.map (QuotientGroup.mk' U.toSubgroup)))
    (hcomm : ⁅V, V⁆ ≤ U.toSubgroup) :
    abelianizationProPExtensionKernel p G V ≤ U.toSubgroup := by
  have : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  let H := V.map (QuotientGroup.mk' U.toSubgroup)
  have hHcomm : ⁅H, H⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa using hcomm)
  have : IsMulCommutative H := Subgroup.commutator_self_eq_bot_iff.mp hHcomm
  let f : V →ₜ* H :=
    ⟨((QuotientGroup.mk' U.toSubgroup).comp V.subtype).codRestrict H fun v ↦ ⟨v, v.2, rfl⟩,
      ((continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _)⟩
  let fab := TopologicalAbelianization.lift f
  let N : OpenNormalSubgroup (TopologicalAbelianization V) :=
    ⟨⟨(fab : TopologicalAbelianization V →* H).ker,
      (isOpen_discrete {(1 : H)}).preimage fab.continuous⟩, inferInstance⟩
  have hN : IsPGroup p (TopologicalAbelianization V ⧸ N.toSubgroup) :=
    (hpro.to_subgroup (fab : TopologicalAbelianization V →* H).range).of_equiv
      (QuotientGroup.quotientKerEquivRange _).symm
  intro x hx
  obtain ⟨hv, hzero⟩ := (mem_abelianizationProPExtensionKernel_iff p G V x).mp hx
  rw [abelianizationProPMk_apply] at hzero
  have h2 : ((⟨x, hv⟩ : V) : TopologicalAbelianization V) ∈ N.toSubgroup :=
    proPKernel_le hN ((QuotientGroup.eq_one_iff _).mp hzero)
  have h3 : f ⟨x, hv⟩ = 1 := (TopologicalAbelianization.lift_mk f ⟨x, hv⟩).symm.trans h2
  exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val h3)

end TauCeti
