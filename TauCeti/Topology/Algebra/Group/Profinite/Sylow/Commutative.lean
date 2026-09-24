/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Containment
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Functoriality

/-!
# Sylow subgroups of commutative profinite groups

In a commutative profinite group `G`, a Sylow pro-`p` subgroup `P` maps isomorphically onto the
maximal pro-`p` quotient `G(p) = G ⧸ proPKernel p G`: the restriction of the quotient map to `P`
is a topological group isomorphism `P ≃ₜ* G(p)`. In particular a pro-`p` subgroup of `G` meets
the pro-`p` kernel trivially. Conversely, a closed subgroup that maps bijectively onto `G(p)` is
Sylow pro-`p`, so the bijection characterizes the Sylow pro-`p` subgroups of a commutative
profinite group.

The isomorphism transfers questions about a Sylow pro-`p` subgroup, a subgroup of `G`, to the
maximal pro-`p` quotient, a quotient of `G` determined by its universal property. This is the
form in which the `p`-Sylow subgroups of the profinite integers are identified with `ℤ_p`, in
`TauCeti.Topology.Algebra.Group.Profinite.ZHat.PadicInt`.

## Main results

* `TauCeti.IsProP.disjoint_proPKernel`: in a commutative profinite group, a pro-`p` subgroup
  meets the pro-`p` kernel trivially.
* `TauCeti.IsProPSylow.bijective_domRestrict_maximalProPQuotient_mk`: a Sylow pro-`p` subgroup maps
  bijectively onto the maximal pro-`p` quotient.
* `TauCeti.IsProPSylow.continuousMulEquivMaximalProPQuotient`: the resulting topological group
  isomorphism `P ≃ₜ* G(p)`.
* `TauCeti.isProPSylow_iff_isClosed_and_bijective_domRestrict_maximalProPQuotient_mk`: the closed
  subgroups mapping bijectively onto `G(p)` are exactly the Sylow pro-`p` subgroups.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsMulCommutative G]
  {P : Subgroup G}

/-- In a commutative profinite group, a pro-`p` subgroup meets the pro-`p` kernel trivially: a
nontrivial element of the subgroup has nontrivial image of `p`-power order in some finite
quotient, hence survives in a `p`-group quotient. -/
theorem IsProP.disjoint_proPKernel (hP : IsProP p P) : Disjoint P (proPKernel p G) := by
  refine Subgroup.disjoint_def.mpr fun {x} hxP hxK ↦ ?_
  by_contra hx1
  obtain ⟨U, hxU⟩ : ∃ U : OpenNormalSubgroup G, x ∉ U.toSubgroup := by
    by_contra h
    exact hx1 (Subgroup.eq_one_of_mem_iInf_openNormalSubgroup (not_exists_not.mp h))
  -- The class of `x` in the finite commutative group `G ⧸ U` is nontrivial of `p`-power order.
  have hcomm : IsMulCommutative (G ⧸ U.toSubgroup) :=
    ⟨⟨fun a b ↦ QuotientGroup.induction_on a fun a ↦ QuotientGroup.induction_on b fun b ↦ by
      rw [← QuotientGroup.mk_mul, mul_comm', QuotientGroup.mk_mul]⟩⟩
  obtain ⟨k, hk⟩ := hP.isPGroup_map_mk' U ⟨x, Subgroup.mem_map_of_mem _ hxP⟩
  obtain ⟨N, hN, hxN⟩ := exists_isPGroup_quotient_notMem_of_pow_pow_eq_one
    (a := (x : G ⧸ U.toSubgroup)) (by simpa [Subtype.ext_iff] using hk)
    (by rwa [Ne, QuotientGroup.eq_one_iff])
  -- Its preimage in `G` is an open normal subgroup with `p`-group quotient not containing `x`.
  let V : OpenNormalSubgroup G :=
    { toOpenSubgroup := ⟨N.comap (QuotientGroup.mk' U.toSubgroup),
        Subgroup.isOpen_mono (fun y hy ↦ by
          simp [Subgroup.mem_comap, (QuotientGroup.eq_one_iff y).mpr hy]) U.isOpen⟩
      isNormal' := inferInstance }
  exact hxN (mem_proPKernel_iff.mp hxK V (hN.quotient_comap _))

namespace IsProPSylow

/-- A Sylow pro-`p` subgroup of a commutative profinite group maps bijectively onto the maximal
pro-`p` quotient. -/
theorem bijective_domRestrict_maximalProPQuotient_mk (hP : IsProPSylow p P) :
    Function.Bijective ((maximalProPQuotient.mk p G).domRestrict P) := by
  refine ⟨fun x y hxy ↦ Subtype.ext ?_, fun z ↦ ?_⟩
  · -- Injectivity: the kernel of the restriction is `P ⊓ proPKernel p G = ⊥`.
    have hmem : ((x : G) * (y : G)⁻¹) ∈ proPKernel p G := by
      rw [← QuotientGroup.ker_mk' (proPKernel p G), MonoidHom.mem_ker, map_mul, map_inv,
        mul_inv_eq_one]
      exact hxy
    exact mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hP.isProP.disjoint_proPKernel
      (P.mul_mem x.2 (P.inv_mem y.2)) hmem)
  · -- Surjectivity: the image of `P` is a Sylow pro-`p` subgroup of the pro-`p` group `G(p)`.
    have himage : P.map (maximalProPQuotient.mk p G) = ⊤ :=
      (hP.map_of_surjective _ (maximalProPQuotient.continuous_mk p G)
        (maximalProPQuotient.mk_surjective p G)).eq_top isProP_maximalProPQuotient
    have hz : z ∈ P.map (maximalProPQuotient.mk p G) := by
      rw [himage]
      exact Subgroup.mem_top z
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **A Sylow pro-`p` subgroup of a commutative profinite group is its maximal pro-`p`
quotient**: the quotient map restricts to a topological group isomorphism `P ≃ₜ* G(p)`. -/
noncomputable def continuousMulEquivMaximalProPQuotient (hP : IsProPSylow p P) :
    P ≃ₜ* maximalProPQuotient p G :=
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP.isClosed.isCompact
  have hcont : Continuous ((maximalProPQuotient.mk p G).domRestrict P) :=
    (maximalProPQuotient.continuous_mk p G).comp continuous_subtype_val
  ContinuousMulEquiv.mk (MulEquiv.ofBijective _ hP.bijective_domRestrict_maximalProPQuotient_mk)
    hcont (hcont.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective _ hP.bijective_domRestrict_maximalProPQuotient_mk).toEquiv))

/-- The isomorphism from a Sylow pro-`p` subgroup onto the maximal pro-`p` quotient is the
quotient map. -/
@[simp]
theorem continuousMulEquivMaximalProPQuotient_apply (hP : IsProPSylow p P) (x : P) :
    hP.continuousMulEquivMaximalProPQuotient x = maximalProPQuotient.mk p G x :=
  (rfl)

end IsProPSylow

/-- **The Sylow pro-`p` subgroups of a commutative profinite group** are exactly the closed
subgroups that map bijectively onto the maximal pro-`p` quotient. -/
theorem isProPSylow_iff_isClosed_and_bijective_domRestrict_maximalProPQuotient_mk :
    IsProPSylow p P ↔
      IsClosed (P : Set G) ∧ Function.Bijective ((maximalProPQuotient.mk p G).domRestrict P) := by
  refine ⟨fun hP ↦ ⟨hP.isClosed, hP.bijective_domRestrict_maximalProPQuotient_mk⟩,
    fun ⟨hclosed, hbij⟩ ↦ ?_⟩
  -- `P` is pro-`p`, being isomorphic to `G(p)`, so it lies in a Sylow pro-`p` subgroup `Q`; the
  -- quotient map is injective on `Q` and already surjective on `P`, so `P = Q`.
  have : CompactSpace P := isCompact_iff_compactSpace.mp hclosed.isCompact
  have hcont : Continuous ((maximalProPQuotient.mk p G).domRestrict P) :=
    (maximalProPQuotient.continuous_mk p G).comp continuous_subtype_val
  have hP : IsProP p P :=
    (isProP_maximalProPQuotient (p := p) (G := G)).of_equiv
      (ContinuousMulEquiv.mk (MulEquiv.ofBijective _ hbij) hcont
        (hcont.continuous_symm_of_equiv_compact_to_t2
          (f := (MulEquiv.ofBijective _ hbij).toEquiv))).symm
  obtain ⟨Q, hQ, hPQ⟩ := hP.exists_le_isProPSylow
  convert hQ using 1
  refine le_antisymm hPQ fun y hy ↦ ?_
  obtain ⟨⟨x, hx⟩, hxy⟩ := hbij.2 (maximalProPQuotient.mk p G y)
  have hxy' : x = y :=
    congrArg Subtype.val (hQ.bijective_domRestrict_maximalProPQuotient_mk.1
      (a₁ := ⟨x, hPQ hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  exact hxy' ▸ hx

end TauCeti
