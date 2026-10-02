/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Congruence
public import TauCeti.Topology.Algebra.Group.Profinite.Limit

/-!
# Profiniteness of the continuous automorphism group

For a topologically finitely generated profinite group `G`, the congruence topology makes the
group `ContinuousAut G` of continuous automorphisms a profinite group, and the group
`ContinuousOut G` of continuous outer automorphisms is profinite for the quotient topology.

The characteristic quotient coordinates `ContinuousAut.mapQuotient` embed `ContinuousAut G` into
the product of the finite discrete groups `MulAut (G ⧸ N)`, `N` ranging over the topologically
characteristic open normal subgroups of `G` (`ContinuousAut.isEmbedding_pi_mapQuotient`). This
file identifies the range of that embedding: it consists exactly of the families of automorphisms
compatible with the quotient maps `G ⧸ N → G ⧸ M` for `N ≤ M`
(`ContinuousAut.range_pi_mapQuotient`). A compatible family is induced by a continuous
automorphism because `G` is the inverse limit of its characteristic open quotients, which are
cofinal among all open quotients; the limit description for homomorphisms along a cofinal family
(`TauCeti.existsUnique_monoidHom_mk'_comp_eq_of_forall_exists_le`) produces the endomorphism of
`G` and its inverse, and its uniqueness clause shows that the two are inverse to each other. The
compatibility conditions are closed in the product, so the range is closed and `ContinuousAut G`
is compact (`ContinuousAut.compactSpace`). The inner automorphisms then form a closed subgroup,
the image of the compact group `G`, and the outer automorphism group is a quotient of a profinite
group by a closed normal subgroup.

## Main results

* `TauCeti.ContinuousAut.exists_mapQuotient_eq`: every compatible family of automorphisms of the
  characteristic open quotients is induced by a continuous automorphism.
* `TauCeti.ContinuousAut.range_pi_mapQuotient`,
  `TauCeti.ContinuousAut.isClosedEmbedding_pi_mapQuotient`: the characteristic quotient
  coordinates are a closed embedding onto the compatible families.
* `TauCeti.ContinuousAut.compactSpace`: the congruence topology on the continuous automorphisms of
  a topologically finitely generated profinite group is compact.
* `TauCeti.ContinuousAut.isClosed_range_conj`: the inner automorphisms form a closed subgroup.
* `TauCeti.ContinuousOut.compactSpace`, `TauCeti.ContinuousOut.t2Space`,
  `TauCeti.ContinuousOut.totallyDisconnectedSpace`: the continuous outer automorphism group is
  profinite.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4.
-/

public section

open Topology

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace ContinuousAut

/-- A family of automorphisms of the characteristic open quotients compatible with the quotient
maps, composed with the quotient maps, is a compatible family of homomorphisms `G →* G ⧸ N`, so it
is induced by a unique endomorphism of `G`. -/
private theorem existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk'
    (hG : IsTopologicallyFinitelyGenerated G)
    (τ : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      MulAut (G ⧸ (N.1 : Subgroup G)))
    (hτ : ∀ ⦃N M : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}⦄ (hle : N.1 ≤ M.1)
      (q : G ⧸ (N.1 : Subgroup G)),
      QuotientGroup.mapOfLE hle (τ N q) = τ M (QuotientGroup.mapOfLE hle q)) :
    ∃! f : G →* G, ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      (QuotientGroup.mk' (N.1 : Subgroup G)).comp f =
        (τ N).toMonoidHom.comp (QuotientGroup.mk' (N.1 : Subgroup G)) :=
  existsUnique_monoidHom_mk'_comp_eq_of_forall_exists_le
    (fun U ↦
      let ⟨N, hN, hle⟩ := hG.exists_isTopCharacteristic_le U.toOpenSubgroup
      ⟨⟨N, hN⟩, hle⟩)
    _ fun N M hle ↦ MonoidHom.ext fun g ↦ by simp [hτ hle]

/-- An endomorphism of `G` whose composite with each characteristic quotient map factors through
that quotient map is continuous, because the characteristic open quotients are discrete and
cofinal. -/
private theorem continuous_of_forall_mk'_comp_eq (hG : IsTopologicallyFinitelyGenerated G)
    (τ : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      MulAut (G ⧸ (N.1 : Subgroup G))) (f : G →* G)
    (hf : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      (QuotientGroup.mk' (N.1 : Subgroup G)).comp f =
        (τ N).toMonoidHom.comp (QuotientGroup.mk' (N.1 : Subgroup G))) :
    Continuous f := by
  refine (continuous_iff_forall_continuous_mk_of_iInf_eq_bot
    (fun N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N} ↦ N.1.isClosed)
    hG.iInf_isTopCharacteristic_eq_bot).mpr fun N ↦ ?_
  have := QuotientGroup.discreteTopology N.1.isOpen
  have : (fun a : G ↦ (f a : G ⧸ (N.1 : Subgroup G))) = τ N ∘ QuotientGroup.mk :=
    funext fun a ↦ DFunLike.congr_fun (hf N) a
  rw [this]
  exact continuous_of_discreteTopology.comp QuotientGroup.continuous_mk

/-- For a topologically finitely generated profinite group `G`, a family of automorphisms of the
characteristic open quotients `G ⧸ N` that is compatible with the quotient maps `G ⧸ N → G ⧸ M`
for `N ≤ M` is induced by a continuous automorphism of `G`. -/
theorem exists_mapQuotient_eq (hG : IsTopologicallyFinitelyGenerated G)
    (σ : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      MulAut (G ⧸ (N.1 : Subgroup G)))
    (hσ : ∀ ⦃N M : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}⦄ (hle : N.1 ≤ M.1)
      (q : G ⧸ (N.1 : Subgroup G)),
      QuotientGroup.mapOfLE hle (σ N q) = σ M (QuotientGroup.mapOfLE hle q)) :
    ∃ φ : ContinuousAut G, ∀ N, mapQuotient N.2 φ = σ N := by
  -- The family and its inverse are realized by endomorphisms `f` and `g` of `G`.
  obtain ⟨f, hf, -⟩ := existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk' hG σ hσ
  obtain ⟨g, hg, -⟩ := existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk' hG
    (fun N ↦ (σ N).symm) fun N M hle q ↦ (σ M).injective (by
      rw [← hσ hle, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])
  -- Both composites induce the identity on every characteristic quotient, so they are the
  -- identity by the uniqueness clause of the limit description.
  have hid : ∀ h : G →* G, (∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      (QuotientGroup.mk' (N.1 : Subgroup G)).comp h = QuotientGroup.mk' (N.1 : Subgroup G)) →
      h = MonoidHom.id G := fun h hh ↦ by
    obtain ⟨f₀, -, huniq⟩ := existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk' hG
      (fun N ↦ MulEquiv.refl _) fun N M hle q ↦ by simp
    exact (huniq h fun N ↦ by simpa using hh N).trans
      (huniq (MonoidHom.id G) fun N ↦ by simp).symm
  have hcomp : ∀ (N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}) (a : G),
      (f (g a) : G ⧸ (N.1 : Subgroup G)) = a ∧ (g (f a) : G ⧸ (N.1 : Subgroup G)) = a := by
    intro N a
    have h1 := DFunLike.congr_fun (hf N) (g a)
    have h2 := DFunLike.congr_fun (hg N) a
    have h3 := DFunLike.congr_fun (hf N) a
    have h4 := DFunLike.congr_fun (hg N) (f a)
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
      at h1 h2 h3 h4
    rw [h1, h2, MulEquiv.apply_symm_apply, h4, h3, MulEquiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  have hfg : f.comp g = MonoidHom.id G :=
    hid _ fun N ↦ MonoidHom.ext fun a ↦ (hcomp N a).1
  have hgf : g.comp f = MonoidHom.id G :=
    hid _ fun N ↦ MonoidHom.ext fun a ↦ (hcomp N a).2
  let φ : ContinuousAut G :=
    { toFun := f
      invFun := g
      left_inv := fun a ↦ DFunLike.congr_fun hgf a
      right_inv := fun a ↦ DFunLike.congr_fun hfg a
      map_mul' := map_mul f
      continuous_toFun := continuous_of_forall_mk'_comp_eq hG σ f hf
      continuous_invFun := continuous_of_forall_mk'_comp_eq hG _ g hg }
  refine ⟨φ, fun N ↦ MulEquiv.ext fun q ↦ ?_⟩
  induction q using QuotientGroup.induction_on with
  | H a => exact (mapQuotient_mk N.2 φ a).trans (DFunLike.congr_fun (hf N) a)

/-- For a topologically finitely generated profinite group, the range of the joint characteristic
quotient coordinate map consists exactly of the families of automorphisms compatible with the
quotient maps between characteristic quotients: the continuous automorphisms of `G` are the
compatible families of automorphisms of its characteristic open quotients. -/
theorem range_pi_mapQuotient (hG : IsTopologicallyFinitelyGenerated G) :
    Set.range (fun (φ : ContinuousAut G)
        (N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}) ↦ mapQuotient N.2 φ) =
      {σ | ∀ ⦃N M : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}⦄ (hle : N.1 ≤ M.1)
        (q : G ⧸ (N.1 : Subgroup G)),
        QuotientGroup.mapOfLE hle (σ N q) = σ M (QuotientGroup.mapOfLE hle q)} := by
  ext σ
  constructor
  · rintro ⟨φ, rfl⟩ N M hle q
    exact mapOfLE_mapQuotient N.2 M.2 hle φ q
  · intro hσ
    obtain ⟨φ, hφ⟩ := exists_mapQuotient_eq hG σ hσ
    exact ⟨φ, funext hφ⟩

/-- For a topologically finitely generated profinite group, the range of the joint characteristic
quotient coordinate map is closed in the product of the discrete automorphism groups. -/
theorem isClosed_range_pi_mapQuotient (hG : IsTopologicallyFinitelyGenerated G) :
    letI : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      TopologicalSpace (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ ⊥
    IsClosed (Set.range fun (φ : ContinuousAut G)
      (N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}) ↦ mapQuotient N.2 φ) := by
  let _ : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
    TopologicalSpace (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ ⊥
  have : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
    DiscreteTopology (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ discreteTopology_bot _
  have : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
    DiscreteTopology (G ⧸ (N.1 : Subgroup G)) := fun N ↦ QuotientGroup.discreteTopology N.1.isOpen
  rw [range_pi_mapQuotient hG]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun N ↦ isClosed_iInter fun M ↦ isClosed_iInter fun hle ↦
    isClosed_iInter fun q ↦ isClosed_eq ?_ ?_
  · exact (continuous_of_discreteTopology
      (f := fun α : MulAut (G ⧸ (N.1 : Subgroup G)) ↦ QuotientGroup.mapOfLE hle (α q))).comp
      (continuous_apply N)
  · exact (continuous_of_discreteTopology
      (f := fun α : MulAut (G ⧸ (M.1 : Subgroup G)) ↦ α (QuotientGroup.mapOfLE hle q))).comp
      (continuous_apply M)

/-- For a topologically finitely generated profinite group, the joint characteristic quotient
coordinate map is a closed embedding of `ContinuousAut G` into the product of the discrete
automorphism groups of the characteristic open quotients. -/
theorem isClosedEmbedding_pi_mapQuotient (hG : IsTopologicallyFinitelyGenerated G) :
    letI : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      TopologicalSpace (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ ⊥
    IsClosedEmbedding fun (φ : ContinuousAut G)
      (N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}) ↦ mapQuotient N.2 φ := by
  let _ : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
    TopologicalSpace (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ ⊥
  exact ⟨isEmbedding_pi_mapQuotient hG, isClosed_range_pi_mapQuotient hG⟩

/-- For a topologically finitely generated profinite group, the congruence topology on the
continuous automorphisms is compact: `ContinuousAut G` is a closed subspace of the product of the
finite automorphism groups of the characteristic open quotients. -/
theorem compactSpace (hG : IsTopologicallyFinitelyGenerated G) :
    CompactSpace (ContinuousAut G) := by
  let _ : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
    TopologicalSpace (MulAut (G ⧸ (N.1 : Subgroup G))) := fun _ ↦ ⊥
  exact (isClosedEmbedding_pi_mapQuotient hG).compactSpace

/-- For a topologically finitely generated profinite group, the inner automorphisms form a closed
subgroup of `ContinuousAut G`: the image of the compact group `G` in a Hausdorff group. -/
theorem isClosed_range_conj (hG : IsTopologicallyFinitelyGenerated G) :
    IsClosed ((conj : G →* ContinuousAut G).range : Set (ContinuousAut G)) := by
  have := t2Space hG
  rw [MonoidHom.coe_range]
  exact (isCompact_range continuous_conj).isClosed

end ContinuousAut

namespace ContinuousOut

/-- For a topologically finitely generated profinite group, the continuous outer automorphism
group is compact for the quotient topology. -/
theorem compactSpace (hG : IsTopologicallyFinitelyGenerated G) : CompactSpace (ContinuousOut G) :=
  have := ContinuousAut.compactSpace hG
  inferInstance

/-- For a topologically finitely generated profinite group, the continuous outer automorphism
group is Hausdorff for the quotient topology: the inner automorphisms form a closed subgroup. -/
theorem t2Space (hG : IsTopologicallyFinitelyGenerated G) : T2Space (ContinuousOut G) :=
  have := ContinuousAut.isClosed_range_conj hG
  inferInstance

/-- For a topologically finitely generated profinite group, the continuous outer automorphism
group is totally disconnected for the quotient topology; with `ContinuousOut.compactSpace` and
`ContinuousOut.t2Space`, it is a profinite group. -/
theorem totallyDisconnectedSpace (hG : IsTopologicallyFinitelyGenerated G) :
    TotallyDisconnectedSpace (ContinuousOut G) :=
  have := ContinuousAut.compactSpace hG
  have := ContinuousAut.totallyDisconnectedSpace hG
  have := ContinuousAut.isClosed_range_conj hG
  inferInstance

end ContinuousOut

end TauCeti
