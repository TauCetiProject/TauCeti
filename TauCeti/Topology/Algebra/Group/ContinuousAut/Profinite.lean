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
* `TauCeti.ContinuousAut.exists_mapQuotient_eq_of_forall_exists_le`: the same along any cofinal
  family of characteristic open normal subgroups.
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

/-- A family of automorphisms of the quotients by a cofinal family of characteristic open normal
subgroups, compatible with the quotient maps and composed with the quotient maps, is a compatible
family of homomorphisms `G →* G ⧸ N i`, so it is induced by a unique endomorphism of `G`. -/
private theorem existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk' {ι : Type*}
    {N : ι → OpenNormalSubgroup G} (hcof : ∀ U : OpenNormalSubgroup G, ∃ i, N i ≤ U)
    (τ : ∀ i, MulAut (G ⧸ (N i : Subgroup G)))
    (hτ : ∀ ⦃i j : ι⦄ (hle : N i ≤ N j) (q : G ⧸ (N i : Subgroup G)),
      QuotientGroup.mapOfLE hle (τ i q) = τ j (QuotientGroup.mapOfLE hle q)) :
    ∃! f : G →* G, ∀ i, (QuotientGroup.mk' (N i : Subgroup G)).comp f =
      (τ i).toMonoidHom.comp (QuotientGroup.mk' (N i : Subgroup G)) :=
  existsUnique_monoidHom_mk'_comp_eq_of_forall_exists_le hcof _
    fun i j hle ↦ MonoidHom.ext fun g ↦ by simp [hτ hle]

/-- An endomorphism of `G` whose composite with the quotient map by each member of a cofinal
family of open normal subgroups factors through that quotient map is continuous, because the
open quotients are discrete. -/
private theorem continuous_of_forall_mk'_comp_eq {ι : Type*} {N : ι → OpenNormalSubgroup G}
    (hcof : ∀ U : OpenNormalSubgroup G, ∃ i, N i ≤ U)
    (τ : ∀ i, MulAut (G ⧸ (N i : Subgroup G))) (f : G →* G)
    (hf : ∀ i, (QuotientGroup.mk' (N i : Subgroup G)).comp f =
      (τ i).toMonoidHom.comp (QuotientGroup.mk' (N i : Subgroup G))) :
    Continuous f := by
  refine continuous_iff_forall_continuous_mk.mpr fun U ↦ ?_
  obtain ⟨i, hle⟩ := hcof U
  have := QuotientGroup.discreteTopology (N i).isOpen
  have : (fun a : G ↦ (f a : G ⧸ U.toSubgroup)) =
      (QuotientGroup.mapOfLE hle ∘ τ i) ∘ QuotientGroup.mk := funext fun a ↦ by
    have h : (f a : G ⧸ (N i : Subgroup G)) = τ i a := DFunLike.congr_fun (hf i) a
    simp [← h]
  rw [this]
  exact continuous_of_discreteTopology.comp QuotientGroup.continuous_mk

/-- Let `N i` be a family of topologically characteristic open normal subgroups of a profinite
group `G`, cofinal among the open normal subgroups. A family of automorphisms of the quotients
`G ⧸ N i` that is compatible with the quotient maps `G ⧸ N i → G ⧸ N j` for `N i ≤ N j` is induced
by a continuous automorphism of `G`. -/
theorem exists_mapQuotient_eq_of_forall_exists_le {ι : Type*} {N : ι → OpenNormalSubgroup G}
    (hN : ∀ i, IsTopCharacteristic G (N i)) (hcof : ∀ U : OpenNormalSubgroup G, ∃ i, N i ≤ U)
    (σ : ∀ i, MulAut (G ⧸ (N i : Subgroup G)))
    (hσ : ∀ ⦃i j : ι⦄ (hle : N i ≤ N j) (q : G ⧸ (N i : Subgroup G)),
      QuotientGroup.mapOfLE hle (σ i q) = σ j (QuotientGroup.mapOfLE hle q)) :
    ∃ φ : ContinuousAut G, ∀ i, mapQuotient (hN i) φ = σ i := by
  -- The family and its inverse are realized by endomorphisms `f` and `g` of `G`.
  obtain ⟨f, hf, -⟩ := existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk' hcof σ hσ
  obtain ⟨g, hg, -⟩ := existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk' hcof
    (fun i ↦ (σ i).symm) fun i j hle q ↦ (σ j).injective (by
      rw [← hσ hle, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])
  -- Both composites induce the identity on every quotient of the family, so they are the
  -- identity by the uniqueness clause of the limit description.
  have hid : ∀ h : G →* G, (∀ i, (QuotientGroup.mk' (N i : Subgroup G)).comp h =
      QuotientGroup.mk' (N i : Subgroup G)) → h = MonoidHom.id G := fun h hh ↦ by
    obtain ⟨f₀, -, huniq⟩ := existsUnique_monoidHom_mk'_comp_eq_toMonoidHom_comp_mk' hcof
      (fun i ↦ MulEquiv.refl _) fun i j hle q ↦ by simp
    exact (huniq h fun i ↦ by simpa using hh i).trans
      (huniq (MonoidHom.id G) fun i ↦ by simp).symm
  have hcomp : ∀ i (a : G),
      (f (g a) : G ⧸ (N i : Subgroup G)) = a ∧ (g (f a) : G ⧸ (N i : Subgroup G)) = a := by
    intro i a
    have h1 := DFunLike.congr_fun (hf i) (g a)
    have h2 := DFunLike.congr_fun (hg i) a
    have h3 := DFunLike.congr_fun (hf i) a
    have h4 := DFunLike.congr_fun (hg i) (f a)
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
      at h1 h2 h3 h4
    rw [h1, h2, MulEquiv.apply_symm_apply, h4, h3, MulEquiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  have hfg : f.comp g = MonoidHom.id G :=
    hid _ fun i ↦ MonoidHom.ext fun a ↦ (hcomp i a).1
  have hgf : g.comp f = MonoidHom.id G :=
    hid _ fun i ↦ MonoidHom.ext fun a ↦ (hcomp i a).2
  let φ : ContinuousAut G :=
    { toFun := f
      invFun := g
      left_inv := fun a ↦ DFunLike.congr_fun hgf a
      right_inv := fun a ↦ DFunLike.congr_fun hfg a
      map_mul' := map_mul f
      continuous_toFun := continuous_of_forall_mk'_comp_eq hcof σ f hf
      continuous_invFun := continuous_of_forall_mk'_comp_eq hcof _ g hg }
  refine ⟨φ, fun i ↦ MulEquiv.ext fun q ↦ ?_⟩
  induction q using QuotientGroup.induction_on with
  | H a => exact (mapQuotient_mk (hN i) φ a).trans (DFunLike.congr_fun (hf i) a)

/-- For a topologically finitely generated profinite group `G`, a family of automorphisms of the
characteristic open quotients `G ⧸ N` that is compatible with the quotient maps `G ⧸ N → G ⧸ M`
for `N ≤ M` is induced by a continuous automorphism of `G`. -/
theorem exists_mapQuotient_eq (hG : IsTopologicallyFinitelyGenerated G)
    (σ : ∀ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N},
      MulAut (G ⧸ (N.1 : Subgroup G)))
    (hσ : ∀ ⦃N M : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}⦄ (hle : N.1 ≤ M.1)
      (q : G ⧸ (N.1 : Subgroup G)),
      QuotientGroup.mapOfLE hle (σ N q) = σ M (QuotientGroup.mapOfLE hle q)) :
    ∃ φ : ContinuousAut G, ∀ N, mapQuotient N.2 φ = σ N :=
  exists_mapQuotient_eq_of_forall_exists_le (N := Subtype.val) Subtype.property
    (fun U ↦
      let ⟨N, hN, hle⟩ := hG.exists_isTopCharacteristic_le U.toOpenSubgroup
      ⟨⟨N, hN⟩, hle⟩)
    σ hσ

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
