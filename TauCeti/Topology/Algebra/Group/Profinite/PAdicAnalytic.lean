/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Characteristic
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Uniform

/-!
# Compact `p`-adic analytic groups

By Lazard's theorem, a profinite group carries the structure of a `p`-adic analytic group exactly
when it has an open subgroup that is a uniform pro-`p` group. This file takes the group-theoretic
side of that characterization as the definition: `TauCeti.IsCompactPAdicAnalytic p G` says that
`G` is compact and totally disconnected and has an open normal subgroup that is uniform at `p`
(`TauCeti.IsUniform`). Finite discrete groups and `ℤ_p ^ d` are examples. Their completed group
algebras are the Iwasawa algebras of noncommutative Iwasawa theory, whose ring-theoretic
properties are controlled through an open normal uniform subgroup.

The **dimension** `TauCeti.padicAnalyticDim p G` is the dimension of any open uniform subgroup. It
does not depend on the subgroup: two open uniform subgroups have the same dimension
(`TauCeti.IsUniform.topologicalGeneratorRankNat_eq_of_isOpen`).

Open subgroups and quotients by closed normal subgroups of compact `p`-adic analytic groups are
again compact `p`-adic analytic, and an open subgroup has the same dimension. The common input is
that an open normal subgroup which is a topologically finitely generated powerful pro-`p` group
contains open normal uniform subgroups of the ambient group inside every neighbourhood of the
identity (`TauCeti.IsPowerful.exists_openNormalSubgroup_isUniform_subset`): the terms `λ_k` of its
lower `p`-series for large `k`.

## Main definitions

* `TauCeti.IsCompactPAdicAnalytic p G`: `G` is compact, totally disconnected, and has an open
  normal uniform subgroup.
* `TauCeti.padicAnalyticDim p G`: the dimension of an open uniform subgroup of `G`.

## Main results

* `TauCeti.IsUniform.padicAnalyticDim_eq`: every open uniform subgroup has dimension
  `padicAnalyticDim p G`.
* `TauCeti.IsCompactPAdicAnalytic.of_isOpen`,
  `TauCeti.IsCompactPAdicAnalytic.padicAnalyticDim_of_isOpen`: an open subgroup of a compact
  `p`-adic analytic group is compact `p`-adic analytic, of the same dimension.
* `TauCeti.IsCompactPAdicAnalytic.quotient`: the quotient by a closed normal subgroup is compact
  `p`-adic analytic.
* `TauCeti.IsCompactPAdicAnalytic.exists_isProP`: a compact `p`-adic analytic group has an open
  normal pro-`p` subgroup.
* `TauCeti.IsUniform.isCompactPAdicAnalytic`, `TauCeti.isCompactPAdicAnalytic_of_finite`,
  `TauCeti.isCompactPAdicAnalytic_multiplicative_pi_padicInt`: compact uniform groups, finite
  discrete groups and `ℤ_p ^ X` for finite `X` are compact `p`-adic analytic.
* `TauCeti.IsUniform.padicAnalyticDim_eq_topologicalGeneratorRankNat`,
  `TauCeti.padicAnalyticDim_of_finite`, `TauCeti.padicAnalyticDim_multiplicative_pi_padicInt`: a
  compact uniform group has its dimension as a uniform group, a finite discrete group has dimension
  `0`, and `ℤ_p ^ X` has dimension `#X`.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, second
  edition, Theorem 4.2 (the terms `λ_k` of a finitely generated powerful pro-`p` group are
  eventually uniform), Chapter 4 (the dimension) and Chapter 8 (Lazard's characterization).
* K. Ardakov and K. A. Brown, *Ring-theoretic properties of Iwasawa algebras: a survey*, §§2.1
  and 2.3.
-/

public section

namespace TauCeti

open Filter Topology

universe u

/-- A topological group is **compact `p`-adic analytic** when it is compact and totally
disconnected, hence profinite, and has an open normal subgroup that is uniform at `p`. This is the
group-theoretic side of Lazard's characterization of the profinite groups that carry a compatible
`p`-adic analytic structure; the analytic side is not formalized here. -/
structure IsCompactPAdicAnalytic (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop where
  /-- A compact `p`-adic analytic group is compact. -/
  compactSpace : CompactSpace G
  /-- A compact `p`-adic analytic group is totally disconnected. -/
  totallyDisconnectedSpace : TotallyDisconnectedSpace G
  /-- A compact `p`-adic analytic group has an open normal uniform subgroup. -/
  exists_isUniform : ∃ U : OpenNormalSubgroup G, IsUniform p U.toSubgroup

/-- The **dimension** of a compact `p`-adic analytic group: the dimension (topological generator
rank) of any of its open uniform subgroups, which does not depend on the subgroup by
`TauCeti.IsUniform.padicAnalyticDim_eq`. It is `0` for a group without open uniform subgroups. -/
noncomputable def padicAnalyticDim (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ℕ :=
  sInf {d | ∃ U : Subgroup G, IsOpen (U : Set G) ∧
    ∃ hU : IsUniform p U, topologicalGeneratorRankNat U hU.isTopologicallyFinitelyGenerated = d}

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

section Compact

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Every open uniform subgroup has dimension `padicAnalyticDim p G`.** -/
theorem IsUniform.padicAnalyticDim_eq {U : Subgroup G} (hU : IsUniform p U)
    (hUo : IsOpen (U : Set G)) :
    padicAnalyticDim p G = topologicalGeneratorRankNat U hU.isTopologicallyFinitelyGenerated := by
  obtain ⟨V, hVo, hV, hVd⟩ := Nat.sInf_mem (⟨_, U, hUo, hU, rfl⟩ :
    {d | ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∃ hU : IsUniform p U,
      topologicalGeneratorRankNat U hU.isTopologicallyFinitelyGenerated = d}.Nonempty)
  rw [padicAnalyticDim, ← hVd]
  exact hV.topologicalGeneratorRankNat_eq_of_isOpen hVo hUo hU

/-- **Open normal uniform subgroups inside a neighbourhood of the identity.** If `U` is an open
normal subgroup that is a topologically finitely generated powerful pro-`p` group, then every
neighbourhood of the identity contains an open normal subgroup of the ambient group that is
uniform: a term `λ_k` of the lower `p`-series of `U` for large `k`. -/
theorem IsPowerful.exists_openNormalSubgroup_isUniform_subset {U : Subgroup G} [U.Normal]
    (hU : IsPowerful p U) (hUo : IsOpen (U : Set G)) (hP : IsProP p U)
    (hfg : IsTopologicallyFinitelyGenerated U) {S : Set G} (hS : S ∈ 𝓝 (1 : G)) :
    ∃ W : OpenNormalSubgroup G, IsUniform p W.toSubgroup ∧ (W : Set G) ⊆ S := by
  obtain ⟨k, hopen, hk, hkS⟩ :=
    hU.exists_isUniform_map_pLowerCentralSeries_subset hUo hP hfg hS
  -- The term `λ_k(U)` is characteristic in the normal subgroup `U`, hence normal in `G`.
  have : ((pLowerCentralSeries p U k).map U.subtype).Normal :=
    (isTopCharacteristic_pLowerCentralSeries (G := U) p k).map_subtype_normal
  exact ⟨⟨⟨_, hopen⟩, this⟩, hk, hkS⟩

end Compact

namespace IsCompactPAdicAnalytic

omit hp in
/-- **A compact `p`-adic analytic group has an open normal pro-`p` subgroup.** -/
theorem exists_isProP (hG : IsCompactPAdicAnalytic p G) :
    ∃ U : OpenNormalSubgroup G, IsProP p U.toSubgroup :=
  hG.exists_isUniform.imp fun _ hU ↦ hU.isProP

/-- **An open subgroup of a compact `p`-adic analytic group is compact `p`-adic analytic.** -/
theorem of_isOpen (hG : IsCompactPAdicAnalytic p G) {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : IsCompactPAdicAnalytic p H := by
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  obtain ⟨U, hU⟩ := hG.exists_isUniform
  obtain ⟨W, hW, hWH⟩ := hU.isPowerful.exists_openNormalSubgroup_isUniform_subset U.isOpen
    hU.isProP hU.isTopologicallyFinitelyGenerated (hH.mem_nhds H.one_mem)
  exact ⟨isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen H hH).isCompact,
    inferInstance,
    ⟨⟨⟨_, Subgroup.subgroupOf_isOpen H W W.isOpen⟩, W.isNormal'.subgroupOf H⟩,
      (isUniform_subgroupOf_iff hWH).mpr hW⟩⟩

/-- **An open subgroup of a compact `p`-adic analytic group has the same dimension.** -/
theorem padicAnalyticDim_of_isOpen (hG : IsCompactPAdicAnalytic p G) {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : padicAnalyticDim p H = padicAnalyticDim p G := by
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  have : CompactSpace H := isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen H hH).isCompact
  obtain ⟨U, hU⟩ := hG.exists_isUniform
  obtain ⟨W, hW, hWH⟩ := hU.isPowerful.exists_openNormalSubgroup_isUniform_subset U.isOpen
    hU.isProP hU.isTopologicallyFinitelyGenerated (hH.mem_nhds H.one_mem)
  rw [((isUniform_subgroupOf_iff hWH).mpr hW).padicAnalyticDim_eq
    (Subgroup.subgroupOf_isOpen H W W.isOpen), hW.padicAnalyticDim_eq W.isOpen]
  exact (topologicalGeneratorRankNat_congr (Subgroup.subgroupOfContinuousMulEquivOfLe hWH) _)

/-- **A quotient of a compact `p`-adic analytic group by a closed normal subgroup is compact
`p`-adic analytic.** -/
theorem quotient (hG : IsCompactPAdicAnalytic p G) (N : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) : IsCompactPAdicAnalytic p (G ⧸ N) := by
  have := hG.compactSpace
  have := hG.totallyDisconnectedSpace
  have : IsClosed (N : Set G) := hN
  obtain ⟨U, hU⟩ := hG.exists_isUniform
  -- The image of `U` is an open normal powerful subgroup of the quotient. It need not be
  -- torsion-free, but it contains an open normal uniform subgroup.
  let f := (QuotientGroup.mk' N).subgroupMap U.toSubgroup
  have hf : Continuous f := continuous_induced_rng.mpr
    (QuotientGroup.continuous_mk.comp continuous_subtypeVal)
  have hfs : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  have : (U.toSubgroup.map (QuotientGroup.mk' N)).Normal :=
    U.isNormal'.map _ (QuotientGroup.mk'_surjective N)
  have hUo : IsOpen (U.toSubgroup.map (QuotientGroup.mk' N) : Set (G ⧸ N)) := by
    rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ U.isOpen
  obtain ⟨W, hW, -⟩ :=
    (hU.isPowerful.of_surjective f hf hfs).exists_openNormalSubgroup_isUniform_subset hUo
      (hU.isProP.of_surjective f hf hfs)
    (hU.isTopologicallyFinitelyGenerated.of_surjective hf hfs) univ_mem
  exact ⟨inferInstance, inferInstance, W, hW⟩

end IsCompactPAdicAnalytic

section Examples

omit hp in
/-- **A compact uniform group is compact `p`-adic analytic**, with the whole group as open normal
uniform subgroup. -/
theorem IsUniform.isCompactPAdicAnalytic [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsUniform p G) : IsCompactPAdicAnalytic p G :=
  ⟨inferInstance, inferInstance, ⊤, isUniform_top_iff.mpr hG⟩

/-- **The dimension of a compact uniform group** as a compact `p`-adic analytic group is its
dimension as a uniform group. -/
theorem IsUniform.padicAnalyticDim_eq_topologicalGeneratorRankNat [CompactSpace G]
    [TotallyDisconnectedSpace G] (hG : IsUniform p G) :
    padicAnalyticDim p G = topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated := by
  have hT := isUniform_top_iff.mpr hG
  rw [hT.padicAnalyticDim_eq isOpen_univ, hG.topologicalGeneratorRankNat_subgroup_eq isOpen_univ hT]

omit hp in
variable (p G) in
/-- **A finite discrete group is compact `p`-adic analytic**, with the trivial subgroup as open
normal uniform subgroup. -/
theorem isCompactPAdicAnalytic_of_finite [Finite G] [DiscreteTopology G] :
    IsCompactPAdicAnalytic p G :=
  ⟨inferInstance, inferInstance, ⟨⟨⊥, isOpen_discrete _⟩, inferInstance⟩,
    isUniform_of_subsingleton p _⟩

variable (p G) in
/-- **A finite discrete group has dimension `0`.** -/
theorem padicAnalyticDim_of_finite [Finite G] [DiscreteTopology G] : padicAnalyticDim p G = 0 := by
  rw [(isUniform_of_subsingleton p (⊥ : Subgroup G)).padicAnalyticDim_eq (isOpen_discrete _)]
  exact topologicalGeneratorRankNat_of_subsingleton _

variable (p) in
/-- **`ℤ_p ^ X` is compact `p`-adic analytic** for finite `X`. -/
theorem isCompactPAdicAnalytic_multiplicative_pi_padicInt (X : Type*) [Finite X] :
    IsCompactPAdicAnalytic p (Multiplicative (X → ℤ_[p])) :=
  (isUniform_multiplicative_pi_padicInt p X).isCompactPAdicAnalytic

variable (p) in
/-- **`ℤ_p ^ X` has dimension `#X`** for finite `X`. -/
theorem padicAnalyticDim_multiplicative_pi_padicInt (X : Type*) [Finite X] :
    padicAnalyticDim p (Multiplicative (X → ℤ_[p])) = Nat.card X := by
  rw [(isUniform_multiplicative_pi_padicInt p X).padicAnalyticDim_eq_topologicalGeneratorRankNat,
    topologicalGeneratorRankNat_multiplicative_pi_padicInt]

end Examples

end TauCeti
