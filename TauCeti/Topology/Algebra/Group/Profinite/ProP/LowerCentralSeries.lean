/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Limit
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration

/-!
# The lower `p`-series of a profinite group

The lower `p`-series `λ_k = TauCeti.pLowerCentralSeries p G k` of a topological group is defined
and studied for arbitrary topological groups in `TauCeti.Topology.Algebra.Group.LowerCentralSeries`.
This file adds what holds for a profinite group `G` and a prime `p`.

For a profinite group and a prime `p`, the first term `λ_1` is the pro-`p` Frattini subgroup
`TauCeti.proPFrattini p G`. Primality matters: for `p = 4` and the cyclic group of order two,
fourth powers and commutators are trivial, so `λ_1` is trivial, while the pro-`4` Frattini
subgroup is the whole group.

For a topologically finitely generated profinite group and a prime `p`, every `λ_k` is open, hence
of finite index, and in a topologically finitely generated pro-`p` group the quotients `G ⧸ λ_k`
are finite `p`-groups; in particular the graded pieces `gr_k(G) = λ_k ⧸ λ_{k+1}` are finite.
Without finite generation the terms need not be open: an infinite product of copies of `ℤ ⧸ p`
has `λ_1 = 1`, so `gr_0(G) = G` is infinite.

In a pro-`p` group the series is **cofinal** among the open normal subgroups: every open normal
subgroup contains some `λ_k`. So the `λ_k` have trivial intersection, and a pro-`p` group is the
inverse limit of its quotients `G ⧸ λ_k`: a compatible sequence of cosets comes from a unique
element, and a map into `G` is continuous as soon as its composites with the quotient maps are.
Cofinality needs no finite generation. With it, the `λ_k` are open, so they form a neighbourhood
basis of `1` and the quotients `G ⧸ λ_k` are finite `p`-groups; this is what lets two topologically
finitely generated pro-`p` groups be compared level by level along their lower `p`-series.

## Main results

* `TauCeti.pLowerCentralSeries_one_eq_proPFrattini`: for a prime `p`, `λ_1` is the pro-`p`
  Frattini subgroup of a profinite group.
* `TauCeti.IsTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries`: for a prime `p`, in a
  topologically finitely generated profinite group every `λ_k` is open, so
  `TauCeti.IsTopologicallyFinitelyGenerated.finite_quotient_pLowerCentralSeries`,
  `TauCeti.IsTopologicallyFinitelyGenerated.finite_gradedPiece` and, for a pro-`p` group,
  `TauCeti.IsProP.isPGroup_quotient_pLowerCentralSeries`.
* `TauCeti.IsProP.exists_pLowerCentralSeries_le`: in a pro-`p` group every open normal subgroup
  contains a term of the lower `p`-series, so `TauCeti.IsProP.iInf_pLowerCentralSeries_eq_bot`.
* `TauCeti.IsProP.existsUnique_forall_mk_eq_pLowerCentralSeries` and
  `TauCeti.IsProP.existsUnique_monoidHom_mk'_comp_eq_pLowerCentralSeries`: a pro-`p` group is the
  inverse limit of its quotients `G ⧸ λ_k`, for elements and for homomorphisms.
* `TauCeti.IsProP.continuous_iff_forall_continuous_mk_pLowerCentralSeries`: a map into a pro-`p`
  group is continuous exactly when its composites with the quotient maps `G → G ⧸ λ_k` are.
* `TauCeti.IsProP.hasAntitoneBasis_nhds_one_pLowerCentralSeries`: in a topologically finitely
  generated pro-`p` group the lower `p`-series is a neighbourhood basis of `1`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- For a profinite group and a prime `p`, the first term of the lower `p`-series is the pro-`p`
Frattini subgroup. -/
theorem pLowerCentralSeries_one_eq_proPFrattini (hp : p.Prime) :
    pLowerCentralSeries p G 1 = proPFrattini p G := by
  rw [pLowerCentralSeries_one, proPFrattini_eq_topologicalClosure hp]

/-- **Openness of the lower `p`-series.** For a prime `p`, in a topologically finitely generated
profinite group every term of the lower `p`-series is open. -/
theorem IsTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    IsOpen (pLowerCentralSeries p G k : Set G) := by
  induction k with
  | zero => rw [pLowerCentralSeries_zero, coe_top]; exact isOpen_univ
  | succ k ih =>
    let U : OpenSubgroup G := ⟨pLowerCentralSeries p G k, ih⟩
    have : CompactSpace U.toSubgroup :=
      isCompact_iff_compactSpace.mp (isClosed_pLowerCentralSeries k).isCompact
    have hopen : IsOpen (proPFrattini p U.toSubgroup : Set U.toSubgroup) :=
      (hG.of_openSubgroup U).isOpen_proPFrattini p
    -- The Frattini subgroup of `λ_k` maps into `λ_{k+1}`.
    have hle : (proPFrattini p U.toSubgroup).map U.toSubgroup.subtype ≤
        pLowerCentralSeries p G (k + 1) := by
      rw [proPFrattini_eq_topologicalClosure hp, pLowerCentralSeries_succ, pLowerCentralStep_def]
      refine (U.toSubgroup.subtype.map_topologicalClosure_le continuous_subtype_val _).trans
        (topologicalClosure_mono ?_)
      rw [Subgroup.map_sup, MonoidHom.map_closure, commutator_def, map_commutator]
      refine sup_le (le_sup_of_le_left ((Subgroup.closure_le _).mpr ?_))
        (le_sup_of_le_right (commutator_mono (map_subtype_le _) le_top))
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨x, x.2, (Subgroup.coe_pow _ x p).symm⟩
    refine isOpen_mono hle ?_
    rw [coe_map, coe_subtype]
    exact ih.isOpenMap_subtype_val _ hopen

/-- For a prime `p`, in a topologically finitely generated profinite group every quotient
`G ⧸ λ_k` is finite. -/
theorem IsTopologicallyFinitelyGenerated.finite_quotient_pLowerCentralSeries
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    Finite (G ⧸ pLowerCentralSeries p G k) :=
  quotient_finite_of_isOpen _ (hG.isOpen_pLowerCentralSeries hp k)

/-- For a prime `p`, in a topologically finitely generated profinite group every graded piece
`gr_k(G) = λ_k ⧸ λ_{k+1}` of the lower `p`-series is finite. -/
theorem IsTopologicallyFinitelyGenerated.finite_gradedPiece
    (hG : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    Finite (gradedPiece p G k) :=
  have := hG.finite_quotient_pLowerCentralSeries hp (k + 1)
  Finite.of_injective _ (gradedPieceInclusion_injective k)

/-- For a prime `p`, in a topologically finitely generated pro-`p` group every quotient `G ⧸ λ_k`
is a finite `p`-group. -/
theorem IsProP.isPGroup_quotient_pLowerCentralSeries (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) (k : ℕ) :
    IsPGroup p (G ⧸ pLowerCentralSeries p G k) :=
  isProP_iff.mp hG ⟨⟨pLowerCentralSeries p G k, hfg.isOpen_pLowerCentralSeries hp k⟩,
    inferInstance⟩

/-! ### Cofinality of the lower `p`-series in a pro-`p` group -/

open Filter Topology

omit [TotallyDisconnectedSpace G] in
/-- **Cofinality of the lower `p`-series.** In a compact pro-`p` group every open normal subgroup
contains a term of the lower `p`-series. No finite generation is needed. -/
theorem IsProP.exists_pLowerCentralSeries_le (hG : IsProP p G) (hp : p.Prime)
    (U : OpenNormalSubgroup G) : ∃ k, pLowerCentralSeries p G k ≤ U.toSubgroup := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := ((isProP_iff.mp hG U).to_subgroup ⊤).exists_pLowerCentralSeries_eq_bot
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.ker_mk' U.toSubgroup, ← Subgroup.map_eq_bot_iff,
    (QuotientGroup.mk' U.toSubgroup).map_pLowerCentralSeries_eq_of_surjective
      QuotientGroup.continuous_mk QuotientGroup.continuous_mk.isClosedMap
      (QuotientGroup.mk'_surjective _),
    pLowerCentralSeries_eq_of_discreteTopology, hk]

/-- In a pro-`p` group the terms of the lower `p`-series have trivial intersection. -/
theorem IsProP.iInf_pLowerCentralSeries_eq_bot (hG : IsProP p G) (hp : p.Prime) :
    ⨅ k, pLowerCentralSeries p G k = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← Subgroup.iInf_openNormalSubgroup_eq_bot (G := G)]
  refine le_iInf fun U ↦ ?_
  obtain ⟨k, hk⟩ := hG.exists_pLowerCentralSeries_le hp U
  exact (iInf_le _ k).trans hk

/-- **A pro-`p` group is the inverse limit of its quotients by the lower `p`-series.** A sequence
of cosets of the `λ_k`, compatible along the quotient maps, is realized by a unique element. -/
theorem IsProP.existsUnique_forall_mk_eq_pLowerCentralSeries (hG : IsProP p G) (hp : p.Prime)
    (x : ∀ k, G ⧸ pLowerCentralSeries p G k)
    (hcompat : ∀ (k : ℕ) (g : G), (g : G ⧸ pLowerCentralSeries p G (k + 1)) = x (k + 1) →
      (g : G ⧸ pLowerCentralSeries p G k) = x k) :
    ∃! g : G, ∀ k, (g : G ⧸ pLowerCentralSeries p G k) = x k :=
  existsUnique_forall_mk_eq_of_iInf_eq_bot isClosed_pLowerCentralSeries
    (hG.iInf_pLowerCentralSeries_eq_bot hp) x hcompat

/-- **A pro-`p` group is the inverse limit of its quotients by the lower `p`-series, for
homomorphisms.** A sequence of homomorphisms `H →* G ⧸ λ_k`, compatible along the quotient maps,
is induced by a unique homomorphism `H →* G`. -/
theorem IsProP.existsUnique_monoidHom_mk'_comp_eq_pLowerCentralSeries (hG : IsProP p G)
    (hp : p.Prime) {H : Type*} [MulOneClass H] (x : ∀ k, H →* G ⧸ pLowerCentralSeries p G k)
    (hx : ∀ k, (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k)).comp (x (k + 1)) = x k) :
    ∃! φ : H →* G, ∀ k, (QuotientGroup.mk' (pLowerCentralSeries p G k)).comp φ = x k :=
  existsUnique_monoidHom_mk'_comp_eq_of_iInf_eq_bot pLowerCentralSeries_succ_le
    isClosed_pLowerCentralSeries (hG.iInf_pLowerCentralSeries_eq_bot hp) x hx

/-- **The lower `p`-series is a neighbourhood basis of `1`** in a topologically finitely generated
pro-`p` group. -/
theorem IsProP.hasAntitoneBasis_nhds_one_pLowerCentralSeries (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hp : p.Prime) :
    (𝓝 (1 : G)).HasAntitoneBasis fun k ↦ (pLowerCentralSeries p G k : Set G) :=
  hasAntitoneBasis_nhds_one_of_iInf_eq_bot pLowerCentralSeries_antitone
    (hfg.isOpen_pLowerCentralSeries hp) (hG.iInf_pLowerCentralSeries_eq_bot hp)

/-- A map into a pro-`p` group is continuous exactly when all of its composites with the quotient
maps `G → G ⧸ λ_k` are. No finite generation is needed. -/
theorem IsProP.continuous_iff_forall_continuous_mk_pLowerCentralSeries (hG : IsProP p G)
    (hp : p.Prime) {X : Type*} [TopologicalSpace X] {f : X → G} :
    Continuous f ↔ ∀ k, Continuous fun x ↦ (f x : G ⧸ pLowerCentralSeries p G k) :=
  continuous_iff_forall_continuous_mk_of_iInf_eq_bot isClosed_pLowerCentralSeries
    (hG.iInf_pLowerCentralSeries_eq_bot hp)

end TauCeti
