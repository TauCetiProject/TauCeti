/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ConjInvariants
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank

/-!
# The invariant part of `H¹(N, 𝔽_p)` and the rank of `N ⧸ Nᵖ[N, G]`

Let `G` be a profinite group, `N` a closed normal subgroup, and `𝔽_p` the trivial `G`-module.
The `G`-invariant classes in `H¹(N, 𝔽_p)` are the continuous homomorphisms `N ⧸ Nᵖ[N, G] → 𝔽_p`
(`TauCeti.ContCohomology.H1ConjInvariantsEquivOfSmulEqSelf`), that is, the continuous `𝔽_p`-dual
of `N ⧸ Nᵖ[N, G]`. This quotient is a profinite group killed by `p`, hence pro-`p` whether or not
`G` is, so by Burnside's basis theorem the dimension of its dual is its topological generator rank.
So `H¹(N, 𝔽_p)^G` is finite exactly when `N ⧸ Nᵖ[N, G]` is topologically finitely generated, and
then it has `p ^ d(N ⧸ Nᵖ[N, G])` elements.

For a minimal presentation `1 → R → F → G → 1` of a pro-`p` group by a free pro-`p` group `F`,
the transgression identifies `H¹(R, 𝔽_p)^F` with `H²(G, 𝔽_p)`, and `d(R ⧸ Rᵖ[R, F])` is the least
number of generators of `R` as a closed normal subgroup of `F`. The count here is therefore what
makes the dimension of `H²(G, 𝔽_p)` the relation rank of `G`.

## Main results

* `TauCeti.finite_H1ConjInvariants_iff`: `H¹(N, 𝔽_p)^G` is finite exactly when
  `N ⧸ Nᵖ[N, G]` is topologically finitely generated.
* `TauCeti.natCard_H1ConjInvariants`: in that case `H¹(N, 𝔽_p)^G` has `p ^ d(N ⧸ Nᵖ[N, G])`
  elements.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.1) and (3.9.5).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §1.4.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {N : Subgroup G} [N.Normal]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]

variable (hN : IsClosed (N : Set G)) (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include hN htriv

/-- **Finiteness of `H¹(N, 𝔽_p)^G`.** For a closed normal subgroup `N` of a profinite group `G`,
the `G`-invariant part of `H¹(N, 𝔽_p)` is finite exactly when `N ⧸ Nᵖ[N, G]` is topologically
finitely generated. -/
theorem finite_H1ConjInvariants_iff :
    Finite (H1ConjInvariants G (ZMod p) N) ↔
      IsTopologicallyFinitelyGenerated (N ⧸ (pLowerCentralStep p N).subgroupOf N) := by
  have hK := isClosed_pLowerCentralStep_subgroupOf (p := p) N
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  have hQ : IsProP p (N ⧸ (pLowerCentralStep p N).subgroupOf N) :=
    (isPGroup_quotient_pLowerCentralStep_subgroupOf N).isProP
  rw [(H1ConjInvariantsEquivOfSmulEqSelf htriv p hN fun m ↦ by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]).toEquiv.finite_iff,
    ← Module.finite_iff_finite (R := ZMod p), ← Module.rank_lt_aleph0_iff,
    ← hQ.topologicalGeneratorRank_eq_rank_continuousZModDual,
    topologicalGeneratorRank_lt_aleph0_iff]

/-- **`H¹(N, 𝔽_p)^G` counts the generators of `N ⧸ Nᵖ[N, G]`.** For a closed normal subgroup `N`
of a profinite group `G` with `N ⧸ Nᵖ[N, G]` topologically finitely generated, the
`G`-invariant part of `H¹(N, 𝔽_p)` has `p ^ d(N ⧸ Nᵖ[N, G])` elements, where `d` is the
topological generator rank. -/
theorem natCard_H1ConjInvariants
    (h : IsTopologicallyFinitelyGenerated (N ⧸ (pLowerCentralStep p N).subgroupOf N)) :
    Nat.card (H1ConjInvariants G (ZMod p) N) =
      p ^ topologicalGeneratorRankNat (N ⧸ (pLowerCentralStep p N).subgroupOf N) h := by
  have hK := isClosed_pLowerCentralStep_subgroupOf (p := p) N
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  have hQ : IsProP p (N ⧸ (pLowerCentralStep p N).subgroupOf N) :=
    (isPGroup_quotient_pLowerCentralStep_subgroupOf N).isProP
  have := finite_continuousZModDual (p := p) h
  rw [Nat.card_congr (H1ConjInvariantsEquivOfSmulEqSelf htriv p hN fun m ↦ by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
    hQ.finrank_continuousZModDual_eq_topologicalGeneratorRankNat h]

end TauCeti
