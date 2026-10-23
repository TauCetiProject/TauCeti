/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank

/-!
# `H¹(G, 𝔽_p)` of a pro-`p` group and its generator rank

For a profinite pro-`p` group `G`, the dimension of `H¹(G, 𝔽_p)` over `𝔽_p` is the topological
generator rank of `G`: the cohomology `cohomFp p G 1` is the continuous `𝔽_p`-dual of `G`
(`TauCeti.cohomFpLinearEquivContinuousZModDual`), whose dimension Burnside's basis theorem reads as
the rank (`TauCeti.IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual`). The identity is
stated first for cardinals, with no finiteness hypothesis, and then for the natural-number rank of
a topologically finitely generated group; in between, `H¹(G, 𝔽_p)` is finite-dimensional exactly
when `G` is topologically finitely generated. These are the statements through which a
finite-dimensionality hypothesis on `H¹(G, 𝔽_p)`, such as the one in the definition of a Demushkin
group, is converted into finite generation and a rank.

## Main results

* `TauCeti.IsProP.rank_cohomFp_one`: `dim_{𝔽_p} H¹(G, 𝔽_p) = d(G)` as cardinals.
* `TauCeti.IsProP.finite_cohomFp_one_iff`: `H¹(G, 𝔽_p)` is finite-dimensional exactly when `G` is
  topologically finitely generated.
* `TauCeti.IsProP.finrank_cohomFp_one`: `dim_{𝔽_p} H¹(G, 𝔽_p) = d(G)` for a topologically finitely
  generated pro-`p` group.

## References

* J.-P. Serre, *Galois Cohomology*, I §4.2.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.1).
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The dimension of `H¹(G, 𝔽_p)` is the topological generator rank**, for a profinite pro-`p`
group `G`, as an identity of cardinals with no finiteness hypothesis. -/
theorem IsProP.rank_cohomFp_one (hG : IsProP p G) :
    Module.rank (ZMod p) (cohomFp p G 1) = topologicalGeneratorRank G := by
  rw [hG.topologicalGeneratorRank_eq_rank_continuousZModDual]
  exact (cohomFpLinearEquivContinuousZModDual p G).rank_eq

/-- **`H¹(G, 𝔽_p)` is finite-dimensional exactly when `G` is topologically finitely generated**,
for a profinite pro-`p` group `G`. -/
theorem IsProP.finite_cohomFp_one_iff (hG : IsProP p G) :
    Module.Finite (ZMod p) (cohomFp p G 1) ↔ IsTopologicallyFinitelyGenerated G := by
  rw [← Module.rank_lt_aleph0_iff, hG.rank_cohomFp_one, topologicalGeneratorRank_lt_aleph0_iff]

/-- **The dimension of `H¹(G, 𝔽_p)` is the topological generator rank**, for a topologically
finitely generated profinite pro-`p` group `G`. -/
theorem IsProP.finrank_cohomFp_one (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) :
    Module.finrank (ZMod p) (cohomFp p G 1) = topologicalGeneratorRankNat G hfg := by
  rw [Module.finrank, hG.rank_cohomFp_one,
    ← topologicalGeneratorRankNat_eq_topologicalGeneratorRank, Cardinal.toNat_natCast]

end TauCeti
