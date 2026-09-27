/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.ContinuousDual
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank

/-!
# The `H¹` interpretation: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of `G`

For a profinite group `G`, a prime `p`, and the trivial `G`-module `𝔽_p = ZMod p`, a class of
`H¹(G, 𝔽_p)` is represented by a continuous `1`-cocycle, and with trivial coefficients a
continuous `1`-cocycle is a continuous character, so
`TauCeti.ContCohomology.H1EquivOfSmulEqSelf` identifies `H¹(G, 𝔽_p)` with the group of
continuous `𝔽_p`-valued characters of `G`. The characteristic fact of this degree is that the
`1`-coboundaries vanish in it — the character group is what is left over, not a quotient of a
larger group of homomorphisms.

This file supplies the `𝔽_p`-vector-space structure that this identification deserves. Scalar `p`
kills the character values, hence every continuous `1`-cocycle with values in `𝔽_p`, hence the
classes of `H¹(G, 𝔽_p)`, which therefore form an `𝔽_p`-vector space
(`TauCeti.instModuleH1`); the additive correspondence of the degree-one file then becomes an
isomorphism of `𝔽_p`-vector spaces (`TauCeti.h1EquivContinuousZModDual`), and composing it with
precomposition along the projection to the pro-`p` Frattini quotient gives the further
identification with the continuous `𝔽_p`-dual of `G ⧸ Φ(G)`
(`TauCeti.h1EquivFrattiniQuotientDual`).

Burnside's basis theorem in cardinal form
(`TauCeti.IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual`) transfers from the
continuous dual to `H¹`, and this is the content of the transfer: the dimension of `H¹(G, 𝔽_p)`
over `𝔽_p` is the topological generator rank of `G`, with no finiteness hypothesis. In particular
`H¹(G, 𝔽_p)` is finite-dimensional exactly when the pro-`p` group `G` is topologically finitely
generated, which is the finite-dimensionality the two-term Euler formula for an open subgroup
`U ≤ G` needs for the four spaces `H⁰` and `H¹` of `U` and `G`, and a topologically finitely
generated `G` has `p ^ d(G)` classes in `H¹(G, 𝔽_p)`, where `d` is the topological generator
rank.

## Main definitions

* `TauCeti.instModuleH1`: `H¹(G, 𝔽_p)` is an `𝔽_p`-vector space.
* `TauCeti.h1EquivContinuousZModDual`: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual
  `TauCeti.continuousZModDual p G` of `G`, as `𝔽_p`-vector spaces.
* `TauCeti.h1EquivFrattiniQuotientDual`: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of the
  pro-`p` Frattini quotient `G ⧸ Φ(G)`.

## Main results

* `TauCeti.IsProP.rank_H1_eq_topologicalGeneratorRank`: the dimension of `H¹(G, 𝔽_p)` over
  `𝔽_p` is the topological generator rank of `G`, as an identity of cardinals.
* `TauCeti.IsProP.finrank_H1_eq_topologicalGeneratorRankNat`: the natural-number form of the
  same identity, for a topologically finitely generated pro-`p` group.
* `TauCeti.IsProP.finite_H1_iff`: `H¹(G, 𝔽_p)` is finite-dimensional over `𝔽_p` exactly when
  `G` is topologically finitely generated.
* `TauCeti.IsProP.natCard_H1`: in that case `H¹(G, 𝔽_p)` has `p ^ d(G)` elements.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §1.3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.1).
-/

public section

namespace TauCeti

open ContCohomology

universe u

-- For prime `p`, `AddCommGroup (ZMod p)` is also derivable from `[IsSimpleAddGroup (ZMod p)]
-- [AddGroup.IsNilpotent (ZMod p)]`; that structure is not reducibly the ring one, so the
-- `DistribMulAction G (ZMod p)` hypothesis below would not match what `H1` expects. Preferring the
-- ring path locally keeps a single additive structure on `ZMod p`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime]

section ModuleStructure

variable {G : Type u} [Monoid G] [TopologicalSpace G] [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)]

/-- **`H¹(G, 𝔽_p)` is an `𝔽_p`-vector space.** Scalar `p` kills every continuous
`𝔽_p`-valued character, so it kills the group of continuous `1`-cocycles, and the quotient by the
`1`-coboundaries inherits the `𝔽_p`-module structure of the character group
`TauCeti.continuousZModDual p G`. -/
noncomputable instance instModuleH1 : Module (ZMod p) (H1 G (ZMod p)) :=
  QuotientAddGroup.zmodModule fun x ↦ by
    -- The `p`-fold multiple of a cocycle with values in `ZMod p` is the zero cocycle, and the
    -- zero cocycle is a `1`-coboundary.
    have hx : (p • x : Z1 G (ZMod p)) = 0 := by
      apply Subtype.ext
      funext g
      simp
    rw [hx]
    exact AddSubgroup.zero_mem _

end ModuleStructure

section ContinuousDual

variable {G : Type u} [Group G] [TopologicalSpace G] [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)] (htriv : ∀ (g : G) (m : ZMod p), g • m = m)

include htriv

/-- **`H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of `G`.** A class of `H¹(G, 𝔽_p)` is sent to
the continuous homomorphism `G → Multiplicative 𝔽_p` that its cocycle defines, which for trivial
coefficients is that cocycle itself, as an isomorphism of `𝔽_p`-vector spaces. -/
noncomputable def h1EquivContinuousZModDual : H1 G (ZMod p) ≃ₗ[ZMod p] continuousZModDual p G :=
  (H1EquivOfSmulEqSelf htriv).toLinearEquiv (ZMod.map_smul (H1EquivOfSmulEqSelf htriv))

/-- **`H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of the pro-`p` Frattini quotient.** Every
continuous `𝔽_p`-valued character of `G` kills the pro-`p` Frattini subgroup, so the continuous
characters of `G` and those of `G ⧸ Φ(G)` are the same, and with them their `𝔽_p`-module
structures. -/
noncomputable def h1EquivFrattiniQuotientDual :
    H1 G (ZMod p) ≃ₗ[ZMod p] continuousZModDual p (G ⧸ proPFrattini p G) :=
  (h1EquivContinuousZModDual htriv).trans
    (frattiniQuotientDualEquiv (p := p)).symm

end ContinuousDual

section Burnside

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]

/-- **Burnside's basis theorem for `H¹`, cardinal form.** The dimension of `H¹(G, 𝔽_p)` over
`𝔽_p` is the topological generator rank of a profinite pro-`p` group `G`, as an identity of
cardinals and with no finiteness hypothesis. -/
theorem IsProP.rank_H1_eq_topologicalGeneratorRank (hG : IsProP p G)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) :
    Module.rank (ZMod p) (H1 G (ZMod p)) = topologicalGeneratorRank G := by
  rw [(h1EquivContinuousZModDual htriv).rank_eq,
    ← hG.topologicalGeneratorRank_eq_rank_continuousZModDual]

/-- **Burnside's basis theorem for `H¹`, numerical form.** The dimension of `H¹(G, 𝔽_p)` over
`𝔽_p` is the natural-number topological generator rank of a topologically finitely generated
profinite pro-`p` group. -/
theorem IsProP.finrank_H1_eq_topologicalGeneratorRankNat (hG : IsProP p G)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) (hfg : IsTopologicallyFinitelyGenerated G) :
    Module.finrank (ZMod p) (H1 G (ZMod p)) =
      topologicalGeneratorRankNat G hfg := by
  rw [(h1EquivContinuousZModDual htriv).finrank_eq,
    hG.finrank_continuousZModDual_eq_topologicalGeneratorRankNat hfg]

/-- **Finiteness of `H¹(G, 𝔽_p)`.** For a profinite pro-`p` group, `H¹(G, 𝔽_p)` is
finite-dimensional over `𝔽_p` exactly when `G` is topologically finitely generated. -/
theorem IsProP.finite_H1_iff (hG : IsProP p G) (htriv : ∀ (g : G) (m : ZMod p), g • m = m) :
    Module.Finite (ZMod p) (H1 G (ZMod p)) ↔ IsTopologicallyFinitelyGenerated G := by
  rw [Module.finite_iff_finite (R := ZMod p), (h1EquivContinuousZModDual htriv).toEquiv.finite_iff,
    ← Module.finite_iff_finite (R := ZMod p), ← Module.rank_lt_aleph0_iff,
    ← hG.topologicalGeneratorRank_eq_rank_continuousZModDual,
    topologicalGeneratorRank_lt_aleph0_iff]

/-- **`H¹(G, 𝔽_p)` counts the generators of `G`.** For a topologically finitely generated
profinite pro-`p` group, `H¹(G, 𝔽_p)` has `p ^ d(G)` elements, where `d` is the topological
generator rank. -/
theorem IsProP.natCard_H1 (hG : IsProP p G) (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    Nat.card (H1 G (ZMod p)) = p ^ topologicalGeneratorRankNat G hfg := by
  -- `hfin` is the finite-dimensionality of the continuous dual, which
  -- `Module.natCard_eq_pow_finrank` needs to count a finite vector space.
  have hfin := finite_continuousZModDual (p := p) (G := G) hfg
  rw [Nat.card_congr (h1EquivContinuousZModDual htriv).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
    hG.finrank_continuousZModDual_eq_topologicalGeneratorRankNat hfg]

end Burnside

end TauCeti
