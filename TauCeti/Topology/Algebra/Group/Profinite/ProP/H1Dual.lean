/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank

/-!
# The `H¹` interpretation for a pro-`p` group: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of the
# Frattini quotient

For a group `G` with a topology, a prime `p`, and the trivial `G`-module `𝔽_p = ZMod p`, a class
of `H¹(G, 𝔽_p)` is represented by a continuous `1`-cocycle, and with trivial coefficients a
continuous `1`-cocycle is a continuous character, so
`TauCeti.ContCohomology.H1EquivOfSmulEqSelf` identifies `H¹(G, 𝔽_p)` with the group of
continuous `𝔽_p`-valued characters of `G`. The characteristic fact of this degree is that the
`1`-coboundaries vanish in it — the character group is what is left over, not a quotient of a
larger group of homomorphisms. The `ZMod p`-module structure that makes this identification an
isomorphism of `𝔽_p`-vector spaces (`TauCeti.instModuleH1`,
`TauCeti.h1EquivContinuousZModDual`) needs neither profiniteness nor a pro-`p` hypothesis, and
holds for every modulus `n`, not only for a prime.

Every continuous `𝔽_p`-valued character of `G` also kills the pro-`p` Frattini subgroup, so
composing the above with precomposition along the projection to the Frattini quotient gives the
further identification with the continuous `𝔽_p`-dual of `G ⧸ Φ(G)`
(`TauCeti.h1EquivFrattiniQuotientDual`), whose application lemmas
`TauCeti.h1EquivFrattiniQuotientDual_apply_mk` and
`TauCeti.h1EquivFrattiniQuotientDual_symm_apply` compute it in both directions. This step, too,
needs neither profiniteness nor a pro-`p` hypothesis; what is specific to a pro-`p` group is the
numerical transfer that follows, for which compactness and total disconnectedness are needed.

Here `H¹` is the explicit inhomogeneous group `TauCeti.ContCohomology.H1 G (ZMod p) = Z¹/B¹`,
which depends on the action of `G` on the coefficients, so a statement about it names the action it
is made under. The canonical carrier of that same cohomology is `TauCeti.cohomFp p G 1`, whose
coefficients carry the trivial action of `G` by themselves, so a statement about it names no
action of `G` at all. The identification of the two models of degree one is the existing
`TauCeti.cohomFpAddEquivH1` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit`, which this file does
not restate; on the canonical carrier it reads as `TauCeti.cohomFpLinearEquivContinuousZModDual`,
the continuous `𝔽_p`-dual of `G`, and `TauCeti.cohomFpEquivFrattiniQuotientDual` here is that
equivalence followed by the precomposition along the projection to the Frattini quotient. The
dimension and finiteness of that carrier are `TauCeti.IsProP.rank_cohomFp_one`,
`TauCeti.IsProP.finrank_cohomFp_one` and `TauCeti.IsProP.finite_cohomFp_one_iff` of
`TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomFp`; this file does not restate them.

For a profinite pro-`p` group, Burnside's basis theorem in cardinal form
(`TauCeti.IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual`) transfers from the
continuous dual to `H¹`, and this is the content of the transfer: the dimension of `H¹(G, 𝔽_p)`
over `𝔽_p` is the topological generator rank of `G`, with no finiteness hypothesis. In particular
`H¹(G, 𝔽_p)` is finite-dimensional exactly when the pro-`p` group `G` is topologically finitely
generated, which is the finite-dimensionality the two-term Euler formula for an open subgroup
`U ≤ G` needs for the four spaces `H⁰` and `H¹` of `U` and `G`. The count of elements,
`p ^ d(G)` for a topologically finitely generated `G` and generator rank `d`, is the existing
`TauCeti.IsProP.natCard_H1_of_natCard_eq` of
`TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.Basic`, which this file does
not restate; on the canonical carrier `TauCeti.cohomFp p G 1` it is that theorem read through the
existing `TauCeti.cohomFpAddEquivH1`, so it is not restated on that carrier either.

## Main definitions

* `TauCeti.h1EquivFrattiniQuotientDual`: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of the
  pro-`p` Frattini quotient `G ⧸ Φ(G)`.
* `TauCeti.cohomFpEquivFrattiniQuotientDual`: the same identification with the Frattini quotient,
  with `TauCeti.cohomFp p G 1` in place of `H¹(G, 𝔽_p)`, read from the two existing
  equivalences rather than from a new comparison of the two models of degree one.

## Main results

* `TauCeti.h1EquivFrattiniQuotientDual_apply_mk` and
  `TauCeti.h1EquivFrattiniQuotientDual_symm_apply`: the identification in both directions, evaluated
  on the Frattini quotient.
* `TauCeti.cohomFpEquivFrattiniQuotientDual_apply` and
  `TauCeti.cohomFpEquivFrattiniQuotientDual_symm_apply`: the same identification in both directions
  on the carrier `TauCeti.cohomFp p G 1`, read through the two equivalences it is built from.
* `TauCeti.IsProP.rank_H1_eq_topologicalGeneratorRank`: the dimension of `H¹(G, 𝔽_p)` over
  `𝔽_p` is the topological generator rank of `G`, as an identity of cardinals.
* `TauCeti.IsProP.finrank_H1_eq_topologicalGeneratorRankNat`: the natural-number form of the
  same identity, for a topologically finitely generated pro-`p` group.
* `TauCeti.IsProP.finite_H1_iff`: `H¹(G, 𝔽_p)` is finite-dimensional over `𝔽_p` exactly when
  `G` is topologically finitely generated.

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

section ContinuousDual

variable {G : Type u} [Group G] [TopologicalSpace G] [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)] (htriv : ∀ (g : G) (m : ZMod p), g • m = m)

include htriv

/-- **`H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of the pro-`p` Frattini quotient.** Every
continuous `𝔽_p`-valued character of `G` kills the pro-`p` Frattini subgroup, so the continuous
characters of `G` and those of `G ⧸ Φ(G)` are the same, and with them their `𝔽_p`-module
structures. -/
noncomputable def h1EquivFrattiniQuotientDual :
    H1 G (ZMod p) ≃ₗ[ZMod p] continuousZModDual p (G ⧸ proPFrattini p G) :=
  (h1EquivContinuousZModDual htriv).trans
    (frattiniQuotientDualEquiv (p := p)).symm

/-- The image of a class of `H¹(G, 𝔽_p)` is the character its cocycle defines on the Frattini
quotient: evaluated on the class of `g` it is the cocycle's value at `g`. -/
@[simp]
theorem h1EquivFrattiniQuotientDual_apply_mk (f : Z1 G (ZMod p)) (g : G) :
    Additive.toMul (h1EquivFrattiniQuotientDual htriv (f : H1 G (ZMod p)))
      (g : G ⧸ proPFrattini p G) = Multiplicative.ofAdd ((f : G → ZMod p) g) := by
  simp [h1EquivFrattiniQuotientDual]

/-- The inverse image of a continuous `𝔽_p`-valued character of the Frattini quotient is the
class in `H¹(G, 𝔽_p)` of the continuous `1`-cocycle that lifts it to `G`. -/
@[simp]
theorem h1EquivFrattiniQuotientDual_symm_apply
    (x : continuousZModDual p (G ⧸ proPFrattini p G)) :
    (h1EquivFrattiniQuotientDual htriv).symm x
      = ((Z1EquivOfSmulEqSelf htriv).symm ((frattiniQuotientDualEquiv (p := p) (G := G)) x)
          : H1 G (ZMod p)) := by
  refine (h1EquivFrattiniQuotientDual htriv).symm_apply_eq.2 ?_
  rw [h1EquivFrattiniQuotientDual, LinearEquiv.trans_apply,
    ← h1EquivContinuousZModDual_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply]

end ContinuousDual

section CohomFp

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **`TauCeti.cohomFp p G 1` is the continuous `𝔽_p`-dual of the pro-`p` Frattini quotient.**
This is `TauCeti.cohomFpLinearEquivContinuousZModDual` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit` followed by the
precomposition along the projection to the Frattini quotient, and it needs no hypothesis on an
action of `G`: the coefficient object of `TauCeti.cohomFp` carries the trivial action by
construction. It is not a second form of `TauCeti.h1EquivFrattiniQuotientDual`; the identification
of the two models of degree one is the existing `TauCeti.cohomFpAddEquivH1`, which this file does
not restate. -/
noncomputable def cohomFpEquivFrattiniQuotientDual :
    cohomFp p G 1 ≃ₗ[ZMod p] continuousZModDual p (G ⧸ proPFrattini p G) :=
  (cohomFpLinearEquivContinuousZModDual p G).trans (frattiniQuotientDualEquiv (p := p)).symm

/-- A class of `TauCeti.cohomFp p G 1` maps to the character of the Frattini quotient obtained by
reading the class, through `TauCeti.cohomFpLinearEquivContinuousZModDual`, on that quotient. -/
@[simp]
theorem cohomFpEquivFrattiniQuotientDual_apply (x : cohomFp p G 1) :
    cohomFpEquivFrattiniQuotientDual (p := p) x
      = (frattiniQuotientDualEquiv (p := p)).symm (cohomFpLinearEquivContinuousZModDual p G x) := by
  rw [cohomFpEquivFrattiniQuotientDual, LinearEquiv.trans_apply]

/-- A continuous `𝔽_p`-valued character of the Frattini quotient is read, through
`TauCeti.frattiniQuotientDualEquiv`, as a character of `G` and then lifted by
`TauCeti.cohomFpLinearEquivContinuousZModDual` to a class of `TauCeti.cohomFp p G 1`. -/
@[simp]
theorem cohomFpEquivFrattiniQuotientDual_symm_apply
    (x : continuousZModDual p (G ⧸ proPFrattini p G)) :
    (cohomFpEquivFrattiniQuotientDual (p := p)).symm x
      = (cohomFpLinearEquivContinuousZModDual p G).symm (frattiniQuotientDualEquiv (p := p) x) := by
  rw [cohomFpEquivFrattiniQuotientDual, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]

end CohomFp

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
    ← Module.finite_iff_finite (R := ZMod p), hG.finite_continuousZModDual_iff]

end Burnside

end TauCeti
