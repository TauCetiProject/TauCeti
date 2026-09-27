/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomFpH1
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
numerical transfer that follows, for which compactness and total disconnectedness are needed. The
same two identifications on the canonical carrier `TauCeti.cohomFp p G 1` are
`TauCeti.cohomFpEquivContinuousZModDual`, stated for every modulus and with no action of `G`
assumed, in `TauCeti.RepresentationTheory.Homological.ContCohomology.CohomFpH1`, and
`TauCeti.cohomFpEquivFrattiniQuotientDual` here, the latter computed in both directions by
`TauCeti.cohomFpEquivFrattiniQuotientDual_apply` and
`TauCeti.cohomFpEquivFrattiniQuotientDual_symm_apply`.

Here `H¹` is the explicit inhomogeneous group `TauCeti.ContCohomology.H1 G (ZMod p) = Z¹/B¹`,
which depends on the action of `G` on the coefficients, so a statement about it names the action it
is made under. Continuous cohomology with the same coefficients is reached through
`TauCeti.h1EquivCohomFp : H1 G (ZMod p) ≃ₗ[ZMod p] cohomFp p G 1`, the degree-one comparison
with the coefficient object `TauCeti.trivialFp p G` of `TauCeti.cohomFp` as a `ZMod p`-linear
isomorphism of modules. That coefficient object carries the trivial action of `G` by itself, so a
statement about the canonical carrier `TauCeti.cohomFp p G 1` is a statement about the
coefficients of `TauCeti.cohomFp` alone, under no action of `G` beyond the one it comes with.
Each of the four
results below is therefore stated on both carriers: the `H¹` form is the one the transfer of
Burnside's basis theorem computes, under the trivial ambient action, and the `cohomFp` form is the
same invariant of the canonical carrier. The `ZMod p`-module structure on the explicit side is
`TauCeti.instModuleH1`, the one on the canonical side is the canonical module structure of
`TauCeti.cohomFp`.

For a profinite pro-`p` group, Burnside's basis theorem in cardinal form
(`TauCeti.IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual`) transfers from the
continuous dual to `H¹`, and this is the content of the transfer: the dimension of `H¹(G, 𝔽_p)`
over `𝔽_p` is the topological generator rank of `G`, with no finiteness hypothesis. In particular
`H¹(G, 𝔽_p)` is finite-dimensional exactly when the pro-`p` group `G` is topologically finitely
generated, which is the finite-dimensionality the two-term Euler formula for an open subgroup
`U ≤ G` needs for the four spaces `H⁰` and `H¹` of `U` and `G`, and a topologically finitely
generated `G` has `p ^ d(G)` classes in `H¹(G, 𝔽_p)`, where `d` is the topological generator
rank. Each of the four statements is also available on the canonical carrier
`TauCeti.cohomFp p G 1`, where no action of `G` has to be named.

## Main definitions

* `TauCeti.h1EquivFrattiniQuotientDual`: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of the
  pro-`p` Frattini quotient `G ⧸ Φ(G)`.
* `TauCeti.cohomFpEquivFrattiniQuotientDual`: the same identification with the Frattini quotient,
  with `TauCeti.cohomFp p G 1` in place of `H¹(G, 𝔽_p)`. Its companion without the Frattini
  quotient, `TauCeti.cohomFpEquivContinuousZModDual`, is in
  `TauCeti.RepresentationTheory.Homological.ContCohomology.CohomFpH1`.

## Main results

* `TauCeti.h1EquivFrattiniQuotientDual_apply_mk` and
  `TauCeti.h1EquivFrattiniQuotientDual_symm_apply`: the identification in both directions, evaluated
  on the Frattini quotient.
* `TauCeti.cohomFpEquivFrattiniQuotientDual_apply` and
  `TauCeti.cohomFpEquivFrattiniQuotientDual_symm_apply`: the identification on the canonical
  carrier, in both directions, evaluated on the homogeneous `1`-cocycle a class carries and on a
  continuous character of the Frattini quotient.
* `TauCeti.IsProP.rank_H1_eq_topologicalGeneratorRank`: the dimension of `H¹(G, 𝔽_p)` over
  `𝔽_p` is the topological generator rank of `G`, as an identity of cardinals.
* `TauCeti.IsProP.finrank_H1_eq_topologicalGeneratorRankNat`: the natural-number form of the
  same identity, for a topologically finitely generated pro-`p` group.
* `TauCeti.IsProP.finite_H1_iff`: `H¹(G, 𝔽_p)` is finite-dimensional over `𝔽_p` exactly when
  `G` is topologically finitely generated.
* `TauCeti.IsProP.natCard_H1`: in that case `H¹(G, 𝔽_p)` has `p ^ d(G)` elements.
* `TauCeti.IsProP.rank_cohomFp_eq_topologicalGeneratorRank`,
  `TauCeti.IsProP.finrank_cohomFp_eq_topologicalGeneratorRankNat`,
  `TauCeti.IsProP.finite_cohomFp_iff` and `TauCeti.IsProP.natCard_cohomFp`: the same four
  results, with the carrier `TauCeti.cohomFp p G 1` of the canonical continuous cohomology, whose
  coefficients carry the trivial action of `G` by themselves.

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

/-- The trivial action of `G` on `ZMod p`, the action the coefficients of `TauCeti.cohomFp` carry by
construction, so that the `H¹(G, 𝔽_p)` appearing in the statement below is the one of those
coefficients and not one made under an ambient action. It is the action
`TauCeti.RepresentationTheory.Homological.ContCohomology.CohomFpH1` uses for the same reason. -/
local instance instTrivialDistribMulActionZMod : DistribMulAction G (ZMod p) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_add _ _ _ := rfl
  smul_zero _ := rfl

/-- The trivial action of `G` on `ZMod p` is continuous, being independent of `G`. -/
local instance instTrivialContinuousSMulZMod : ContinuousSMul G (ZMod p) where
  continuous_smul := ⟨fun _s hs => hs.preimage continuous_snd⟩

/-- **`TauCeti.cohomFp p G 1` is the continuous `𝔽_p`-dual of the pro-`p` Frattini quotient.** This
is `TauCeti.cohomFpEquivContinuousZModDual` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.CohomFpH1` followed by precomposition
along the projection to the Frattini quotient, and it needs no hypothesis on an action of `G`: the
coefficient object of `TauCeti.cohomFp` carries the trivial action by construction. -/
noncomputable def cohomFpEquivFrattiniQuotientDual :
    cohomFp p G 1 ≃ₗ[ZMod p] continuousZModDual p (G ⧸ proPFrattini p G) :=
  (cohomFpEquivContinuousZModDual p G).trans (frattiniQuotientDualEquiv (p := p)).symm

/-- The image of a canonical cohomology class is the character its homogeneous cocycle defines on
the pro-`p` Frattini quotient: evaluated on the class of `g` it is the value of the inhomogeneous
`1`-cocycle the class carries, read through `TauCeti.trivialFpEquiv`. -/
@[simp]
theorem cohomFpEquivFrattiniQuotientDual_apply
    (c : _root_.ContinuousCohomology.cocycles (trivialFp p G) 1) (g : G) :
    Additive.toMul (cohomFpEquivFrattiniQuotientDual
        ((TopRep.homogeneousCochains (trivialFp p G)).homologyπ 1 c))
      (g : G ⧸ proPFrattini p G) = Multiplicative.ofAdd
          (trivialFpEquiv p G (((cohomFpCocycleEquiv1 p G).symm c :
            G → ULift.{u} (ZMod p)) g)) := by
  simp only [cohomFpEquivFrattiniQuotientDual, LinearEquiv.trans_apply,
    frattiniQuotientDualEquiv_symm_apply_mk, cohomFpEquivContinuousZModDual_apply]

/-- The inverse image of a continuous `𝔽_p`-valued character of the pro-`p` Frattini
quotient is the canonical cohomology class of the homogeneous `1`-cocycle it corresponds to, read
from the class in `H¹(G, 𝔽_p)`. -/
@[simp]
theorem cohomFpEquivFrattiniQuotientDual_symm_apply
    (φ : continuousZModDual p (G ⧸ proPFrattini p G)) :
    (cohomFpEquivFrattiniQuotientDual).symm φ
      = h1EquivCohomFp (fun _ _ => rfl)
          (((Z1EquivOfSmulEqSelf (fun _ _ => rfl)).symm
              ((frattiniQuotientDualEquiv (p := p) (G := G)) φ) : H1 G (ZMod p))) := by
  refine (cohomFpEquivFrattiniQuotientDual).symm_apply_eq.2 ?_
  rw [cohomFpEquivFrattiniQuotientDual, LinearEquiv.trans_apply,
    ← cohomFpEquivContinuousZModDual_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply]

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

section BurnsideCohomFp

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Burnside's basis theorem for `TauCeti.cohomFp p G 1`, cardinal form.** The dimension of the
degree-one continuous cohomology of a pro-`p` group `G` with trivial `𝔽_p` coefficients over
`TauCeti.cohomFp` is the topological generator rank of `G`, as an identity of cardinals and with
no finiteness hypothesis. The coefficients of `TauCeti.cohomFp` carry the trivial action of `G` by
construction, so this statement mentions no action of `G`. -/
theorem IsProP.rank_cohomFp_eq_topologicalGeneratorRank (hG : IsProP p G) :
    Module.rank (ZMod p) (cohomFp p G 1) = topologicalGeneratorRank G := by
  rw [cohomFpEquivContinuousZModDual p G |>.rank_eq,
    ← hG.topologicalGeneratorRank_eq_rank_continuousZModDual]

/-- **Burnside's basis theorem for `TauCeti.cohomFp p G 1`, numerical form.** The dimension of the
degree-one continuous cohomology of a topologically finitely generated profinite pro-`p` group
with trivial `𝔽_p` coefficients over `TauCeti.cohomFp` is its topological generator rank. -/
theorem IsProP.finrank_cohomFp_eq_topologicalGeneratorRankNat (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    Module.finrank (ZMod p) (cohomFp p G 1) = topologicalGeneratorRankNat G hfg := by
  rw [cohomFpEquivContinuousZModDual p G |>.finrank_eq,
    hG.finrank_continuousZModDual_eq_topologicalGeneratorRankNat hfg]

/-- **Finiteness of the degree-one continuous cohomology with trivial `𝔽_p` coefficients.** For a
profinite pro-`p` group, `TauCeti.cohomFp p G 1` is finite-dimensional over `𝔽_p` exactly when `G`
is topologically finitely generated. -/
theorem IsProP.finite_cohomFp_iff (hG : IsProP p G) :
    Module.Finite (ZMod p) (cohomFp p G 1) ↔ IsTopologicallyFinitelyGenerated G := by
  rw [Module.finite_iff_finite (R := ZMod p),
    (cohomFpEquivContinuousZModDual p G).toEquiv.finite_iff,
    ← Module.finite_iff_finite (R := ZMod p), hG.finite_continuousZModDual_iff]

/-- **`TauCeti.cohomFp p G 1` counts the generators of `G`.** For a topologically finitely
generated profinite pro-`p` group, the degree-one continuous cohomology with trivial `𝔽_p`
coefficients has `p ^ d(G)` elements, where `d` is the topological generator rank. -/
theorem IsProP.natCard_cohomFp (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) :
    Nat.card (cohomFp p G 1) = p ^ topologicalGeneratorRankNat G hfg := by
  -- `hfin` is the finite-dimensionality of the continuous dual, which
  -- `Module.natCard_eq_pow_finrank` needs to count a finite vector space.
  have hfin : Module.Finite (ZMod p) (continuousZModDual p G) :=
    hG.finite_continuousZModDual_iff.mpr hfg
  rw [Nat.card_congr (cohomFpEquivContinuousZModDual p G).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
    hG.finrank_continuousZModDual_eq_topologicalGeneratorRankNat hfg]

end BurnsideCohomFp

end TauCeti
