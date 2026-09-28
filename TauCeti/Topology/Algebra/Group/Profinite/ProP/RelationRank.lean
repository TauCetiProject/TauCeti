/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.MinimalPresentation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.NormalGeneration
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Transgression
import TauCeti.Data.Set.Finite
import TauCeti.Data.ZMod.TrivialAction
import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.Basic

/-!
# `H²(G, 𝔽_p)` counts the relations of a pro-`p` group

Let `G` be a profinite group with `H²(G, 𝔽_p) = 0`, for instance a free pro-`p` group, and let `N`
be a closed normal subgroup contained in the pro-`p` Frattini subgroup `Φ(G)`. The transgression
`H¹(N, 𝔽_p)^G → H²(G ⧸ N, 𝔽_p)` is then bijective
(`TauCeti.transgression_bijective_of_le_proPFrattini`), and `H¹(N, 𝔽_p)^G` is the continuous
`𝔽_p`-dual of `N ⧸ Nᵖ[N, G]` (`TauCeti.natCard_H1ConjInvariants`). So `H²(G ⧸ N, 𝔽_p)` is finite
exactly when `N ⧸ Nᵖ[N, G]` is topologically finitely generated, and then it has
`p ^ d(N ⧸ Nᵖ[N, G])` elements.

Applied to a minimal presentation `G ≅ ⟨X ∣ rels⟩` of a pro-`p` group, that is a presentation whose
relators lie in the Frattini subgroup of the free pro-`p` group `F` on `X`
(`TauCeti.presentedProP.subset_proPFrattini_iff_card_eq`), with relation subgroup `R` the closed
normal closure of the relators, this identifies the order of `H²(G, 𝔽_p)` with
`p ^ d(R ⧸ Rᵖ[R, F])`. By Burnside's basis theorem for normal generation
(`TauCeti.IsProP.topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_iff`), the exponent
`d(R ⧸ Rᵖ[R, F])` is the least number of generators of `R` as a closed normal subgroup of `F`: the
exponent `r` in the order `p ^ r` of `H²(G, 𝔽_p)` **counts the relations** of `G`. Since
`H²(G, 𝔽_p)` does not see the presentation, that count is the same for every minimal presentation
of `G`. This is the presentation independence of the relation rank.

For a presentation `G ≅ ⟨X ∣ rels⟩` on a finite type `X` that need not be minimal, the count is the
five-term exact sequence of `1 → R → F → G → 1`,

```text
0 → H¹(G, 𝔽_p) → H¹(F, 𝔽_p) → H¹(R, 𝔽_p)^F → H²(G, 𝔽_p) → H²(F, 𝔽_p) = 0,
```

in which `H¹(F, 𝔽_p)` has dimension `#X`, `H¹(G, 𝔽_p)` has dimension `d(G)` and `H¹(R, 𝔽_p)^F` has
dimension `d(R ⧸ Rᵖ[R, F])`: exactness gives `#X + r(G) = d(G) + d(R ⧸ Rᵖ[R, F])`
(`TauCeti.presentedProP.card_add_finrank_H2`). The surjectivity of the transgression alone shows
that `H²(G, 𝔽_p)` is finite as soon as `R ⧸ Rᵖ[R, F]` is topologically finitely generated, in
particular when there are finitely many relators, on any generating type `X`
(`TauCeti.presentedProP.finite_H2_of_finite`).

Since `H²(G, 𝔽_p)` is killed by `p` it is a vector space over `𝔽_p`
(`TauCeti.ContCohomology.instModuleZModH2`), and its dimension is the relation rank `r(G)` of `G`.
Read as an identity of cardinals, `dim H²(G, 𝔽_p) = d(R ⧸ Rᵖ[R, F])` needs no finiteness
hypothesis, exactly as Burnside's basis theorem
(`TauCeti.IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual`) does not: a topologically
finitely generated pro-`p` group with infinitely many relations has an `H²(G, 𝔽_p)` of infinite
dimension. When `R ⧸ Rᵖ[R, F]` is topologically finitely generated the dimension is the
natural-number rank, the exponent `r` in the count `p ^ r` above.

The statements are about the order and the dimension of `H²(G, 𝔽_p)`, for the explicit
continuous cohomology `H2` of the trivial `G`-module `𝔽_p`; the action of `G` on `ZMod p` is
carried as an instance together with the hypothesis that it is trivial, as in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual`. The statements about a quotient
`G ≅ F ⧸ R` of a free pro-`p` group `F` (`TauCeti.finite_H2_iff_of_le_proPFrattini`,
`TauCeti.natCard_H2_of_le_proPFrattini` and `TauCeti.card_add_finrank_H2_of_isClosed`) carry the
action of `F` on `𝔽_p` in the same way, as an instance with the hypothesis that it is trivial. The
`TauCeti.presentedProP` statements about a presentation do not: they supply the trivial action of
`F` internally, and only the action of `G` appears. The count and the finiteness for a presentation
on a finite type are also stated on the canonical carrier `cohomFp p G 2` of the relation rank, in
which no action appears at all (`TauCeti.presentedProP.card_add_finrank_cohomFp_two` and
`TauCeti.presentedProP.module_finite_cohomFp_two_of_finite`).

## Main results

* `TauCeti.natCard_H2_quotient_of_le_proPFrattini`: for profinite `G` with `H²(G, 𝔽_p) = 0` and
  `N ≤ Φ(G)` closed normal, `H²(G ⧸ N, 𝔽_p)` has `p ^ d(N ⧸ Nᵖ[N, G])` elements;
  `TauCeti.finite_H2_quotient_iff_of_le_proPFrattini` is the finiteness criterion.
* `TauCeti.natCard_H2_of_le_proPFrattini`: for `G ≅ F ⧸ R` with `F` a free pro-`p` group and
  `R ≤ Φ(F)` closed normal, `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])` elements;
  `TauCeti.finite_H2_iff_of_le_proPFrattini` is the finiteness criterion, and
  `TauCeti.lift_rank_H2_of_le_proPFrattini`, `TauCeti.finrank_H2_of_le_proPFrattini` are the
  dimension form of the count, as cardinals and as natural numbers.
* `TauCeti.presentedProP.natCard_H2`: for a minimal presentation `⟨X ∣ rels⟩ ≅ G` with relation
  subgroup `R`, `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])` elements, and
  `TauCeti.presentedProP.natCard_H2_le_pow_iff`: it has at most `p ^ n` elements exactly when `R`
  is generated as a closed normal subgroup of `F` by at most `n` elements.
* `TauCeti.presentedProP.lift_rank_H2`: the relation rank,
  `dim_{𝔽_p} H²(G, 𝔽_p) = d(R ⧸ Rᵖ[R, F])`, as an identity of cardinals, with
  `TauCeti.presentedProP.finrank_H2` its topologically finitely generated case, and
  `TauCeti.presentedProP.finrank_H2_le_iff`: that dimension is at most `n` exactly when `R` is
  generated as a closed normal subgroup of `F` by at most `n` elements.
* `TauCeti.presentedProP.finite_H2_iff`: `H²(G, 𝔽_p)` is finite exactly when `R ⧸ Rᵖ[R, F]` is
  topologically finitely generated.
* `TauCeti.natCard_H2_mul_pow_card_of_isClosed` and `TauCeti.card_add_finrank_H2_of_isClosed`: for
  `G ≅ F ⧸ R` with `F` free pro-`p` on a finite type `X` and `R` closed normal with `R ⧸ Rᵖ[R, F]`
  topologically finitely generated, `|H²(G, 𝔽_p)| · p ^ #X = p ^ (d(G) + d(R ⧸ Rᵖ[R, F]))` and
  `#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F])`; no minimality is assumed.
* `TauCeti.presentedProP.card_add_finrank_H2` and
  `TauCeti.presentedProP.card_add_finrank_cohomFp_two`: the same identity for a presentation
  `⟨X ∣ rels⟩ ≅ G` on a finite type, on the explicit and on the canonical carrier.
* `TauCeti.finite_H2_of_isClosed`, `TauCeti.presentedProP.finite_H2_of_finite` and
  `TauCeti.presentedProP.module_finite_cohomFp_two_of_finite`: `H²(G, 𝔽_p)` is finite when
  `R ⧸ Rᵖ[R, F]` is topologically finitely generated, in particular for finitely many relators on
  any generating type.
* `TauCeti.presentedProP.isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite`:
  finitely many relators make `R ⧸ Rᵖ[R, F]` topologically finitely generated, and
  `TauCeti.presentedProP.topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_card`: they
  bound `d(R ⧸ Rᵖ[R, F])`, the least number of generators of `R` as a closed normal subgroup.
* `TauCeti.presentedProP.topologicalGeneratorRankNat_quotient_pLowerCentralStep_eq`: the count
  `d(R ⧸ Rᵖ[R, F])` is the same for any two minimal presentations of `G`, and
  `TauCeti.presentedProP.isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_iff`: so is
  its finiteness.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.5).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §1.4.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.3.
-/

public section

namespace TauCeti

open ContCohomology Subgroup

universe u v w

-- For prime `p`, `AddCommGroup (ZMod p)` is also derivable from `[IsSimpleAddGroup (ZMod p)]
-- [AddGroup.IsNilpotent (ZMod p)]`; that structure is not reducibly the ring one, so the
-- `DistribMulAction` hypotheses below would not match what the cohomology API expects.
-- Preferring the ring path locally keeps a single additive structure on `ZMod p`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime]

section Quotient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {N : Subgroup G} [N.Normal]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)] [Subsingleton (H2 G (ZMod p))]

variable (hN : IsClosed (N : Set G)) (hle : N ≤ proPFrattini p G)
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include hN hle htriv

/-- **Finiteness of `H²(G ⧸ N, 𝔽_p)`.** Let `G` be a profinite group acting trivially on `𝔽_p`
with `H²(G, 𝔽_p) = 0`, and let `N ≤ Φ(G)` be a closed normal subgroup. Then `H²(G ⧸ N, 𝔽_p)` is
finite exactly when `N ⧸ Nᵖ[N, G]` is topologically finitely generated. -/
theorem finite_H2_quotient_iff_of_le_proPFrattini :
    Finite (H2 (G ⧸ N) (FixedPoints.addSubgroup N (ZMod p))) ↔
      IsTopologicallyFinitelyGenerated (N ⧸ (pLowerCentralStep p N).subgroupOf N) := by
  rw [← finite_H1ConjInvariants_iff hN htriv]
  exact (Equiv.ofBijective _ (transgression_bijective_of_le_proPFrattini hN hle htriv
    fun m ↦ by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])).finite_iff.symm

/-- **`H²(G ⧸ N, 𝔽_p)` counts the generators of `N ⧸ Nᵖ[N, G]`.** Let `G` be a profinite group
acting trivially on `𝔽_p` with `H²(G, 𝔽_p) = 0`, and let `N ≤ Φ(G)` be a closed normal subgroup
with `N ⧸ Nᵖ[N, G]` topologically finitely generated. Then `H²(G ⧸ N, 𝔽_p)` has
`p ^ d(N ⧸ Nᵖ[N, G])` elements, where `d` is the topological generator rank. -/
theorem natCard_H2_quotient_of_le_proPFrattini
    (h : IsTopologicallyFinitelyGenerated (N ⧸ (pLowerCentralStep p N).subgroupOf N)) :
    Nat.card (H2 (G ⧸ N) (FixedPoints.addSubgroup N (ZMod p))) =
      p ^ topologicalGeneratorRankNat (N ⧸ (pLowerCentralStep p N).subgroupOf N) h := by
  rw [← natCard_H1ConjInvariants hN htriv h]
  exact (Nat.card_congr (Equiv.ofBijective _ (transgression_bijective_of_le_proPFrattini hN hle
    htriv fun m ↦ by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]))).symm

end Quotient

section Presentation

variable {X : Type u} [DistribMulAction (freeProP p X) (ZMod p)]
  [ContinuousSMul (freeProP p X) (ZMod p)] {R : Subgroup (freeProP p X)} [R.Normal]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]

/-- Transport of `H²(F ⧸ R, 𝔽_p ^ R)` along a topological isomorphism `F ⧸ R ≃ₜ* G`, when both `F`
and `G` act trivially on `𝔽_p`; `TauCeti.h2QuotientEquiv_apply` reads it on the explicit models. -/
noncomputable def h2QuotientEquiv (e : freeProP p X ⧸ R ≃ₜ* G)
    (htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) :
    H2 (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p)) ≃+ H2 G (ZMod p) :=
  explicitMap2Equiv (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p)) G (ZMod p) e.symm
    (AddEquiv.ofBijective (FixedPoints.addSubgroup R (ZMod p)).subtype
      ⟨Subtype.val_injective, fun m ↦ ⟨⟨m, by
        rw [fixedPoints_addSubgroup_eq_top_of_smul_eq (ZMod p) R htrivF]
        exact AddSubgroup.mem_top m⟩, rfl⟩⟩)
    continuous_of_discreteTopology continuous_of_discreteTopology fun g m ↦ by
      rw [htriv, quotient_smul_fixedPoints_addSubgroup_eq_of_smul_eq htrivF]

/-- On the explicit models, the transport of `H²(F ⧸ R, 𝔽_p ^ R)` along `e : F ⧸ R ≃ₜ* G` is the
pullback along `e.symm`, with the coefficients `𝔽_p ^ R = 𝔽_p` read through the inclusion. -/
@[simp]
theorem h2QuotientEquiv_apply (e : freeProP p X ⧸ R ≃ₜ* G)
    (htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
    (x : H2 (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p))) :
    h2QuotientEquiv e htrivF htriv x =
      explicitMap2 (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p)) G (ZMod p) e.symm
        (FixedPoints.addSubgroup R (ZMod p)).subtype continuous_of_discreteTopology
        (fun g m ↦ (congrArg Subtype.val
          (quotient_smul_fixedPoints_addSubgroup_eq_of_smul_eq htrivF (e.symm g) m)).trans
            (htriv g m).symm) x :=
  explicitMap2Equiv_apply _ _ _ _ _ _ _ _ _ x

variable (hRc : IsClosed (R : Set (freeProP p X))) (hR : R ≤ proPFrattini p (freeProP p X))
  (e : freeProP p X ⧸ R ≃ₜ* G) (htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m)
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include hRc hR e htrivF htriv

/-- **Finiteness of `H²(G, 𝔽_p)` for a quotient of a free pro-`p` group.** Let `F` be the free
pro-`p` group on `X`, let `R ≤ Φ(F)` be a closed normal subgroup, and let `G ≅ F ⧸ R` be a group
acting trivially on `𝔽_p`, as does `F`. Then `H²(G, 𝔽_p)` is finite exactly when `R ⧸ Rᵖ[R, F]`
is topologically finitely generated. -/
theorem finite_H2_iff_of_le_proPFrattini :
    Finite (H2 G (ZMod p)) ↔
      IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R) := by
  have := freeProP.subsingleton_H2_zmod (p := p) (X := X)
  rw [← finite_H2_quotient_iff_of_le_proPFrattini hRc hR htrivF]
  exact (h2QuotientEquiv e htrivF htriv).toEquiv.finite_iff.symm

/-- **`H²(G, 𝔽_p)` counts the generators of `R ⧸ Rᵖ[R, F]` for a quotient of a free pro-`p`
group.** Let `F` be the free pro-`p` group on `X`, let `R ≤ Φ(F)` be a closed normal subgroup with
`R ⧸ Rᵖ[R, F]` topologically finitely generated, and let `G ≅ F ⧸ R` be a group acting trivially
on `𝔽_p`, as does `F`. Then `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])` elements, where `d` is the
topological generator rank. -/
theorem natCard_H2_of_le_proPFrattini
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Nat.card (H2 G (ZMod p)) =
      p ^ topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h := by
  have := freeProP.subsingleton_H2_zmod (p := p) (X := X)
  rw [← natCard_H2_quotient_of_le_proPFrattini hRc hR htrivF h]
  exact Nat.card_congr (h2QuotientEquiv e htrivF htriv).toEquiv.symm

/-- **`dim H²(G, 𝔽_p)` is the rank of `R ⧸ Rᵖ[R, F]` for a quotient of a free pro-`p` group.** Let
`F` be the free pro-`p` group on `X`, let `R ≤ Φ(F)` be a closed normal subgroup, and let
`G ≅ F ⧸ R` be a group acting trivially on `𝔽_p`, as does `F`. Then the dimension of `H²(G, 𝔽_p)`
over `𝔽_p` is the topological generator rank of `R ⧸ Rᵖ[R, F]`. No finiteness hypothesis is needed,
and the statement is an identity of cardinals; `TauCeti.finrank_H2_of_le_proPFrattini` is the
finite case. -/
theorem lift_rank_H2_of_le_proPFrattini :
    Cardinal.lift.{u} (Module.rank (ZMod p) (H2 G (ZMod p))) =
      Cardinal.lift.{v} (topologicalGeneratorRank (R ⧸ (pLowerCentralStep p R).subgroupOf R)) := by
  have := freeProP.subsingleton_H2_zmod (p := p) (X := X)
  have hpM : ∀ m : ZMod p, p • m = 0 := fun m ↦ by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  -- `R ⧸ Rᵖ[R, F]` is a profinite pro-`p` group: `IsClosed` and `CompactSpace` are the instances
  -- its topology and Burnside's basis theorem need.
  have := isClosed_pLowerCentralStep_subgroupOf (p := p) R
  have : CompactSpace R := isCompact_iff_compactSpace.mp hRc.isCompact
  have hQ : IsProP p (R ⧸ (pLowerCentralStep p R).subgroupOf R) :=
    (isPGroup_quotient_pLowerCentralStep_subgroupOf R).isProP
  -- Transgression and the duality of `TauCeti.ContCohomology.H1ConjInvariantsEquivOfSmulEqSelf`
  -- identify `H²(G, 𝔽_p)` with the continuous `𝔽_p`-dual of `R ⧸ Rᵖ[R, F]`, additively, hence
  -- `𝔽_p`-linearly; Burnside's basis theorem in cardinal form reads its dimension as the rank.
  have f : H2 G (ZMod p) ≃+ continuousZModDual p (R ⧸ (pLowerCentralStep p R).subgroupOf R) :=
    ((h2QuotientEquiv e htrivF htriv).symm.trans (AddEquiv.ofBijective _
      (transgression_bijective_of_le_proPFrattini hRc hR htrivF hpM)).symm).trans
      (H1ConjInvariantsEquivOfSmulEqSelf htrivF p hRc hpM)
  rw [hQ.topologicalGeneratorRank_eq_rank_continuousZModDual]
  exact (LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap p) f.bijective).lift_rank_eq

/-- **`dim H²(G, 𝔽_p)` counts the generators of `R ⧸ Rᵖ[R, F]` for a quotient of a free pro-`p`
group.** Let `F` be the free pro-`p` group on `X`, let `R ≤ Φ(F)` be a closed normal subgroup with
`R ⧸ Rᵖ[R, F]` topologically finitely generated, and let `G ≅ F ⧸ R` be a group acting trivially
on `𝔽_p`, as does `F`. Then `H²(G, 𝔽_p)` has dimension `d(R ⧸ Rᵖ[R, F])` over `𝔽_p`, where `d` is
the topological generator rank. This is the finite case of
`TauCeti.lift_rank_H2_of_le_proPFrattini`. -/
theorem finrank_H2_of_le_proPFrattini
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Module.finrank (ZMod p) (H2 G (ZMod p)) =
      topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h := by
  -- The profinite instances on `R ⧸ Rᵖ[R, F]`, as in `TauCeti.lift_rank_H2_of_le_proPFrattini`.
  have := isClosed_pLowerCentralStep_subgroupOf (p := p) R
  have : CompactSpace R := isCompact_iff_compactSpace.mp hRc.isCompact
  have hrank := lift_rank_H2_of_le_proPFrattini hRc hR e htrivF htriv
  rw [← topologicalGeneratorRankNat_eq_topologicalGeneratorRank h, Cardinal.lift_natCast] at hrank
  rw [Module.finrank, ← Cardinal.toNat_lift.{u}, hrank, Cardinal.toNat_natCast]

end Presentation

section FiniteRank

variable {X : Type u} [Finite X] [DistribMulAction (freeProP p X) (ZMod p)]
  [ContinuousSMul (freeProP p X) (ZMod p)] {R : Subgroup (freeProP p X)} [R.Normal]
  (hRc : IsClosed (R : Set (freeProP p X)))
  (htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m)
include hRc htrivF

/-- **The five-term count for a quotient of a free pro-`p` group of finite rank.** Let `F` be the
free pro-`p` group on a finite type `X`, acting trivially on `𝔽_p`, and let `R` be a closed normal
subgroup with `R ⧸ Rᵖ[R, F]` topologically finitely generated. Then
`|H²(F ⧸ R, 𝔽_p ^ R)| · p ^ #X = p ^ (d(F ⧸ R) + d(R ⧸ Rᵖ[R, F]))`: the five-term sequence of
`1 → R → F → F ⧸ R → 1` has `|H¹(F, 𝔽_p)| = p ^ #X`, `|H¹(F ⧸ R, 𝔽_p ^ R)| = p ^ d(F ⧸ R)`,
`|H¹(R, 𝔽_p)^F| = p ^ d(R ⧸ Rᵖ[R, F])` and `H²(F, 𝔽_p) = 0`. -/
theorem natCard_H2_quotient_mul_pow_card_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Nat.card (H2 (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p))) * p ^ Nat.card X =
      p ^ (topologicalGeneratorRankNat (freeProP p X ⧸ R)
        ((isTopologicallyFinitelyGenerated_freeProP p X).quotient R) +
        topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h) := by
  -- Closedness of `R` supplies the profinite instances on `F ⧸ R`.
  have := hRc
  have := freeProP.subsingleton_H2_zmod (p := p) (X := X)
  have hF : Nat.card (H1 (freeProP p X) (ZMod p)) = p ^ Nat.card X := by
    rw [(isProP_freeProP p X).natCard_H1_of_natCard_eq
      (isTopologicallyFinitelyGenerated_freeProP p X) (Nat.card_zmod p) htrivF,
      topologicalGeneratorRankNat_freeProP]
  have hA : Nat.card (FixedPoints.addSubgroup R (ZMod p)) = p := by
    rw [fixedPoints_addSubgroup_eq_top_of_smul_eq (ZMod p) R htrivF, AddSubgroup.card_top,
      Nat.card_zmod]
  have hQ := ((isProP_freeProP p X).quotient R).natCard_H1_of_natCard_eq
    ((isTopologicallyFinitelyGenerated_freeProP p X).quotient R) hA
    (quotient_smul_fixedPoints_addSubgroup_eq_of_smul_eq htrivF)
  have hC := natCard_H1ConjInvariants hRc htrivF h
  have key := natCard_H1_mul_natCard_H2_quotient_of_subsingleton (freeProP p X) (ZMod p) R hRc
  rw [hF, hQ, hC, ← pow_add] at key
  rw [mul_comm, key]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (e : freeProP p X ⧸ R ≃ₜ* G) (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include e htriv

omit [Finite X] in
/-- **`H²(G, 𝔽_p)` is finite when the relation subgroup is finitely normally generated.** Let `F`
be the free pro-`p` group on any type `X`, let `R` be a closed normal subgroup with `R ⧸ Rᵖ[R, F]`
topologically finitely generated, and let `G ≅ F ⧸ R` act trivially on `𝔽_p`, as does `F`. Then
`H²(G, 𝔽_p)` is finite: it is the image of the finite `H¹(R, 𝔽_p)^F` under the transgression, which
is surjective since `H²(F, 𝔽_p) = 0`. -/
theorem finite_H2_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Finite (H2 G (ZMod p)) := by
  have := hRc
  have := freeProP.subsingleton_H2_zmod (p := p) (X := X)
  have := (finite_H1ConjInvariants_iff hRc htrivF).2 h
  rw [← (h2QuotientEquiv e htrivF htriv).toEquiv.finite_iff]
  exact Finite.of_surjective _ ((transgression_surjective_iff (freeProP p X) (ZMod p) R hRc).2
    (AddMonoidHom.ext fun _ ↦ Subsingleton.elim _ _))

/-- **The five-term count for a group presented by a free pro-`p` group of finite rank.** Let `F`
be the free pro-`p` group on a finite type `X`, let `R` be a closed normal subgroup with
`R ⧸ Rᵖ[R, F]` topologically finitely generated, and let `G ≅ F ⧸ R` act trivially on `𝔽_p`, as
does `F`. Then `|H²(G, 𝔽_p)| · p ^ #X = p ^ (d(G) + d(R ⧸ Rᵖ[R, F]))`, where `G` is topologically
finitely generated as a quotient of `F`. -/
theorem natCard_H2_mul_pow_card_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Nat.card (H2 G (ZMod p)) * p ^ Nat.card X =
      p ^ (topologicalGeneratorRankNat G ((isTopologicallyFinitelyGenerated_congr e).mp
          ((isTopologicallyFinitelyGenerated_freeProP p X).quotient R)) +
        topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h) := by
  have := hRc
  rw [← Nat.card_congr (h2QuotientEquiv e htrivF htriv).toEquiv,
    natCard_H2_quotient_mul_pow_card_of_isClosed hRc htrivF h, topologicalGeneratorRankNat_congr e]

/-- **The generator, relation and normal-generator counts of a presentation.** Let `F` be the free
pro-`p` group on a finite type `X`, let `R` be a closed normal subgroup with `R ⧸ Rᵖ[R, F]`
topologically finitely generated, and let `G ≅ F ⧸ R` act trivially on `𝔽_p`, as does `F`. Then

```text
#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F]),
```

where `d(R ⧸ Rᵖ[R, F])` is the least number of generators of `R` as a closed normal subgroup of
`F`, and `G` is topologically finitely generated as a quotient of `F`. No minimality of the
presentation is assumed. -/
theorem card_add_finrank_H2_of_isClosed
    (h : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R)) :
    Nat.card X + Module.finrank (ZMod p) (H2 G (ZMod p)) =
      topologicalGeneratorRankNat G ((isTopologicallyFinitelyGenerated_congr e).mp
          ((isTopologicallyFinitelyGenerated_freeProP p X).quotient R)) +
        topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) h := by
  have := finite_H2_of_isClosed hRc htrivF e htriv h
  have key := natCard_H2_mul_pow_card_of_isClosed hRc htrivF e htriv h
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, ← pow_add] at key
  have := Nat.pow_right_injective (Fact.out : p.Prime).two_le key
  omega

end FiniteRank

namespace presentedProP

section Relators

variable {X : Type u} {rels : Set (freeProP p X)}

omit [Fact p.Prime] in
/-- A finite set of relators is a finset of its closed normal closure `R` in the free pro-`p`
group, with as many elements: `rels` is the image under `Subtype.val` of a finset of `R` of
`Nat.card rels` elements. -/
theorem exists_finset_card_eq_image_val_eq (hrels : rels.Finite) :
    ∃ s : Finset (normalClosure rels).topologicalClosure, s.card = Nat.card rels ∧
      Subtype.val '' (s : Set (normalClosure rels).topologicalClosure) = rels :=
  hrels.exists_finset_subtype_image_val_eq fun _ hx ↦
    le_topologicalClosure _ (subset_normalClosure hx)

/-- **A finite relator set normally generates its relation subgroup finitely.** For a finite set of
relators `rels`, with closed normal closure `R` in the free pro-`p` group `F`, the quotient
`R ⧸ Rᵖ[R, F]` is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite
    (hrels : rels.Finite) :
    IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure) := by
  obtain ⟨s, -, hs⟩ := exists_finset_card_eq_image_val_eq hrels
  exact ((isProP_freeProP p X).isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_iff
    Fact.out (isClosed_topologicalClosure _)).2 ⟨s, by rw [hs]⟩

/-- **The relators bound the least number of normal generators.** For a finite set of relators
`rels` with closed normal closure `R` in the free pro-`p` group `F`, the topological generator rank
of `R ⧸ Rᵖ[R, F]`, which is the least number of generators of `R` as a closed normal subgroup, is
at most the number of relators. -/
theorem topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_card (hrels : rels.Finite) :
    topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)
      (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels) ≤
      Nat.card rels := by
  obtain ⟨s, hcard, hs⟩ := exists_finset_card_eq_image_val_eq hrels
  exact ((isProP_freeProP p X).topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_iff
    Fact.out (isClosed_topologicalClosure _) _ _).2 ⟨s, hcard.le, by rw [hs]⟩

end Relators

section Count

variable {X : Type u} [Finite X] {rels : Set (freeProP p X)} {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)] (e : presentedProP p X rels ≃ₜ* G)
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include e htriv

/-- **The generator, relation and normal-generator counts of a presentation.** Let `G ≅ ⟨X ∣ rels⟩`
be a presentation, on a finite type `X`, of a group acting trivially on `𝔽_p`, and let `R` be the
closed normal closure of the relators, with `R ⧸ Rᵖ[R, F]` topologically finitely generated. Then

```text
#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F]),
```

where `d(R ⧸ Rᵖ[R, F])` is the least number of generators of `R` as a closed normal subgroup of
`F`, and `G` is topologically finitely generated as a group presented on a finite type. The
presentation need not be minimal. -/
theorem card_add_finrank_H2
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) :
    Nat.card X + Module.finrank (ZMod p) (H2 G (ZMod p)) =
      topologicalGeneratorRankNat G
          ((isTopologicallyFinitelyGenerated_congr e).mp isTopologicallyFinitelyGenerated) +
        topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
          (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
            (normalClosure rels).topologicalClosure) h := by
  -- The count needs an action of `F` on `𝔽_p`; the trivial one is installed.
  let := trivialZModAction p (freeProP p X)
  have : ContinuousSMul (freeProP p X) (ZMod p) := ⟨continuous_snd⟩
  exact card_add_finrank_H2_of_isClosed (isClosed_topologicalClosure _) (fun _ _ ↦ rfl) e htriv h

omit [Finite X] in
/-- **`H²(G, 𝔽_p)` is finite for finitely many relators.** Let `G ≅ ⟨X ∣ rels⟩` be a presentation,
on any type `X`, by finitely many relators, of a group acting trivially on `𝔽_p`. Then `H²(G, 𝔽_p)`
is finite. -/
theorem finite_H2_of_finite (hrels : rels.Finite) : Finite (H2 G (ZMod p)) := by
  -- The count needs an action of `F` on `𝔽_p`; the trivial one is installed.
  let := trivialZModAction p (freeProP p X)
  have : ContinuousSMul (freeProP p X) (ZMod p) := ⟨continuous_snd⟩
  exact finite_H2_of_isClosed (isClosed_topologicalClosure _) (fun _ _ ↦ rfl) e htriv
    (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels)

end Count

section CohomFp

variable {X : Type u} [Finite X] {rels : Set (freeProP p X)} {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (e : presentedProP p X rels ≃ₜ* G)
include e

/-- **The generator, relation and normal-generator counts of a presentation**, on the canonical
carrier. Let `G ≅ ⟨X ∣ rels⟩` be a presentation on a finite type `X`, and let `R` be the closed
normal closure of the relators, with `R ⧸ Rᵖ[R, F]` topologically finitely generated. Then

```text
#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F]),
```

where `d(R ⧸ Rᵖ[R, F])` is the least number of generators of `R` as a closed normal subgroup of
`F`, and `G` is topologically finitely generated as a group presented on a finite type. The
presentation need not be minimal. -/
theorem card_add_finrank_cohomFp_two
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) :
    Nat.card X + Module.finrank (ZMod p) (cohomFp p G 2) =
      topologicalGeneratorRankNat G
          ((isTopologicallyFinitelyGenerated_congr e).mp isTopologicallyFinitelyGenerated) +
        topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
          (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
            (normalClosure rels).topologicalClosure) h := by
  -- `G` is compact, being isomorphic to a quotient of a free pro-`p` group, and the explicit
  -- `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed.
  have : LocallyCompactSpace G := e.toHomeomorph.locallyCompactSpace_iff.1 inferInstance
  let := trivialZModAction p G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  rw [(cohomFpLinearEquivH2 p G fun _ _ ↦ rfl).finrank_eq]
  exact card_add_finrank_H2 e (fun _ _ ↦ rfl) h

omit [Finite X] in
/-- **`H²(G, 𝔽_p)` is finite-dimensional for finitely many relators**, on any type of generators,
so that the relation rank `r(G) = dim_{𝔽_p} H²(G, 𝔽_p)` of a group presented by finitely many
relators is a natural number. -/
theorem module_finite_cohomFp_two_of_finite (hrels : rels.Finite) :
    Module.Finite (ZMod p) (cohomFp p G 2) := by
  -- `G` is compact, being isomorphic to a quotient of a free pro-`p` group, and the explicit
  -- `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed.
  have : LocallyCompactSpace G := e.toHomeomorph.locallyCompactSpace_iff.1 inferInstance
  let := trivialZModAction p G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have := finite_H2_of_finite e (fun _ _ ↦ rfl) hrels
  exact Module.Finite.equiv (cohomFpLinearEquivH2 p G fun _ _ ↦ rfl).symm

end CohomFp

section MinimalPresentation

variable {X : Type u} (rels : Set (freeProP p X)) (hrels : rels ⊆ proPFrattini p (freeProP p X))
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (e : presentedProP p X rels ≃ₜ* G) (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include hrels e htriv

/-- **Finiteness of `H²(G, 𝔽_p)` from a minimal presentation.** Let `G ≅ ⟨X ∣ rels⟩` be a
presentation of a group acting trivially on `𝔽_p` whose relators lie in the Frattini subgroup of
the free pro-`p` group `F` on `X`, and let `R` be the closed normal closure of the relators. Then
`H²(G, 𝔽_p)` is finite exactly when `R ⧸ Rᵖ[R, F]` is topologically finitely generated. -/
theorem finite_H2_iff :
    Finite (H2 G (ZMod p)) ↔
      IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure) := by
  let := trivialZModAction p (freeProP p X)
  have : ContinuousSMul (freeProP p X) (ZMod p) := ⟨continuous_snd⟩
  exact finite_H2_iff_of_le_proPFrattini (isClosed_topologicalClosure _)
    ((topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).mpr hrels) e (fun _ _ ↦ rfl)
    htriv

/-- **`H²(G, 𝔽_p)` counts the relations of a minimal presentation.** Let `G ≅ ⟨X ∣ rels⟩` be a
presentation of a group acting trivially on `𝔽_p` whose relators lie in the Frattini subgroup of
the free pro-`p` group `F` on `X`, and let `R` be the closed normal closure of the relators, with
`R ⧸ Rᵖ[R, F]` topologically finitely generated. Then `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])`
elements, where `d` is the topological generator rank. -/
theorem natCard_H2
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) :
    Nat.card (H2 G (ZMod p)) =
      p ^ topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure) h := by
  let := trivialZModAction p (freeProP p X)
  have : ContinuousSMul (freeProP p X) (ZMod p) := ⟨continuous_snd⟩
  exact natCard_H2_of_le_proPFrattini (isClosed_topologicalClosure _)
    ((topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).mpr hrels) e (fun _ _ ↦ rfl)
    htriv h

/-- **The order of `H²(G, 𝔽_p)` bounds the number of relations.** Let `G ≅ ⟨X ∣ rels⟩` be a
presentation of a group acting trivially on `𝔽_p` whose relators lie in the Frattini subgroup of
the free pro-`p` group `F` on `X`, and let `R` be the closed normal closure of the relators, with
`R ⧸ Rᵖ[R, F]` topologically finitely generated. Then `H²(G, 𝔽_p)` has at most `p ^ n` elements
exactly when `R` is generated as a closed normal subgroup of `F` by at most `n` elements. -/
theorem natCard_H2_le_pow_iff
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) (n : ℕ) :
    Nat.card (H2 G (ZMod p)) ≤ p ^ n ↔
      ∃ s : Finset (normalClosure rels).topologicalClosure, s.card ≤ n ∧
        Subgroup.topologicalClosure
          (normalClosure (Subtype.val '' (s : Set (normalClosure rels).topologicalClosure))) =
          (normalClosure rels).topologicalClosure := by
  rw [natCard_H2 rels hrels e htriv h, pow_le_pow_iff_right₀ (Fact.out : p.Prime).one_lt,
    (isProP_freeProP p X).topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_iff Fact.out
      (isClosed_topologicalClosure _) h n]

/-- **The relation rank of a pro-`p` group is the dimension of `H²(G, 𝔽_p)`, cardinal form.** Let
`G ≅ ⟨X ∣ rels⟩` be a presentation of a group acting trivially on `𝔽_p` whose relators lie in the
Frattini subgroup of the free pro-`p` group `F` on `X`, and let `R` be the closed normal closure of
the relators. Then the dimension of `H²(G, 𝔽_p)` over `𝔽_p` is `d(R ⧸ Rᵖ[R, F])`, the relation rank
of `G`, as an identity of cardinals and with no finiteness hypothesis: a group with infinitely many
relations has an `H²(G, 𝔽_p)` of infinite dimension. `TauCeti.presentedProP.finrank_H2` is the
finite case. -/
theorem lift_rank_H2 :
    Cardinal.lift.{u} (Module.rank (ZMod p) (H2 G (ZMod p))) =
      Cardinal.lift.{v} (topologicalGeneratorRank ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure)) := by
  let := trivialZModAction p (freeProP p X)
  have : ContinuousSMul (freeProP p X) (ZMod p) := ⟨continuous_snd⟩
  exact lift_rank_H2_of_le_proPFrattini (isClosed_topologicalClosure _)
    ((topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).mpr hrels) e (fun _ _ ↦ rfl)
    htriv

/-- **The relation rank of a pro-`p` group is the dimension of `H²(G, 𝔽_p)`.** Let
`G ≅ ⟨X ∣ rels⟩` be a presentation of a group acting trivially on `𝔽_p` whose relators lie in the
Frattini subgroup of the free pro-`p` group `F` on `X`, and let `R` be the closed normal closure of
the relators, with `R ⧸ Rᵖ[R, F]` topologically finitely generated. Then `H²(G, 𝔽_p)` has dimension
`d(R ⧸ Rᵖ[R, F])` over `𝔽_p`, the least number of generators of `R` as a closed normal subgroup of
`F`. This is the finite case of `TauCeti.presentedProP.lift_rank_H2`. -/
theorem finrank_H2
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) :
    Module.finrank (ZMod p) (H2 G (ZMod p)) =
      topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure) h := by
  let := trivialZModAction p (freeProP p X)
  have : ContinuousSMul (freeProP p X) (ZMod p) := ⟨continuous_snd⟩
  exact finrank_H2_of_le_proPFrattini (isClosed_topologicalClosure _)
    ((topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).mpr hrels) e (fun _ _ ↦ rfl)
    htriv h

/-- **The dimension of `H²(G, 𝔽_p)` bounds the number of relations.** Let `G ≅ ⟨X ∣ rels⟩` be a
presentation of a group acting trivially on `𝔽_p` whose relators lie in the Frattini subgroup of
the free pro-`p` group `F` on `X`, and let `R` be the closed normal closure of the relators, with
`R ⧸ Rᵖ[R, F]` topologically finitely generated. Then `H²(G, 𝔽_p)` has dimension at most `n` over
`𝔽_p` exactly when `R` is generated as a closed normal subgroup of `F` by at most `n` elements. -/
theorem finrank_H2_le_iff
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) (n : ℕ) :
    Module.finrank (ZMod p) (H2 G (ZMod p)) ≤ n ↔
      ∃ s : Finset (normalClosure rels).topologicalClosure, s.card ≤ n ∧
        Subgroup.topologicalClosure
          (normalClosure (Subtype.val '' (s : Set (normalClosure rels).topologicalClosure))) =
          (normalClosure rels).topologicalClosure := by
  rw [finrank_H2 rels hrels e htriv h,
    (isProP_freeProP p X).topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_iff Fact.out
      (isClosed_topologicalClosure _) h n]

end MinimalPresentation

section Independence

variable {X : Type u} {Y : Type w} (rels : Set (freeProP p X)) (rels' : Set (freeProP p Y))
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Presentation independence of the finiteness of the relation rank.** For two minimal
presentations `G ≅ ⟨X ∣ rels⟩` and `G ≅ ⟨Y ∣ rels'⟩` of the same group, with relators in the
Frattini subgroups of the free pro-`p` groups `F` on `X` and `F'` on `Y` and relation subgroups `R`
and `R'`, the quotient `R ⧸ Rᵖ[R, F]` is topologically finitely generated exactly when
`R' ⧸ R'ᵖ[R', F']` is: both mean that `H²(G, 𝔽_p)` is finite. -/
theorem isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_iff
    (hrels : rels ⊆ proPFrattini p (freeProP p X)) (hrels' : rels' ⊆ proPFrattini p (freeProP p Y))
    (e : presentedProP p X rels ≃ₜ* G) (e' : presentedProP p Y rels' ≃ₜ* G) :
    IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure) ↔
      IsTopologicallyFinitelyGenerated ((normalClosure rels').topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels').topologicalClosure).subgroupOf
          (normalClosure rels').topologicalClosure) := by
  let := trivialZModAction p G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  rw [← finite_H2_iff rels hrels e (fun _ _ ↦ rfl), ← finite_H2_iff rels' hrels' e' (fun _ _ ↦ rfl)]

/-- **Presentation independence of the relation rank.** For two minimal presentations
`G ≅ ⟨X ∣ rels⟩` and `G ≅ ⟨Y ∣ rels'⟩` of the same group, with relators in the Frattini subgroups
of the free pro-`p` groups `F` on `X` and `F'` on `Y` and relation subgroups `R` and `R'`, the
counts `d(R ⧸ Rᵖ[R, F])` and `d(R' ⧸ R'ᵖ[R', F'])` agree: both are the exponent of the order
`p ^ r` of `H²(G, 𝔽_p)`. Finite generation of `R' ⧸ R'ᵖ[R', F']` is supplied by
`TauCeti.presentedProP.isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_iff`. -/
theorem topologicalGeneratorRankNat_quotient_pLowerCentralStep_eq
    (hrels : rels ⊆ proPFrattini p (freeProP p X)) (hrels' : rels' ⊆ proPFrattini p (freeProP p Y))
    (e : presentedProP p X rels ≃ₜ* G) (e' : presentedProP p Y rels' ≃ₜ* G)
    (h : IsTopologicallyFinitelyGenerated ((normalClosure rels).topologicalClosure ⧸
      (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
        (normalClosure rels).topologicalClosure)) :
    topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure) h =
      topologicalGeneratorRankNat ((normalClosure rels').topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels').topologicalClosure).subgroupOf
          (normalClosure rels').topologicalClosure)
        ((isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_iff rels rels' hrels hrels'
          e e').mp h) := by
  let := trivialZModAction p G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le
    ((natCard_H2 rels hrels e (fun _ _ ↦ rfl) h).symm.trans
      (natCard_H2 rels' hrels' e' (fun _ _ ↦ rfl) _))

end Independence

end presentedProP

end TauCeti
