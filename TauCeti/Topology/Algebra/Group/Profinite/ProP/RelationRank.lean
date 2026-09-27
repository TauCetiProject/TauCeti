/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.MinimalPresentation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.NormalGeneration
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Transgression

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

The statements are about the order of `H²(G, 𝔽_p)`, for the explicit continuous cohomology `H2` of
the trivial `G`-module `𝔽_p`; the action of `G` on `ZMod p` is carried as an instance together
with the hypothesis that it is trivial, as in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual`. The statements about a quotient
`G ≅ F ⧸ R` of a free pro-`p` group `F` (`TauCeti.finite_H2_iff_of_le_proPFrattini` and
`TauCeti.natCard_H2_of_le_proPFrattini`) carry the action of `F` on `𝔽_p` in the same way, as an
instance with the hypothesis that it is trivial. The `TauCeti.presentedProP` statements about a
minimal presentation do not: they supply the trivial action of `F` internally, and only the action
of `G` appears.

## Main results

* `TauCeti.natCard_H2_quotient_of_le_proPFrattini`: for profinite `G` with `H²(G, 𝔽_p) = 0` and
  `N ≤ Φ(G)` closed normal, `H²(G ⧸ N, 𝔽_p)` has `p ^ d(N ⧸ Nᵖ[N, G])` elements;
  `TauCeti.finite_H2_quotient_iff_of_le_proPFrattini` is the finiteness criterion.
* `TauCeti.natCard_H2_of_le_proPFrattini`: for `G ≅ F ⧸ R` with `F` a free pro-`p` group and
  `R ≤ Φ(F)` closed normal, `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])` elements;
  `TauCeti.finite_H2_iff_of_le_proPFrattini` is the finiteness criterion.
* `TauCeti.presentedProP.natCard_H2`: for a minimal presentation `⟨X ∣ rels⟩ ≅ G` with relation
  subgroup `R`, `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])` elements, and
  `TauCeti.presentedProP.natCard_H2_le_pow_iff`: it has at most `p ^ n` elements exactly when `R`
  is generated as a closed normal subgroup of `F` by at most `n` elements.
* `TauCeti.presentedProP.finite_H2_iff`: `H²(G, 𝔽_p)` is finite exactly when `R ⧸ Rᵖ[R, F]` is
  topologically finitely generated.
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
and `G` act trivially on `𝔽_p`. Only its existence is used, to compare orders. -/
private noncomputable def h2QuotientEquiv (e : freeProP p X ⧸ R ≃ₜ* G)
    (htrivF : ∀ (g : freeProP p X) (m : ZMod p), g • m = m)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) :
    H2 (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p)) ≃+ H2 G (ZMod p) :=
  explicitMap2Equiv (freeProP p X ⧸ R) (FixedPoints.addSubgroup R (ZMod p)) G (ZMod p) e.symm
    (AddEquiv.ofBijective (FixedPoints.addSubgroup R (ZMod p)).subtype
      ⟨Subtype.val_injective, fun m ↦ ⟨⟨m, by
        rw [fixedPoints_addSubgroup_eq_top_of_smul_eq (ZMod p) R htrivF]
        exact AddSubgroup.mem_top m⟩, rfl⟩⟩)
    continuous_of_discreteTopology continuous_of_discreteTopology fun g m ↦ by
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm g)
      rw [htriv, ← hx, coe_quotient_smul_fixedPoints_addSubgroup]
      exact congrArg _ (Subtype.ext ((coe_smul_fixedPoints_addSubgroup x m).trans (htrivF x m)))

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

end Presentation

namespace presentedProP

/-- The trivial action of a group on `𝔽_p`, used to read the relation subgroup of a presentation
through the transgression; no statement below mentions it. -/
private abbrev trivialZModAction (F : Type u) [Monoid F] : DistribMulAction F (ZMod p) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

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
  let := trivialZModAction (p := p) (freeProP p X)
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
  let := trivialZModAction (p := p) (freeProP p X)
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
  let := trivialZModAction (p := p) G
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
  let := trivialZModAction (p := p) G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le
    ((natCard_H2 rels hrels e (fun _ _ ↦ rfl) h).symm.trans
      (natCard_H2 rels' hrels' e' (fun _ _ ↦ rfl) _))

end Independence

end presentedProP

end TauCeti
