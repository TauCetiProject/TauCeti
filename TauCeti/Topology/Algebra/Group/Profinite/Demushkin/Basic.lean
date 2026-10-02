/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Empty
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ULift
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Relation.Rank

/-!
# Demushkin groups

A **Demushkin group** is a pro-`p` group `G` whose cohomology with trivial `𝔽_p` coefficients looks
like that of a closed surface: `H¹(G, 𝔽_p)` is finite-dimensional, `H²(G, 𝔽_p)` is one-dimensional,
and the cup product `H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)` is a nondegenerate pairing (Labute,
p. 106). The maximal pro-`p` quotients of the absolute Galois groups of `p`-adic fields containing
the `p`-th roots of unity are the motivating examples.

The definition is the predicate `IsDemushkin p G`, stated against the continuous cohomology
`cohomFp p G n` and the cup product `cupFp p G` on it. Its first consequences are proved here: a
Demushkin group is topologically finitely generated, its rank `demushkinRank` is the dimension of
`H¹(G, 𝔽_p)`, and it is a one-relator pro-`p` group, presented on `demushkinRank` generators by a
single relator lying in the Frattini subgroup of the free pro-`p` group, and its rank is positive.
A free pro-`p` group is not Demushkin, since its `H²(G, 𝔽_p)` vanishes.

## Main definitions

* `TauCeti.IsDemushkin`: the Demushkin predicate.
* `TauCeti.demushkinRank`: the rank of a Demushkin group, its topological generator rank.

## Main results

* `TauCeti.IsDemushkin.isTopologicallyFinitelyGenerated`: a Demushkin group is topologically
  finitely generated.
* `TauCeti.IsDemushkin.finrank_cohomFp_one`: `dim_{𝔽_p} H¹(G, 𝔽_p) = demushkinRank`.
* `TauCeti.IsDemushkin.finite_cohomFp_two`: `H²(G, 𝔽_p)` is finite.
* `TauCeti.IsDemushkin.exists_mem_proPFrattini_continuousMulEquiv_presentedProP`: a Demushkin group
  is a one-relator pro-`p` group with relator in the Frattini subgroup.
* `TauCeti.IsDemushkin.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin`: the same
  on the generating type `Fin (demushkinRank hG)`, whatever the universe of `G`.
* `TauCeti.IsDemushkin.demushkinRank_pos`: a Demushkin group has positive rank.
* `TauCeti.IsDemushkin.card_pos_presentedProP`: a presentation of a Demushkin group has at least
  one generator.
* `TauCeti.not_isDemushkin_freeProP`: a free pro-`p` group is not Demushkin.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
* J.-P. Serre, *Galois Cohomology*, I §4.5.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.9).
-/

public section

namespace TauCeti

open Subgroup TauCeti.ContCohomology

universe u v

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- action installed below is the one the explicit `H²(G, 𝔽_p)` is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

section Predicate

variable (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The Demushkin predicate** (Labute, p. 106), for a prime `p` and a profinite group `G`: a
pro-`p` group whose `H¹(G, 𝔽_p)` is finite-dimensional, whose `H²(G, 𝔽_p)` is one-dimensional, and
on which the cup product `H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)` is nondegenerate on both sides.
The primality and profiniteness of the ambient data are hypotheses of the predicate, so that it is
only stated on its mathematical domain, and the pro-`p` hypothesis is a field, so that no theorem
about Demushkin groups applies to a group that satisfies only the cohomological clauses. Finite
generation is a consequence, `IsDemushkin.isTopologicallyFinitelyGenerated`, and is not assumed. -/
structure IsDemushkin : Prop where
  /-- `G` is a pro-`p` group. -/
  isProP : IsProP p G
  /-- `H¹(G, 𝔽_p)` is finite-dimensional. -/
  finite_cohomFp_one : Module.Finite (ZMod p) (cohomFp p G 1)
  /-- `H²(G, 𝔽_p)` is one-dimensional. -/
  finrank_cohomFp_two : Module.finrank (ZMod p) (cohomFp p G 2) = 1
  /-- The cup product is left-separating: every nonzero class pairs nontrivially with some
  class on its right. -/
  cup_separatingLeft : ∀ a : cohomFp p G 1, a ≠ 0 → ∃ b : cohomFp p G 1, cupFp p G a b ≠ 0
  /-- The cup product is right-separating: every nonzero class pairs nontrivially with some
  class on its left. -/
  cup_separatingRight : ∀ b : cohomFp p G 1, b ≠ 0 → ∃ a : cohomFp p G 1, cupFp p G a b ≠ 0

end Predicate

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsDemushkin

variable (hG : IsDemushkin p G)
include hG

/-- **A Demushkin group is topologically finitely generated**: its `H¹(G, 𝔽_p)` is
finite-dimensional, and the dimension of `H¹(G, 𝔽_p)` is the topological generator rank. -/
theorem isTopologicallyFinitelyGenerated : IsTopologicallyFinitelyGenerated G :=
  hG.isProP.finite_cohomFp_one_iff.1 hG.finite_cohomFp_one

end IsDemushkin

/-- **The rank of a Demushkin group**: its topological generator rank, as a natural number. Every
numerical statement about a Demushkin group is about this accessor. -/
noncomputable def demushkinRank (hG : IsDemushkin p G) : ℕ :=
  topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated

/-- The rank of a Demushkin group is its topological generator rank. -/
theorem demushkinRank_def (hG : IsDemushkin p G) :
    demushkinRank hG = topologicalGeneratorRankNat G hG.isTopologicallyFinitelyGenerated :=
  (rfl)

/-- **The rank of a presented Demushkin group is the number of generators** when the relators lie
in the Frattini subgroup: such a presentation is minimal. -/
theorem demushkinRank_presentedProP {X : Type v} [Finite X] {rels : Set (freeProP p X)}
    (hrels : rels ⊆ proPFrattini p (freeProP p X)) (hG : IsDemushkin p (presentedProP p X rels)) :
    demushkinRank hG = Nat.card X := by
  rw [demushkinRank_def]
  exact (presentedProP.topologicalGeneratorRankNat_eq_card_iff rels).mpr hrels

/-- The rank of a Demushkin group is an isomorphism invariant. -/
theorem demushkinRank_congr {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H] (hG : IsDemushkin p G) (hH : IsDemushkin p H)
    (e : G ≃ₜ* H) : demushkinRank hG = demushkinRank hH :=
  topologicalGeneratorRankNat_congr e _

namespace IsDemushkin

variable (hG : IsDemushkin p G)
include hG

/-- **The rank of a Demushkin group is the dimension of `H¹(G, 𝔽_p)`.** -/
theorem finrank_cohomFp_one : Module.finrank (ZMod p) (cohomFp p G 1) = demushkinRank hG :=
  hG.isProP.finrank_cohomFp_one hG.isTopologicallyFinitelyGenerated

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- **`H²(G, 𝔽_p)` of a Demushkin group is finite**, being one-dimensional over `𝔽_p`. -/
theorem finite_cohomFp_two : Finite (cohomFp p G 2) :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have := Module.finite_of_finrank_eq_succ hG.finrank_cohomFp_two
  Module.finite_of_finite (ZMod p)

/-- **A Demushkin group is a one-relator pro-`p` group.** On any finite type `X` with
`demushkinRank hG` elements, a Demushkin group `G` is presented by a single relator `r` of the free
pro-`p` group on `X`, and `r` lies in the Frattini subgroup `Φ(F) = closure (Fᵖ [F, F])`, so the
presentation is minimal: the number of relators of a minimal presentation is the dimension of
`H²(G, 𝔽_p)`, which is `1`. -/
theorem exists_mem_proPFrattini_continuousMulEquiv_presentedProP (X : Type u) [Finite X]
    (hX : Nat.card X = demushkinRank hG) :
    ∃ r ∈ proPFrattini p (freeProP p X), Nonempty (presentedProP p X {r} ≃ₜ* G) := by
  obtain ⟨rels, hrels, ⟨e⟩⟩ := hG.isProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP
    hG.isTopologicallyFinitelyGenerated X hX
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  -- `H²(G, 𝔽_p)` is one-dimensional, so the relation subgroup is normally generated by one element.
  have h2 : Module.finrank (ZMod p) (H2 G (ZMod p)) = 1 := by
    rw [← (cohomFpLinearEquivH2 p G htriv).finrank_eq]
    exact hG.finrank_cohomFp_two
  have hfin : Finite (H2 G (ZMod p)) :=
    (cohomFpLinearEquivH2 p G htriv).toEquiv.finite_iff.1 hG.finite_cohomFp_two
  have hfg := (presentedProP.finite_H2_iff rels hrels e htriv).1 hfin
  obtain ⟨s, hs, hsR⟩ := (presentedProP.finrank_H2_le_iff rels hrels e htriv hfg 1).1 h2.le
  obtain ⟨x, hx⟩ := Finset.card_le_one_iff_subset_singleton.1 hs
  -- The closed normal closure of the relators is that of the single relator `x`.
  have hR : (normalClosure rels).topologicalClosure =
      (normalClosure {(x : freeProP p X)}).topologicalClosure := by
    refine le_antisymm (hsR.symm.trans_le ?_) ?_
    · refine (topologicalClosure_normalClosure_le_iff (isClosed_topologicalClosure _)).2 ?_
      refine ((Set.image_mono (Finset.coe_subset.2 hx)).trans ?_).trans
        (subset_normalClosure.trans (le_topologicalClosure _))
      rw [Finset.coe_singleton, Set.image_singleton]
    · exact (topologicalClosure_normalClosure_le_iff (isClosed_topologicalClosure _)).2
        (Set.singleton_subset_iff.2 x.2)
  exact ⟨x, (topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).2 hrels x.2,
    ⟨(presentedProP.congrOfClosureEq hR).symm.trans e⟩⟩

/-- **A Demushkin group is a one-relator pro-`p` group on `Fin n`**, `n = demushkinRank hG`: it is
presented by a single relator `r ∈ Φ(F)` of the free pro-`p` group on `Fin (demushkinRank hG)`,
whatever the universe of `G`. -/
theorem exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin :
    ∃ r ∈ proPFrattini p (freeProP p (Fin (demushkinRank hG))),
      Nonempty (presentedProP p (Fin (demushkinRank hG)) {r} ≃ₜ* G) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP
    (ULift.{u} (Fin (demushkinRank hG))) (by simp)
  set φ : freeProP p (ULift.{u} (Fin (demushkinRank hG))) ≃ₜ* freeProP p (Fin (demushkinRank hG)) :=
    freeProP.uliftEquiv p (Fin (demushkinRank hG))
  refine ⟨φ r, ?_, ⟨(presentedProP.congr φ ?_ ?_).symm.trans e⟩⟩
  · rw [← φ.map_proPFrattini_eq]
    exact Subgroup.mem_map_of_mem _ hr
  · intro s hs
    rw [Set.mem_singleton_iff.1 hs]
    exact presentedProP.mk_relator _ (Set.mem_singleton _)
  · intro s hs
    rw [Set.mem_singleton_iff.1 hs, φ.symm_apply_apply]
    exact presentedProP.mk_relator _ (Set.mem_singleton _)

/-- **A Demushkin group has positive rank**: on an empty generating type the presented group is
trivial, and a trivial group has vanishing `H²(G, 𝔽_p)`, which is not one-dimensional. -/
theorem demushkinRank_pos : 0 < demushkinRank hG := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  obtain ⟨r, -, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP
    (ULift.{u} (Fin 0)) (by simp [h0])
  have : Subsingleton (presentedProP p (ULift.{u} (Fin 0)) {r}) :=
    (presentedProP.mk_surjective p {r}).subsingleton
  have : Subsingleton G := e.symm.injective.subsingleton
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  have h2 : Module.finrank (ZMod p) (H2 G (ZMod p)) = 0 := Module.finrank_zero_of_subsingleton
  rw [← (cohomFpLinearEquivH2 p G htriv).finrank_eq, hG.finrank_cohomFp_two] at h2
  exact one_ne_zero h2

end IsDemushkin

/-- **A presentation of a Demushkin group has at least one generator**: the rank of the group is
positive and at most the number of generators. -/
theorem IsDemushkin.card_pos_presentedProP {X : Type v} [Finite X] {rels : Set (freeProP p X)}
    (hG : IsDemushkin p (presentedProP p X rels)) : 0 < Nat.card X := by
  have h := hG.demushkinRank_pos
  rw [demushkinRank_def] at h
  exact h.trans_le (presentedProP.topologicalGeneratorRankNat_le_card rels)

/-- **A relator presenting a Demushkin group lies in the Frattini subgroup**: a one-relator
presentation `⟨X ∣ r⟩` of a Demushkin group on a finite type `X` is minimal. In the count
`#X + dim H²(G, 𝔽_p) = d(G) + d(R ⧸ Rᵖ[R, F])` of the presentation, `H²(G, 𝔽_p)` is
one-dimensional and the single relator normally generates `R`, so `d(G) ≥ #X`, and `d(G) ≤ #X`
always. -/
theorem IsDemushkin.mem_proPFrattini_of_presentedProP_singleton {X : Type v} [Finite X]
    {r : freeProP p X} (hG : IsDemushkin p (presentedProP p X {r})) :
    r ∈ proPFrattini p (freeProP p X) := by
  have hfin := presentedProP.isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite
    (p := p) (Set.finite_singleton r)
  have h1 := presentedProP.card_add_finrank_cohomFp_two (ContinuousMulEquiv.refl _) hfin
  have h2 := presentedProP.topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_card
    (p := p) (Set.finite_singleton r)
  have h3 := presentedProP.topologicalGeneratorRankNat_le_card (p := p) {r}
  rw [hG.finrank_cohomFp_two] at h1
  rw [Nat.card_unique] at h2
  exact Set.singleton_subset_iff.1
    ((presentedProP.topologicalGeneratorRankNat_eq_card_iff {r}).1 (by omega))

/-- **A free pro-`p` group is not Demushkin**: its `H²(F, 𝔽_p)` vanishes, so it is not
one-dimensional. This covers the trivial group and `ℤ_p`. -/
theorem not_isDemushkin_freeProP (X : Type u) : ¬ IsDemushkin p (freeProP p X) := fun h ↦ by
  -- The explicit `H²(F, 𝔽_p)` needs an action of `F` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction (freeProP p X) (ZMod p) :=
    DistribMulAction.compHom (ZMod p) (1 : freeProP p X →* (ZMod p)ˣ)
  have htriv : ∀ (g : freeProP p X) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul (freeProP p X) (ZMod p) :=
    ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  have := freeProP.subsingleton_H2_zmod (p := p) (X := X)
  have h2 : Module.finrank (ZMod p) (H2 (freeProP p X) (ZMod p)) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [← (cohomFpLinearEquivH2 p (freeProP p X) htriv).finrank_eq, h.finrank_cohomFp_two] at h2
  exact one_ne_zero h2

end TauCeti
