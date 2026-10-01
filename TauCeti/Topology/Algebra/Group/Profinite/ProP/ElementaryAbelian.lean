/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Graded
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank

/-!
# Generator rank and relation rank of a finite elementary abelian `p`-group

Let `G` be a finite elementary abelian `p`-group, that is, a topologically finitely generated
profinite group whose pro-`p` Frattini subgroup `Φ(G)` is trivial (such a group is automatically
pro-`p`); the model is `(ℤ/p)^X = X → Multiplicative (ZMod p)` for a finite type `X`. Its
topological generator rank `d = d(G)` satisfies `|G| = p ^ d`, and its second cohomology with
trivial coefficients `𝔽_p` has order `p ^ (d (d + 1) / 2)`: the relation rank of `G` is
`d (d + 1) / 2`. In the model, `d((ℤ/p)^X) = #X` and `r((ℤ/p)^X) = #X (#X + 1) / 2`.

The count is read off a minimal presentation. A minimal presentation `G ≅ F ⧸ R` by the free
pro-`p` group `F` of rank `d` has `R = Φ(F)`
(`TauCeti.presentedProP.topologicalClosure_normalClosure_eq_proPFrattini`), which is the first
term `λ_1(F)` of the lower `p`-series, so `R ⧸ Rᵖ[R, F] = λ_1(F) ⧸ λ_2(F) = gr_1(F)` is the
degree-one graded piece, of order `p ^ (d + (d choose 2))`
(`TauCeti.freeProP.natCard_gradedPiece_one`). Since `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])`
elements (`TauCeti.presentedProP.natCard_H2`) and `R ⧸ Rᵖ[R, F]` is elementary abelian, its rank
is its `𝔽_p`-dimension `d + (d choose 2) = d (d + 1) / 2`.

This is the value against which the normalisation of `H²` is checked: an `H²` counting `d choose 2`
or `d ^ 2` classes for `(ℤ/p)^d` would be wrong. The counting statements are about the order of the
explicit continuous cohomology `H2 G (ZMod p)`, with the action of `G` on `𝔽_p` carried as an
instance as in `TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank`; no triviality
hypothesis is needed, since `G` is a `p`-group (`TauCeti.isPGroup_of_proPFrattini_eq_bot`) and a
`p`-group can only act trivially on `𝔽_p` (`IsPGroup.smul_zmod_eq_self`). The count is then read
as the `𝔽_p`-dimension of the continuous cohomology `cohomFp p G 2` with trivial coefficients,
through `TauCeti.cohomFpLinearEquivH2`.

## Main results

* `TauCeti.natCard_H2_of_proPFrattini_eq_bot`: for a topologically finitely generated profinite
  group `G` with `Φ(G) = 1`, `H²(G, 𝔽_p)` has `p ^ (d(G) (d(G) + 1) / 2)` elements;
  `TauCeti.finite_H2_of_proPFrattini_eq_bot` records its finiteness, and
  `TauCeti.finrank_cohomFp_two_of_proPFrattini_eq_bot` reads the count as
  `dim H²(G, 𝔽_p) = d(G) (d(G) + 1) / 2`.
* `TauCeti.topologicalGeneratorRankNat_pi_multiplicative_zmod`: `d((ℤ/p)^X) = #X`.
* `TauCeti.natCard_H2_pi_multiplicative_zmod`: `H²((ℤ/p)^X, 𝔽_p)` has `p ^ (#X (#X + 1) / 2)`
  elements.
* `TauCeti.proPFrattini_multiplicative_zmod_eq_bot` and
  `TauCeti.topologicalGeneratorRankNat_multiplicative_zmod`: the cyclic group `ℤ/p` itself has
  trivial pro-`p` Frattini subgroup and `d(ℤ/p) = 1`.
* `TauCeti.finrank_cohomFp_one_multiplicative_zmod` and
  `TauCeti.finrank_cohomFp_two_multiplicative_zmod`: `H¹(ℤ/p, 𝔽_p)` and `H²(ℤ/p, 𝔽_p)` are
  one-dimensional.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.5).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.2 and §4.3.
-/

public section

namespace TauCeti

open ContCohomology Subgroup

universe u

-- For prime `p`, `AddCommGroup (ZMod p)` is also derivable from `[IsSimpleAddGroup (ZMod p)]
-- [AddGroup.IsNilpotent (ZMod p)]`; that structure is not reducibly the ring one, so the
-- `DistribMulAction` hypotheses below would not match what the cohomology API expects.
-- Preferring the ring path locally keeps a single additive structure on `ZMod p`, as in
-- `TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ}

section ElementaryAbelian

variable [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)]

/-- **The relation rank of a finite elementary abelian `p`-group.** Let `G` be a topologically
finitely generated profinite group with trivial pro-`p` Frattini subgroup. Then `H²(G, 𝔽_p)` has
`p ^ (d (d + 1) / 2)` elements for every continuous action of `G` on `𝔽_p` (which is necessarily
trivial), where `d = d(G)` is the topological generator rank: the relation rank of `G` is
`d (d + 1) / 2`. -/
theorem natCard_H2_of_proPFrattini_eq_bot (hfg : IsTopologicallyFinitelyGenerated G)
    (hΦ : proPFrattini p G = ⊥) :
    Nat.card (H2 G (ZMod p)) =
      p ^ (topologicalGeneratorRankNat G hfg * (topologicalGeneratorRankNat G hfg + 1) / 2) := by
  have hp : p.Prime := Fact.out
  have htriv := (isPGroup_of_proPFrattini_eq_bot hΦ).smul_zmod_eq_self
  set d := topologicalGeneratorRankNat G hfg
  -- A minimal presentation `G ≅ ⟨X ∣ rels⟩` on a type `X` with `d` elements; its relation
  -- subgroup is `R = Φ(F) = λ_1(F)`.
  obtain ⟨rels, hrels, ⟨e⟩⟩ :=
    (isProP_of_proPFrattini_eq_bot hΦ).exists_subset_proPFrattini_continuousMulEquiv_presentedProP
      hfg (ULift.{u} (Fin d)) (by rw [Nat.card_ulift, Nat.card_fin])
  set R := (normalClosure rels).topologicalClosure
  have hR1 : R = pLowerCentralSeries p (freeProP p (ULift.{u} (Fin d))) 1 :=
    (presentedProP.topologicalClosure_normalClosure_eq_proPFrattini hrels e hΦ).trans
      (pLowerCentralSeries_one_eq_proPFrattini hp).symm
  -- The quotient `R ⧸ Rᵖ[R, F]` is `gr_1(F)`, of order `p ^ (d + (d choose 2))`.
  have hcard : Nat.card (R ⧸ (pLowerCentralStep p R).subgroupOf R) = p ^ (d + d.choose 2) := by
    rw [natCard_quotient_pLowerCentralStep_eq_natCard_gradedPiece hR1,
      freeProP.natCard_gradedPiece_one, Nat.card_ulift, Nat.card_fin]
  have hfin : Finite (R ⧸ (pLowerCentralStep p R).subgroupOf R) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hp.ne_zero)
  have hQfg : IsTopologicallyFinitelyGenerated (R ⧸ (pLowerCentralStep p R).subgroupOf R) :=
    isTopologicallyFinitelyGenerated_of_fg
  -- `H²(G, 𝔽_p)` has `p ^ d(R ⧸ Rᵖ[R, F])` elements, and `d(R ⧸ Rᵖ[R, F]) = d + (d choose 2)`
  -- because that quotient is elementary abelian.
  have hRc : IsClosed (R : Set (freeProP p (ULift.{u} (Fin d)))) := isClosed_topologicalClosure _
  have : CompactSpace R := isCompact_iff_compactSpace.mp hRc.isCompact
  have hK := isClosed_pLowerCentralStep_subgroupOf (p := p) R
  have hrank : topologicalGeneratorRankNat (R ⧸ (pLowerCentralStep p R).subgroupOf R) hQfg =
      d + d.choose 2 :=
    topologicalGeneratorRankNat_eq_of_natCard_eq_pow hQfg
      (proPFrattini_quotient_pLowerCentralStep_eq_bot hp R hRc) hcard
  have harith : d + d.choose 2 = d * (d + 1) / 2 := by
    rw [Nat.choose_two_right, add_comm, ← Nat.triangle_succ, Nat.add_sub_cancel, mul_comm]
  rw [presentedProP.natCard_H2 rels hrels e htriv hQfg, hrank, harith]

/-- `H²(G, 𝔽_p)` is finite for a topologically finitely generated profinite group `G` with trivial
pro-`p` Frattini subgroup. -/
theorem finite_H2_of_proPFrattini_eq_bot (hfg : IsTopologicallyFinitelyGenerated G)
    (hΦ : proPFrattini p G = ⊥) : Finite (H2 G (ZMod p)) :=
  Nat.finite_of_card_ne_zero <|
    (natCard_H2_of_proPFrattini_eq_bot hfg hΦ) ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero

omit [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)] in
/-- **The relation rank of a finite elementary abelian `p`-group, as a dimension.** Let `G` be a
topologically finitely generated profinite group with trivial pro-`p` Frattini subgroup and
topological generator rank `d = d(G)`. Then `H²(G, 𝔽_p)` with trivial coefficients is
`d (d + 1) / 2`-dimensional over `𝔽_p`. -/
theorem finrank_cohomFp_two_of_proPFrattini_eq_bot (hfg : IsTopologicallyFinitelyGenerated G)
    (hΦ : proPFrattini p G = ⊥) :
    Module.finrank (ZMod p) (cohomFp p G 2) =
      topologicalGeneratorRankNat G hfg * (topologicalGeneratorRankNat G hfg + 1) / 2 := by
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed for
  -- the duration of the proof and does not appear in the statement.
  let _ : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  have : Finite (H2 G (ZMod p)) := finite_H2_of_proPFrattini_eq_bot hfg hΦ
  have : Module.Finite (ZMod p) (H2 G (ZMod p)) := Module.Finite.of_finite
  rw [(cohomFpLinearEquivH2 p G htriv).finrank_eq]
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := H2 G (ZMod p))
  rw [natCard_H2_of_proPFrattini_eq_bot hfg hΦ, Nat.card_zmod] at hpow
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hpow).symm

end ElementaryAbelian

/-! ### The example `(ℤ/p)ⁿ` -/

section PiZMod

variable (p) (X : Type u) [Finite X]

/-- The group `(ℤ/p)^X`, a product of `#X` copies of `ℤ/p`, has `p ^ #X` elements. -/
@[simp]
theorem natCard_pi_multiplicative_zmod :
    Nat.card (X → Multiplicative (ZMod p)) = p ^ Nat.card X := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]

variable [Fact p.Prime]

omit [Finite X] in
/-- The pro-`p` Frattini subgroup of `(ℤ/p)^X` is trivial. -/
@[simp]
theorem proPFrattini_pi_multiplicative_zmod_eq_bot :
    proPFrattini p (X → Multiplicative (ZMod p)) = ⊥ := by
  refine (proPFrattini_eq_bot_iff Fact.out).mpr ⟨⟨⟨mul_comm⟩⟩,
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun f ↦ funext fun x ↦ ?_⟩
  have h := Monoid.pow_exponent_eq_one (f x)
  rw [Monoid.exponent_multiplicative, ZMod.exponent] at h
  rwa [Pi.pow_apply, Pi.one_apply]

/-- **`d((ℤ/p)^X) = #X`.** The topological generator rank of the finite elementary abelian group
`(ℤ/p)^X` is `#X`. -/
@[simp]
theorem topologicalGeneratorRankNat_pi_multiplicative_zmod
    (h : IsTopologicallyFinitelyGenerated (X → Multiplicative (ZMod p))) :
    topologicalGeneratorRankNat (X → Multiplicative (ZMod p)) h = Nat.card X :=
  topologicalGeneratorRankNat_eq_of_natCard_eq_pow h
    (proPFrattini_pi_multiplicative_zmod_eq_bot p X) (natCard_pi_multiplicative_zmod p X)

variable [DistribMulAction (X → Multiplicative (ZMod p)) (ZMod p)]
  [ContinuousSMul (X → Multiplicative (ZMod p)) (ZMod p)]

/-- **`r((ℤ/p)^X) = #X (#X + 1) / 2`.** For the finite elementary abelian group `(ℤ/p)^X`,
`H²((ℤ/p)^X, 𝔽_p)` has `p ^ (#X (#X + 1) / 2)` elements. -/
@[simp high]
theorem natCard_H2_pi_multiplicative_zmod :
    Nat.card (H2 (X → Multiplicative (ZMod p)) (ZMod p)) =
      p ^ (Nat.card X * (Nat.card X + 1) / 2) := by
  rw [natCard_H2_of_proPFrattini_eq_bot isTopologicallyFinitelyGenerated_of_fg
    (proPFrattini_pi_multiplicative_zmod_eq_bot p X),
    topologicalGeneratorRankNat_pi_multiplicative_zmod]

end PiZMod

/-! ### The example `ℤ/p` -/

section ZMod

variable (p : ℕ) [Fact p.Prime]

/-- The pro-`p` Frattini subgroup of the cyclic group `ℤ/p` is trivial. -/
@[simp]
theorem proPFrattini_multiplicative_zmod_eq_bot : proPFrattini p (Multiplicative (ZMod p)) = ⊥ :=
  (proPFrattini_eq_bot_iff Fact.out).mpr
    ⟨⟨⟨mul_comm⟩⟩, by rw [Monoid.exponent_multiplicative, ZMod.exponent]⟩

/-- **`d(ℤ/p) = 1`.** The topological generator rank of the cyclic group `ℤ/p` is `1`. -/
@[simp]
theorem topologicalGeneratorRankNat_multiplicative_zmod
    (h : IsTopologicallyFinitelyGenerated (Multiplicative (ZMod p))) :
    topologicalGeneratorRankNat (Multiplicative (ZMod p)) h = 1 :=
  topologicalGeneratorRankNat_eq_of_natCard_eq_pow h (proPFrattini_multiplicative_zmod_eq_bot p)
    (by rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod, pow_one])

/-- **`H¹(ℤ/p, 𝔽_p)` is one-dimensional**: the cyclic group `ℤ/p` has topological generator rank
one. -/
@[simp]
theorem finrank_cohomFp_one_multiplicative_zmod :
    Module.finrank (ZMod p) (cohomFp p (Multiplicative (ZMod p)) 1) = 1 := by
  rw [(isProP_of_proPFrattini_eq_bot
    (proPFrattini_multiplicative_zmod_eq_bot p)).finrank_cohomFp_one
    isTopologicallyFinitelyGenerated_of_fg, topologicalGeneratorRankNat_multiplicative_zmod]

/-- **`H²(ℤ/p, 𝔽_p)` is one-dimensional**: the relation rank of the cyclic group `ℤ/p` is
`1 · 2 / 2 = 1`. -/
@[simp]
theorem finrank_cohomFp_two_multiplicative_zmod :
    Module.finrank (ZMod p) (cohomFp p (Multiplicative (ZMod p)) 2) = 1 := by
  rw [finrank_cohomFp_two_of_proPFrattini_eq_bot isTopologicallyFinitelyGenerated_of_fg
    (proPFrattini_multiplicative_zmod_eq_bot p), topologicalGeneratorRankNat_multiplicative_zmod]

end ZMod

end TauCeti
