/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Generation

/-!
# The topological generator rank of a profinite group

The **topological generator rank** `topologicalGeneratorRank G` of a topological group `G` is the
least cardinality of a subset that converges to `1` and generates a dense subgroup. Convergence to
`1` is not decoration: without it the invariant is the least cardinality of a dense subgroup, which
is the wrong notion for a profinite group. A product of continuum many copies of `ℤ/p` has a
countable dense subgroup, yet every generating set converging to `1` has cardinality `2 ^ ℵ₀`,
which is the number the Frattini quotient and every later rank formula see.

For a profinite `G` the family being minimized over is nonempty — that is
`TauCeti.exists_convergesToOne_topologicallyGenerates` — so the infimum is attained, cardinals
being well-ordered. Attainment is what all the theorems below run on: an isomorphism-invariant,
surjection-monotone cardinal whose finiteness is exactly
`TauCeti.IsTopologicallyFinitelyGenerated`.

Alongside it sits the natural-number accessor `topologicalGeneratorRankNat G h`, the least
cardinality of a *finite* topological generating set, available exactly when `G` is topologically
finitely generated. Every numerical rank statement — Schreier-type bounds, deficiencies, Euler
formulas, anything that subtracts ranks — is about the accessor rather than about the cardinal,
and `TauCeti.topologicalGeneratorRankNat_eq_topologicalGeneratorRank` is what ties the two
together. A comparison of the cardinal ranks of two groups is stated in `Cardinal.lift` form, so
that the groups need not share a universe, with the same-universe form derived from it. The
accessor needs no compactness and no convergence condition, since a finite set converges to `1`
in any topological group; compactness enters only through the comparison with the cardinal
rank.

## Main definitions

* `TauCeti.topologicalGeneratorRank`: the least cardinality of a topological generating set
  converging to `1`.
* `TauCeti.topologicalGeneratorRankNat`: the least cardinality of a finite topological generating
  set, for a topologically finitely generated group.

## Main results

* `TauCeti.topologicalGeneratorRank_le`: a topological generating set converging to `1` bounds the
  rank by its cardinality.
* `TauCeti.lift_topologicalGeneratorRank_congr`, `TauCeti.topologicalGeneratorRank_congr`: the
  rank is invariant under a topological group isomorphism, with no compactness needed.
* `TauCeti.exists_convergesToOne_mk_eq_topologicalGeneratorRank`: in a profinite group the
  infimum is attained.
* `TauCeti.lift_topologicalGeneratorRank_le_of_surjective`,
  `TauCeti.topologicalGeneratorRank_le_of_surjective`,
  `TauCeti.topologicalGeneratorRank_quotient_le`: a continuous surjection does not raise the rank.
* `TauCeti.topologicalGeneratorRank_lt_aleph0_iff`: the rank is finite exactly under topological
  finite generation.
* `TauCeti.topologicalGeneratorRank_eq_zero_iff`: the rank vanishes exactly on the trivial group.
* `TauCeti.topologicalGeneratorRankNat_eq_topologicalGeneratorRank`: the accessor computes the
  cardinal rank whenever it is available.
* `TauCeti.topologicalGeneratorRankNat_eq_rank`: on a discrete group the accessor is Mathlib's
  `Group.rank`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.6; Proposition 2.6.2 for the existence
  of a generating set converging to `1`.
-/

public section

namespace TauCeti

open scoped Cardinal

universe u v

section Defs

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **topological generator rank** of a topological group: the least cardinality of a subset
that converges to `1` and generates a dense subgroup. For a profinite group the family is
nonempty (`TauCeti.exists_convergesToOne_topologicallyGenerates`), so the infimum is attained;
for a group with no such generating set the empty infimum makes the rank `0`, and every theorem
below assumes what it needs. -/
noncomputable def topologicalGeneratorRank : Cardinal.{u} :=
  ⨅ s : {s : Set G // ConvergesToOne s ∧ (Subgroup.closure s).topologicalClosure = ⊤},
    #(s.1 : Set G)

/-- The defining equation of the topological generator rank: the body of
`TauCeti.topologicalGeneratorRank` is not exposed, so unfolding it goes through this lemma. -/
theorem topologicalGeneratorRank_def :
    topologicalGeneratorRank G =
      ⨅ s : {s : Set G // ConvergesToOne s ∧ (Subgroup.closure s).topologicalClosure = ⊤},
        #(s.1 : Set G) := by
  rw [topologicalGeneratorRank]

/-- The **natural-number topological generator rank** of a topologically finitely generated
topological group: the least cardinality of a finite topological generating set. This is the
accessor every numerical rank statement uses; it agrees with the cardinal-valued
`TauCeti.topologicalGeneratorRank` on a profinite group by
`TauCeti.topologicalGeneratorRankNat_eq_topologicalGeneratorRank`. -/
noncomputable def topologicalGeneratorRankNat (_h : IsTopologicallyFinitelyGenerated G) : ℕ :=
  sInf {n : ℕ | ∃ s : Finset G,
    s.card = n ∧ (Subgroup.closure (s : Set G)).topologicalClosure = ⊤}

/-- The defining equation of the natural-number topological generator rank: the body of
`TauCeti.topologicalGeneratorRankNat` is not exposed, so unfolding it goes through this lemma. -/
theorem topologicalGeneratorRankNat_def (h : IsTopologicallyFinitelyGenerated G) :
    topologicalGeneratorRankNat G h =
      sInf {n : ℕ | ∃ s : Finset G,
        s.card = n ∧ (Subgroup.closure (s : Set G)).topologicalClosure = ⊤} := by
  rw [topologicalGeneratorRankNat]

end Defs

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological generating set converging to `1` bounds the topological generator rank by its
cardinality. -/
theorem topologicalGeneratorRank_le {s : Set G} (hs : ConvergesToOne s)
    (hgen : (Subgroup.closure s).topologicalClosure = ⊤) :
    topologicalGeneratorRank G ≤ #(s : Set G) := by
  rw [topologicalGeneratorRank_def]
  exact ciInf_le (OrderBot.bddBelow _)
    (⟨s, hs, hgen⟩ : {t : Set G // ConvergesToOne t ∧
      (Subgroup.closure t).topologicalClosure = ⊤})

section Congr

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Topologically isomorphic groups have the same topological generator rank: an isomorphism
carries the generating sets converging to `1` of one group bijectively onto those of the other, so
the two infima are taken over the same cardinals. No compactness is needed, the empty case
included: if neither group has such a generating set both ranks are the empty infimum `0`. The two
groups need not share a universe, so the comparison is between `Cardinal.lift`s;
`TauCeti.topologicalGeneratorRank_congr` is the same-universe form. -/
theorem lift_topologicalGeneratorRank_congr (e : G ≃ₜ* H) :
    Cardinal.lift.{v} (topologicalGeneratorRank G)
      = Cardinal.lift.{u} (topologicalGeneratorRank H) := by
  have hrange : Set.range (fun s : {s : Set G // ConvergesToOne s ∧
        (Subgroup.closure s).topologicalClosure = ⊤} ↦ Cardinal.lift.{v} #(s.1 : Set G))
      = Set.range (fun t : {t : Set H // ConvergesToOne t ∧
        (Subgroup.closure t).topologicalClosure = ⊤} ↦ Cardinal.lift.{u} #(t.1 : Set H)) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨s, hs, hgen⟩, rfl⟩
      refine ⟨⟨(e.toMulEquiv.toMonoidHom : G →* H) '' s,
        hs.image (e.toMulEquiv.toMonoidHom : G →* H) e.continuous,
        topologicalClosure_closure_image_eq_top hgen e.continuous e.surjective.denseRange⟩, ?_⟩
      exact Cardinal.mk_congr_lift
        (Equiv.Set.image (e.toMulEquiv.toMonoidHom : G → H) s e.injective).symm
    · rintro _ ⟨⟨t, ht, hgen⟩, rfl⟩
      refine ⟨⟨(e.symm.toMulEquiv.toMonoidHom : H →* G) '' t,
        ht.image (e.symm.toMulEquiv.toMonoidHom : H →* G) e.symm.continuous,
        topologicalClosure_closure_image_eq_top hgen e.symm.continuous
          e.symm.surjective.denseRange⟩, ?_⟩
      exact Cardinal.mk_congr_lift
        (Equiv.Set.image (e.symm.toMulEquiv.toMonoidHom : H → G) t e.symm.injective).symm
  rw [topologicalGeneratorRank_def, topologicalGeneratorRank_def, Cardinal.lift_iInf,
    Cardinal.lift_iInf]
  exact congrArg sInf hrange

/-- Topologically isomorphic groups in the same universe have the same topological generator
rank. -/
theorem topologicalGeneratorRank_congr {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (e : G ≃ₜ* H) :
    topologicalGeneratorRank G = topologicalGeneratorRank H := by
  simpa using lift_topologicalGeneratorRank_congr e

end Congr

section Profinite

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (G) in
/-- In a profinite group the infimum defining the topological generator rank is **attained**:
some topological generating set converging to `1` has exactly that cardinality. The family is
nonempty by `TauCeti.exists_convergesToOne_topologicallyGenerates` and the cardinals are
well-ordered. -/
theorem exists_convergesToOne_mk_eq_topologicalGeneratorRank [CompactSpace G]
    [TotallyDisconnectedSpace G] :
    ∃ s : Set G, ConvergesToOne s ∧ (Subgroup.closure s).topologicalClosure = ⊤ ∧
      #(s : Set G) = topologicalGeneratorRank G := by
  have : Nonempty {s : Set G // ConvergesToOne s ∧
      (Subgroup.closure s).topologicalClosure = ⊤} :=
    let ⟨s, hs, hgen⟩ := exists_convergesToOne_topologicallyGenerates (G := G)
    ⟨⟨s, hs, hgen⟩⟩
  obtain ⟨s, hs⟩ := ciInf_mem fun s : {s : Set G // ConvergesToOne s ∧
    (Subgroup.closure s).topologicalClosure = ⊤} ↦ #(s.1 : Set G)
  refine ⟨s.1, s.2.1, s.2.2, ?_⟩
  rw [topologicalGeneratorRank_def]
  exact hs

/-- A continuous surjective homomorphism cannot raise the topological generator rank: the image
of a topological generating set converging to `1` is one again. The source and the target need
not share a universe, so the comparison is between `Cardinal.lift`s;
`TauCeti.topologicalGeneratorRank_le_of_surjective` is the same-universe form. Compactness of the
source is what supplies the generating set that is pushed forward: a group admitting no set
converging to `1` at all has rank `0` by the empty infimum, while its quotients can have positive
rank, so the hypothesis is not decoration. -/
theorem lift_topologicalGeneratorRank_le_of_surjective [CompactSpace G]
    [TotallyDisconnectedSpace G] (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) :
    Cardinal.lift.{u} (topologicalGeneratorRank H)
      ≤ Cardinal.lift.{v} (topologicalGeneratorRank G) := by
  obtain ⟨s, hs, hgen, hcard⟩ := exists_convergesToOne_mk_eq_topologicalGeneratorRank G
  calc Cardinal.lift.{u} (topologicalGeneratorRank H)
      ≤ Cardinal.lift.{u} #((f '' s : Set H)) :=
        Cardinal.lift_le.mpr (topologicalGeneratorRank_le (hs.image f hf)
          (topologicalClosure_closure_image_eq_top hgen hf hsurj.denseRange))
    _ ≤ Cardinal.lift.{v} #(s : Set G) := Cardinal.mk_image_le_lift
    _ = Cardinal.lift.{v} (topologicalGeneratorRank G) := by rw [hcard]

/-- A continuous surjective homomorphism onto a group in the same universe cannot raise the
topological generator rank. -/
theorem topologicalGeneratorRank_le_of_surjective {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace G] [TotallyDisconnectedSpace G] (f : G →* H)
    (hf : Continuous f) (hsurj : Function.Surjective f) :
    topologicalGeneratorRank H ≤ topologicalGeneratorRank G := by
  simpa using lift_topologicalGeneratorRank_le_of_surjective f hf hsurj

/-- Passing to a quotient cannot raise the topological generator rank. -/
theorem topologicalGeneratorRank_quotient_le [CompactSpace G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] :
    topologicalGeneratorRank (G ⧸ N) ≤ topologicalGeneratorRank G :=
  topologicalGeneratorRank_le_of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

/-- The topological generator rank of a profinite group is finite exactly when the group is
topologically finitely generated. -/
theorem topologicalGeneratorRank_lt_aleph0_iff [CompactSpace G] [TotallyDisconnectedSpace G] :
    topologicalGeneratorRank G < ℵ₀ ↔ IsTopologicallyFinitelyGenerated G := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨t, -, hgen, hcard⟩ := exists_convergesToOne_mk_eq_topologicalGeneratorRank G
    have hlt : #(t : Set G) < ℵ₀ := by rw [hcard]; exact h
    exact (Cardinal.lt_aleph0_iff_set_finite.mp hlt).isTopologicallyFinitelyGenerated hgen
  · obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp h
    refine lt_of_le_of_lt (topologicalGeneratorRank_le s.finite_toSet.convergesToOne hs) ?_
    exact Cardinal.lt_aleph0_iff_set_finite.mpr s.finite_toSet

/-- The topological generator rank of a profinite group vanishes exactly on the trivial group. -/
theorem topologicalGeneratorRank_eq_zero_iff [CompactSpace G] [TotallyDisconnectedSpace G] :
    topologicalGeneratorRank G = 0 ↔ Subsingleton G := by
  constructor
  · intro h
    obtain ⟨s, -, hgen, hcard⟩ := exists_convergesToOne_mk_eq_topologicalGeneratorRank G
    rw [h, Cardinal.mk_set_eq_zero_iff] at hcard
    subst hcard
    rw [Subgroup.closure_empty] at hgen
    have hbot : (⊥ : Subgroup G).topologicalClosure ≤ ⊥ :=
      Subgroup.topologicalClosure_minimal ⊥ le_rfl (by
        rw [Subgroup.coe_bot]
        exact isClosed_singleton)
    rw [hgen] at hbot
    have htop : (⊤ : Subgroup G) = ⊥ := le_antisymm hbot bot_le
    have hall : ∀ x : G, x = 1 := fun x ↦
      (Subgroup.eq_bot_iff_forall _).mp htop x (Subgroup.mem_top x)
    exact ⟨fun a b ↦ (hall a).trans (hall b).symm⟩
  · intro _
    refine le_antisymm ?_ zero_le
    have hgen : (Subgroup.closure (∅ : Set G)).topologicalClosure = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr fun g ↦ by
        rw [Subsingleton.elim g 1]
        exact Subgroup.one_mem _
    simpa using topologicalGeneratorRank_le Set.finite_empty.convergesToOne hgen

end Profinite

section Nat

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A finite topological generating set bounds the natural-number topological generator rank by
its cardinality. -/
theorem topologicalGeneratorRankNat_le (h : IsTopologicallyFinitelyGenerated G) {s : Finset G}
    (hs : (Subgroup.closure (s : Set G)).topologicalClosure = ⊤) :
    topologicalGeneratorRankNat G h ≤ s.card := by
  rw [topologicalGeneratorRankNat_def]
  exact Nat.sInf_le ⟨s, rfl, hs⟩

/-- The infimum defining the natural-number topological generator rank is **attained**: some
finite topological generating set has exactly that cardinality. -/
theorem exists_finset_card_eq_topologicalGeneratorRankNat
    (h : IsTopologicallyFinitelyGenerated G) :
    ∃ s : Finset G, s.card = topologicalGeneratorRankNat G h ∧
      (Subgroup.closure (s : Set G)).topologicalClosure = ⊤ := by
  rw [topologicalGeneratorRankNat_def]
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp h
  have hne : {n : ℕ | ∃ s : Finset G,
      s.card = n ∧ (Subgroup.closure (s : Set G)).topologicalClosure = ⊤}.Nonempty :=
    ⟨s.card, s, rfl, hs⟩
  exact Nat.sInf_mem hne

/-- A continuous surjective homomorphism cannot raise the natural-number topological generator
rank. Unlike its cardinal counterpart this needs no compactness: a finite generating set of the
source has a finite image. -/
theorem topologicalGeneratorRankNat_le_of_surjective (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) (hG : IsTopologicallyFinitelyGenerated G) :
    topologicalGeneratorRankNat H (hG.of_surjective hf hsurj)
      ≤ topologicalGeneratorRankNat G hG := by
  classical
  obtain ⟨s, hcard, hgen⟩ := exists_finset_card_eq_topologicalGeneratorRankNat hG
  have himg : (Subgroup.closure ((s.image f : Finset H) : Set H)).topologicalClosure = ⊤ := by
    rw [Finset.coe_image]
    exact topologicalClosure_closure_image_eq_top hgen hf hsurj.denseRange
  calc topologicalGeneratorRankNat H (hG.of_surjective hf hsurj)
      ≤ (s.image f).card := topologicalGeneratorRankNat_le _ himg
    _ ≤ s.card := Finset.card_image_le
    _ = topologicalGeneratorRankNat G hG := hcard

/-- The natural-number accessor computes the cardinal topological generator rank whenever it is
available. Every theorem that subtracts ranks is stated with the accessor, and this is how it
connects to the general cardinal theory. -/
@[simp]
theorem topologicalGeneratorRankNat_eq_topologicalGeneratorRank [CompactSpace G]
    [TotallyDisconnectedSpace G] (h : IsTopologicallyFinitelyGenerated G) :
    (topologicalGeneratorRankNat G h : Cardinal.{u}) = topologicalGeneratorRank G := by
  obtain ⟨s, -, hgen, hcard⟩ := exists_convergesToOne_mk_eq_topologicalGeneratorRank G
  have hlt : #(s : Set G) < ℵ₀ := by
    rw [hcard]
    exact topologicalGeneratorRank_lt_aleph0_iff.mpr h
  have hfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.mp hlt
  obtain ⟨t, rfl⟩ : ∃ t : Finset G, (t : Set G) = s := ⟨hfin.toFinset, hfin.coe_toFinset⟩
  refine le_antisymm ?_ ?_
  · rw [← hcard]
    calc (topologicalGeneratorRankNat G h : Cardinal.{u})
        ≤ (t.card : Cardinal.{u}) := by exact_mod_cast topologicalGeneratorRankNat_le h hgen
      _ = #((t : Set G)) := by simp
  · obtain ⟨u, hucard, hugen⟩ := exists_finset_card_eq_topologicalGeneratorRankNat h
    rw [← hucard]
    refine le_trans (topologicalGeneratorRank_le u.finite_toSet.convergesToOne hugen) ?_
    simp

/-- On a discrete group the natural-number topological generator rank is Mathlib's `Group.rank`:
in a discrete group every subgroup is its own topological closure, so a dense subgroup is the
whole group and the two infima range over the same generating sets. -/
theorem topologicalGeneratorRankNat_eq_rank [DiscreteTopology G] [Group.FG G]
    (h : IsTopologicallyFinitelyGenerated G) :
    topologicalGeneratorRankNat G h = Group.rank G := by
  refine le_antisymm ?_ ?_
  · obtain ⟨S, hScard, hS⟩ := Group.rank_spec G
    refine le_trans (topologicalGeneratorRankNat_le h ?_) hScard.le
    rw [hS]
    exact eq_top_iff.mpr (Subgroup.le_topologicalClosure ⊤)
  · obtain ⟨t, htcard, htgen⟩ := exists_finset_card_eq_topologicalGeneratorRankNat h
    refine le_trans (Group.rank_le ?_) htcard.le
    refine le_antisymm le_top ?_
    rw [← htgen]
    exact Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_discrete _)

end Nat

end TauCeti
