/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation

/-!
# Minimal presentations of pro-`p` groups

A continuous surjection `f : G ↠ H` of pro-`p` groups, with `G` topologically finitely generated,
preserves the topological generator rank exactly when `ker f ≤ Φ(G)`
(`TauCeti.IsProP.topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini`). Applied to the
quotient map from a free pro-`p` group of finite rank onto a presented pro-`p` group, whose kernel
is the closed normal closure of the relators (`TauCeti.presentedProP.ker_mk`), this characterizes
**minimal presentations**: a presentation `G ≅ ⟨X ∣ rels⟩` with `X` finite is minimal, meaning
`Nat.card X = d(G)`, exactly when every relator lies in the Frattini subgroup
`Φ(F) = closure (Fᵖ [F, F])` of the free pro-`p` group `F` on `X`. Every topologically finitely
generated pro-`p` group has such a presentation, on any finite type of cardinality `d(G)`. This is
the condition `R ≤ Φ(F)` on the relation subgroup under which the relation rank of `G` is read off
from the presentation, and it is the normalization a Demushkin relator satisfies.

## Main results

* `TauCeti.presentedProP.topologicalGeneratorRankNat_eq_card_iff`: a pro-`p` group presented on a
  finite type `X` has rank `Nat.card X` exactly when the relators lie in the Frattini subgroup of
  the free pro-`p` group on `X`.
* `TauCeti.presentedProP.subset_proPFrattini_iff_card_eq`: a presentation of `G` on a finite type
  `X` has its relators in the Frattini subgroup exactly when `Nat.card X = d(G)`.
* `TauCeti.IsProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP`: every
  topologically finitely generated pro-`p` group has a minimal presentation on any finite type of
  cardinality `d(G)`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8 and Section 7.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Section III.9.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 1.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} [Fact p.Prime]

namespace presentedProP

variable {X : Type u} [Finite X] (rels : Set (freeProP p X))

/-- **Minimal presentations.** A pro-`p` group presented on a finite type `X` has topological
generator rank `Nat.card X` exactly when every relator lies in the Frattini subgroup of the free
pro-`p` group on `X`. -/
theorem topologicalGeneratorRankNat_eq_card_iff :
    topologicalGeneratorRankNat (presentedProP p X rels) isTopologicallyFinitelyGenerated =
        Nat.card X ↔
      rels ⊆ proPFrattini p (freeProP p X) := by
  rw [← topologicalGeneratorRankNat_freeProP p (isTopologicallyFinitelyGenerated_freeProP p X),
    (isProP_freeProP p X).topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini
      (isTopologicallyFinitelyGenerated_freeProP p X) (mk p rels : freeProP p X →* _)
      (map_continuous (mk p rels)) (mk_surjective p rels),
    ker_mk, Subgroup.topologicalClosure_normalClosure_le_iff isClosed_proPFrattini]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A presentation `G ≅ ⟨X ∣ rels⟩` of a topologically finitely generated group on a finite type
`X` has all its relators in the Frattini subgroup of the free pro-`p` group on `X` exactly when it
is minimal, that is when `Nat.card X` is the topological generator rank of `G`. -/
theorem subset_proPFrattini_iff_card_eq (e : presentedProP p X rels ≃ₜ* G)
    (h : IsTopologicallyFinitelyGenerated G) :
    rels ⊆ proPFrattini p (freeProP p X) ↔ Nat.card X = topologicalGeneratorRankNat G h := by
  rw [← topologicalGeneratorRankNat_eq_card_iff, topologicalGeneratorRankNat_congr e, eq_comm]

end presentedProP

/-- **Existence of minimal presentations.** A topologically finitely generated pro-`p` group has a
presentation on any finite type of cardinality its topological generator rank, with all relators in
the Frattini subgroup of the free pro-`p` group. -/
theorem IsProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsProP p G) (h : IsTopologicallyFinitelyGenerated G) (X : Type u) [Finite X]
    (hX : Nat.card X = topologicalGeneratorRankNat G h) :
    ∃ rels : Set (freeProP p X), rels ⊆ proPFrattini p (freeProP p X) ∧
      Nonempty (presentedProP p X rels ≃ₜ* G) := by
  obtain ⟨rels, ⟨e⟩⟩ := hG.exists_continuousMulEquiv_presentedProP h X hX.ge
  exact ⟨rels, (presentedProP.subset_proPFrattini_iff_card_eq rels e h).mpr hX, ⟨e⟩⟩

end TauCeti
