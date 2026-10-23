/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Rank

/-!
# Serre's theorem: `cd_p ≤ 1` implies free pro-`p`

Let `G` be a topologically finitely generated pro-`p` group. If `G` is projective, meaning that
every continuous homomorphism from `G` into a quotient of a profinite pro-`p` group lifts
continuously, then `G` is free pro-`p` of rank `d(G)`; in particular this holds when `cd_p G ≤ 1`.

A minimal generating set of `G` gives a continuous surjection `φ : F ↠ G` from the free pro-`p`
group `F` on `d(G)` generators. Since `φ` preserves the generator rank, its kernel lies in the
Frattini subgroup `Φ(F)`, so `φ` is a Frattini cover. Projectivity of `G` lifts the identity of
`G` through `φ` to a continuous homomorphic section, and a Frattini cover of a pro-`p` group with
such a section is an isomorphism (`TauCeti.IsProP.continuousMulEquivOfLeftInverse`).

The generating type `X` of the free group ranges over the finite types in the universe of `G`
with `Nat.card X = d(G)`, as in `TauCeti.IsProP.exists_surjective_freeProP`; the type
`ULift (Fin (d G))` is one such choice. Only this direction of Serre's characterization of free
pro-`p` groups is proved here.

## Main results

* `TauCeti.IsProP.nonempty_continuousMulEquiv_freeProP_of_isProjective`: a projective
  topologically finitely generated pro-`p` group is free pro-`p` of rank `d(G)`.
* `TauCeti.IsProP.nonempty_continuousMulEquiv_freeProP_of_cohomologicalDimensionAt_le_one`:
  **Serre's theorem**, a topologically finitely generated pro-`p` group with `cd_p ≤ 1` is free
  pro-`p` of rank `d(G)`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2 and §5.9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 7.7.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace IsProP

/-- **Projective topologically finitely generated pro-`p` groups are free.** A topologically
finitely generated pro-`p` group `G` that is projective is topologically isomorphic to the free
pro-`p` group on any finite type of cardinality `d(G)`. -/
theorem nonempty_continuousMulEquiv_freeProP_of_isProjective (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hproj : IsProjective.{u, u, u} p G) (X : Type u)
    [Finite X] (hX : Nat.card X = topologicalGeneratorRankNat G hfg) :
    Nonempty (G ≃ₜ* freeProP p X) := by
  -- A minimal generating set gives a continuous surjection `φ : F ↠ G` from the free pro-`p`
  -- group on `X`; it preserves the generator rank, so its kernel lies in `Φ(F)`.
  obtain ⟨φ, hφ⟩ := hG.exists_surjective_freeProP hfg X hX.ge
  have hker : φ.toMonoidHom.ker ≤ proPFrattini p (freeProP p X) := by
    rw [← (isProP_freeProP p X).topologicalGeneratorRankNat_eq_iff_ker_le_proPFrattini
      (isTopologicallyFinitelyGenerated_freeProP p X) φ.toMonoidHom φ.continuous hφ,
      topologicalGeneratorRankNat_freeProP]
    exact hX.symm
  -- Projectivity lifts the identity of `G` through `φ` to a continuous homomorphic section.
  obtain ⟨s, hs⟩ := hproj.exists_continuous_lift (isProP_freeProP p X) φ hφ (.id G)
  have hs' : Function.LeftInverse φ s := fun g ↦ by simpa using DFunLike.congr_fun hs g
  exact ⟨((isProP_freeProP p X).continuousMulEquivOfLeftInverse φ s hs' hker).symm⟩

/-- **Serre's theorem.** A topologically finitely generated pro-`p` group `G` with `cd_p G ≤ 1`
is free pro-`p`: it is topologically isomorphic to the free pro-`p` group on any finite type of
cardinality `d(G)`. -/
theorem nonempty_continuousMulEquiv_freeProP_of_cohomologicalDimensionAt_le_one (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hcd : cohomologicalDimensionAt.{u} p G ≤ 1)
    (X : Type u) [Finite X] (hX : Nat.card X = topologicalGeneratorRankNat G hfg) :
    Nonempty (G ≃ₜ* freeProP p X) :=
  hG.nonempty_continuousMulEquiv_freeProP_of_isProjective hfg
    ((cohomologicalDimensionAt_le_iff p G 1).mp (by exact_mod_cast hcd)).isProjective X hX

end IsProP

end TauCeti
