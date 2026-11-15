/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Content
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.Amenable.Expansion
public import TauCeti.MeasureTheory.Group.Paradoxical

/-!
# Tarski's alternative for the left regular action

A discrete group `G` is amenable exactly when it is not paradoxical for its left regular action:
exactly one of a left-invariant finitely additive probability on all subsets of `G` and a finite
paradoxical decomposition of `G` exists.

If `G` has Følner sets, it is amenable for the discrete topology, so it carries a left-invariant
finitely additive probability on all of its subsets (`TauCeti.Amenable.exists_invariantContent`),
and such a probability rules out a paradoxical decomposition
(`TauCeti.not_paradoxical_univ_of_addContent`).

Conversely, if `G` has no Følner sets, expansion and Hall's marriage theorem give a finite set
`D ⊆ G` and an injection `j : G × Fin 2 → G` with `j (x, i) = d * x` for some `d ∈ D`
(`TauCeti.exists_injective_mul_of_not_hasFoelnerSets`). For each `i`, the injective map
`x ↦ j (x, i)` moves every point by one of the finitely many elements of `D`, so `G` is
equidecomposable with its range. The two ranges are disjoint since `j` is injective, so they are
two disjoint copies of `G` inside `G`, and the subcopy criterion
`TauCeti.paradoxical_iff_exists_subset` gives a paradoxical decomposition of `G`.

Neither direction needs a countability assumption on `G`. The statements in terms of Følner sets
involve no topology; by the Følner characterization `TauCeti.amenable_iff_hasFoelnerSets` they
become statements about amenability of discrete groups.

## Main results

* `TauCeti.paradoxical_univ_of_not_hasFoelnerSets`: a group without Følner sets is paradoxical
  for its left regular action.
* `TauCeti.hasFoelnerSets_iff_not_paradoxical_univ`: a group has Følner sets exactly when it is
  not paradoxical for its left regular action.
* `TauCeti.paradoxical_univ_of_not_amenable`: a nonamenable topological group is paradoxical for
  its left regular action.
* `TauCeti.amenable_iff_not_paradoxical_univ`: **Tarski's alternative**, a discrete group is
  amenable exactly when it is not paradoxical for its left regular action.

## References

* A. Garrido, *An introduction to amenable groups*, Theorem 1.11 (for `X = E = G`) and
  Theorem 1.15.
* T. Ceccherini-Silberstein, R. Grigorchuk, P. de la Harpe, *Amenability and paradoxical
  decompositions for pseudogroups and for discrete metric spaces*, Theorem 7.
-/

public section

open Set

namespace TauCeti

variable {G : Type*} [Group G]

/-- A group without Følner sets is paradoxical for its left regular action. -/
theorem paradoxical_univ_of_not_hasFoelnerSets (h : ¬HasFoelnerSets G) :
    Paradoxical G (univ : Set G) := by
  obtain ⟨D, j, hj, hjD⟩ := exists_injective_mul_of_not_hasFoelnerSets h 2
  -- Each copy `x ↦ j (x, i)` moves every point by an element of `D`, so `G` is equidecomposable
  -- with its range.
  have hcopy (i : Fin 2) : Equidecomposable G (range fun x => j (x, i)) univ := by
    rw [← image_univ]
    refine (Equidecomp.IsDecompOn.equidecomposable_image (S := D) (fun x _ => ?_)
      fun x _ y _ hxy => congrArg Prod.fst (hj hxy)).symm
    obtain ⟨d, hd, e⟩ := hjD (x, i)
    exact ⟨d, hd, ((smul_eq_mul d x).trans e).symm⟩
  refine paradoxical_iff_exists_subset.2 ⟨univ_nonempty, _, subset_univ _, _, subset_univ _,
    disjoint_range_iff.2 fun x y hxy => ?_, hcopy 0, hcopy 1⟩
  exact absurd (congrArg Prod.snd (hj hxy)) Fin.zero_ne_one

/-- **Tarski's alternative**, topology-free form: a group has Følner sets exactly when it is not
paradoxical for its left regular action. -/
theorem hasFoelnerSets_iff_not_paradoxical_univ :
    HasFoelnerSets G ↔ ¬Paradoxical G (univ : Set G) := by
  refine ⟨fun hF => ?_, not_imp_comm.1 paradoxical_univ_of_not_hasFoelnerSets⟩
  let : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  have : Amenable G := .of_hasFoelnerSets hF
  obtain ⟨ν, hν₁, hν⟩ := Amenable.exists_invariantContent (G := G)
  exact not_paradoxical_univ_of_addContent hν hν₁

/-- A nonamenable topological group is paradoxical for its left regular action. -/
theorem paradoxical_univ_of_not_amenable [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ¬Amenable G) : Paradoxical G (univ : Set G) :=
  paradoxical_univ_of_not_hasFoelnerSets (mt Amenable.of_hasFoelnerSets h)

/-- **Tarski's alternative**: a discrete group is amenable exactly when it is not paradoxical for
its left regular action. -/
theorem amenable_iff_not_paradoxical_univ [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] : Amenable G ↔ ¬Paradoxical G (univ : Set G) :=
  amenable_iff_hasFoelnerSets.trans hasFoelnerSets_iff_not_paradoxical_univ

end TauCeti
