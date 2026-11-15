/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular

/-!
# Restricting regular pair colors to an embedded host

Deleting auxiliary vertices from a padded host restricts both the coloring and the vertex
cells. Pair-color densities are preserved by the embedding, so regularity transports exactly
between source sets and their images. If each retained cell occupies at least an `α`-fraction
of its original cell, the slicing lemma gives regularity with parameter `max (2ε) (ε / α)`.
The skeleton theorem permits any partition into such retained subcells, without assuming
that the original or restricted partition is equitable.

All statements include diagonal cell pairs: densities are normalized by the number of
ordered distinct pairs, not the product of the cell sizes. No nonempty palette or host is
required.

## Main results

* `PairColorSystem.isRegularPair_comap_iff`: exact transport to image cells.
* `PairColorSystem.IsRegularPair.comap_of_card_le`: quantitative restriction to subcells.
* `PairSkeleton3.IsPairColorRegular.comap`: restriction of the entire lower skeleton.

## References

* J. Komlós and M. Simonovits, *Szemerédi's regularity lemma and its applications in graph
  theory* (1996), Fact 1.5 (slicing).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007) (the padding-and-restriction setting).
-/

public section

open Finset

namespace TauCeti

namespace PairColorSystem

variable {κ V W : Type*} {S : PairColorSystem κ W} {ε : ℝ} {s t : Finset V}

/-- A pair of sets in the restricted host is regular exactly when its image pair is regular.
The regularity parameter is unchanged. -/
@[simp]
theorem isRegularPair_comap_iff (S : PairColorSystem κ W) (f : V ↪ W) :
    (S.comap f).IsRegularPair ε s t ↔ S.IsRegularPair ε (s.map f) (t.map f) := by
  classical
  simp only [isRegularPair_iff]
  constructor
  · intro h c a ha b hb haε hbε
    rw [map_eq_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := subset_image_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := subset_image_iff.mp hb
    simpa only [pairColorDensity_comap, map_eq_image] using
      h c a' ha' b' hb'
        (by simpa only [card_map, card_image_of_injective _ f.injective] using haε)
        (by simpa only [card_map, card_image_of_injective _ f.injective] using hbε)
  · intro h c a ha b hb haε hbε
    simpa only [pairColorDensity_comap] using
      h c (a.map f) (map_subset_map.mpr ha) (b.map f) (map_subset_map.mpr hb)
        (by simpa using haε) (by simpa using hbε)

/-- A regular pair restricts to a pair whose image cells retain at least an `α`-fraction
of the original cell sizes, with the usual slicing loss. -/
theorem IsRegularPair.comap_of_card_le {A B : Finset W} (h : S.IsRegularPair ε A B)
    (f : V ↪ W) (hs : s.map f ⊆ A) (ht : t.map f ⊆ B) {α : ℝ} (hα : 0 < α)
    (hsizeS : α * #A ≤ #s) (hsizeT : α * #B ≤ #t) :
    (S.comap f).IsRegularPair (max (2 * ε) (ε / α)) s t := by
  apply (isRegularPair_comap_iff S f).mpr
  exact h.of_subset hs ht hα (by simpa using hsizeS) (by simpa using hsizeT)

end PairColorSystem

namespace PairSkeleton3

variable {κ V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {S : PairSkeleton3 κ W} {ε α : ℝ}

/-- Restrict a regular lower skeleton along an embedding. Each new cell must lie in an
original cell and retain at least an `α`-fraction of its size. The partition may split cells,
and no equitability is needed. -/
theorem IsPairColorRegular.comap (h : S.IsPairColorRegular ε) (f : V ↪ W)
    (P : Finpartition (univ : Finset V)) (hα : 0 < α)
    (hcells : ∀ A ∈ P.parts, ∃ B ∈ S.vertexPart.parts,
      A.map f ⊆ B ∧ α * #B ≤ #A) :
    (⟨P, S.pairColors.comap f⟩ : PairSkeleton3 κ V).IsPairColorRegular
      (max (2 * ε) (ε / α)) := by
  apply isPairColorRegular_iff.mpr
  intro c A hA B hB
  obtain ⟨A₀, hA₀, hsubA, hsizeA⟩ := hcells A hA
  obtain ⟨B₀, hB₀, hsubB, hsizeB⟩ := hcells B hB
  exact PairColorSystem.isRegularPair_iff.mp
    ((h.isRegularPair hA₀ hB₀).comap_of_card_le f hsubA hsubB hα hsizeA hsizeB) c

end PairSkeleton3

end TauCeti
