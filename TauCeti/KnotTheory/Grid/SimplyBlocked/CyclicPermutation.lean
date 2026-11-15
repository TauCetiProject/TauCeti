/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Grading.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked

/-!
# Cyclic permutations of the simply blocked grid complex

Cyclically permuting the rows of a grid diagram fixes every `O`-marking column, so the row
relabeling of grid chains commutes with setting `V_i = 0` and intertwines the simply blocked
differentials with the same blocked column `i`. Cyclically permuting the columns moves the
`O`-marking of column `i` to column `finRotate n i`. The column relabeling therefore renames the
surviving variables along the same permutation, as `TauCeti.simplyBlockedRenameEquiv` does, and
intertwines the differential blocking column `i` with the one blocking column `finRotate n i`.

Both relabelings also identify the homogeneous pieces of the `(O-Maslov, Alexander)` bigrading of
an odd-component grid in both directions.

The column relabeling `TauCeti.GridChain.simplyBlockedRelabelColumnsEquiv` is defined, and both
relabelings commute with specialization, for arbitrary permutations in
`TauCeti.KnotTheory.Grid.SimplyBlocked.Basic`; only the comparison of differentials needs a cyclic
permutation, since only cyclic permutations carry empty rectangles on the torus to empty
rectangles. The chain identities hold over any commutative semiring.

## Main results

* `TauCeti.GridDiagram.simplyBlockedDifferential_relabelRows_finRotate_apply` and
  `TauCeti.GridDiagram.simplyBlockedDifferential_relabelColumns_finRotate_apply`: the cyclic
  relabelings intertwine the simply blocked differentials.
* `TauCeti.OddComponentGridDiagram.relabelRowsEquiv_mem_bigradedChainHatPiece_iff` and
  `TauCeti.OddComponentGridDiagram.simplyBlockedRelabelColumnsEquiv_mem_bigradedChainHatPiece_iff`:
  they identify the homogeneous chain pieces.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1. The chain
identities specialize `TauCeti.GridDiagram.unblockedDifferential_relabelRows_finRotate_apply` and
`TauCeti.GridDiagram.unblockedDifferential_relabelColumns_finRotate_apply`.
-/

public section

open MvPolynomial

namespace TauCeti

variable {n : ℕ} (R : Type*) [CommSemiring R]

namespace GridDiagram

variable (G : GridDiagram n) (i : Fin n)

/-- The row relabeling by a cyclic permutation intertwines the simply blocked differentials, with
the same blocked column. -/
@[simp]
theorem simplyBlockedDifferential_relabelRows_finRotate_apply (c : GridChainHat R n i) :
    (G.relabelRows (finRotate n)).simplyBlockedDifferential R i
        (GridChain.relabelRowsEquiv (finRotate n) c) =
      GridChain.relabelRowsEquiv (finRotate n) (G.simplyBlockedDifferential R i c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R i c
  rw [← simplyBlockedSpecialization_relabelRowsEquiv,
    ← simplyBlockedSpecialization_unblockedDifferential,
    unblockedDifferential_relabelRows_finRotate_apply,
    simplyBlockedSpecialization_relabelRowsEquiv,
    simplyBlockedSpecialization_unblockedDifferential]

/-- The column relabeling by a cyclic permutation, renaming the surviving variables, intertwines
the simply blocked differentials, with the blocked column moved to `finRotate n i`. -/
@[simp]
theorem simplyBlockedDifferential_relabelColumns_finRotate_apply (c : GridChainHat R n i) :
    (G.relabelColumns (finRotate n)).simplyBlockedDifferential R (finRotate n i)
        (GridChain.simplyBlockedRelabelColumnsEquiv R (finRotate n) i c) =
      GridChain.simplyBlockedRelabelColumnsEquiv R (finRotate n) i
        (G.simplyBlockedDifferential R i c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R i c
  rw [← simplyBlockedSpecialization_relabelColumnsRenameEquiv,
    ← simplyBlockedSpecialization_unblockedDifferential,
    unblockedDifferential_relabelColumns_finRotate_apply,
    simplyBlockedSpecialization_relabelColumnsRenameEquiv,
    simplyBlockedSpecialization_unblockedDifferential]

end GridDiagram

namespace OddComponentGridDiagram

variable (G : OddComponentGridDiagram n) {R} {i : Fin n}

/-- Cyclic row relabeling identifies the homogeneous pieces of the specialized complex.

Not a simp lemma: the chain-piece membership criterion is already a simp lemma. -/
theorem relabelRowsEquiv_mem_bigradedChainHatPiece_iff {g : ℤ × ℤ} {c : GridChainHat R n i} :
    GridChain.relabelRowsEquiv (finRotate n) c ∈
        (G.relabelRows (finRotate n)).bigradedChainHatPiece R i g ↔
      c ∈ G.bigradedChainHatPiece R i g := by
  rw [mem_bigradedChainHatPiece, mem_bigradedChainHatPiece]
  constructor
  · intro hc x e he
    have hx := hc (x.relabelRows (finRotate n)) e
      (by rwa [GridChain.relabelRowsEquiv_apply_relabelRows])
    rwa [bidegree_relabelRows_finRotate] at hx
  · intro hc x e he
    obtain ⟨x, rfl⟩ : ∃ x', x'.relabelRows (finRotate n) = x :=
      ⟨x.relabelRows (finRotate n).symm, by simp⟩
    rw [GridChain.relabelRowsEquiv_apply_relabelRows] at he
    rw [bidegree_relabelRows_finRotate]
    exact hc x e he

/-- Cyclic column relabeling, renaming the surviving variables, identifies the homogeneous pieces
of the specialized complexes blocking `i` and `finRotate n i`.

Not a simp lemma: the chain-piece membership criterion is already a simp lemma. -/
theorem simplyBlockedRelabelColumnsEquiv_mem_bigradedChainHatPiece_iff {g : ℤ × ℤ}
    {c : GridChainHat R n i} :
    GridChain.simplyBlockedRelabelColumnsEquiv R (finRotate n) i c ∈
        (G.relabelColumns (finRotate n)).bigradedChainHatPiece R (finRotate n i) g ↔
      c ∈ G.bigradedChainHatPiece R i g := by
  classical
  -- Renaming the surviving variables renames the monomials without changing their degrees.
  have hs (x : GridState n) :
      (GridChain.simplyBlockedRelabelColumnsEquiv R (finRotate n) i c
        (x.relabelColumns (finRotate n))).support =
          (c x).support.image (Finsupp.mapDomain ((finRotate n).subtypeEquiv
            fun _ => not_congr (finRotate n).injective.eq_iff.symm)) := by
    rw [GridChain.simplyBlockedRelabelColumnsEquiv_apply, GridState.relabelColumns_relabelColumns,
      Equiv.self_trans_symm, GridState.relabelColumns_refl, simplyBlockedRenameEquiv_apply,
      support_rename_of_injective (Equiv.injective _)]
  rw [mem_bigradedChainHatPiece, mem_bigradedChainHatPiece]
  constructor
  · intro hc x e he
    have hx := hc (x.relabelColumns (finRotate n)) (e.mapDomain _)
      (by rw [hs]; exact Finset.mem_image_of_mem _ he)
    rwa [bidegree_relabelColumns_finRotate, Finsupp.degree_mapDomain] at hx
  · intro hc x e he
    obtain ⟨x, rfl⟩ : ∃ x', x'.relabelColumns (finRotate n) = x :=
      ⟨x.relabelColumns (finRotate n).symm, by simp⟩
    rw [hs, Finset.mem_image] at he
    obtain ⟨e, he, rfl⟩ := he
    rw [bidegree_relabelColumns_finRotate, Finsupp.degree_mapDomain]
    exact hc x e he

end OddComponentGridDiagram

end TauCeti
