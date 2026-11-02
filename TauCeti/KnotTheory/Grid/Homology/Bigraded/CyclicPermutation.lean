/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic
public import TauCeti.KnotTheory.Grid.Homology.CyclicPermutation

/-!
# Cyclic permutations preserve bigraded unblocked grid homology

The specified cyclic-row and cyclic-column equivalences on `GH⁻` identify each
`(O-Maslov, Alexander)` homogeneous piece, not just its Alexander degree. The column map
renames the polynomial variables, while both maps are linear over the ground ring. Restricting
these maps gives ground-ring linear equivalences of the homogeneous pieces, with forward and
inverse computation rules inherited from the original homology equivalences.

The chain-level statements work over commutative semirings; the homology comparisons require
commutative rings of characteristic two. As in the chain and homology bigradings, an odd number
of components ensures integral Alexander degrees. No knot hypothesis or field assumption is
needed.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3, 4.6 and Chapter 5.
The underlying equivalences are `GridDiagram.unblockedHomologyRelabelRowsFinRotateEquiv` and
`GridDiagram.unblockedHomologyRelabelColumnsFinRotateEquiv`.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section Chains

variable [CommSemiring R]

/-- Cyclically permuting rows preserves the bidegree of a monomial times a grid state. -/
@[simp]
theorem monomialBidegree_relabelRows_finRotate (x : GridState n) (d : Fin n →₀ ℕ) :
    (G.relabelRows (finRotate n)).monomialBidegree (x.relabelRows (finRotate n)) d =
      G.monomialBidegree x d := by
  have hM := G.1.maslovO_relabelRows_finRotate x
  rw [GridDiagram.maslovO_eq_intCast, GridDiagram.maslovO_eq_intCast,
    ← G.val_relabelRows] at hM
  have hM' : (G.relabelRows (finRotate n)).1.maslovOℤ
      (x.relabelRows (finRotate n)) = G.1.maslovOℤ x := by exact_mod_cast hM
  apply Prod.ext <;>
    simp only [monomialBidegree_fst, monomialBidegree_snd, hM',
      alexanderℤ_relabelRows_finRotate]

/-- Cyclically permuting columns and renaming the monomial variables preserves bidegree.

Not a simp lemma: simplification expands `finRotate` inside `Finsupp.mapDomain`. -/
theorem monomialBidegree_relabelColumns_finRotate (x : GridState n) (d : Fin n →₀ ℕ) :
    (G.relabelColumns (finRotate n)).monomialBidegree (x.relabelColumns (finRotate n))
        (d.mapDomain (finRotate n)) = G.monomialBidegree x d := by
  have hM := G.1.maslovO_relabelColumns_finRotate x
  rw [GridDiagram.maslovO_eq_intCast, GridDiagram.maslovO_eq_intCast,
    ← G.val_relabelColumns] at hM
  have hM' : (G.relabelColumns (finRotate n)).1.maslovOℤ
      (x.relabelColumns (finRotate n)) = G.1.maslovOℤ x := by exact_mod_cast hM
  apply Prod.ext <;>
    simp only [monomialBidegree_fst, monomialBidegree_snd, hM',
      alexanderℤ_relabelColumns_finRotate, Finsupp.degree_mapDomain]

/-- Row relabeling identifies the full homogeneous chain pieces in both directions.

Not a simp lemma: the chain-piece membership criterion is already a simp lemma. -/
theorem relabelRowsEquiv_mem_bigradedChainMinusPiece_iff {g : ℤ × ℤ}
    {c : GridChainMinus R n} :
    GridChain.relabelRowsEquiv (finRotate n) c ∈
        (G.relabelRows (finRotate n)).bigradedChainMinusPiece R g ↔
      c ∈ G.bigradedChainMinusPiece R g := by
  rw [mem_bigradedChainMinusPiece, mem_bigradedChainMinusPiece]
  constructor
  · intro hc x d hd
    have hx := hc (x.relabelRows (finRotate n)) d (by
      simpa only [GridChain.relabelRowsEquiv_apply, GridState.relabelRows_relabelRows,
        Equiv.self_trans_symm, GridState.relabelRows_refl] using hd)
    simpa only [monomialBidegree_relabelRows_finRotate] using hx
  · intro hc x d hd
    obtain ⟨x, rfl⟩ : ∃ x', x'.relabelRows (finRotate n) = x :=
      ⟨x.relabelRows (finRotate n).symm, by simp⟩
    rw [GridChain.relabelRowsEquiv_apply, GridState.relabelRows_relabelRows,
      Equiv.self_trans_symm, GridState.relabelRows_refl] at hd
    rw [monomialBidegree_relabelRows_finRotate]
    exact hc x d hd

/-- Column relabeling, including coefficient renaming, identifies homogeneous chain pieces.

Not a simp lemma: the chain-piece membership criterion is already a simp lemma. -/
theorem relabelColumnsRenameEquiv_mem_bigradedChainMinusPiece_iff {g : ℤ × ℤ}
    {c : GridChainMinus R n} :
    GridChain.relabelColumnsRenameEquiv R (finRotate n) c ∈
        (G.relabelColumns (finRotate n)).bigradedChainMinusPiece R g ↔
      c ∈ G.bigradedChainMinusPiece R g := by
  classical
  rw [mem_bigradedChainMinusPiece, mem_bigradedChainMinusPiece]
  have hs (x : GridState n) :
      ((GridChain.relabelColumnsRenameEquiv R (finRotate n) c)
        (x.relabelColumns (finRotate n))).support =
          (c x).support.image (Finsupp.mapDomain (finRotate n)) := by
    rw [← LinearEquiv.coe_coe, GridChain.relabelColumnsRenameEquiv_apply,
      GridState.relabelColumns_relabelColumns, Equiv.self_trans_symm,
      GridState.relabelColumns_refl, support_rename_of_injective (finRotate n).injective]
  constructor
  · intro hc x d hd
    have hx := hc (x.relabelColumns (finRotate n)) (d.mapDomain (finRotate n))
      (by rw [hs]; exact Finset.mem_image_of_mem _ hd)
    simpa only [monomialBidegree_relabelColumns_finRotate] using hx
  · intro hc x d hd
    obtain ⟨x, rfl⟩ : ∃ x', x'.relabelColumns (finRotate n) = x :=
      ⟨x.relabelColumns (finRotate n).symm, by simp⟩
    rw [hs, Finset.mem_image] at hd
    obtain ⟨d, hd, rfl⟩ := hd
    rw [monomialBidegree_relabelColumns_finRotate]
    exact hc x d hd

end Chains

variable [CommRing R] [CharP R 2]

-- Spell out the odd-component witnesses so that the target carriers are the targets of the
-- specified homology maps. The public relabeling definitions are opaque across module boundaries.
local notation "Gᵣ" => (Subtype.mk (GridDiagram.relabelRows (finRotate n) (Subtype.val G))
  (Eq.mpr (congrArg Odd (GridDiagram.componentCount_relabelRows (Subtype.val G) (finRotate n)))
    (Subtype.property G)) : OddComponentGridDiagram n)
local notation "Gc" => (Subtype.mk (GridDiagram.relabelColumns (finRotate n) (Subtype.val G))
  (Eq.mpr (congrArg Odd (GridDiagram.componentCount_relabelColumns (Subtype.val G) (finRotate n)))
    (Subtype.property G)) : OddComponentGridDiagram n)

/-- The specified row-move homology equivalence identifies every Maslov--Alexander piece. -/
@[simp]
theorem unblockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedPiece_iff
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    G.1.unblockedHomologyRelabelRowsFinRotateEquiv R y ∈
        bigradedUnblockedHomologyPiece Gᵣ R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g := by
  refine G.unblockedHomologyEquiv_mem_bigradedPiece_iff R Gᵣ
    (GridChain.relabelRowsEquiv (finRotate n))
    (G.1.unblockedDifferential_relabelRows_finRotate_apply R)
    (G.1.unblockedHomologyRelabelRowsFinRotateEquiv R)
    (G.1.unblockedHomologyRelabelRowsFinRotateEquiv_unblockedHomologyClass R) ?_
  have hG : G.relabelRows (finRotate n) = Gᵣ := Subtype.ext (G.val_relabelRows _)
  intro g c
  rw [← hG]
  exact G.relabelRowsEquiv_mem_bigradedChainMinusPiece_iff R

/-- The specified column-move homology equivalence identifies every Maslov--Alexander piece. -/
@[simp]
theorem unblockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedPiece_iff
    {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    G.1.unblockedHomologyRelabelColumnsFinRotateEquiv R y ∈
        bigradedUnblockedHomologyPiece Gc R g ↔
      y ∈ G.bigradedUnblockedHomologyPiece R g := by
  refine G.unblockedHomologyEquiv_mem_bigradedPiece_iff R Gc
    (GridChain.relabelColumnsRenameEquiv R (finRotate n))
    (G.1.unblockedDifferential_relabelColumns_finRotate_apply R)
    (G.1.unblockedHomologyRelabelColumnsFinRotateEquiv R)
    (G.1.unblockedHomologyRelabelColumnsFinRotateEquiv_unblockedHomologyClass R) ?_
  have hG : G.relabelColumns (finRotate n) = Gc := Subtype.ext (G.val_relabelColumns _)
  intro g c
  rw [← hG]
  exact G.relabelColumnsRenameEquiv_mem_bigradedChainMinusPiece_iff R

/-- Cyclic row permutation gives a specified linear equivalence in each bidegree of `GH⁻`. -/
noncomputable def bigradedUnblockedHomologyRelabelRowsFinRotateEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      bigradedUnblockedHomologyPiece Gᵣ R g where
  toEquiv := (G.1.unblockedHomologyRelabelRowsFinRotateEquiv R).toEquiv.subtypeEquiv
    (fun _ => (G.unblockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedPiece_iff R).symm)
  map_add' x y := Subtype.ext
    ((G.1.unblockedHomologyRelabelRowsFinRotateEquiv R).map_add x y)
  map_smul' r y := Subtype.ext
    (((G.1.unblockedHomologyRelabelRowsFinRotateEquiv R).restrictScalars R).map_smul r y)

/-- On underlying classes the row-piece equivalence is the original row equivalence. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRelabelRowsFinRotateEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyRelabelRowsFinRotateEquiv R g y :
      (G.1.relabelRows (finRotate n)).unblockedHomology R) =
        G.1.unblockedHomologyRelabelRowsFinRotateEquiv R y := (rfl)

/-- The inverse row-piece equivalence is the inverse of the specified row comparison. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRelabelRowsFinRotateEquiv_symm (g : ℤ × ℤ)
    (y : bigradedUnblockedHomologyPiece Gᵣ R g) :
    ((G.bigradedUnblockedHomologyRelabelRowsFinRotateEquiv R g).symm y :
      G.1.unblockedHomology R) =
        (G.1.unblockedHomologyRelabelRowsFinRotateEquiv R).symm y := (rfl)

/-- Cyclic column permutation gives a specified ground-ring equivalence in each bidegree.
The underlying map still renames the polynomial variables by `finRotate n`. -/
noncomputable def bigradedUnblockedHomologyRelabelColumnsFinRotateEquiv (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      bigradedUnblockedHomologyPiece Gc R g where
  toEquiv := (G.1.unblockedHomologyRelabelColumnsFinRotateEquiv R).toEquiv.subtypeEquiv
    (fun _ => (G.unblockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedPiece_iff R).symm)
  map_add' x y := Subtype.ext
    ((G.1.unblockedHomologyRelabelColumnsFinRotateEquiv R).map_add x y)
  map_smul' r y := Subtype.ext (by
    have hr : ((renameEquiv R (finRotate n)).toRingEquiv :
        MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)
          (algebraMap R (MvPolynomial (Fin n) R) r) =
        algebraMap R (MvPolynomial (Fin n) R) r :=
      (renameEquiv R (finRotate n)).commutes r
    have h := (G.1.unblockedHomologyRelabelColumnsFinRotateEquiv R).map_smulₛₗ
      (algebraMap R (MvPolynomial (Fin n) R) r) y
    rw [hr, algebraMap_smul, algebraMap_smul] at h
    exact h)

/-- On underlying classes the column-piece equivalence is the original column equivalence. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRelabelColumnsFinRotateEquiv (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    (G.bigradedUnblockedHomologyRelabelColumnsFinRotateEquiv R g y :
      (G.1.relabelColumns (finRotate n)).unblockedHomology R) =
        G.1.unblockedHomologyRelabelColumnsFinRotateEquiv R y := (rfl)

/-- The inverse column-piece equivalence is the inverse of the specified column comparison. -/
@[simp]
theorem coe_bigradedUnblockedHomologyRelabelColumnsFinRotateEquiv_symm (g : ℤ × ℤ)
    (y : bigradedUnblockedHomologyPiece Gc R g) :
    ((G.bigradedUnblockedHomologyRelabelColumnsFinRotateEquiv R g).symm y :
      G.1.unblockedHomology R) =
        (G.1.unblockedHomologyRelabelColumnsFinRotateEquiv R).symm y := (rfl)

end TauCeti.OddComponentGridDiagram
