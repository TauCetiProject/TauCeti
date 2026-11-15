/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain

/-!
# Cyclic permutations preserve the bigrading of the unblocked grid complex

Cyclic row and column relabeling preserve the Maslov--Alexander bidegree of monomials
and identify the homogeneous pieces of `GC⁻` in both directions. The column map also
renames polynomial variables. These chain-level statements work over commutative semirings;
an odd number of components ensures integral Alexander degrees.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
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

end TauCeti.OddComponentGridDiagram
