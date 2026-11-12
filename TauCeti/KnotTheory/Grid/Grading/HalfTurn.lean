/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.JFunction.Diagonal
public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.KnotTheory.Grid.Grading.Parity
public import TauCeti.KnotTheory.Grid.Rectangle.Relabeling
public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain

/-!
# Gradings under the half-turn

The half-turn moves marking squares by `Fin.rev` and grid points by negation modulo the
grid size. These different coordinate maps preserve the absolute `O`-Maslov and Alexander gradings.
Consequently the half-turn equivalence on grid homology can be used in grading-sensitive
arguments, such as comparison of the two corner types of stabilization.

Rectangle grading changes are preserved because the half-turn preserves covered marking
counts and the count of source-state points in the covered squares. The additive constant is
fixed at the diagonal state: its marking pairing is
invariant under reversal of the marking coordinates, as are the marking self-pairings.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 5.2.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The half-turn preserves the absolute `O`-Maslov grading, including its normalization. -/
theorem maslovO_rotate_halfTurn (x : GridState n) :
    G.rotate.maslovO x.halfTurn = G.maslovO x := by
  have hdiag (c : Fin n) : (GridState.mk 1 : GridState n) c = c := rfl
  have hhalf : (GridState.mk 1 : GridState n).halfTurn = GridState.mk 1 := by
    ext c
    rw [GridState.halfTurn_apply, hdiag, Fin.finRotate_rev_finRotate_rev, hdiag]
  have hbase : G.rotate.maslovO (GridState.mk 1).halfTurn = G.maslovO (GridState.mk 1) := by
    rw [hhalf, maslovO_def, maslovO_def]
    simp only [JO_def, OSet_def, rotate_O, GridState.JCenter_diagonal_rotate, GridState.J_rotate]
  refine GridState.eq_of_forall_sub_eq (f := fun x ↦ G.rotate.maslovO x.halfTurn)
    (GridState.mk 1) hbase (fun u v r ↦ ?_) x
  rw [maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card _
      (GridRectangleBetween.halfTurnEquiv u v r),
    maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card _ r,
    GridRectangleBetween.card_source_pointSet_inter_halfTurnEquiv,
    OSet_def, OSet_def, rotate_O, GridRectangleBetween.card_pointSet_inter_halfTurnEquiv]

/-- The half-turn preserves the integer `O`-Maslov grading. -/
theorem maslovOℤ_rotate_halfTurn (x : GridState n) :
    G.rotate.maslovOℤ x.halfTurn = G.maslovOℤ x := by
  have h := G.maslovO_rotate_halfTurn x
  rw [maslovO_eq_intCast, maslovO_eq_intCast] at h
  exact_mod_cast h

/-- The half-turn of a diagram and a grid state preserves the absolute Alexander grading. -/
theorem alexander_rotate_halfTurn (x : GridState n) :
    G.rotate.alexander x.halfTurn = G.alexander x := by
  have hdiag (c : Fin n) : (GridState.mk 1 : GridState n) c = c := rfl
  have hhalf : (GridState.mk 1 : GridState n).halfTurn = GridState.mk 1 := by
    ext c
    rw [GridState.halfTurn_apply, hdiag, Fin.finRotate_rev_finRotate_rev]
    rw [hdiag]
  have hbase : G.rotate.alexander (GridState.mk 1).halfTurn =
      G.alexander (GridState.mk 1) := by
    rw [hhalf, alexander_eq, alexander_eq]
    simp only [JO_def, JX_def, OSet_def, XSet_def, rotate_O, rotate_X,
      GridState.JCenter_diagonal_rotate, GridState.J_rotate]
  refine GridState.eq_of_forall_sub_eq (f := fun x => G.rotate.alexander x.halfTurn)
    (GridState.mk 1) hbase (fun u v R => ?_) x
  have hchange := G.rotate.alexander_sub_alexander_eq_card_sub_card
    (GridRectangleBetween.halfTurnEquiv u v R)
  rw [OSet_def, XSet_def, rotate_O, rotate_X,
    GridRectangleBetween.card_pointSet_inter_halfTurnEquiv,
    GridRectangleBetween.card_pointSet_inter_halfTurnEquiv] at hchange
  have horiginal := G.alexander_sub_alexander_eq_card_sub_card R
  rw [OSet_def, XSet_def] at horiginal
  exact hchange.trans horiginal.symm

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- The half-turn preserves the integer Alexander grading. -/
@[simp]
theorem alexanderℤ_rotate_halfTurn (x : GridState n) :
    G.rotate.alexanderℤ x.halfTurn = G.alexanderℤ x := by
  have h := G.1.alexander_rotate_halfTurn x
  rw [← G.val_rotate, alexander_eq_intCast, alexander_eq_intCast] at h
  exact_mod_cast h

section Chains

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

/-- The half-turn, including reversal of coefficient-variable indices, preserves the full
`O`-Maslov--Alexander bigrading of unblocked chains. -/
theorem halfTurnRenameEquiv_mem_bigradedChainMinusPiece {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    GridChain.halfTurnRenameEquiv R c ∈ G.rotate.bigradedChainMinusPiece R g := by
  classical
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro x e he
  rw [GridChain.halfTurnRenameEquiv_apply,
    support_rename_of_injective Fin.rev_injective, Finset.mem_image] at he
  obtain ⟨e, he, rfl⟩ := he
  have hM := G.1.maslovOℤ_rotate_halfTurn x.halfTurn
  have hA := G.alexanderℤ_rotate_halfTurn x.halfTurn
  rw [GridState.halfTurn_halfTurn] at hM hA
  have hdegree : G.rotate.monomialBidegree x (e.mapDomain Fin.rev) =
      G.monomialBidegree x.halfTurn e := by
    apply Prod.ext <;>
      simp only [monomialBidegree_fst, monomialBidegree_snd, hM, hA,
        Finsupp.degree_mapDomain]
  rw [hdegree]
  exact hc x.halfTurn e he

/-- The half-turn, including reversal of coefficient-variable indices, preserves the Alexander
grading of unblocked chains. -/
theorem halfTurnRenameEquiv_mem_alexanderChainMinusPiece {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    GridChain.halfTurnRenameEquiv R c ∈ G.rotate.alexanderChainMinusPiece R a := by
  classical
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  intro x e he
  rw [GridChain.halfTurnRenameEquiv_apply,
    support_rename_of_injective Fin.rev_injective, Finset.mem_image] at he
  obtain ⟨e, he, rfl⟩ := he
  have hx := G.alexanderℤ_rotate_halfTurn x.halfTurn
  rw [GridState.halfTurn_halfTurn] at hx
  rw [hx, Finsupp.degree_mapDomain]
  exact hc x.halfTurn e he

end Chains

end OddComponentGridDiagram

end TauCeti
