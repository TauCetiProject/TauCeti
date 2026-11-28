/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Block
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Orders of split Bessel unitriangular groups

In a split reduction, the unipotent factor of the Bessel group is block upper unitriangular
for `splitLevel`. Its freely chosen entries come from two strict triangular blocks, the
rectangle between the hyperbolic halves, and the two rectangles adjacent to the middle block.
This gives the order locally and over a product of split places.

The count is the finite matrix part of `New.Filling.card_reducedImage_besselU` in
`grh/src/New/Spanning/Unfolding/ReducedGroups.lean` of [lsernau/grh-lean][source].
This file does not identify the image of an adelic reduction map.

[source]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
-/

public section

open Finset

namespace TauCeti

/-- The number of entries strictly above the block diagonal for the split levels with a
middle block indexed by `μ` and `r` hyperbolic pairs. -/
theorem natCard_splitLevel_lt (r : ℕ) (μ : Type*) [Fintype μ] :
    Nat.card {p : SplitIndex r μ × SplitIndex r μ // splitLevel p.1 < splitLevel p.2} =
      r * (2 * Fintype.card μ + 2 * r - 1) := by
  classical
  have hlt : (∑ a : Fin r, ∑ b : Fin r, if a < b then 1 else 0) = r.choose 2 := by
    have hp := Finset.natCast_card_filter (R := ℕ) (fun p : Fin r × Fin r ↦ p.1 < p.2) univ
    rw [Nat.cast_id, Fintype.sum_prod_type] at hp
    rw [← hp]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin] using
      (Fintype.natCard_subtype_lt (α := Fin r))
  have hgt : (∑ a : Fin r, ∑ b : Fin r, if b < a then 1 else 0) = r.choose 2 := by
    rw [Finset.sum_comm, hlt]
  have hlast (a b : Fin r) : (2 * r - a.val < 2 * r - b.val) ↔ b < a := by
    rw [Fin.lt_def]
    omega
  have hhigh (a b : Fin r) : a.val < 2 * r - b.val := by omega
  have hlow (a : Fin r) : r < 2 * r - a.val := by omega
  -- Split both indices into the first isotropic block, the middle block and its opposite.
  have hcount : Nat.card {p : SplitIndex r μ × SplitIndex r μ // splitLevel p.1 < splitLevel p.2} =
      r.choose 2 + r * Fintype.card μ + r * r + (Fintype.card μ * r + r.choose 2) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h := Finset.natCast_card_filter (R := ℕ)
      (fun p : SplitIndex r μ × SplitIndex r μ ↦ splitLevel p.1 < splitLevel p.2) univ
    rw [Nat.cast_id] at h
    rw [h, Fintype.sum_prod_type]
    simp only [SplitIndex, Fintype.sum_sum_type, splitLevel_inl, splitLevel_middle,
      splitLevel_eStar, hlast, hhigh, hlow, Fin.isLt, ite_true, not_lt_of_ge (Fin.isLt _).le,
      not_lt_of_ge (hlow _).le, not_lt_of_ge (hhigh _ _).le, lt_irrefl, ite_false,
      sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_zero,
      add_zero, ← Fin.lt_def, hlt, hgt]
    ac_rfl
  rw [hcount]
  calc
    _ = 2 * r.choose 2 + r * (2 * Fintype.card μ + r) := by ring
    _ = r * (r + (2 * Fintype.card μ + r) - 1) := Nat.two_mul_choose_two_add_mul _ _
    _ = _ := by congr 1; omega

/-- In the Bessel basis the middle block is `κ ⊕ Unit`. The block upper unitriangular
subgroup at a split place has order `q ^ (r * (2 * k + 2 * r + 1))`, where `q` is the
residue field cardinality and `k` is the cardinality of `κ`. -/
theorem natCard_bessel_block_unitriangular (r : ℕ) (κ R : Type*) [Fintype κ] [DecidableEq κ]
    [CommRing R] :
    Nat.card (unitriangularSubgroup (splitLevel (ϱ := r) (μ := κ ⊕ Unit)) R) =
      Nat.card R ^ (r * (2 * Fintype.card κ + 2 * r + 1)) := by
  rw [natCard_unitriangularSubgroup, natCard_splitLevel_lt, Fintype.card_sum, Fintype.card_unit]
  congr 2
  omega

/-- Over finitely many split places the block upper unitriangular groups have order equal to
the product of the residue field sizes raised to the common number of free entries. -/
theorem natCard_pi_bessel_block_unitriangular {w : Type*} [Fintype w] (R : w → Type*)
    [∀ i, CommRing (R i)] (r : ℕ) (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Nat.card (∀ i, unitriangularSubgroup (splitLevel (ϱ := r) (μ := κ ⊕ Unit)) (R i)) =
      (∏ i, Nat.card (R i)) ^ (r * (2 * Fintype.card κ + 2 * r + 1)) := by
  rw [Nat.card_pi, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ ↦ natCard_bessel_block_unitriangular r κ (R i)

end TauCeti
