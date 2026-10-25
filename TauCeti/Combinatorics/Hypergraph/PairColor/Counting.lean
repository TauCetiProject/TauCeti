/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Density
import TauCeti.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Pair-color bounds for finite families of maps

A family of maps taking each coordinate into a prescribed finite cell is bounded by the
volume of its box times the density of any color required on two distinct coordinates.
The cells may overlap, and maps need not be injective. Additional pair-color or higher-order
conditions only restrict the family, so this bound applies without any regularity input.
-/

public section

open Finset Fintype

namespace TauCeti.PairColorSystem

variable {ι κ V : Type*} [Fintype ι]

/-- A family of maps in a finite box that requires one prescribed pair color has size at most
that pair's density times the box volume. Cells may overlap: the density denominator counts
only distinct pairs, which is at most the full rectangle size. -/
theorem card_le_pairColorDensity_mul_prod (S : PairColorSystem κ V)
    (T : Finset (ι → V)) (A : ι → Finset V) {i j : ι} (hij : i ≠ j) (c : κ)
    (hcell : ∀ g ∈ T, ∀ k, g k ∈ A k)
    (hcolor : ∀ g ∈ T, S.colorOfPair (g i) (g j) = some c) :
    (#T : ℝ) ≤ (pairColorDensity S c (A i) (A j) : ℝ) * ∏ k, (#(A k) : ℝ) := by
  classical
  let R := ∏ k ∈ univ \ {i, j}, #(A k)
  have hcount : #{g ∈ piFinset A | S.colorOfPair (g i) (g j) = some c} =
      R * #((A i ×ˢ A j).filter fun p => S.colorOfPair p.1 p.2 = some c) := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [Fintype.sum_piFinset_apply_apply hij A
      (fun x y ↦ if S.colorOfPair x y = some c then (1 : ℕ) else 0)]
    simp only [sum_product, nsmul_eq_mul]
    rfl
  have hT : #T ≤ R * #((A i ×ˢ A j).filter
      fun p => S.colorOfPair p.1 p.2 = some c) := by
    rw [← hcount]
    exact card_le_card fun g hg ↦ mem_filter.mpr ⟨mem_piFinset.mpr (hcell g hg), hcolor g hg⟩
  have hvol : R * (#(A i) * #(A j)) = ∏ k, #(A k) := by
    rw [← prod_sdiff (by simp : {i, j} ⊆ (univ : Finset ι))]
    simp [R, hij, mul_comm]
  have hd : (0 : ℝ) ≤ pairColorDensity S c (A i) (A j) :=
    mod_cast pairColorDensity_nonneg S c (A i) (A j)
  have hnum := pairColorDensity_mul_card_support S c (A i) (A j)
  have hsupport : #((A i ×ˢ A j).filter fun p => p.1 ≠ p.2) ≤ #(A i) * #(A j) := by
    simpa using card_filter_le (A i ×ˢ A j) (fun p => p.1 ≠ p.2)
  have hnum' : (#((A i ×ˢ A j).filter
      fun p => S.colorOfPair p.1 p.2 = some c) : ℝ) ≤
      (pairColorDensity S c (A i) (A j) : ℝ) * (#(A i) * #(A j)) := by
    have heq : (pairColorDensity S c (A i) (A j) : ℝ) *
        #((A i ×ˢ A j).filter fun p => p.1 ≠ p.2) =
        #((A i ×ˢ A j).filter fun p => S.colorOfPair p.1 p.2 = some c) := by
      exact_mod_cast hnum
    rw [← heq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsupport) hd
  calc (#T : ℝ) ≤ R * #((A i ×ˢ A j).filter
          fun p => S.colorOfPair p.1 p.2 = some c) := by exact_mod_cast hT
    _ ≤ R * ((pairColorDensity S c (A i) (A j) : ℝ) * (#(A i) * #(A j))) :=
      mul_le_mul_of_nonneg_left hnum' (Nat.cast_nonneg R)
    _ = (pairColorDensity S c (A i) (A j) : ℝ) * ∏ k, (#(A k) : ℝ) := by
      rw [mul_left_comm]
      congr 1
      exact_mod_cast hvol

end TauCeti.PairColorSystem
