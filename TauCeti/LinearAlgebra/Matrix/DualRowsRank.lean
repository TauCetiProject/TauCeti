/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Rank bounds for matrices with dual rows over local rings

Over a local ring `O`, columns of a block-indexed matrix `Q : Matrix (X × I) E O` that admit dual
rows in a matrix `R` remain linearly independent after reduction to the residue field
`ResidueField O`. Consequently, if every `X`-block of those columns reduces into a subspace
`S ≤ (I → ResidueField O)`, the number of such columns is at most `Fintype.card X * finrank S`.

## Main results

* `TauCeti.card_le_mul_finrank_of_dual_rows`: if columns `j ∈ s` of `Q` have dual rows in `R`
  and reduce blockwise into `S`, then `s.card ≤ Fintype.card X * Module.finrank (ResidueField O) S`.
* `TauCeti.card_add_card_le_mul_finrank`: if `R * Q = 1` and `R` kills columns `j ∈ J` of an
  invertible matrix `U`, and both sets of columns reduce blockwise into `S`, then
  `Fintype.card E + J.card ≤ Fintype.card X * Module.finrank (ResidueField O) S`.
* `TauCeti.dvd_of_forall_dvd_mul_inv_apply`: if `z` divides `c * P⁻¹.val j i` for every `j` in a
  column of an invertible matrix `P`, then `z ∣ c`.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/Edges.lean`
  (`New.card_le_mul_finrank_of_dual_rows`, `New.dvd_of_forall_dvd_mul_inv_apply`) and
  `src/New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean`
  (`New.card_add_card_le_mul_finrank`).
-/

public section

namespace TauCeti

open Matrix IsLocalRing Module Finset

/-- If the columns `j ∈ s` of `Q : Matrix (X × I) E O` have dual rows in `R` and every `X`-block
of each such column reduces into `S` over `ResidueField O`, then
`s.card ≤ Fintype.card X * Module.finrank (ResidueField O) S`. -/
theorem card_le_mul_finrank_of_dual_rows {O X I E : Type*} [CommRing O] [IsLocalRing O]
    [Fintype X] [Fintype I] [DecidableEq E] (Q : Matrix (X × I) E O) (R : Matrix E (X × I) O)
    {s : Finset E} {S : Submodule (ResidueField O) (I → ResidueField O)}
    (h_dual : ∀ j ∈ s, ∀ i : E, (R * Q) i j = if i = j then 1 else 0)
    (h_mem : ∀ j ∈ s, ∀ x : X, (fun i : I ↦ residue O (Q (x, i) j)) ∈ S) :
    s.card ≤ Fintype.card X * finrank (ResidueField O) S := by
  let v (j : s) (x : X) : S := ⟨fun i ↦ residue O (Q (x, i) j), h_mem j j.property x⟩
  have h_indep : LinearIndependent (ResidueField O) v := by
    refine Fintype.linearIndependent_iff.mpr fun c hc i ↦ ?_
    have h_entry (y : X × I) : ∑ j : s, c j * residue O (Q y j) = 0 := by
      simpa [v] using congrArg (fun f : X → S ↦ S.subtype (f y.fst) y.snd) hc
    calc c i = ∑ j : s, c j * residue O ((R * Q) i j) := by
          simp [h_dual]
      _ = ∑ y : X × I, residue O (R i y) * ∑ j : s, c j * residue O (Q y j) := by
          simp only [Matrix.mul_apply, map_sum, mul_sum, mul_left_comm]
          exact sum_comm
      _ = 0 := by simp only [h_entry, mul_zero, sum_const_zero]
  simpa [finrank_pi_fintype] using h_indep.fintype_card_le_finrank

/-- If `R * Q = 1` and `R` kills the columns `j ∈ J` of an invertible matrix `U`, and both the
columns of `Q` and those columns of `U` reduce blockwise into `S` over `ResidueField O`, then
`Fintype.card E + J.card ≤ Fintype.card X * Module.finrank (ResidueField O) S`. -/
theorem card_add_card_le_mul_finrank {O X I E : Type*} [CommRing O] [IsLocalRing O]
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I] [Fintype E] [DecidableEq E]
    {Q : Matrix (X × I) E O} {R : Matrix E (X × I) O} {U : GL (X × I) O} {J : Finset (X × I)}
    {S : Submodule (ResidueField O) (I → ResidueField O)} (hR : R * Q = 1)
    (h_ker : ∀ j ∈ J, R *ᵥ U.val.col j = 0)
    (hQ : ∀ (j : E) (x : X), (fun i : I ↦ residue O (Q (x, i) j)) ∈ S)
    (hU : ∀ j ∈ J, ∀ x : X, (fun i : I ↦ residue O (U.val (x, i) j)) ∈ S) :
    Fintype.card E + J.card ≤ Fintype.card X * finrank (ResidueField O) S := by
  let Q' : Matrix (X × I) (E ⊕ X × I) O := fun y c ↦
    match c with | .inl j => Q y j | .inr j => U.val y j
  let R' : Matrix (E ⊕ X × I) (X × I) O := fun r y ↦
    match r with | .inl i => R i y | .inr i => (U⁻¹.val - U⁻¹.val * Q * R) i y
  have hRU (i : E) {j : X × I} (hj : j ∈ J) : (R * U.val) i j = 0 := congrFun (h_ker j hj) i
  rw [← card_univ, ← card_disjSum]
  refine card_le_mul_finrank_of_dual_rows Q' R' ?_ ?_
  · rintro (j | j) hj (i | i)
    · rw [Matrix.mul_apply]
      simpa [Q', R', ← Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hR i) j
    · change ((U⁻¹.val - U⁻¹.val * Q * R) * Q) i j = 0
      simp [Matrix.sub_mul, Matrix.mul_assoc, hR]
    · rw [Matrix.mul_apply]
      simpa [Q', R', ← Matrix.mul_apply] using hRU i (inr_mem_disjSum.mp hj)
    · change ((U⁻¹.val - U⁻¹.val * Q * R) * U.val) i j = if Sum.inr i = Sum.inr j then 1 else 0
      have h1 : (U⁻¹.val - U⁻¹.val * Q * R) * U.val = 1 - U⁻¹.val * Q * (R * U.val) := by
        simp [Matrix.sub_mul, Matrix.mul_assoc]
      rw [h1]
      simp [Matrix.one_apply, Matrix.mul_apply (N := R * U.val), hRU _ (inr_mem_disjSum.mp hj)]
  · rintro (j | j) hj
    exacts [hQ j, hU j (inr_mem_disjSum.mp hj)]

/-- If `z` divides `c * P⁻¹.val j i` for every `j` in a column of an invertible matrix `P`, then
`z ∣ c`. -/
theorem dvd_of_forall_dvd_mul_inv_apply {O I : Type*} [CommRing O] [Fintype I] [DecidableEq I]
    (P : GL I O) {z c : O} {i : I} (h_col : ∀ j : I, z ∣ c * P⁻¹.val j i) : z ∣ c := by
  have h_diag : ∑ j : I, P.val i j * (c * P⁻¹.val j i) = c := by
    simp only [mul_left_comm, ← mul_sum, ← Matrix.mul_apply, P.mul_inv, one_apply_eq, mul_one]
  rw [← h_diag]
  exact dvd_sum fun j _ ↦ (h_col j).mul_left _

end TauCeti
