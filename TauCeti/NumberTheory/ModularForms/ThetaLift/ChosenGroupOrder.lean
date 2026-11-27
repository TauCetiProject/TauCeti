/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Totient

/-!
# The size of the finite reduction group for a theta-lift chain

The product of the general linear groups at the chosen places bounds the orders of
class stabilizers. The rank bound and the product bound for the residue norms give a
logarithmic order budget of `x ^ 32`. The sharper tower degree estimate, rather than the
coarse bound `x ^ 12` on the number of places, leaves room for the auxiliary level.

The order budget is that of `New.Data.log_chosenGroupOrder_le` in lsernau/grh-lean
(`72fead1`, `grh/src/New/UpperBound/Objects/LiftChains.lean`).
-/

public section

open scoped BigOperators MatrixGroups

namespace TauCeti.OneSidedBound

/-- Let `L` be the logarithm of the large cutoff, and `T` the tower degree, so that
`φ(q) T` is the number of chosen places over each principal-level prime. If the product of
residue-field sizes is at most `M ^ (φ(q) T)`, the product of the rank-`r * (5 * r)` general
linear groups has logarithmic order at most `x ^ 32`. The same upper bound applies if the
residue fields are replaced by finite semirings of the same sizes. -/
theorem log_chosenGroupOrder_le {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, Semiring (R i)] [∀ i, Finite (R i)] {q T r M : ℕ} {x L : ℝ}
    (hL : 2 ≤ L) (hx : L ^ 100 ≤ x) (hr : (r : ℝ) ≤ 3 * x ^ 5)
    (hφ : (q.totient : ℝ) ≤ L) (hT : (T : ℝ) ≤ x ^ 11 * L ^ (1 / 5 : ℝ))
    (hM : Real.log M ≤ 22 * L) (hres : (∏ i, Nat.card (R i)) ≤ M ^ (q.totient * T)) :
    Real.log (Nat.card (∀ i, GL (Fin (r * (5 * r))) (R i))) ≤ x ^ 32 := by
  have hL₀ : 0 ≤ L := by linarith
  have hx₀ : 0 ≤ x := (pow_nonneg hL₀ _).trans hx
  have hcard : 0 < (∏ i, (Nat.card (R i) : ℝ)) := by
    exact Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (Nat.card_pos (α := R i))
  have hlog : Real.log (∏ i, (Nat.card (R i) : ℝ)) ≤
      ((q.totient * T : ℕ) : ℝ) * Real.log M := by
    rw [← Real.log_pow, ← Nat.cast_pow, ← Nat.cast_prod]
    apply Real.log_le_log _ (Nat.cast_le.mpr hres)
    simpa only [Nat.cast_prod] using hcard
  have hTL : (T : ℝ) ≤ x ^ 11 * L :=
    hT.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_self_of_one_le (by linarith) (by norm_num)) (pow_nonneg hx₀ _))
  have hbudget : 44550 * L ^ 3 ≤ x := by
    calc
      _ ≤ L ^ 16 * L ^ 3 := by
        gcongr
        exact (by norm_num : (44550 : ℝ) ≤ 2 ^ 16).trans (pow_le_pow_left₀ zero_le_two hL _)
      _ = L ^ 19 := by ring
      _ ≤ L ^ 100 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ x := hx
  calc
    _ ≤ (Nat.card (Fin (r * (5 * r))) : ℝ) ^ 2 *
        Real.log (∏ i, (Nat.card (R i) : ℝ)) := Matrix.log_natCard_pi_GL_le R
    _ ≤ ((r : ℝ) * (5 * r)) ^ 2 * ((q.totient : ℝ) * T * Real.log M) := by
      push_cast [Nat.card_fin] at hlog ⊢
      gcongr
    _ ≤ ((3 * x ^ 5) * (5 * (3 * x ^ 5))) ^ 2 * (L * (x ^ 11 * L) * (22 * L)) := by
      gcongr
    _ = x ^ 31 * (44550 * L ^ 3) := by ring
    _ ≤ x ^ 31 * x := mul_le_mul_of_nonneg_left hbudget (pow_nonneg hx₀ _)
    _ = x ^ 32 := (pow_succ x 31).symm

end TauCeti.OneSidedBound
