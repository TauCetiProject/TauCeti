/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Depth cost weights and coordinate-mean identities for Frobenius cycles

For a Frobenius cycle `T` with `N` letters and Frobenius power `P = p ^ e`, a variable `(b, s)` is
deep for `r ≤ k` when `s` is even and `r ≤ b`, or `s` is odd and `b < r`. Assigning cost
`P ^ (-(2 * r))` to deep variables with `2 * r ≤ b`, `P ^ (-1)` to deep variables with `b < 2 * r`,
and `0` to non-deep variables yields the divisor constant
`c_div(k, n, r) = N * n * (P ^ (-(2 * r)) + r ^ 2 / (k * P))`.

## Main definitions and results

* `TauCeti.FrobeniusCycle.divisorConstant`: the constant `N * n * (P ^ (-2r) + r ^ 2 / (k * P))`.
* `TauCeti.FrobeniusCycle.sum_isDeep_div_le`: for `2 * r ≤ k`, the sum of the depth cost weights
  over all variables `(b, s) : Fin k × ZMod N` is at most `N * (k / P ^ (2 * r) + r ^ 2 / P)`.
* `TauCeti.FrobeniusCycle.mul_sum_exponent_val`: by symmetry across `Fin k`, for every variable
  `x : Fin k × ZMod N`,
  `k * ∑ β : Exponent N k n, (β.val x : ℝ) = Fintype.card (Exponent N k n) * n`.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/Depth.lean`
  (`New.FrobeniusCycle.divisorConstant`, `New.FrobeniusCycle.sum_deepIndicator_div_le`,
  `New.FrobeniusCycle.mul_sum_exponentOf`).
-/

public section

namespace TauCeti.FrobeniusCycle

open Finset

/-- The divisor constant `N * n * (P ^ (-(2 * r)) + r ^ 2 / (k * P))` bounding the mean depth cost
of a form of degree `n` in each of `N` letters in `k` variables. -/
noncomputable def divisorConstant {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N : ℕ}
    (T : FrobeniusCycle W R N) (k n r : ℕ) : ℝ :=
  (N : ℝ) * n * (1 / (T.P : ℝ) ^ (2 * r) + (r : ℝ) ^ 2 / ((k : ℝ) * T.P))

/-- Every index `b : Fin k` is deep in exactly half of the `N` letters of a Frobenius cycle `T`. -/
theorem sum_isDeep_letter {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N k r : ℕ}
    [NeZero N] (T : FrobeniusCycle W R N) (b : Fin k) :
    ∑ s : ZMod N, (if T.IsDeep r (b, s) then (1 : ℝ) else 0) = (N : ℝ) / 2 := by
  classical
  have h_bij : (univ.filter fun s : ZMod N ↦ T.isEven s = true).card =
      (univ.filter fun s : ZMod N ↦ ¬T.isEven s = true).card := by
    refine Finset.card_bij (fun s _ ↦ s + 1) (fun s hs ↦ by
      simp only [mem_filter, mem_univ, true_and] at hs ⊢; rw [T.isEven_add_one, hs]; simp)
      (fun _ _ _ _ h ↦ add_right_cancel h) fun s hs ↦ ⟨s - 1, ?_, sub_add_cancel s 1⟩
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    have h1 := T.isEven_add_one (s - 1); rw [sub_add_cancel] at h1
    cases h2 : T.isEven (s - 1) <;> simp_all
  have h_tot : 2 * (univ.filter fun s : ZMod N ↦ T.isEven s = true).card = N := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (ZMod N)))
      (p := fun s ↦ T.isEven s = true)
    simp only [card_univ, ZMod.card] at h; omega
  have h_eq : (∑ s : ZMod N, if T.IsDeep r (b, s) then (1 : ℝ) else 0) =
      ((univ.filter fun s : ZMod N ↦ T.isEven s = true).card : ℝ) := by
    rw [sum_boole]
    by_cases hb : r ≤ b.val
    · congr 1; exact congrArg card (by ext s; simp [isDeep_iff, hb, Nat.not_lt.mpr hb])
    · rw [show (univ.filter fun s : ZMod N ↦ T.IsDeep r (b, s)) =
        univ.filter fun s : ZMod N ↦ ¬T.isEven s = true by
        ext s; simp [isDeep_iff, hb, Nat.lt_of_not_ge hb], ← h_bij]
  rw [h_eq]; linarith [show (2 : ℝ) * (univ.filter fun s : ZMod N ↦ T.isEven s = true).card = N
    by exact_mod_cast h_tot]

/-- For `2 * r ≤ k`, the sum of the depth cost weights over all variables `(b, s) : Fin k × ZMod N`
is at most `N * (k / P ^ (2 * r) + r ^ 2 / P)`. -/
theorem sum_isDeep_div_le {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N k r : ℕ}
    [NeZero N] (T : FrobeniusCycle W R N) (hk : 2 * r ≤ k) :
    ∑ x : Fin k × ZMod N,
        (if T.IsDeep r x then (1 : ℝ) else 0) /
          (T.P : ℝ) ^ (if 2 * r ≤ x.fst.val then 2 * r else 1) ≤
      (N : ℝ) * (k / (T.P : ℝ) ^ (2 * r) + (r : ℝ) ^ 2 / T.P) := by
  classical
  have hr_sq : (r : ℝ) ≤ r ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero r
  have hP_nonneg : (0 : ℝ) ≤ T.P := Nat.cast_nonneg _
  have h_card : ((univ.filter fun b : Fin k ↦ 2 * r ≤ b.val).card : ℝ) ≤ k :=
    Nat.cast_le.mpr (by simpa using card_filter_le (univ : Finset (Fin k)) _)
  have h_lt_card : (univ.filter fun b : Fin k ↦ ¬2 * r ≤ b.val).card = 2 * r := by
    simpa [not_le, Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := k) (m := 2 * r))
  calc ∑ x : Fin k × ZMod N,
        (if T.IsDeep r x then (1 : ℝ) else 0) /
          (T.P : ℝ) ^ (if 2 * r ≤ x.fst.val then 2 * r else 1)
      = ∑ b : Fin k, ((N : ℝ) / 2) / (T.P : ℝ) ^ (if 2 * r ≤ b.val then 2 * r else 1) := by
        rw [Fintype.sum_prod_type]
        exact sum_congr rfl fun b _ ↦ by dsimp only; rw [← T.sum_isDeep_letter b, Finset.sum_div]
    _ = ((univ.filter fun b : Fin k ↦ 2 * r ≤ b.val).card : ℝ) *
          (((N : ℝ) / 2) / (T.P : ℝ) ^ (2 * r)) + (2 * r : ℝ) * (((N : ℝ) / 2) / T.P) := by
        rw [← sum_filter_add_sum_filter_not univ (fun b : Fin k ↦ 2 * r ≤ b.val)]
        congr 1
        · rw [sum_congr rfl (g := fun _ ↦ ((N : ℝ) / 2) / (T.P : ℝ) ^ (2 * r))
            fun b hb ↦ by simp [(mem_filter.mp hb).right], sum_const, nsmul_eq_mul]
        · rw [sum_congr rfl (g := fun _ ↦ ((N : ℝ) / 2) / T.P)
            fun b hb ↦ by simp [(mem_filter.mp hb).right], sum_const, nsmul_eq_mul, h_lt_card]
          push_cast; rfl
    _ ≤ (k : ℝ) * (((N : ℝ) / 2) / (T.P : ℝ) ^ (2 * r)) +
        (2 * r : ℝ) * (((N : ℝ) / 2) / T.P) := by gcongr
    _ = (N : ℝ) * (k / (T.P : ℝ) ^ (2 * r) / 2 + r / T.P) := by ring
    _ ≤ (N : ℝ) * (k / (T.P : ℝ) ^ (2 * r) + (r : ℝ) ^ 2 / T.P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (half_le_self (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hP_nonneg _)))
            (div_le_div_of_nonneg_right hr_sq hP_nonneg)) (Nat.cast_nonneg _)

/-- By symmetry across `Fin k`, for every variable `x : Fin k × ZMod N`,
`k * ∑ β : Exponent N k n, (β.val x : ℝ) = Fintype.card (Exponent N k n) * n`. -/
theorem mul_sum_exponent_val {N k n : ℕ} [NeZero N] (x : Fin k × ZMod N) :
    (k : ℝ) * ∑ β : Exponent N k n, (β.val x : ℝ) =
      (Fintype.card (Exponent N k n) : ℝ) * n := by
  have h_symm (a b : Fin k) (s : ZMod N) :
      ∑ β : Exponent N k n, (β.val (a, s) : ℝ) = ∑ β : Exponent N k n, (β.val (b, s) : ℝ) := by
    let e : (Fin k × ZMod N) ≃ (Fin k × ZMod N) :=
      Equiv.prodCongr (Equiv.swap a b) (Equiv.refl (ZMod N))
    let swapExp : Exponent N k n ≃ Exponent N k n :=
      { toFun β := ⟨Finsupp.equivCongrLeft e β.val, fun t ↦ by
          simpa [e] using (Equiv.sum_comp (Equiv.swap a b) fun c ↦ β.val (c, t)).trans
            (β.property t)⟩
        invFun β := ⟨Finsupp.equivCongrLeft e.symm β.val, fun t ↦ by
          simpa [e] using (Equiv.sum_comp (Equiv.swap a b) fun c ↦ β.val (c, t)).trans
            (β.property t)⟩
        left_inv β := Exponent.ext fun ⟨c, t⟩ ↦ by simp [e]
        right_inv β := Exponent.ext fun ⟨c, t⟩ ↦ by simp [e] }
    rw [← swapExp.sum_comp]
    refine sum_congr rfl fun _ _ ↦ ?_
    simp [swapExp, e]
  calc (k : ℝ) * ∑ β : Exponent N k n, (β.val x : ℝ)
      = ∑ b : Fin k, ∑ β : Exponent N k n, (β.val (b, x.snd) : ℝ) := by
        simp [h_symm _ x.fst]
    _ = ∑ _ : Exponent N k n, (n : ℝ) := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun β _ ↦ ?_
        exact_mod_cast β.property x.snd
    _ = (Fintype.card (Exponent N k n) : ℝ) * n := by simp

end TauCeti.FrobeniusCycle
