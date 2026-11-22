/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Chebyshev.Growth

import Mathlib.LinearAlgebra.Reflection

/-!
# Rank-two tropical denominator recurrence

The initial vectors are the two negative coordinate vectors. Each subsequent vector
is the alternating exchange exponent times the positive part of the current vector,
minus the previous vector. When the product of the two positive exchange exponents
is at least four, the forward recurrence is described by rescaled Chebyshev
polynomials. Under these same nonnegative-exponent and product hypotheses, all even-indexed vectors
are pairwise distinct, giving the infinite-denominator step in the rank-two finite-type
obstruction. No Laurent-numerator or cluster-variable realization is asserted here.

The closed form uses Mathlib's Chebyshev formulas for products of two linear reflections.
Positivity and growth use `one_le_S_eval` and `nonneg_S_eval_sub_one` for the coordinate signs, and
`S_eval_add_S_sub_one_eval_strictMono` for growth of the even first coordinates.

## Reference

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Annals of Mathematics 158 (2003), §§5 and 7.
-/

public section

namespace TauCeti.Cluster

open Polynomial.Chebyshev

/-- One vector update in the rank-two denominator recurrence. -/
def rankTwoDenominatorUpdate (k : ℤ) (u v : ℤ × ℤ) : ℤ × ℤ :=
  k • v⁺ - u

/-- The vector formula uses the positive part of the current denominator vector. -/
theorem rankTwoDenominatorUpdate_def (k : ℤ) (u v : ℤ × ℤ) :
    rankTwoDenominatorUpdate k u v = k • v⁺ - u := by rfl

/-- The coordinate formula for one denominator-vector update. -/
@[simp] theorem rankTwoDenominatorUpdate_eq (k : ℤ) (u v : ℤ × ℤ) :
    rankTwoDenominatorUpdate k u v =
      (k * max v.1 0 - u.1, k * max v.2 0 - u.2) := by
  ext <;> simp [rankTwoDenominatorUpdate, posPart_def]

/-- Two consecutive vector updates, in the alternating order `c` then `b`. -/
def rankTwoDenominatorStep (b c : ℤ) (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  let v := rankTwoDenominatorUpdate c p.1 p.2
  (v, rankTwoDenominatorUpdate b p.2 v)

/-- The pair step consists of a `c` update followed by a `b` update. -/
@[simp] theorem rankTwoDenominatorStep_eq (b c : ℤ) (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    rankTwoDenominatorStep b c p =
      (rankTwoDenominatorUpdate c p.1 p.2,
        rankTwoDenominatorUpdate b p.2 (rankTwoDenominatorUpdate c p.1 p.2)) := by
  rfl

/-- Adjacent pairs of denominator vectors in the rank-two tropical recurrence.
Pair `n` consists of the vectors at indices `2n` and `2n+1`. -/
def rankTwoDenominatorPair (b c : ℤ) (n : ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  (rankTwoDenominatorStep b c)^[n] ((-1, 0), (0, -1))

/-- Pair zero consists of the two negative coordinate vectors, independently of the exponents. -/
@[simp] theorem rankTwoDenominatorPair_zero (b c : ℤ) :
    rankTwoDenominatorPair b c 0 = ((-1, 0), (0, -1)) :=
  Function.iterate_zero_apply _ _

/-- Two consecutive tropical mutations advance one pair. -/
@[grind =]
theorem rankTwoDenominatorPair_succ (b c : ℤ) (n : ℕ) :
    rankTwoDenominatorPair b c (n + 1) =
      rankTwoDenominatorStep b c (rankTwoDenominatorPair b c n) :=
  Function.iterate_succ_apply' _ _ _

/-- Any pair sequence with the same initial pair and transition equals the denominator
recurrence, for arbitrary integer exponents. -/
theorem eq_rankTwoDenominatorPair (b c : ℤ) (f : ℕ → (ℤ × ℤ) × (ℤ × ℤ))
    (hzero : f 0 = ((-1, 0), (0, -1)))
    (hstep : ∀ n, f (n + 1) = rankTwoDenominatorStep b c (f n)) :
    f = rankTwoDenominatorPair b c := by
  have h : Function.Semiconj f Nat.succ (rankTwoDenominatorStep b c) := hstep
  funext n
  simpa [Nat.succ_iterate, hzero, rankTwoDenominatorPair] using h.iterate_right n 0

/-- The first forward pair has already passed the two negative initial vectors. -/
@[simp] theorem rankTwoDenominatorPair_one (b c : ℤ) :
    rankTwoDenominatorPair b c 1 = ((1, 0), (b, 1)) := by
  rw [rankTwoDenominatorPair_succ, rankTwoDenominatorPair_zero]
  simp only [rankTwoDenominatorStep_eq, rankTwoDenominatorUpdate_eq]
  norm_num

/-- On a nonnegative current vector the tropical update is linear. -/
theorem rankTwoDenominatorUpdate_of_nonneg (k : ℤ) (u v : ℤ × ℤ) (hv : 0 ≤ v) :
    rankTwoDenominatorUpdate k u v = k • v - u := by
  simp [rankTwoDenominatorUpdate, posPart_def, sup_eq_left.mpr hv]

private def firstReflection (b : ℤ) : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) :=
  Module.reflection (x := (1, 0))
    (f := 2 • LinearMap.fst ℤ ℤ ℤ - b • LinearMap.snd ℤ ℤ ℤ) (by simp)

private def secondReflection (c : ℤ) : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) :=
  Module.reflection (x := (0, 1))
    (f := 2 • LinearMap.snd ℤ ℤ ℤ - c • LinearMap.fst ℤ ℤ ℤ) (by simp)

private theorem firstReflection_apply (b : ℤ) (z : ℤ × ℤ) :
    firstReflection b z = (b * z.2 - z.1, z.2) := by
  rw [firstReflection, Module.reflection_apply]
  ext
  · simp
    ring
  · simp

private theorem secondReflection_apply (c : ℤ) (z : ℤ × ℤ) :
    secondReflection c z = (z.1, c * z.1 - z.2) := by
  rw [secondReflection, Module.reflection_apply]
  ext
  · simp
  · simp
    ring

private theorem firstReflection_power_apply (b c : ℤ) (n : ℕ) :
    ((firstReflection b * secondReflection c) ^ n) (1, 0) =
      let t := b * c - 2
      let s := (S ℤ (n : ℤ)).eval t
      let p := (S ℤ ((n : ℤ) - 1)).eval t
      (s + p, c * p) := by
  unfold firstReflection secondReflection
  rw [Module.reflection_mul_reflection_pow_apply_self _ _ n (b * c - 2) (by simp)]
  ext <;> simp [mul_comm]

private theorem secondReflection_power_apply (b c : ℤ) (n : ℕ) :
    (((firstReflection b * secondReflection c) ^ n) * firstReflection b) (0, 1) =
      let t := b * c - 2
      let s := (S ℤ (n : ℤ)).eval t
      let p := (S ℤ ((n : ℤ) - 1)).eval t
      (b * s, s + p) := by
  rw [mul_pow_mul]
  unfold firstReflection secondReflection
  rw [Module.reflection_mul_reflection_mul_reflection_pow_apply_self _ _ n
    (b * c - 2) (by simp; ring)]
  ext <;> simp [mul_comm]

private theorem rankTwoDenominatorPair_reflection_power {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    rankTwoDenominatorPair b c (n + 1) =
      (((firstReflection b * secondReflection c) ^ n) (1, 0),
        (((firstReflection b * secondReflection c) ^ n) * firstReflection b) (0, 1)) := by
  have hc : 0 ≤ c := (pos_of_mul_pos_right (by omega : 0 < b * c) hb).le
  have ht : 2 ≤ b * c - 2 := by omega
  let T := firstReflection b * secondReflection c
  let e : ℤ × ℤ := (1, 0)
  let o : ℤ × ℤ := firstReflection b (0, 1)
  change rankTwoDenominatorPair b c (n + 1) = ((T ^ n) e, ((T ^ n) * firstReflection b) (0, 1))
  simp only [mul_apply_eq_comp]
  change rankTwoDenominatorPair b c (n + 1) = ((T ^ n) e, (T ^ n) o)
  have he : c • o - e = T e := by
    simp only [T, e, o, mul_apply_eq_comp, firstReflection_apply, secondReflection_apply]
    ext <;> simp [mul_comm]
  have ho : b • T e - o = T o := by
    simp only [T, e, o, mul_apply_eq_comp, firstReflection_apply, secondReflection_apply]
    ext <;> simp <;> ring_nf
    simp
  have he_pos (j : ℕ) : 0 ≤ (T ^ j) e := by
    change 0 ≤ ((firstReflection b * secondReflection c) ^ j) (1, 0)
    rw [firstReflection_power_apply]
    exact ⟨add_nonneg (le_trans zero_le_one (one_le_S_eval ht j)) (nonneg_S_eval_sub_one ht j),
      mul_nonneg hc (nonneg_S_eval_sub_one ht j)⟩
  have ho_pos (j : ℕ) : 0 ≤ (T ^ j) o := by
    change 0 ≤ (T ^ j) (firstReflection b (0, 1))
    rw [← mul_apply_eq_comp, secondReflection_power_apply]
    exact ⟨mul_nonneg hb (le_trans zero_le_one (one_le_S_eval ht j)),
      add_nonneg (le_trans zero_le_one (one_le_S_eval ht j)) (nonneg_S_eval_sub_one ht j)⟩
  induction n with
  | zero => simp [e, o, firstReflection_apply]
  | succ n ih =>
    have he_step : rankTwoDenominatorUpdate c ((T ^ n) e) ((T ^ n) o) =
        (T ^ (n + 1)) e := by
      rw [rankTwoDenominatorUpdate_of_nonneg _ _ _ (ho_pos n), pow_succ,
        mul_apply_eq_comp, ← he, map_sub, map_smul]
    rw [rankTwoDenominatorPair_succ, ih, rankTwoDenominatorStep_eq, he_step]
    congr 1
    rw [rankTwoDenominatorUpdate_of_nonneg _ _ _ (he_pos (n + 1)), pow_succ,
      mul_apply_eq_comp, ← map_smul, ← map_sub, ho,
      ← mul_apply_eq_comp, ← pow_succ]

/-- For `0 ≤ b` and `4 ≤ b * c`, the forward even and odd denominator vectors have the
following Chebyshev closed form. -/
theorem rankTwoDenominatorPair_succ_eq_chebyshev {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let t := b * c - 2
    let s := (S ℤ (n : ℤ)).eval t
    let p := (S ℤ ((n : ℤ) - 1)).eval t
    rankTwoDenominatorPair b c (n + 1) = ((s + p, c * p), (b * s, s + p)) := by
  rw [rankTwoDenominatorPair_reflection_power hb hbc, firstReflection_power_apply,
    secondReflection_power_apply]

private theorem rankTwo_forward_signs {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    (0 < p.1.1 ∧ 0 ≤ p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2) := by
  have hprod : 0 < b * c := lt_of_lt_of_le (by norm_num) hbc
  have hc : 0 < c := pos_of_mul_pos_right hprod hb
  have hb' : 0 < b := pos_of_mul_pos_left hprod hc.le
  have ht : 2 ≤ b * c - 2 := by omega
  have hs : 0 < (S ℤ (n : ℤ)).eval (b * c - 2) :=
    lt_of_lt_of_le zero_lt_one (one_le_S_eval ht n)
  have hp := nonneg_S_eval_sub_one ht n
  have hsum := add_pos_of_pos_of_nonneg hs hp
  rw [rankTwoDenominatorPair_succ_eq_chebyshev hb hbc n]
  exact ⟨⟨hsum, mul_nonneg hc.le hp⟩, ⟨mul_pos hb' hs, hsum⟩⟩

/-- For `0 ≤ b` and `4 ≤ b * c`, each even forward vector has positive first coordinate and
nonnegative second coordinate. -/
theorem rankTwoDenominatorPair_forward_even_fst_pos_and_snd_nonneg {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    0 < p.1.1 ∧ 0 ≤ p.1.2 :=
  (rankTwo_forward_signs hb hbc n).1

/-- For `0 ≤ b` and `4 ≤ b * c`, each odd forward vector is strictly positive in both
coordinates. -/
theorem rankTwoDenominatorPair_forward_odd_fst_pos_and_snd_pos {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    0 < p.2.1 ∧ 0 < p.2.2 :=
  (rankTwo_forward_signs hb hbc n).2

/-- For `0 ≤ b` and `4 ≤ b * c`, the first entries of the even denominator vectors grow
strictly, including the initial pair. -/
theorem rankTwoDenominatorPair_even_fst_strictMono {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    StrictMono fun n : ℕ ↦ (rankTwoDenominatorPair b c n).1.1 := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have h := Polynomial.Chebyshev.S_eval_add_S_sub_one_eval_strictMono
      (R := ℤ) (t := b * c - 2) (by omega)
    simpa only [rankTwoDenominatorPair_succ_eq_chebyshev hb hbc] using h (Nat.lt_succ_self n)

/-- Under the growth hypotheses, all even denominator vectors are pairwise distinct. -/
theorem rankTwoDenominatorPair_even_injective {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    Function.Injective fun n : ℕ ↦ (rankTwoDenominatorPair b c n).1 :=
  Function.Injective.of_comp (f := Prod.fst)
    (rankTwoDenominatorPair_even_fst_strictMono hb hbc).injective

end TauCeti.Cluster
