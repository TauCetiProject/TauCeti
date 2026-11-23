/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Chebyshev.Growth

import TauCeti.LinearAlgebra.Matrix.Cartan.ColumnReflection
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Rank-two tropical denominator recurrence

The initial vectors are the two negative coordinate vectors. Each subsequent vector
is the alternating exchange exponent times the positive part of the current vector,
minus the previous vector. When the product of the two positive exchange exponents
is at least four, the forward recurrence is described by rescaled Chebyshev
polynomials. Under these hypotheses the even subsequence and the odd subsequence are both
injective, giving the infinite-denominator step in the rank-two finite-type obstruction.

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

private def rankTwoCartan (b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -c; -b, 2]

private theorem rankTwoCartan_diag (b c : ℤ) (i : Fin 2) : rankTwoCartan b c i i = 2 := by
  fin_cases i <;> rfl

private def rankTwoReflection (b c : ℤ) (i : Fin 2) : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (rankTwoCartan b c).columnReflection (rankTwoCartan_diag b c) i

private abbrev coordinates : (Fin 2 → ℤ) ≃ₗ[ℤ] (ℤ × ℤ) :=
  LinearEquiv.finTwoArrow ℤ ℤ

private theorem coordinates_apply (v : Fin 2 → ℤ) : coordinates v = (v 0, v 1) := rfl

private theorem coordinates_reflection_zero (b c : ℤ) (v : Fin 2 → ℤ) :
    coordinates (rankTwoReflection b c 0 v) =
      (b * (coordinates v).2 - (coordinates v).1, (coordinates v).2) := by
  rw [coordinates_apply, coordinates_apply]
  simp [rankTwoReflection, rankTwoCartan, Fin.sum_univ_two]
  ring

private theorem coordinates_reflection_one (b c : ℤ) (v : Fin 2 → ℤ) :
    coordinates (rankTwoReflection b c 1 v) =
      ((coordinates v).1, c * (coordinates v).1 - (coordinates v).2) := by
  rw [coordinates_apply, coordinates_apply]
  simp [rankTwoReflection, rankTwoCartan, Fin.sum_univ_two]
  ring

private def rankTwoReflectedPair (b c : ℤ) (n : ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  let r₀ := rankTwoReflection b c 0
  let r₁ := rankTwoReflection b c 1
  let T := r₀ * r₁
  (coordinates ((T ^ n) (Pi.single 0 1)),
    coordinates ((T ^ n) (r₀ (Pi.single 1 1))))

private theorem rankTwoReflectedPair_eq_chebyshev (b c : ℤ) (n : ℕ) :
    let t := b * c - 2
    let s := (S ℤ (n : ℤ)).eval t
    let p := (S ℤ ((n : ℤ) - 1)).eval t
    rankTwoReflectedPair b c n = ((s + p, c * p), (b * s, s + p)) := by
  unfold rankTwoReflectedPair
  dsimp only
  rw [← mul_apply_eq_comp, mul_pow_mul]
  unfold rankTwoReflection
  rw [Matrix.columnReflection_mul_columnReflection_pow_single,
    Matrix.columnReflection_mul_columnReflection_mul_columnReflection_pow_single]
  simp [coordinates_apply, rankTwoCartan, mul_comm]

private theorem rankTwoReflectedPair_signs {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoReflectedPair b c n
    (0 < p.1.1 ∧ 0 ≤ p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2) := by
  have hprod : 0 < b * c := by omega
  have hc : 0 < c := pos_of_mul_pos_right hprod hb
  have hb' : 0 < b := pos_of_mul_pos_left hprod hc.le
  have ht : 2 ≤ b * c - 2 := by omega
  have hs : 0 < (S ℤ (n : ℤ)).eval (b * c - 2) :=
    lt_of_lt_of_le zero_lt_one (one_le_S_eval ht n)
  have hp := nonneg_S_eval_sub_one ht n
  have hsum := add_pos_of_pos_of_nonneg hs hp
  rw [rankTwoReflectedPair_eq_chebyshev]
  exact ⟨⟨hsum, mul_nonneg hc.le hp⟩, ⟨mul_pos hb' hs, hsum⟩⟩

private theorem rankTwoDenominatorPair_eq_rankTwoReflectedPair {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    rankTwoDenominatorPair b c (n + 1) = rankTwoReflectedPair b c n := by
  let r₀ := rankTwoReflection b c 0
  let r₁ := rankTwoReflection b c 1
  let T := r₀ * r₁
  let e : Fin 2 → ℤ := Pi.single 0 1
  let o := r₀ (Pi.single 1 1)
  have coord_e : coordinates e = (1, 0) := by simp [coordinates_apply, e]
  have coord_o : coordinates o = (b, 1) := by
    change coordinates (rankTwoReflection b c 0 (Pi.single 1 1)) = (b, 1)
    rw [coordinates_reflection_zero, coordinates_apply]
    simp
  have he : c • o - e = T e := by
    apply coordinates.injective
    simp only [map_sub, map_smul, T, r₀, r₁, mul_apply_eq_comp, coordinates_reflection_zero,
      coordinates_reflection_one, coord_e, coord_o]
    simp [mul_comm]
  have ho : b • T e - o = T o := by
    apply coordinates.injective
    simp only [map_sub, map_smul, T, r₀, r₁, mul_apply_eq_comp, coordinates_reflection_zero,
      coordinates_reflection_one, coord_e, coord_o]
    ext <;> simp <;> ring_nf
    simp
  have hs₀ (j : ℕ) : 0 ≤ coordinates ((T ^ j) e) :=
    ⟨(rankTwoReflectedPair_signs hb hbc j).1.1.le, (rankTwoReflectedPair_signs hb hbc j).1.2⟩
  have hs₁ (j : ℕ) : 0 ≤ coordinates ((T ^ j) o) :=
    ⟨(rankTwoReflectedPair_signs hb hbc j).2.1.le, (rankTwoReflectedPair_signs hb hbc j).2.2.le⟩
  change rankTwoDenominatorPair b c (n + 1) =
    (coordinates ((T ^ n) e), coordinates ((T ^ n) o))
  induction n with
  | zero => simp [coord_e, coord_o]
  | succ n ih =>
    have he_step : rankTwoDenominatorUpdate c (coordinates ((T ^ n) e))
        (coordinates ((T ^ n) o)) = coordinates ((T ^ (n + 1)) e) := by
      rw [rankTwoDenominatorUpdate_def, posPart_eq_self.mpr (hs₁ n), pow_succ,
        mul_apply_eq_comp, ← he]
      simp only [map_sub, map_smul]
    rw [rankTwoDenominatorPair_succ, ih, rankTwoDenominatorStep_eq, he_step]
    congr 1
    have hpow (v : Fin 2 → ℤ) : (T ^ (n + 1)) v = (T ^ n) (T v) := by
      rw [pow_succ, mul_apply_eq_comp]
    rw [rankTwoDenominatorUpdate_def, posPart_eq_self.mpr (hs₀ (n + 1)), hpow e, hpow o, ← ho]
    simp only [map_sub, map_smul]

/-- For `0 ≤ b` and `4 ≤ b * c`, the forward even and odd denominator vectors have the
following Chebyshev closed form. -/
theorem rankTwoDenominatorPair_succ_eq_chebyshev {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let t := b * c - 2
    let s := (S ℤ (n : ℤ)).eval t
    let p := (S ℤ ((n : ℤ) - 1)).eval t
    rankTwoDenominatorPair b c (n + 1) = ((s + p, c * p), (b * s, s + p)) := by
  rw [rankTwoDenominatorPair_eq_rankTwoReflectedPair hb hbc, rankTwoReflectedPair_eq_chebyshev]

private theorem rankTwo_forward_signs {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    (0 < p.1.1 ∧ 0 ≤ p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2) := by
  rw [rankTwoDenominatorPair_eq_rankTwoReflectedPair hb hbc]
  exact rankTwoReflectedPair_signs hb hbc n

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

/-- The second coordinates of the odd denominator subsequence grow strictly, including
the initial odd vector. -/
theorem rankTwoDenominatorPair_odd_snd_strictMono {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    StrictMono fun n : ℕ ↦ (rankTwoDenominatorPair b c n).2.2 := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have h := S_eval_add_S_sub_one_eval_strictMono (R := ℤ) (t := b * c - 2) (by omega)
    simpa only [rankTwoDenominatorPair_succ_eq_chebyshev hb hbc] using h (Nat.lt_succ_self n)

/-- Under the growth hypotheses, all odd denominator vectors are pairwise distinct. -/
theorem rankTwoDenominatorPair_odd_injective {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    Function.Injective fun n : ℕ ↦ (rankTwoDenominatorPair b c n).2 :=
  Function.Injective.of_comp (f := Prod.snd)
    (rankTwoDenominatorPair_odd_snd_strictMono hb hbc).injective

end TauCeti.Cluster
