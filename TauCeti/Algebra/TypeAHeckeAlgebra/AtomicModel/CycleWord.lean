/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.CycleWord
import Mathlib.Tactic.LinearCombination

/-!
# Atomic traces of cycle words

Let `ι` be a finite linearly ordered alphabet of positive and negative letters with weights
`p : ι → R`, and write `Q = q ^ 2` and `gᵢ = q • T i`. This file computes the atomic trace
`TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p m` of the cycle word
`ζₘ = g_(m-2) * ⋯ * g_0` (`TauCeti.TypeAHeckeAlgebra.cycleWord`). The answer is the generating
identity

`1 + (Q - 1) * ∑ (m ≥ 1), tr (ζₘ) * X ^ m = ∏ (a positive), (1 - p a * X) / (1 - Q * p a * X) *
  ∏ (a negative), (1 + Q * p a * X) / (1 + p a * X)`

in the power series ring `R⟦X⟧`, stated with the denominators cleared
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_cycleWord_generating_function`). The weights are
arbitrary: they need not sum to `1` and need not satisfy the scalar slice condition under which
the atomic trace is a Markov trace.

The computation rests on the shape of the diagonal coefficients of `ζₘ` in the word basis. Since
`ζₘ₊₂ = g_m * ζₘ₊₁` and `ζₘ₊₁` does not move the last letter, the diagonal coefficient of `ζₘ₊₂`
at a word `w` is that of `ζₘ₊₁` at `w` with its last letter removed, times the diagonal
coefficient of the signed checked R-matrix at the last two letters `b = w m` and `c = w (m + 1)`:
`Q` or `-1` if `b = c` is positive or negative, `Q - 1` if `b < c`, and `0` if `b > c`. Hence only
weakly increasing words contribute. Grouping words by their last letter `c` turns this into a
recursion over the ordered alphabet: if `G c` is the generating series of the weighted diagonal
coefficients of words ending in `c`, then

`G c * (1 - ε c * p c * X) = p c * (1 + (Q - 1) * X * ∑ (b < c), G b)`,

with `ε c = Q` or `-1` according to the sign of `c`. Adding the letters in increasing order
multiplies `1 + (Q - 1) * X * ∑ G b` by one factor `(1 + (Q - 1 - ε c) * p c * X) /
(1 - ε c * p c * X)` at a time.

## Main results

* `TauCeti.TypeAHeckeAlgebra.atomicTrace_cycleWord_generating_function`: **the cycle-trace
  generating identity** for atomic traces.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the signed product model.
* A. Ram, *A Frobenius formula for the characters of the Hecke algebras*, Invent. Math. 106
  (1991), 461–488, for the cycle words `g_(m-1) ⋯ g_1`.
-/

public section

open Function Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- The diagonal coefficient of the signed checked R-matrix on two strands carrying the letters
`b` and `c`. -/
private def crossingDiag (b c : ι) : R :=
  if b = c then (if pos c then (q : R) ^ 2 else -1) else if b < c then (q : R) ^ 2 - 1 else 0

/-- In the diagonal coefficient of `T n * x`, for `x` on the first `n + 1` strands, at a word
ending in the letters `w (Fin.last n)` and `c`, only the colour-preserving part of the last
crossing survives. -/
private theorem signedChecked_T_last_mul_strandIncl_single_snoc_apply
    (x : TypeAHeckeAlgebra R q (n + 1)) (w : Fin (n + 1) → ι) (c : ι) :
    signedChecked pos q (T q (Fin.last n) * strandIncl R q (n + 1) x)
        (single (Fin.snoc w c) 1) (Fin.snoc w c) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        crossingDiag pos q (w (Fin.last n)) c := by
  have hj : BraidGroup.strand (Fin.last n : Fin (n + 2 - 1)) = (Fin.last n).castSucc :=
    Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.last n : Fin (n + 2 - 1)) = Fin.last (n + 1) :=
    Fin.ext (by simp)
  have hswap : Fin.snoc w c ∘ Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1)) =
      Fin.snoc (update w (Fin.last n) c) (w (Fin.last n)) := by
    rw [Equiv.comp_swap_eq_update]
    simp [← Fin.snoc_update, Fin.update_snoc_last]
  -- The last letter of the exchanged word is `w (Fin.last n)`, which `x` does not change.
  rw [map_mul, mul_apply_eq_comp, signedChecked_T, hj, hk, LinearMap.smul_apply,
    Finsupp.smul_apply, signedCheckedR_apply, hswap]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, smul_eq_mul, crossingDiag,
    signedChecked_strandIncl_single_snoc_apply_snoc]
  rcases lt_trichotomy (w (Fin.last n)) c with h | h | h
  · simp only [h.ne, h.ne', h, ↓reduceIte]
    ring
  · subst h
    simp only [↓reduceIte]
    ring
  · simp only [h.ne', h.ne, h.not_gt, ↓reduceIte]
    ring

variable [Fintype ι]

/-- Summing the diagonal coefficient of a crossing against a function of its first letter. -/
private theorem sum_crossingDiag_mul (c : ι) (f : ι → R) :
    ∑ b, crossingDiag pos q b c * f b =
      (if pos c then (q : R) ^ 2 else -1) * f c + ((q : R) ^ 2 - 1) * ∑ b with b < c, f b := by
  classical
  have h (b : ι) : crossingDiag pos q b c * f b =
      (if b = c then (if pos c then (q : R) ^ 2 else -1) * f c else 0) +
        (if b < c then ((q : R) ^ 2 - 1) * f b else 0) := by
    rcases lt_trichotomy b c with hbc | rfl | hbc
    · simp [crossingDiag, hbc.ne, hbc]
    · simp [crossingDiag]
    · simp [crossingDiag, hbc.ne', hbc.not_gt]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

variable (p : ι → R)

/-- The weighted sum of the diagonal coefficients of the cycle word on `m + 1` strands over the
words ending in the letter `c`. -/
private noncomputable def lastLetterSum (m : ℕ) (c : ι) : R :=
  ∑ w : Fin m → ι, signedChecked pos q (cycleWord q (m + 1))
    (single (Fin.snoc w c : Fin (m + 1) → ι) 1) (Fin.snoc w c) * (∏ i, p (w i)) * p c

/-- The atomic trace of a cycle word is the sum of its contributions by last letter. -/
private theorem atomicTrace_cycleWord_eq_sum_lastLetterSum (m : ℕ) :
    atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) = ∑ c, lastLetterSum pos q p m c := by
  rw [atomicTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (m + 1) ↦ ι)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, lastLetterSum, mul_assoc]

/-- On one strand only the one-letter word ending in `c` contributes, with its weight. -/
private theorem lastLetterSum_zero (c : ι) : lastLetterSum pos q p 0 c = p c := by
  simp [lastLetterSum]

/-- The recursion of the contributions by last letter: a word on `m + 2` strands contributes the
contribution of its first `m + 1` letters times the diagonal coefficient of the last crossing and
the weight of the last letter. -/
private theorem lastLetterSum_succ (m : ℕ) (c : ι) :
    lastLetterSum pos q p (m + 1) c =
      p c * ∑ b, crossingDiag pos q b c * lastLetterSum pos q p m b := by
  have hq : (q : R) * ((q⁻¹ : Rˣ) : R) = 1 := Units.mul_inv q
  rw [lastLetterSum, ← (Fin.snocEquiv (fun _ : Fin (m + 1) ↦ ι)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, cycleWord_add_two,
    smul_mul_assoc, map_smul, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    signedChecked_T_last_mul_strandIncl_single_snoc_apply, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, lastLetterSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
  linear_combination (signedChecked pos q (cycleWord q (m + 1)) (single (Fin.snoc w b) 1)
    (Fin.snoc w b) * crossingDiag pos q b c * (∏ i, p (w i)) * p b * p c) * hq

open PowerSeries

/-- The generating series `∑ m, lastLetterSum m c * X ^ m` of the contributions by last letter. -/
private noncomputable def lastLetterSeries (c : ι) : R⟦X⟧ :=
  PowerSeries.mk fun m ↦ lastLetterSum pos q p m c

/-- The recursion of the contributions by last letter, in generating series. -/
private theorem lastLetterSeries_mul (c : ι) :
    lastLetterSeries pos q p c * (1 - C ((if pos c then (q : R) ^ 2 else -1) * p c) * X) =
      C (p c) * (1 + C ((q : R) ^ 2 - 1) * X * ∑ b with b < c, lastLetterSeries pos q p b) := by
  set ε : R := if pos c then (q : R) ^ 2 else -1
  set S := ∑ b with b < c, lastLetterSeries pos q p b
  -- Put both sides in the form `constant + series * X`, so that the coefficients of degree
  -- `m + 1` follow from `coeff_succ_mul_X` without expanding a product of two series.
  rw [show lastLetterSeries pos q p c * (1 - C (ε * p c) * X) =
      lastLetterSeries pos q p c - C (ε * p c) * lastLetterSeries pos q p c * X by ring,
    show C (p c) * (1 + C ((q : R) ^ 2 - 1) * X * S) =
      C (p c) + C (p c * ((q : R) ^ 2 - 1)) * S * X by rw [map_mul]; ring]
  ext (_ | m)
  · simp [lastLetterSeries, lastLetterSum_zero]
  · simp only [map_sub, map_add, coeff_succ_mul_X, coeff_C_mul, coeff_C, lastLetterSeries,
      coeff_mk, S, map_sum, lastLetterSum_succ, sum_crossingDiag_mul, ε]
    simp only [reduceCtorEq, ↓reduceIte, zero_add]
    split_ifs <;> ring

/-- Adding the letters of a lower set of the alphabet in increasing order: the series
`1 + (Q - 1) * X * ∑ G b` over a lower set times its denominators is the product of its
numerators. -/
private theorem lastLetterSeries_prod (s : Finset ι) (hs : ∀ a ∈ s, ∀ b < a, b ∈ s) :
    (1 + C ((q : R) ^ 2 - 1) * X * ∑ b ∈ s, lastLetterSeries pos q p b) *
        ∏ b ∈ s, (1 - C ((if pos b then (q : R) ^ 2 else -1) * p b) * X) =
      ∏ b ∈ s, (1 + C (((q : R) ^ 2 - 1 - if pos b then (q : R) ^ 2 else -1) * p b) * X) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h ↦ (hlt a h).false
    -- The letters before `a` are exactly those of `s`.
    have hfilter : ({b | b < a} : Finset ι) = s := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hb ↦ (Finset.mem_insert.mp (hs a (Finset.mem_insert_self a s) b hb)).resolve_left
        hb.ne, hlt b⟩
    have hs' : ∀ a ∈ s, ∀ b < a, b ∈ s := fun x hx b hb ↦
      (Finset.mem_insert.mp (hs x (Finset.mem_insert_of_mem hx) b hb)).resolve_left
        (hb.trans (hlt x hx)).ne
    have ha := lastLetterSeries_mul pos q p a
    rw [hfilter] at ha
    rw [Finset.sum_insert has, Finset.prod_insert has, Finset.prod_insert has]
    simp only [map_mul, map_sub, map_one] at ha ih ⊢
    linear_combination (1 - C (if pos a then (q : R) ^ 2 else -1) * C (p a) * X +
        (C ((q : R) ^ 2) - 1) * X * C (p a)) * ih hs' +
      (C ((q : R) ^ 2) - 1) * X * (∏ b ∈ s, (1 - C (if pos b then (q : R) ^ 2 else -1) *
        C (p b) * X)) * ha

/-- **The cycle-trace generating identity for atomic traces.** With `Q = q ^ 2`, the generating
series `1 + (Q - 1) * ∑ (m ≥ 1), tr (ζₘ) * X ^ m` of the atomic traces of the cycle words, times
the factor `1 - Q * p a * X` of each positive letter and `1 + p a * X` of each negative letter,
is the product of the factors `1 - p a * X` of the positive letters and `1 + Q * p a * X` of the
negative letters. -/
theorem atomicTrace_cycleWord_generating_function :
    PowerSeries.mk (fun m ↦
        if m = 0 then 1 else ((q : R) ^ 2 - 1) * atomicTrace pos q p m (cycleWord q m)) *
        ∏ a, (if pos a then 1 - C ((q : R) ^ 2 * p a) * X else 1 + C (p a) * X) =
      ∏ a, (if pos a then 1 - C (p a) * X else 1 + C ((q : R) ^ 2 * p a) * X) := by
  have hseries : PowerSeries.mk (fun m ↦
      if m = 0 then 1 else ((q : R) ^ 2 - 1) * atomicTrace pos q p m (cycleWord q m)) =
      1 + C ((q : R) ^ 2 - 1) * X * ∑ b, lastLetterSeries pos q p b := by
    ext (_ | m)
    · simp
    · rw [mul_assoc, map_add, coeff_C_mul, coeff_succ_X_mul, map_sum]
      simp [lastLetterSeries, atomicTrace_cycleWord_eq_sum_lastLetterSum]
  have hD : ∏ a, (if pos a then 1 - C ((q : R) ^ 2 * p a) * X else 1 + C (p a) * X) =
      ∏ a, (1 - C ((if pos a then (q : R) ^ 2 else -1) * p a) * X) :=
    Finset.prod_congr rfl fun a _ ↦ by
      split_ifs
      · rfl
      · simp only [map_mul, map_neg, map_one]
        ring
  have hN : ∏ a, (if pos a then 1 - C (p a) * X else 1 + C ((q : R) ^ 2 * p a) * X) =
      ∏ a, (1 + C (((q : R) ^ 2 - 1 - if pos a then (q : R) ^ 2 else -1) * p a) * X) :=
    Finset.prod_congr rfl fun a _ ↦ by
      split_ifs <;> simp only [map_mul, map_sub, map_neg, map_one, map_pow] <;> ring
  rw [hseries, hD, hN]
  exact lastLetterSeries_prod pos q p Finset.univ fun _ _ b _ ↦ Finset.mem_univ b

end TauCeti.TypeAHeckeAlgebra
