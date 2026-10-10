/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTime.Lists
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Polynomial-time unary arithmetic

Division is implemented by a bounded search, binary length by repeated halving, and
primality by trial division. In particular, binary length does not require constructing
an exponentially large power of two.
-/

@[expose] public section

namespace Turing.PolyTime

open Computability BitEncoding

@[fun_prop] theorem succ : PolyTime Nat.succ :=
  of_eq (f := fun n : ℕ => n + 1) (by fun_prop) fun _ => rfl

/-- Evaluation of a fixed natural-coefficient polynomial on unary input. -/
@[fun_prop] theorem polynomial_eval (P : Polynomial ℕ) :
    PolyTime (fun n : ℕ => P.eval n) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using comp add (pair hP hQ)
  | monomial d c =>
    simpa only [Polynomial.eval_monomial] using comp mul (pair (const c) (pow d))

theorem filter_range_lt (n k : ℕ) :
    (List.range n).filter (fun i => decide (i < k)) = List.range (Min.min n k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : n < k
    · rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
      simp [h, List.range_succ]
    · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      simp [h]

theorem countP_multiples (n m : ℕ) (hm : 0 < m) :
    (List.range n).countP (fun i => decide (m * (i + 1) ≤ n)) = n / m := by
  have h : (fun i => decide (m * (i + 1) ≤ n)) = (fun i => decide (i < n / m)) := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le hm, Nat.add_one_le_iff]
  rw [h, List.countP_eq_length_filter, filter_range_lt,
    Nat.min_eq_right (Nat.div_le_self ..), List.length_range]

@[fun_prop] theorem div : PolyTime (fun p : ℕ × ℕ => p.1 / p.2) := by
  have h : PolyTime (fun p : ℕ × ℕ => bif decide (p.2 = 0) then 0 else
      (List.range p.1).countP (fun i => decide (p.2 * (i + 1) ≤ p.1))) := by
    fun_prop
  exact of_eq h fun p => by
    by_cases hm : p.2 = 0
    · simp [hm]
    · simp [hm, countP_multiples p.1 p.2 (by omega)]

@[fun_prop] theorem mod : PolyTime (fun p : ℕ × ℕ => p.1 % p.2) :=
  of_eq (f := fun p : ℕ × ℕ => p.1 - (p.1 / p.2) * p.2) (by fun_prop)
    fun _ => Nat.mod_eq_sub_div_mul.symm

@[fun_prop] theorem dvd : PolyTime (fun p : ℕ × ℕ => decide (p.1 ∣ p.2)) :=
  of_eq (f := fun p : ℕ × ℕ => decide (p.2 % p.1 = 0)) (by fun_prop)
    fun _ => by simp only [Nat.dvd_iff_mod_eq_zero]

/-- One step of the halving algorithm for binary length. -/
def sizeStep (q : ℕ × ℕ) : ℕ × ℕ :=
  bif decide (q.1 = 0) then q else (q.1 / 2, q.2 + 1)

theorem size_eq_halving {n : ℕ} (hn : n ≠ 0) : n.size = (n / 2).size + 1 := by
  have hb : Nat.bit n.bodd n.div2 ≠ 0 := by simpa only [Nat.bit_bodd_div2] using hn
  have h := Nat.size_bit hb
  rw [Nat.bit_bodd_div2] at h
  simpa only [Nat.div2_val, Nat.succ_eq_add_one] using h

theorem iterate_sizeStep (n c i : ℕ) (hi : n ≤ i) :
    sizeStep^[i] (n, c) = (0, c + n.size) := by
  induction n using Nat.strong_induction_on generalizing c i with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using Function.iterate_fixed (f := sizeStep) (x := (0, c)) rfl i
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := by
        cases i with
        | zero => omega
        | succ j => exact ⟨j, rfl⟩
      have hd : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      rw [Function.iterate_succ_apply,
        show sizeStep (n, c) = (n / 2, c + 1) by simp [sizeStep, hn],
        ih (n / 2) hd (c + 1) j (by omega), size_eq_halving hn]
      congr 1
      omega

@[fun_prop] theorem size : PolyTime Nat.size := by
  have hstep : PolyTime (fun p : Unit × (ℕ × ℕ) => sizeStep p.2) := by
    unfold sizeStep
    fun_prop
  have hb : ∀ (u : Unit) q, (enc (sizeStep q)).length ≤
      (enc q).length + ((enc u).length + 2) ^ 1 := by
    intro u q
    by_cases h : q.1 = 0
    · simp [sizeStep, h]
    · simp only [sizeStep, h, decide_false, Bool.cond_false, length_enc_prod, length_enc_nat]
      have := Nat.div_le_self q.1 2
      have hq : (enc q).length = 2 * q.1 + 1 + q.2 := by
        change (enc (q.1, q.2)).length = _
        rw [length_enc_prod, length_enc_nat, length_enc_nat]
      have hu : (enc u).length = 0 := rfl
      rw [hu, hq]
      omega
  have hI := iterate₂ hstep 1 hb
  have hw : PolyTime (fun n : ℕ => ((), n, (n, 0))) := by fun_prop
  exact of_eq (comp snd (comp hI hw)) fun n => by
    rw [iterate_sizeStep n 0 n le_rfl]
    simp

@[fun_prop] theorem prime : PolyTime (fun n : ℕ => decide n.Prime) := by
  have hp : PolyTime (fun p : ℕ × ℕ => !decide (2 ≤ p.2) || !decide (p.2 ∣ p.1)) := by
    exact comp or (pair (comp not (by fun_prop)) (comp not (comp dvd (pair snd fst))))
  have ha := all (f := fun n m => !decide (2 ≤ m) || !decide (m ∣ n))
    hp (range : PolyTime List.range)
  have h : PolyTime (fun n : ℕ => decide (2 ≤ n) &&
      (List.range n).all (fun m => !decide (2 ≤ m) || !decide (m ∣ n))) := by
    exact comp and (pair (by fun_prop) ha)
  apply of_eq h
  intro n
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun m hm hmn => (h m hmn).resolve_left (by omega)⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun m hmn => ?_⟩
    by_cases hm : 2 ≤ m
    · exact Or.inr (h m hm hmn)
    · exact Or.inl hm

end Turing.PolyTime
