/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
public import TauCeti.GroupTheory.OrderOfElement.NegOne
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The transfer budget at marked primes of a theta lift

Passing Hecke operators through a theta-lift chain costs a transfer exponent for each marked
prime and a charge for the columns other than the long rows at its inducing places. For primes
below the chain length, the separation of scales pays for the entire charge. For larger primes,
the signed Frobenius has trivial base class, so the main part of the charge is paid by the short
weight at each inducing place, all of which are then of base class `1`.

The estimate corresponds to `New.Data.IsMarked.card_mul_transferExponent_add_sum_lowColumns_le`
in `New/UpperBound/Divisibility/MarkedPrimes.lean` of lsernau/grh-lean at
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset

namespace TauCeti.ThetaLift

/-- The denominator-cleared transfer exponent is paid for by the total order `a`. -/
private theorem transferExponent_le {x X a m p r f n : ℝ} (hx : 2 ≤ x)
    (hm : m ≤ x) (hp : p ≤ X) (hr : r ≤ x) (hf : f ≤ x ^ 12) (hn : n ≤ x ^ 7)
    (hX : x ^ 61 ≤ X) (ha : X ^ 2 ≤ a)
    (hp₀ : 0 ≤ p) (hr₀ : 0 ≤ r) (hf₀ : 0 ≤ f) (hn₀ : 0 ≤ n) :
    m * p * (r * f * (n + r)) ≤ a := by
  have hmono (i j : ℕ) (hij : i ≤ j) : x ^ i ≤ x ^ j := pow_le_pow_right₀ (by linarith) hij
  have hsum : n + r ≤ 2 * x ^ 7 := by
    linarith [hmono 1 7 (by decide), pow_one x]
  calc
    m * p * (r * f * (n + r)) ≤ x * p * (x * x ^ 12 * (2 * x ^ 7)) := by gcongr
    _ = p * (2 * x ^ 21) := by ring
    _ ≤ p * X := by
      gcongr
      exact (mul_le_mul_of_nonneg_right hx (by positivity)).trans
        ((by ring : x * x ^ 21 = x ^ 22).le.trans ((hmono 22 61 (by decide)).trans hX))
    _ ≤ X ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hp (hp₀.trans hp)
    _ ≤ a := ha

/-- Below the chain length, the scale separation pays for the short weight as well as its
column-count error; no subtraction for the base class is needed. -/
private theorem mul_shortWeight_add_slack_le {x X a m p r : ℝ} (hx : 2 ≤ x)
    (hm : m ≤ x) (hp : p ≤ m) (hr : r ≤ x) (hX : x ^ 61 ≤ X) (ha : X ^ 2 ≤ a)
    (hp₀ : 0 ≤ p) (hr₀ : 0 ≤ r) :
    m * p * r * (a / X + x ^ 60) ≤ a := by
  have hmono (i j : ℕ) (hij : i ≤ j) : x ^ i ≤ x ^ j := pow_le_pow_right₀ (by linarith) hij
  have hX₀ : 0 < X := (pow_pos (by linarith) _).trans_le hX
  have hslack : x ^ 60 ≤ a / X := (le_div_iff₀ hX₀).mpr (calc
    x ^ 60 * X ≤ X ^ 2 := by rw [sq]; gcongr; exact (hmono 60 61 (by decide)).trans hX
    _ ≤ a := ha)
  have ha₀ : 0 ≤ a := (sq_nonneg X).trans ha
  have hcoef : 2 * x ^ 3 ≤ X := calc
    2 * x ^ 3 ≤ x * x ^ 3 := by gcongr
    _ = x ^ 4 := by ring
    _ ≤ X := (hmono 4 61 (by decide)).trans hX
  calc
    m * p * r * (a / X + x ^ 60) ≤ x ^ 3 * (2 * (a / X)) := by
      rw [pow_succ x 2, sq]
      gcongr <;> linarith
    _ = (2 * x ^ 3) * (a / X) := by ring
    _ ≤ X * (a / X) := by gcongr
    _ = a := by field_simp

open Classical in
/-- The charge for one inducing place is paid by the per-place budget, with a short weight
credited at places of base class `1`. -/
private theorem mul_lowColumns_le {C : Type*} [Monoid C] {c σ : C} {lc m p : ℕ}
    {x X a : ℝ} (hp : 1 < p) (hm₂ : 2 ≤ m) (hm : (m : ℝ) ≤ x)
    (hpX : (p : ℝ) ≤ X) (hX : x ^ 61 ≤ X) (ha : X ^ 2 ≤ a)
    (hcols : (lc : ℝ) ≤ a / X + x ^ 60) (horder₀ : 0 < orderOf c)
    (horder : orderOf c ≤ Nat.clog p m) (horbit : ∃ i : ℕ, σ = c ^ i) :
    (Nat.clog p m : ℝ) * lc ≤ a / (m * p) + if σ = 1 then a / X else 0 := by
  have hx : 2 ≤ x := (by exact_mod_cast hm₂ : (2 : ℝ) ≤ m).trans hm
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hmp := mul_pos hm₀ hp₀
  have hX₀ := hp₀.trans_le hpX
  by_cases hbig : m ≤ p
  · have hr₁ := Nat.clog_eq_one hm₂ hbig
    have hc : c = 1 := orderOf_eq_one_iff.mp (by omega)
    obtain ⟨i, hi⟩ := horbit
    have hσ : σ = 1 := by simp [hi, hc]
    have hslack : x ^ 60 ≤ a / (m * p) := by
      apply (le_div_iff₀ hmp).2
      calc
        x ^ 60 * ((m : ℝ) * p) = (x ^ 60 * m) * p := (mul_assoc _ _ _).symm
        _ ≤ (x ^ 60 * x) * X := mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity))
          hpX hp₀.le (mul_nonneg (by positivity) (by linarith))
        _ ≤ X ^ 2 := by rw [← pow_succ, sq]; gcongr
        _ ≤ a := ha
    rw [hr₁, Nat.cast_one, one_mul, ite_eq_left hσ]
    linarith only [hcols, hslack]
  · have hlow : (Nat.clog p m : ℝ) * lc ≤ a / (m * p) := by
      apply (le_div_iff₀ hmp).2
      calc
        (Nat.clog p m : ℝ) * lc * ((m : ℝ) * p) = m * p * Nat.clog p m * lc := by ring
        _ ≤ m * p * Nat.clog p m * (a / X + x ^ 60) := by gcongr
        _ ≤ a := mul_shortWeight_add_slack_le hx hm (by exact_mod_cast (le_of_not_ge hbig))
          ((by exact_mod_cast Nat.clog_le_of_le_pow ((Nat.lt_pow_self hp : m < p ^ m).le) :
            (Nat.clog p m : ℝ) ≤ m).trans hm) hX ha hp₀.le (Nat.cast_nonneg _)
    exact hlow.trans (le_add_of_nonneg_right (by
      split_ifs
      · exact div_nonneg ((sq_nonneg X).trans ha) hX₀.le
      · exact le_rfl))

open Classical in
/-- Bound the combined transfer and column charges for a set `Λ` of marked primes. Here `m`
is the chain length, `n` its final rank, `p` the rational prime, `X` the second cutoff, and `a`
the total order. The number `f` of places is the cardinality of `G`. The weight is `b` on the
base-class-`−1` set `B` and `a / X` elsewhere.

The orbit premise says that each marked prime is induced by a base-class-`1` place, and all
places inducing that prime lie in the same signed Frobenius orbit. The budget is
`2 * f * a / (m * p)` plus one short weight for each marked inducing place of base class `1`.
In particular the budget fits the base loss per lift when `2 ≤ (log b)^2`. -/
theorem card_mul_transferExponent_add_sum_lowColumns_le
    {G C ι : Type*} [Monoid G] [Fintype G] [Monoid C] [HasDistribNeg C]
    {cls : G →* C} {g : G} {w : G → ι} {Λ : Finset ι} {B : Finset G} {lc : G → ℕ}
    {x X a b : ℝ} {m p n : ℕ}
    (hm : (m : ℝ) ≤ x) (hn : (n : ℝ) ≤ x ^ 7)
    (hf : (Fintype.card G : ℝ) ≤ x ^ 12) (hX : x ^ 61 ≤ X) (ha : X ^ 2 ≤ a)
    (hpX : (p : ℝ) ≤ X) (hneg : (-1 : C) ≠ 1) (hodd : Odd (orderOf (cls g)))
    (horder : orderOf (cls g) ≤ Nat.clog p m)
    (hB : ∀ σ ∈ B, cls σ = -1)
    (horbit : ∀ v ∈ Λ, ∃ τ, cls τ = 1 ∧ w τ = v ∧
      ∀ σ, w σ = v → ∃ i : ℕ, σ = g ^ i * τ)
    (hlc : ∀ σ, w σ ∈ Λ → (lc σ : ℝ) ≤ (if σ ∈ B then b else a / X) + x ^ 60) :
    let r := Nat.clog p m
    let f := Fintype.card G
    let S := univ.filter (fun σ ↦ w σ ∈ Λ)
    (Λ.card : ℝ) * (r * f * (n + r)) + r * ∑ σ ∈ S, (lc σ : ℝ) ≤
      2 * f * a / (m * p) + ((S.filter (fun σ ↦ cls σ = 1)).card : ℝ) * (a / X) := by
  intro r f S
  have horder₀ : 0 < orderOf (cls g) := by obtain ⟨k, hk⟩ := hodd; omega
  have hr₀ := horder₀.trans_le horder
  have hp : 1 < p := not_le.mp fun h ↦ hr₀.ne' (Nat.clog_of_left_le_one h m)
  have hm₂ : 2 ≤ m := by
    by_contra! h
    exact hr₀.ne' (Nat.clog_of_right_le_one (by omega) p)
  have hx : 2 ≤ x := (by exact_mod_cast hm₂ : (2 : ℝ) ≤ m).trans hm
  have hmp : 0 < (m : ℝ) * p :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have hpay : 0 ≤ a / (m * p) := div_nonneg ((sq_nonneg X).trans ha) hmp.le
  have hrm : (r : ℝ) ≤ m := by
    exact_mod_cast Nat.clog_le_of_le_pow ((Nat.lt_pow_self hp : m < p ^ m).le)
  have hr := hrm.trans hm
  have hcardΛ : (Λ.card : ℝ) ≤ f := by
    exact_mod_cast (card_le_card_of_surjOn w (s := univ) (t := Λ) fun v hv ↦ by
      obtain ⟨τ, _, hτ, _⟩ := horbit v hv
      exact ⟨τ, mem_univ _, hτ⟩)
  have htransfer : (r : ℝ) * f * (n + r) ≤ a / (m * p) := by
    apply (le_div_iff₀ hmp).2
    rw [mul_comm]
    exact transferExponent_le hx hm hpX hr hf hn hX ha (by positivity) (by positivity)
      (by positivity) (by positivity)
  have hlocal (σ : G) (hσ : σ ∈ S) :
      (r : ℝ) * lc σ ≤ a / (m * p) + if cls σ = 1 then a / X else 0 := by
    obtain ⟨τ, hτ, _, hfiber⟩ := horbit (w σ) (mem_filter.mp hσ).2
    obtain ⟨i, hi⟩ := hfiber σ rfl
    have hout : σ ∉ B := fun h ↦
      (cls.map_pow_mul_ne_neg_one_of_odd_orderOf hneg hodd hτ i) (hi ▸ hB σ h)
    have hcols : (lc σ : ℝ) ≤ a / X + x ^ 60 := by
      simpa only [ite_eq_right hout] using hlc σ (mem_filter.mp hσ).2
    exact mul_lowColumns_le hp hm₂ hm hpX hX ha hcols horder₀ horder ⟨i, by simp [hi, hτ]⟩
  have hsum := sum_le_sum hlocal
  have hcardS : (S.card : ℝ) ≤ f := by exact_mod_cast card_filter_le _ _
  rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter, sum_const,
    nsmul_eq_mul] at hsum
  have ht := mul_le_mul hcardΛ htransfer (by positivity) (by positivity)
  have hc := mul_le_mul_of_nonneg_right hcardS hpay
  linarith only [hsum, ht, hc, (by ring : (2 : ℝ) * f * a / (m * p) = 2 * (f * (a / (m * p))))]

end TauCeti.ThetaLift
