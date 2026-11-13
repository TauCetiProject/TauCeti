/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Sums of extended nonnegative series

A series in `ℝ≥0∞` with a finite sum has a convergent real-valued series obtained by applying
`ENNReal.toReal` termwise. The real sum is the `toReal` of the original sum. This converts
nonnegative mass series into real probability formulas without repeating the finiteness argument.

Summing the indicator of a set `s` with value one counts its elements: the sum is `s.encard`.
This is the indicator form of `ENNReal.tsum_set_one`.

Every `y : ℝ≥0∞` is bounded by the dyadic series `1 + ∑ₖ 2^(k+1) 1{2^k < y}`. Applied pointwise to
a nonnegative function and integrated, this bounds its integral by a weighted sum of the measures
of its dyadic level sets.

An infinite sum over a finite dependent product of a product of terms in `ℝ≥0∞` factors as the
product of the infinite sums (`ENNReal.tsum_prod_pi`).

## Main declarations

* `HasSum.toReal`: a series in `ℝ≥0∞` with finite sum has the termwise `toReal` sum.
* `ENNReal.tsum_indicator_one`: summing the indicator of `s` with value one gives `s.encard`.
* `ENNReal.le_one_add_tsum_pow_indicator`: `y ≤ 1 + ∑ₖ 2^(k+1) 1{2^k < y}`.
* `ENNReal.tsum_prod_pi`: `∑' x : ∀ i, κ i, ∏ i, f i (x i) = ∏ i, ∑' y, f i y`.
-/

public section

open scoped ENNReal

/-- Applying `ENNReal.toReal` termwise preserves a series with finite sum. -/
theorem HasSum.toReal {ι : Type*} {f : ι → ℝ≥0∞} {s : ℝ≥0∞}
    (h : HasSum f s) (hs : s ≠ ∞) : HasSum (fun i ↦ (f i).toReal) s.toReal := by
  have hfin : ∑' i, f i ≠ ∞ := by rwa [h.tsum_eq]
  simpa only [← ENNReal.tsum_toReal_eq (_root_.ne_top_of_tsum_ne_top hfin), h.tsum_eq]
    using ENNReal.hasSum_toReal hfin

/-- Summing the indicator of a set with value one counts its elements. -/
theorem ENNReal.tsum_indicator_one {β : Type*} (s : Set β) :
    ∑' b, s.indicator (fun _ => (1 : ℝ≥0∞)) b = s.encard := by
  rw [← ENNReal.tsum_set_one, tsum_subtype _ fun _ => (1 : ℝ≥0∞)]

/-- A nonnegative extended real is at most `1 + ∑ₖ 2^(k+1) 1{2^k < y}`. -/
theorem ENNReal.le_one_add_tsum_pow_indicator (y : ℝ≥0∞) :
    y ≤ 1 + ∑' k : ℕ, if (2 : ℝ≥0∞) ^ k < y then 2 ^ (k + 1) else 0 := by
  set R : ℝ≥0∞ := 1 + ∑' k : ℕ, if (2 : ℝ≥0∞) ^ k < y then 2 ^ (k + 1) else 0
  by_contra! hR
  -- If `R < y`, then inductively `2^k < y` and `2^(k+1) ≤ R` for every `k`, so `R = ∞`.
  have hk : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k < y := by
    intro k
    induction k with
    | zero => exact lt_of_le_of_lt (by simp [R]) hR
    | succ k ih =>
      refine lt_of_le_of_lt (le_trans ?_ le_add_self) hR
      exact le_trans (by simp [ih]) (le_tsum _ k)
  have hRtop : R ≠ ∞ := hR.ne_top
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hRtop
  have h2 : (2 : ℝ≥0∞) ^ (n + 1) ≤ R :=
    le_trans (by simp [hk n]) ((le_tsum _ n).trans le_add_self)
  have : (n : ℝ≥0∞) < 2 ^ (n + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact (hn.trans (this.trans_le h2)).false

private theorem ENNReal.tsum_prod_pi_fin :
    ∀ {m : ℕ} {κ : Fin m → Type*} (f : ∀ i, κ i → ℝ≥0∞),
      ∑' x : ∀ i, κ i, ∏ i, f i (x i) = ∏ i, ∑' y : κ i, f i y
  | 0, _, f => by simp
  | m + 1, κ, f => by
    rw [← (Fin.consEquiv κ).tsum_eq]
    simp_rw [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [tsum_prod' (f := fun p : κ 0 × (∀ i : Fin m, κ i.succ) ↦
      f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod_pi_fin fun i ↦ f i.succ]

/-- An infinite sum in `ℝ≥0∞` of a finite product factors as the product of the infinite
sums. -/
theorem ENNReal.tsum_prod_pi {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (f : ∀ i, κ i → ℝ≥0∞) :
    ∑' x : ∀ i, κ i, ∏ i, f i (x i) = ∏ i, ∑' y : κ i, f i y := by
  let e := (Fintype.equivFin ι).symm
  rw [← (Equiv.piCongrLeft κ e).tsum_eq]
  have hprod (x : ∀ j : Fin (Fintype.card ι), κ (e j)) :
      (∏ i : ι, f i (Equiv.piCongrLeft κ e x i)) =
        ∏ j : Fin (Fintype.card ι), f (e j) (x j) :=
    (Fintype.prod_equiv e (fun j ↦ f (e j) (x j))
      (fun i ↦ f i (Equiv.piCongrLeft κ e x i)) fun j ↦ by
        simp [Equiv.piCongrLeft_apply_apply (P := κ) (e := e) x j]).symm
  simp_rw [hprod]
  rw [ENNReal.tsum_prod_pi_fin,
    Fintype.prod_equiv e (fun j ↦ ∑' y : κ (e j), f (e j) y) (fun i ↦ ∑' y : κ i, f i y)
      fun _ ↦ rfl]
