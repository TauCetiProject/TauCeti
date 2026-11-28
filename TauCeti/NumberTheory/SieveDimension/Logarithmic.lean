/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.AbelSummation

/-!
# Logarithmic sieve dimension

A density `g : ℕ → ℝ` on a set `P` of natural numbers has *logarithmic sieve dimension* `κ` with
constant `C` if `∑_{p ∈ P, p prime, p ≤ z} g(p) log p ≤ κ log z + C` for every real `z ≥ 2`. This
is the hypothesis under which the sieve of Eratosthenes, with Rankin's trick, gives an estimate of
the right order: in the classical applications `g(p) = ω(p) / p` for a number `ω(p)` of excluded
residue classes modulo `p`.

The predicate records only the displayed inequality. Under it the sum of `g(p)` over the selected
primes up to `z` is at most `κ log log z + O(1)`, with no sign condition on `g`, `κ` or `C`; and
for a density that is nonnegative at the selected primes the finite Euler product
`∏ (1 + g(p) p ^ (1 / log z))` over the same primes is `O((log z) ^ κ)`. The constants are
explicit. No theorem on the distribution of primes
is used: the bounds follow from the hypothesis by summation by parts.

## Main definitions

* `TauCeti.HasLogSieveDimension P g κ C`: the bound
  `∑_{p ∈ P, p prime, p ≤ z} g(p) log p ≤ κ log z + C` for every real `z ≥ 2`.

## Main results

* `TauCeti.HasLogSieveDimension.mono_const`, `TauCeti.HasLogSieveDimension.mono_dim`,
  `TauCeti.HasLogSieveDimension.mono_density`: monotonicity in the constant, the dimension and
  the density.
* `TauCeti.hasLogSieveDimension_empty_iff`: on the empty set the predicate holds exactly when
  `0 ≤ κ` and `0 ≤ κ log 2 + C`.
* `TauCeti.HasLogSieveDimension.dim_nonneg`: for a density nonnegative at the selected primes the
  dimension is nonnegative.
* `TauCeti.HasLogSieveDimension.sum_le_log_log`:
  `∑_{p ∈ P, p ≤ z} g(p) ≤ κ log log z + (κ - κ log log 2 + C / log 2)` for `z ≥ 2`.
* `TauCeti.HasLogSieveDimension.sum_mul_rpow_le`:
  `∑_{p ∈ P, p ≤ z} g(p) p ^ (1 / log z) ≤ κ log log z + A` for `z ≥ 2`, with
  `A = κ - κ log log 2 + C / log 2 + 2 (κ + max C 0 / log 2)`.
* `TauCeti.HasLogSieveDimension.prod_one_add_mul_rpow_le`,
  `TauCeti.HasLogSieveDimension.exists_prod_one_add_mul_rpow_le`:
  `∏_{p ∈ P, p ≤ z} (1 + g(p) p ^ (1 / log z)) ≤ exp A (log z) ^ κ` for `z ≥ 2`.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 11, §11.4: the hypothesis is
  (11.4.1), and the Euler product bound is the step of Exercise 11.6.1 after Rankin's trick.
-/

public section

open Finset

namespace TauCeti

variable {P : Set ℕ} {g g' : ℕ → ℝ} {κ κ' C C' z : ℝ}

open Classical in
/-- A density `g` on a set `P` of naturals has logarithmic sieve dimension `κ` with constant `C`
if `∑ g(p) log p ≤ κ log z + C` for every real `z ≥ 2`, the sum being over the primes `p ≤ z` in
`P`. No sign condition on `g`, `κ` or `C` is part of the predicate. -/
def HasLogSieveDimension (P : Set ℕ) (g : ℕ → ℝ) (κ C : ℝ) : Prop :=
  ∀ z : ℝ, 2 ≤ z →
    ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p * Real.log p ≤ κ * Real.log z + C

open Classical in
/-- The defining property of `TauCeti.HasLogSieveDimension`. -/
theorem hasLogSieveDimension_def :
    HasLogSieveDimension P g κ C ↔ ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p * Real.log p ≤ κ * Real.log z + C :=
  Iff.rfl

open Classical in
/-- The bound of a logarithmic sieve dimension at a cutoff `z ≥ 2`. -/
theorem HasLogSieveDimension.sum_le (h : HasLogSieveDimension P g κ C) (hz : 2 ≤ z) :
    ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p * Real.log p ≤ κ * Real.log z + C :=
  h z hz

/-- The constant of a logarithmic sieve dimension can be increased. -/
theorem HasLogSieveDimension.mono_const (h : HasLogSieveDimension P g κ C) (hC : C ≤ C') :
    HasLogSieveDimension P g κ C' :=
  fun z hz ↦ (h z hz).trans (add_le_add_right hC _)

/-- The dimension of a logarithmic sieve dimension can be increased. -/
theorem HasLogSieveDimension.mono_dim (h : HasLogSieveDimension P g κ C) (hκ : κ ≤ κ') :
    HasLogSieveDimension P g κ' C :=
  fun z hz ↦ (h z hz).trans <| add_le_add_left
    (mul_le_mul_of_nonneg_right hκ (Real.log_nonneg (by linarith))) _

/-- A density that is smaller at the selected primes has the same logarithmic sieve dimension. -/
theorem HasLogSieveDimension.mono_density (h : HasLogSieveDimension P g κ C)
    (hle : ∀ p ∈ P, p.Prime → g' p ≤ g p) : HasLogSieveDimension P g' κ C := by
  classical
  intro z hz
  refine (sum_le_sum fun p hp ↦ ?_).trans (h z hz)
  obtain ⟨hp, hpP⟩ := mem_filter.1 hp
  exact mul_le_mul_of_nonneg_right (hle p hpP (Nat.mem_primesLE.1 hp).2)
    (Real.log_natCast_nonneg p)

/-- For a density that is nonnegative at the selected primes, the dimension is nonnegative:
otherwise the bound `κ log z + C` would be negative for large `z`. -/
theorem HasLogSieveDimension.dim_nonneg (h : HasLogSieveDimension P g κ C)
    (hg : ∀ p ∈ P, p.Prime → 0 ≤ g p) : 0 ≤ κ := by
  classical
  by_contra hκ
  rw [not_le] at hκ
  set z : ℝ := max 2 (Real.exp ((C + 1) / -κ))
  have hsum : 0 ≤ ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p * Real.log p :=
    sum_nonneg fun p hp ↦ mul_nonneg
      (hg p (mem_filter.1 hp).2 (Nat.mem_primesLE.1 (mem_filter.1 hp).1).2)
      (Real.log_natCast_nonneg p)
  have hlog : (C + 1) / -κ ≤ Real.log z := by
    rw [← Real.log_exp ((C + 1) / -κ)]
    exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
  have h1 : κ * Real.log z ≤ κ * ((C + 1) / -κ) := mul_le_mul_of_nonpos_left hlog hκ.le
  have h2 : κ * ((C + 1) / -κ) = -(C + 1) := by
    rw [div_neg, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hκ.ne]
  linarith [h z (le_max_left _ _)]

/-- On the empty set, a density has logarithmic sieve dimension `κ` with constant `C` exactly when
`0 ≤ κ` and `0 ≤ κ log 2 + C`: the sum is empty, and `κ log z + C` is nonnegative for every
`z ≥ 2` exactly under these two conditions. -/
@[simp]
theorem hasLogSieveDimension_empty_iff (g : ℕ → ℝ) :
    HasLogSieveDimension ∅ g κ C ↔ 0 ≤ κ ∧ 0 ≤ κ * Real.log 2 + C := by
  refine ⟨fun h ↦ ⟨h.dim_nonneg fun p hp _ ↦ absurd hp (Set.notMem_empty p), ?_⟩,
    fun ⟨hκ, hC⟩ z hz ↦ ?_⟩
  · simpa using h 2 le_rfl
  · have hlog : Real.log 2 ≤ Real.log z := Real.log_le_log two_pos hz
    simpa using hC.trans (add_le_add_left (mul_le_mul_of_nonneg_left hlog hκ) C)

open Classical in
/-- **The density sum under a logarithmic sieve dimension.** If `g` has logarithmic sieve dimension
`κ` with constant `C` on `P`, then
`∑_{p ∈ P, p ≤ z} g(p) ≤ κ log log z + (κ - κ log log 2 + C / log 2)` for every real `z ≥ 2`. No
sign condition on `g`, `κ` or `C` is needed. -/
theorem HasLogSieveDimension.sum_le_log_log (h : HasLogSieveDimension P g κ C) (hz : 2 ≤ z) :
    ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p ≤
      κ * Real.log (Real.log z) + (κ - κ * Real.log (Real.log 2) + C / Real.log 2) := by
  set c : ℕ → ℝ := fun k ↦ if k.Prime ∧ k ∈ P then g k * Real.log k else 0 with hc
  have hsum (t : ℝ) (ht : 2 ≤ t) : ∑ k ∈ Icc 2 ⌊t⌋₊, c k ≤ κ * Real.log t + C := by
    have ht' := h t ht
    rwa [Nat.primesLE_eq_filter_Icc_two, filter_filter, sum_filter] at ht'
  have hdiv : ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p =
      ∑ k ∈ Icc 2 ⌊z⌋₊, c k / Real.log k := by
    rw [Nat.primesLE_eq_filter_Icc_two, filter_filter, sum_filter]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk0 : Real.log k ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < k from (mem_Icc.1 hk).1))).ne'
    simp only [hc]
    split_ifs
    · rw [mul_div_cancel_right₀ _ hk0]
    · rw [zero_div]
  rw [hdiv]
  exact sum_Icc_div_log_le_of_forall_sum_Icc_le hz fun t ht _ ↦ hsum t ht

open Classical in
/-- **The tilted density sum under a logarithmic sieve dimension.** If `g` is nonnegative at the
selected primes and has logarithmic sieve dimension `κ` with constant `C` on `P`, then for every
real `z ≥ 2`
`∑_{p ∈ P, p ≤ z} g(p) p ^ (1 / log z) ≤ κ log log z + A`, where
`A = κ - κ log log 2 + C / log 2 + 2 (κ + max C 0 / log 2)`. The exponent `log p / log z` lies in
`[0, 1]`, where `p ^ (1 / log z) ≤ 1 + 2 log p / log z` by `Real.abs_rpow_sub_one_le`. -/
theorem HasLogSieveDimension.sum_mul_rpow_le (h : HasLogSieveDimension P g κ C)
    (hg : ∀ p ∈ P, p.Prime → 0 ≤ g p) (hz : 2 ≤ z) :
    ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p * (p : ℝ) ^ (1 / Real.log z) ≤
      κ * Real.log (Real.log z) +
        (κ - κ * Real.log (Real.log 2) + C / Real.log 2 +
          2 * (κ + max C 0 / Real.log 2)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  set T : Finset ℕ := (Nat.primesLE ⌊z⌋₊).filter (· ∈ P)
  have hterm (p : ℕ) (hp : p ∈ T) : g p * (p : ℝ) ^ (1 / Real.log z) ≤
      g p + 2 / Real.log z * (g p * Real.log p) := by
    obtain ⟨hp, hpP⟩ := mem_filter.1 hp
    obtain ⟨hpz, hpp⟩ := Nat.mem_primesLE.1 hp
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hpp.pos
    have hu0 : 0 ≤ Real.log p * (1 / Real.log z) :=
      mul_nonneg (Real.log_natCast_nonneg p) (one_div_nonneg.2 hlz.le)
    have hu1 : Real.log p * (1 / Real.log z) ≤ 1 := by
      rw [mul_one_div]
      exact (div_le_one hlz).2 (Real.log_le_log hp0 ((Nat.le_floor_iff (by linarith)).1 hpz))
    have hpow := Real.abs_rpow_sub_one_le hp0 ((abs_of_nonneg hu0).trans_le hu1)
    rw [abs_of_nonneg hu0] at hpow
    calc g p * (p : ℝ) ^ (1 / Real.log z)
        ≤ g p * (1 + 2 * (Real.log p * (1 / Real.log z))) :=
          mul_le_mul_of_nonneg_left
            (by linarith [le_abs_self ((p : ℝ) ^ (1 / Real.log z) - 1)]) (hg p hpP hpp)
      _ = g p + 2 / Real.log z * (g p * Real.log p) := by ring
  have h1 := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at h1
  have h2 := h.sum_le_log_log hz
  have h3 : 2 / Real.log z * ∑ p ∈ T, g p * Real.log p ≤ 2 * (κ + max C 0 / Real.log 2) :=
    calc 2 / Real.log z * ∑ p ∈ T, g p * Real.log p
        ≤ 2 / Real.log z * (κ * Real.log z + C) :=
          mul_le_mul_of_nonneg_left (h z hz) (div_nonneg zero_le_two hlz.le)
      _ = 2 * (κ + C / Real.log z) := by
          field_simp
      _ ≤ 2 * (κ + max C 0 / Real.log 2) :=
          mul_le_mul_of_nonneg_left (add_le_add_right
            ((div_le_div_of_nonneg_right (le_max_left C 0) hlz.le).trans
              (div_le_div_of_nonneg_left (le_max_right C 0) hl2
                (Real.log_le_log two_pos hz))) _) zero_le_two
  linarith

open Classical in
/-- **The tilted Euler product under a logarithmic sieve dimension.** If `g` is nonnegative at the
selected primes and has logarithmic sieve dimension `κ` with constant `C` on `P`, then for every
real `z ≥ 2`
`∏_{p ∈ P, p ≤ z} (1 + g(p) p ^ (1 / log z)) ≤ exp A (log z) ^ κ`, where
`A = κ - κ log log 2 + C / log 2 + 2 (κ + max C 0 / log 2)`. -/
theorem HasLogSieveDimension.prod_one_add_mul_rpow_le (h : HasLogSieveDimension P g κ C)
    (hg : ∀ p ∈ P, p.Prime → 0 ≤ g p) (hz : 2 ≤ z) :
    ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), (1 + g p * (p : ℝ) ^ (1 / Real.log z)) ≤
      Real.exp (κ - κ * Real.log (Real.log 2) + C / Real.log 2 +
        2 * (κ + max C 0 / Real.log 2)) * Real.log z ^ κ := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  set T : Finset ℕ := (Nat.primesLE ⌊z⌋₊).filter (· ∈ P)
  have hprod := Real.prod_one_add_le_exp_sum T
    (f := fun p ↦ if p ∈ T then g p * (p : ℝ) ^ (1 / Real.log z) else 0) fun p ↦ by
      split_ifs with hp
      · exact mul_nonneg (hg p (mem_filter.1 hp).2 (Nat.mem_primesLE.1 (mem_filter.1 hp).1).2)
          (Real.rpow_nonneg p.cast_nonneg _)
      · exact le_rfl
  rw [prod_congr rfl fun p hp ↦ congrArg (1 + ·) (ite_eq_left hp),
    sum_congr rfl fun p hp ↦ ite_eq_left hp] at hprod
  refine hprod.trans ((Real.exp_le_exp.2 (h.sum_mul_rpow_le hg hz)).trans_eq ?_)
  rw [Real.exp_add, Real.rpow_def_of_pos hlz, mul_comm κ, mul_comm]

open Classical in
/-- **The tilted Euler product is `O((log z) ^ κ)`.** If `g` is nonnegative at the selected primes
and has logarithmic sieve dimension `κ` on `P`, then there is a constant `K > 0` with
`∏_{p ∈ P, p ≤ z} (1 + g(p) p ^ (1 / log z)) ≤ K (log z) ^ κ` for every real `z ≥ 2`. -/
theorem HasLogSieveDimension.exists_prod_one_add_mul_rpow_le (h : HasLogSieveDimension P g κ C)
    (hg : ∀ p ∈ P, p.Prime → 0 ≤ g p) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℝ, 2 ≤ z →
      ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), (1 + g p * (p : ℝ) ^ (1 / Real.log z)) ≤
        K * Real.log z ^ κ :=
  ⟨_, Real.exp_pos _, fun _ hz ↦ h.prod_one_add_mul_rpow_le hg hz⟩

/-! ### Examples -/

/-- The empty set with `κ = C = 0`: the sum is empty. -/
example (g : ℕ → ℝ) : HasLogSieveDimension ∅ g 0 0 :=
  (hasLogSieveDimension_empty_iff g).2 ⟨le_rfl, by simp⟩

/-- The empty set with `κ = 0` and `C = -1` fails: the empty sum is not at most `-1`. -/
example (g : ℕ → ℝ) : ¬HasLogSieveDimension ∅ g 0 (-1) := fun h ↦ by
  have h2 := ((hasLogSieveDimension_empty_iff g).1 h).2
  norm_num at h2

/-- `P = {2}` with `g(2) = 1 / 2`, `κ = 0` and `C = log 2 / 2`: equality at every cutoff. -/
example : HasLogSieveDimension {2} (fun _ ↦ 1 / 2) 0 (Real.log 2 / 2) := by
  intro z hz
  have hfl : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  rw [Nat.primesLE_eq_filter_Icc_two, filter_filter, sum_filter]
  refine (sum_eq_single 2 (fun k _ hk ↦ ?_) fun hnot ↦ ?_).trans_le ?_
  · exact ite_eq_right fun hk' ↦ hk (Set.mem_singleton_iff.1 hk'.2)
  · exact absurd (mem_Icc.2 ⟨le_rfl, hfl⟩) hnot
  · simp only [Nat.prime_two, Set.mem_singleton_iff, and_self, ite_true, Nat.cast_ofNat, zero_mul,
      zero_add]
    exact (one_div_mul_eq_div _ _).le

end TauCeti
