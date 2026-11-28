/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.NumberTheory.AbelSummation

/-!
# Logarithmic sieve dimension

A density `g : ℕ → ℝ` on a set `P` of natural numbers has *logarithmic sieve dimension* `κ` with
constant `C` if `∑_{p ∈ P, p prime, p ≤ z} g(p) log p ≤ κ log z + C` for every real `z ≥ 2`. This
is the hypothesis under which the sieve of Eratosthenes, with Rankin's trick, gives an estimate of
the right order: in the classical applications `g(p) = ω(p) / p` for a number `ω(p)` of excluded
residue classes modulo `p`.

The predicate records only the displayed inequality. Under it, and for a density that is
nonnegative at the selected primes, the sum of `g(p)` over the selected primes up to `z` is at
most `κ log log z + O(1)`, and the finite Euler product `∏ (1 + g(p) p ^ (1 / log z))` over the
same primes is `O((log z) ^ κ)`, with explicit constants. No theorem on the distribution of primes
is used: the bounds follow from the hypothesis by summation by parts.

## Main definitions

* `TauCeti.HasLogSieveDimension P g κ C`: the bound
  `∑_{p ∈ P, p prime, p ≤ z} g(p) log p ≤ κ log z + C` for every real `z ≥ 2`.

## Main results

* `TauCeti.HasLogSieveDimension.mono_const`, `TauCeti.HasLogSieveDimension.mono_dim`,
  `TauCeti.HasLogSieveDimension.mono_density`, `TauCeti.hasLogSieveDimension_empty`: monotonicity
  in the constant, the dimension and the density, and the empty set.
* `TauCeti.HasLogSieveDimension.dim_nonneg`: for a density nonnegative at the selected primes the
  dimension is nonnegative.
* `TauCeti.HasLogSieveDimension.sum_le_log_log`:
  `∑_{p ∈ P, p ≤ z} g(p) ≤ κ log log z + (κ - κ log log 2 + C / log 2)` for `z ≥ 2`.
* `TauCeti.HasLogSieveDimension.sum_mul_rpow_le`:
  `∑_{p ∈ P, p ≤ z} g(p) p ^ (1 / log z) ≤ κ log log z + O(1)` for `z ≥ 2`, with an explicit
  constant.
* `TauCeti.HasLogSieveDimension.prod_one_add_mul_rpow_le`,
  `TauCeti.HasLogSieveDimension.exists_prod_one_add_mul_rpow_le`:
  `∏_{p ∈ P, p ≤ z} (1 + g(p) p ^ (1 / log z)) ≤ K (log z) ^ κ` for `z ≥ 2`, with an explicit `K`.

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

/-- On the empty set every density has every nonnegative dimension with every nonnegative
constant. -/
theorem hasLogSieveDimension_empty (g : ℕ → ℝ) (hκ : 0 ≤ κ) (hC : 0 ≤ C) :
    HasLogSieveDimension ∅ g κ C := by
  intro z hz
  simpa using add_nonneg (mul_nonneg hκ (Real.log_nonneg (by linarith))) hC

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

open Classical in
/-- A sum over the selected primes up to `N` as a sum over `2 ≤ k ≤ N` of an indicator. -/
private theorem sum_filter_primesLE_eq (P : Set ℕ) (F : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ (Nat.primesLE N).filter (· ∈ P), F p =
      ∑ k ∈ Icc 2 N, if k.Prime ∧ k ∈ P then F k else 0 := by
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ ↦ rfl
  ext p
  simp only [mem_filter, Nat.mem_primesLE, mem_Icc]
  exact ⟨fun ⟨⟨hpN, hp⟩, hpP⟩ ↦ ⟨⟨hp.two_le, hpN⟩, hp, hpP⟩,
    fun ⟨⟨_, hpN⟩, hp, hpP⟩ ↦ ⟨⟨hpN, hp⟩, hpP⟩⟩

open Classical in
/-- **The density sum under a logarithmic sieve dimension.** If `g` has logarithmic sieve dimension
`κ ≥ 0` with constant `C` on `P`, then
`∑_{p ∈ P, p ≤ z} g(p) ≤ κ log log z + (κ - κ log log 2 + C / log 2)` for every real `z ≥ 2`. No
sign condition on `g` is needed. -/
theorem HasLogSieveDimension.sum_le_log_log (h : HasLogSieveDimension P g κ C) (hκ : 0 ≤ κ)
    (hz : 2 ≤ z) :
    ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p ≤
      κ * Real.log (Real.log z) + (κ - κ * Real.log (Real.log 2) + C / Real.log 2) := by
  have hN : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  set c : ℕ → ℝ := fun k ↦ if k.Prime ∧ k ∈ P then g k * Real.log k else 0 with hc
  have hsum (n : ℕ) (hn : 2 ≤ n) : ∑ k ∈ Icc 2 n, c k ≤ κ * Real.log n + C := by
    have hn' := h n (by exact_mod_cast hn)
    rwa [Nat.floor_natCast, sum_filter_primesLE_eq] at hn'
  have hdiv : ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p =
      ∑ k ∈ Icc 2 ⌊z⌋₊, c k / Real.log k := by
    rw [sum_filter_primesLE_eq]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk0 : Real.log k ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < k from (mem_Icc.1 hk).1))).ne'
    simp only [hc]
    split_ifs
    · rw [mul_div_cancel_right₀ _ hk0]
    · rw [zero_div]
  rw [hdiv]
  refine (sum_Icc_div_log_le_of_forall_sum_Icc_le hκ hsum hN).trans ?_
  have hfl : Real.log (Real.log ⌊z⌋₊) ≤ Real.log (Real.log z) :=
    Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1 < ⌊z⌋₊ by omega)))
      (Real.log_le_log (by exact_mod_cast (show 0 < ⌊z⌋₊ by omega)) (Nat.floor_le (by linarith)))
  exact add_le_add_left (mul_le_mul_of_nonneg_left hfl hκ) _

/-- For `1 ≤ x ≤ z` and `1 < z`, `x ^ (1 / log z) ≤ 1 + e log x / log z`: the exponent
`u = log x / log z` lies in `[0, 1]`, where `exp u ≤ 1 + e u`. -/
private theorem rpow_one_div_log_le {x z : ℝ} (hx : 1 ≤ x) (hxz : x ≤ z) (hz : 1 < z) :
    x ^ (1 / Real.log z) ≤ 1 + Real.exp 1 * (Real.log x / Real.log z) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlz : 0 < Real.log z := Real.log_pos hz
  set u : ℝ := Real.log x / Real.log z
  have hu0 : 0 ≤ u := div_nonneg (Real.log_nonneg hx) hlz.le
  have hu1 : u ≤ 1 := (div_le_one hlz).2 (Real.log_le_log hx0 hxz)
  have h1 : (1 - u) * Real.exp u ≤ 1 :=
    calc (1 - u) * Real.exp u ≤ Real.exp (-u) * Real.exp u :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-u)]) (Real.exp_pos u).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : u * Real.exp u ≤ u * Real.exp 1 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hu1) hu0
  rw [Real.rpow_def_of_pos hx0, mul_one_div]
  linarith

open Classical in
/-- **The tilted density sum under a logarithmic sieve dimension.** If `g` is nonnegative at the
selected primes and has logarithmic sieve dimension `κ` with constant `C ≥ 0` on `P`, then for
every real `z ≥ 2`
`∑_{p ∈ P, p ≤ z} g(p) p ^ (1 / log z) ≤ κ log log z + ((1 + e) (κ + C / log 2) - κ log log 2)`. -/
theorem HasLogSieveDimension.sum_mul_rpow_le (h : HasLogSieveDimension P g κ C)
    (hg : ∀ p ∈ P, p.Prime → 0 ≤ g p) (hC : 0 ≤ C) (hz : 2 ≤ z) :
    ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), g p * (p : ℝ) ^ (1 / Real.log z) ≤
      κ * Real.log (Real.log z) +
        ((1 + Real.exp 1) * (κ + C / Real.log 2) - κ * Real.log (Real.log 2)) := by
  have hκ : 0 ≤ κ := h.dim_nonneg hg
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  set T : Finset ℕ := (Nat.primesLE ⌊z⌋₊).filter (· ∈ P)
  have hterm (p : ℕ) (hp : p ∈ T) : g p * (p : ℝ) ^ (1 / Real.log z) ≤
      g p + Real.exp 1 / Real.log z * (g p * Real.log p) := by
    obtain ⟨hp, hpP⟩ := mem_filter.1 hp
    obtain ⟨hpz, hpp⟩ := Nat.mem_primesLE.1 hp
    calc g p * (p : ℝ) ^ (1 / Real.log z)
        ≤ g p * (1 + Real.exp 1 * (Real.log p / Real.log z)) :=
          mul_le_mul_of_nonneg_left (rpow_one_div_log_le (by exact_mod_cast hpp.one_le)
            ((Nat.le_floor_iff (by linarith)).1 hpz) (by linarith)) (hg p hpP hpp)
      _ = g p + Real.exp 1 / Real.log z * (g p * Real.log p) := by ring
  have h1 := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at h1
  have h2 := h.sum_le_log_log hκ hz
  have h3 : Real.exp 1 / Real.log z * ∑ p ∈ T, g p * Real.log p ≤
      Real.exp 1 * (κ + C / Real.log 2) :=
    calc Real.exp 1 / Real.log z * ∑ p ∈ T, g p * Real.log p
        ≤ Real.exp 1 / Real.log z * (κ * Real.log z + C) :=
          mul_le_mul_of_nonneg_left (h z hz) (div_nonneg (Real.exp_pos 1).le hlz.le)
      _ = Real.exp 1 * (κ + C / Real.log z) := by
          field_simp
      _ ≤ Real.exp 1 * (κ + C / Real.log 2) :=
          mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_left hC hl2
            (Real.log_le_log two_pos hz)) _) (Real.exp_pos 1).le
  linarith

open Classical in
/-- **The tilted Euler product under a logarithmic sieve dimension.** If `g` is nonnegative at the
selected primes and has logarithmic sieve dimension `κ` with constant `C ≥ 0` on `P`, then for
every real `z ≥ 2`
`∏_{p ∈ P, p ≤ z} (1 + g(p) p ^ (1 / log z)) ≤ K (log z) ^ κ`, where
`K = exp ((1 + e) (κ + C / log 2) - κ log log 2)`. -/
theorem HasLogSieveDimension.prod_one_add_mul_rpow_le (h : HasLogSieveDimension P g κ C)
    (hg : ∀ p ∈ P, p.Prime → 0 ≤ g p) (hC : 0 ≤ C) (hz : 2 ≤ z) :
    ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (· ∈ P), (1 + g p * (p : ℝ) ^ (1 / Real.log z)) ≤
      Real.exp ((1 + Real.exp 1) * (κ + C / Real.log 2) - κ * Real.log (Real.log 2)) *
        Real.log z ^ κ := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  set T : Finset ℕ := (Nat.primesLE ⌊z⌋₊).filter (· ∈ P)
  have hnonneg (p : ℕ) (hp : p ∈ T) : 0 ≤ g p * (p : ℝ) ^ (1 / Real.log z) :=
    mul_nonneg (hg p (mem_filter.1 hp).2 (Nat.mem_primesLE.1 (mem_filter.1 hp).1).2)
      (Real.rpow_nonneg p.cast_nonneg _)
  calc ∏ p ∈ T, (1 + g p * (p : ℝ) ^ (1 / Real.log z))
      ≤ ∏ p ∈ T, Real.exp (g p * (p : ℝ) ^ (1 / Real.log z)) :=
        prod_le_prod₀ (fun p hp ↦ add_nonneg zero_le_one (hnonneg p hp))
          fun p _ ↦ (add_comm _ _).le.trans (Real.add_one_le_exp _)
    _ = Real.exp (∑ p ∈ T, g p * (p : ℝ) ^ (1 / Real.log z)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (κ * Real.log (Real.log z) +
          ((1 + Real.exp 1) * (κ + C / Real.log 2) - κ * Real.log (Real.log 2))) :=
        Real.exp_le_exp.2 (h.sum_mul_rpow_le hg hC hz)
    _ = Real.exp ((1 + Real.exp 1) * (κ + C / Real.log 2) - κ * Real.log (Real.log 2)) *
          Real.log z ^ κ := by
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
  ⟨_, Real.exp_pos _, fun _ hz ↦
    (h.mono_const (le_max_left C 0)).prod_one_add_mul_rpow_le hg (le_max_right C 0) hz⟩

/-! ### Examples -/

/-- The empty set with `κ = C = 0`: the sum is empty. -/
example (g : ℕ → ℝ) : HasLogSieveDimension ∅ g 0 0 := hasLogSieveDimension_empty g le_rfl le_rfl

/-- The empty set with `κ = 0` and `C = -1` fails: the empty sum is not at most `-1`. -/
example (g : ℕ → ℝ) : ¬HasLogSieveDimension ∅ g 0 (-1) := fun h ↦ by
  have h2 := h 2 le_rfl
  simp at h2
  linarith

/-- `P = {2}` with `g(2) = 1 / 2`, `κ = 0` and `C = log 2 / 2`: equality at every cutoff. -/
example : HasLogSieveDimension {2} (fun _ ↦ 1 / 2) 0 (Real.log 2 / 2) := by
  intro z hz
  have hfl : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  rw [sum_filter_primesLE_eq]
  refine (sum_eq_single 2 (fun k _ hk ↦ ?_) fun hnot ↦ ?_).trans_le ?_
  · exact ite_eq_right fun hk' ↦ hk (Set.mem_singleton_iff.1 hk'.2)
  · exact absurd (mem_Icc.2 ⟨le_rfl, hfl⟩) hnot
  · simp only [Nat.prime_two, Set.mem_singleton_iff, and_self, ite_true, Nat.cast_ofNat, zero_mul,
      zero_add]
    exact (one_div_mul_eq_div _ _).le

end TauCeti
