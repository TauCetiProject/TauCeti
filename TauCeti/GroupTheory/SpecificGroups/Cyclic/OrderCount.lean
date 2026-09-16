/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.Data.ZMod.Count
public import TauCeti.GroupTheory.OrderOfElement

/-!
# Counting the elements of a cyclic group by a condition on their order

In a finite cyclic group, the number of elements whose order satisfies a predicate `p` is the sum
of `φ d` over the divisors `d` of the group order that satisfy `p`.

Mathlib counts elements of an *exact* order: `IsCyclic.card_orderOf_eq_totient` says there are
`φ d` of them for each `d` dividing the group order. Summing that over the divisors selected by
`p` is the whole content here.

The point of stating it for a predicate is that it turns a count defined by a condition on orders
into an arithmetic sum over divisors, where the group has disappeared. Whatever `p` is, the answer
is a totient sum over `{d ∣ #α | p d}`, so it can then be evaluated or estimated by number theory
alone.

## Main results

* `IsCyclic.card_filter_orderOf_eq_sum_totient`, and its additive counterpart: the count of
  elements whose order satisfies `p` is `∑ φ d` over the divisors `d` of the group order with
  `p d`.
* `IsCyclic.card_filter_dvd_orderOf_eq_sum_totient`: the case `p = (f ∣ ·)`.
* `IsCyclic.card_filter_dvd_orderOf_mul_prod_primeFactors`: that case in closed form, in `ℕ`.
* `IsCyclic.card_filter_dvd_orderOf_eq_mul_prod_primeFactors`: the closed form as a product
  over `ℚ`.
* `IsCyclic.le_card_filter_dvd_orderOf`: the uniform lower bound `(1 - 2 ^ -r) ^ #f.primeFactors`
  for the proportion of elements of order divisible by `f`, when `f ^ r ∣ #α`.

## The elements of order divisible by `f`, in closed form

Let `α` have order `h` and let `f` divide `h`. The elements of `α` whose order is a multiple of
`f` are counted exactly:

`#{τ | f ∣ orderOf τ} = h * ∏ p ∣ f, (1 - p ^ -(v_p h - v_p f + 1))`,

the product running over the primes of `f`. Writing `τ = g ^ k` for a generator `g`, `f` divides
the order of `τ` exactly when `p ^ (v_p h - v_p f + 1)` fails to divide `k` for every prime `p` of
`f` (`IsOfFinOrder.dvd_orderOf_pow_iff`). Those conditions constrain `k` modulo coprime prime
powers, so they are independent and the count is a product.

Two forms of the count are recorded: an identity in `ℕ`, cleared of denominators, and the
displayed product over `ℚ`. At `f = h` every exponent is `1` and the count becomes Euler's
product formula `Nat.totient_mul_prod_primeFactors`, since the elements whose order is a multiple
of `h` are the `φ h` generators.

The third result is the estimate that makes the count usable when `f` is fixed and `h` is
divisible by a high power of `f`: if `f ^ r ∣ h` with `1 ≤ r`, every factor of the product is at
least `1 - 2 ^ -r`, so the proportion of elements of order divisible by `f` is at least
`(1 - 2 ^ -r) ^ #f.primeFactors`, which tends to `1` as `r` grows.
-/

public section

open Finset Nat

open scoped Function -- for the `on` notation in `Pairwise (Nat.Coprime on a)`

variable {α : Type*} [Group α] [Fintype α] [IsCyclic α]

/-- **The elements of a cyclic group whose order satisfies `p`, counted by order.**
Each divisor `d` of the group order contributes its `φ d` elements of order exactly `d`, and the
condition `p (orderOf τ)` keeps precisely the divisors satisfying `p`. -/
@[to_additive
/-- **The elements of a finite additive cyclic group whose order satisfies `p`, counted by
order.** Each divisor `d` of the group order contributes its `φ d` elements of `addOrderOf`
exactly `d`, and the condition `p (addOrderOf τ)` keeps precisely the divisors satisfying
`p`. -/]
theorem IsCyclic.card_filter_orderOf_eq_sum_totient (p : ℕ → Prop) [DecidablePred p] :
    #{τ : α | p (orderOf τ)} =
      ∑ d ∈ {d ∈ (Fintype.card α).divisors | p d}, φ d := by
  classical
  calc #{τ : α | p (orderOf τ)}
      -- Every element's order divides the group order, so selecting by `p` and selecting by
      -- membership in the `p`-divisors keep the same elements.
      = #{τ ∈ (Finset.univ : Finset α) | orderOf τ ∈ {d ∈ (Fintype.card α).divisors | p d}} := by
        refine congrArg Finset.card (filter_congr fun τ _ ↦ ?_)
        simp only [mem_filter, Nat.mem_divisors]
        exact ⟨fun h ↦ ⟨⟨orderOf_dvd_card, Fintype.card_ne_zero⟩, h⟩, fun h ↦ h.2⟩
    _ = ∑ d ∈ {d ∈ (Fintype.card α).divisors | p d},
          #{τ ∈ (Finset.univ : Finset α) | orderOf τ = d} :=
        (Finset.sum_card_fiberwise_eq_card_filter _ _ _).symm
    _ = ∑ d ∈ {d ∈ (Fintype.card α).divisors | p d}, φ d := by
        refine sum_congr rfl fun d hd ↦ ?_
        rw [mem_filter, Nat.mem_divisors] at hd
        exact IsCyclic.card_orderOf_eq_totient hd.1.1

/-- **The elements of a cyclic group whose order is a multiple of `f`, counted by order.**
The divisibility case of `IsCyclic.card_filter_orderOf_eq_sum_totient`. -/
@[to_additive
/-- **The elements of a finite additive cyclic group whose order is a multiple of `f`, counted by
order.** The divisibility case of
`IsAddCyclic.card_filter_addOrderOf_eq_sum_totient`. -/]
theorem IsCyclic.card_filter_dvd_orderOf_eq_sum_totient (f : ℕ) :
    #{τ : α | f ∣ orderOf τ} =
      ∑ d ∈ {d ∈ (Fintype.card α).divisors | f ∣ d}, φ d :=
  IsCyclic.card_filter_orderOf_eq_sum_totient (f ∣ ·)

-- Source. The count and the uniform bound are specified by the Chebotarev roadmap,
-- `TauCetiRoadmap/Chebotarev/README.md` §9, which displays them for the cyclic Galois group of a
-- cyclotomic extension as `#{τ ∈ H | f ∣ orderOf τ} = h * ∏_{p ∣ f} (1 - p^{-(v_p h - v_p f + 1)})`
-- and `c_q ≥ (1 - 2^{-r})^{#f.primeFactors} / #G`.

namespace IsCyclic

variable {f : ℕ}

/-- Reindexing the elements of a cyclic group of order `h` by `ZMod h`, through a generator: the
elements of order divisible by `f` correspond to the residues avoiding a prime power at each prime
of `f`. -/
private theorem card_filter_dvd_orderOf_eq_card_zmod [NeZero (Fintype.card α)]
    (hf : f ∣ Fintype.card α) :
    #{τ : α | f ∣ orderOf τ}
      = #{x : ZMod (Fintype.card α) | ∀ p ∈ f.primeFactors,
          ¬p ^ ((Fintype.card α).factorization p - f.factorization p + 1) ∣ x.val} := by
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := α)
  have hg : orderOf g = Fintype.card α := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card]
  have hcrit : ∀ k : ℕ, f ∣ orderOf (g ^ k) ↔ ∀ p ∈ f.primeFactors,
      ¬p ^ ((Fintype.card α).factorization p - f.factorization p + 1) ∣ k := by
    intro k
    have h := (isOfFinOrder_of_finite g).dvd_orderOf_pow_iff (hg ▸ hf) k
    rwa [hg] at h
  refine (Finset.card_bij (fun x _ => g ^ x.val) ?_ ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (hcrit x.val).mpr hx
  · intro x _ y _ hxy
    have hlt : ∀ z : ZMod (Fintype.card α), z.val ∈ Set.Iio (orderOf g) := fun z => by
      rw [hg]; exact z.val_lt
    have : x.val = y.val := pow_injOn_Iio_orderOf (hlt x) (hlt y) hxy
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, this]
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff τ g).mp
      ((isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr (hgen τ))
    refine ⟨(k : ZMod (Fintype.card α)), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine (hcrit _).mp ?_
      rwa [ZMod.val_natCast, ← hg, pow_mod_orderOf, hk]
    · rw [ZMod.val_natCast, ← hg, pow_mod_orderOf, hk]

/-- **The number of elements of a cyclic group whose order is a multiple of `f`.** For `f`
dividing the order `h` of a cyclic group, the elements of order divisible by `f` number
`h * ∏ p ∣ f, (1 - p ^ -(v_p h - v_p f + 1))`, stated here cleared of denominators.

At `f = h` every exponent is `1` and this is Euler's product formula
`Nat.totient_mul_prod_primeFactors`, the elements of order divisible by `h` being the `φ h`
generators. -/
theorem card_filter_dvd_orderOf_mul_prod_primeFactors (hf : f ∣ Fintype.card α) :
    #{τ : α | f ∣ orderOf τ} *
        ∏ p ∈ f.primeFactors,
          p ^ ((Fintype.card α).factorization p - f.factorization p + 1)
      = Fintype.card α *
        ∏ p ∈ f.primeFactors,
          (p ^ ((Fintype.card α).factorization p - f.factorization p + 1) - 1) := by
  -- The three steps are: reindex the group by `ZMod h` through a generator (`hstep1`); reduce
  -- the resulting condition modulo the product of the prime powers it involves (`hstep2`); and
  -- split that product by the Chinese remainder theorem (`hstep3`).
  have : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ,
      ∀ p, e p = (Fintype.card α).factorization p - f.factorization p + 1 := ⟨_, fun _ => rfl⟩
  -- the prime powers `p ^ e p`, indexed by the primes of `f`, are pairwise coprime and their
  -- product divides the order
  set a : ↥f.primeFactors → ℕ := fun i => (i : ℕ) ^ e i with ha
  have hprime : ∀ i : ↥f.primeFactors, (i : ℕ).Prime := fun i => Nat.prime_of_mem_primeFactors i.2
  have hane : ∀ i, NeZero (a i) := fun i => ⟨pow_ne_zero _ (hprime i).ne_zero⟩
  have : NeZero (∏ i, a i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (hane i).ne⟩
  have hcop : Pairwise (Nat.Coprime on a) := fun i j hij =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime i) (hprime j)).mpr
      fun h => hij (Subtype.ext h))
  have hprod : ∏ i, a i = ∏ p ∈ f.primeFactors, p ^ e p := by
    simp only [ha]
    exact Finset.prod_coe_sort f.primeFactors fun p => p ^ e p
  have hdvd : (∏ i, a i) ∣ Fintype.card α := by
    rw [hprod, Finset.prod_congr rfl fun p _ => by rw [he p]]
    exact TauCeti.Nat.prod_pow_sub_factorization_add_one_dvd Fintype.card_ne_zero hf
  have hmem : ∀ p (hp : p ∈ f.primeFactors), p ^ e p ∣ ∏ i, a i := fun p hp =>
    Finset.dvd_prod_of_mem a (Finset.mem_univ (⟨p, hp⟩ : ↥f.primeFactors))
  -- reducing a residue modulo a multiple of `p ^ e p` does not change divisibility by `p ^ e p`
  have hstep2 :
      (∏ i, a i) * #{x : ZMod (Fintype.card α) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val}
        = Fintype.card α * #{y : ZMod (∏ i, a i) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val} := by
    have key := ZMod.mul_card_filter_natCast_val (m := ∏ i, a i) (n := Fintype.card α) hdvd
      (Q := fun y : ZMod (∏ i, a i) => ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val)
    rwa [Finset.filter_congr (q := fun x : ZMod (Fintype.card α) =>
      ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val) fun x _ =>
      forall₂_congr fun p hp => not_congr (by
        rw [ZMod.val_natCast, Nat.dvd_mod_iff (hmem p hp)])] at key
  have hstep3 : #{y : ZMod (∏ i, a i) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val}
      = ∏ p ∈ f.primeFactors, (p ^ e p - 1) := by
    have key := ZMod.card_filter_forall_natCast_val a hcop
      (Q := fun i (z : ZMod (a i)) => ¬a i ∣ z.val)
    rw [Finset.filter_congr (q := fun y : ZMod (∏ i, a i) =>
      ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val) fun y _ => by
        rw [Subtype.forall]
        exact forall₂_congr fun p hp => not_congr (by
          rw [ZMod.val_natCast, Nat.dvd_mod_iff dvd_rfl])] at key
    rw [key, Finset.prod_congr rfl fun i _ => ZMod.card_filter_not_self_dvd_val,
      Finset.prod_coe_sort f.primeFactors fun p => p ^ e p - 1]
  have hstep1 : #{τ : α | f ∣ orderOf τ}
      = #{x : ZMod (Fintype.card α) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val} := by
    have key := card_filter_dvd_orderOf_eq_card_zmod (α := α) (f := f) hf
    rwa [Finset.filter_congr (q := fun x : ZMod (Fintype.card α) =>
      ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val) fun x _ =>
      forall₂_congr fun p _ => not_congr (by rw [he p])] at key
  simp only [← he]
  calc #{τ : α | f ∣ orderOf τ} * ∏ p ∈ f.primeFactors, p ^ e p
      = (∏ i, a i) * #{x : ZMod (Fintype.card α) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val} := by
        rw [hprod, hstep1]; ring
    _ = Fintype.card α * #{y : ZMod (∏ i, a i) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val} := hstep2
    _ = Fintype.card α * ∏ p ∈ f.primeFactors, (p ^ e p - 1) := by rw [hstep3]

/-- **Euler's product formula for the elements of order divisible by `f`.** For `f` dividing the
order `h` of a cyclic group, the elements of order divisible by `f` are a proportion
`∏ p ∣ f, (1 - p ^ -(v_p h - v_p f + 1))` of the group, the product running over the primes of
`f`. -/
theorem card_filter_dvd_orderOf_eq_mul_prod_primeFactors (hf : f ∣ Fintype.card α) :
    (#{τ : α | f ∣ orderOf τ} : ℚ) = Fintype.card α *
      ∏ p ∈ f.primeFactors,
        (1 - ((p : ℚ) ^ ((Fintype.card α).factorization p - f.factorization p + 1))⁻¹) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ,
      ∀ p, e p = (Fintype.card α).factorization p - f.factorization p + 1 := ⟨_, fun _ => rfl⟩
  have hkey := card_filter_dvd_orderOf_mul_prod_primeFactors (α := α) hf
  simp only [← he] at hkey ⊢
  have hne : ∀ p ∈ f.primeFactors, ((p : ℚ) ^ e p) ≠ 0 := fun p hp =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hDne : (∏ p ∈ f.primeFactors, ((p : ℚ) ^ e p)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hsub : ((∏ p ∈ f.primeFactors, (p ^ e p - 1) : ℕ) : ℚ)
      = ∏ p ∈ f.primeFactors, ((p : ℚ) ^ e p - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (Nat.pos_of_mem_primeFactors hp))]
    push_cast
    ring
  have hfactor : ∏ p ∈ f.primeFactors, ((p : ℚ) ^ e p - 1)
      = (∏ p ∈ f.primeFactors, (1 - ((p : ℚ) ^ e p)⁻¹)) *
          ∏ p ∈ f.primeFactors, ((p : ℚ) ^ e p) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp => by
      rw [sub_mul, one_mul, inv_mul_cancel₀ (hne p hp)]
  refine mul_right_cancel₀ hDne ?_
  calc (#{τ : α | f ∣ orderOf τ} : ℚ) * ∏ p ∈ f.primeFactors, ((p : ℚ) ^ e p)
      = ((#{τ : α | f ∣ orderOf τ} * ∏ p ∈ f.primeFactors, p ^ e p : ℕ) : ℚ) := by push_cast; ring
    _ = ((Fintype.card α * ∏ p ∈ f.primeFactors, (p ^ e p - 1) : ℕ) : ℚ) := by rw [hkey]
    _ = (Fintype.card α : ℚ) * ∏ p ∈ f.primeFactors, ((p : ℚ) ^ e p - 1) := by
        rw [Nat.cast_mul, hsub]
    _ = (Fintype.card α : ℚ) * (∏ p ∈ f.primeFactors, (1 - ((p : ℚ) ^ e p)⁻¹)) *
          ∏ p ∈ f.primeFactors, ((p : ℚ) ^ e p) := by rw [hfactor]; ring

/-- **A uniform lower bound for the elements of order divisible by `f`.** If the order of the
cyclic group is divisible by `f ^ r` with `1 ≤ r`, then at least a proportion
`(1 - 2 ^ -r) ^ #f.primeFactors` of its elements have order divisible by `f`.

Each factor of `card_filter_dvd_orderOf_eq_mul_prod_primeFactors` is bounded below by `1 - 2 ^ -r`
because `f ^ r ∣ h` forces the exponent `v_p h - v_p f + 1` to be at least `r` at every prime `p`
of `f`, and `p` is at least `2`. The bound depends on `f` only through its number of prime
factors, so it tends to `1` as `r` grows. -/
theorem le_card_filter_dvd_orderOf {r : ℕ} (hr : 1 ≤ r) (hfr : f ^ r ∣ Fintype.card α) :
    (1 - (2 : ℚ)⁻¹ ^ r) ^ f.primeFactors.card * Fintype.card α
      ≤ #{τ : α | f ∣ orderOf τ} := by
  have hf : f ∣ Fintype.card α := (dvd_pow_self f (by omega)).trans hfr
  have hf0 : f ≠ 0 := fun h0 => Fintype.card_ne_zero (zero_dvd_iff.mp (h0 ▸ hf))
  rw [card_filter_dvd_orderOf_eq_mul_prod_primeFactors hf, mul_comm (Fintype.card α : ℚ)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => ?_) fun p hp => ?_
  · have : (2 : ℚ)⁻¹ ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · -- the exponent at `p` is at least `r`, and `2 ≤ p`
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpos : 0 < f.factorization p :=
      hprime.factorization_pos_of_dvd hf0 (Nat.dvd_of_mem_primeFactors hp)
    have hle : r * f.factorization p ≤ (Fintype.card α).factorization p := by
      have := (Nat.factorization_le_iff_dvd (pow_ne_zero r hf0) Fintype.card_ne_zero).mpr hfr p
      rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at this
    have hre : r ≤ (Fintype.card α).factorization p - f.factorization p + 1 := by
      have h1 : r - 1 ≤ (r - 1) * f.factorization p := Nat.le_mul_of_pos_right _ hpos
      have h2 : (r - 1) * f.factorization p + f.factorization p = r * f.factorization p := by
        cases r with
        | zero => omega
        | succ n => simp [Nat.succ_mul]
      omega
    have h2p : (2 : ℚ) ^ r ≤ (p : ℚ) ^ ((Fintype.card α).factorization p - f.factorization p + 1) :=
      calc (2 : ℚ) ^ r
          ≤ (2 : ℚ) ^ ((Fintype.card α).factorization p - f.factorization p + 1) :=
            pow_le_pow_right₀ (by norm_num) hre
        _ ≤ (p : ℚ) ^ ((Fintype.card α).factorization p - f.factorization p + 1) :=
            pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hprime.two_le) _
    have hinv : ((p : ℚ) ^ ((Fintype.card α).factorization p - f.factorization p + 1))⁻¹
        ≤ (2 : ℚ)⁻¹ ^ r := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) h2p
    linarith

end IsCyclic
