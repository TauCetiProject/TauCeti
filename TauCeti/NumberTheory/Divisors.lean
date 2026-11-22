/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.PNat.Defs
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Divisor equivalences, factor pairs, and shifted-index sums

For `N ≠ 0`, the divisors `d` of `N` with `a = N + d` (respectively `a = N - d`) are at most one,
and such a divisor exists exactly when `a - N` divides `N` (respectively `N - a` divides `a`).
These lemmas evaluate the corresponding indicator products (and sums) over `N.divisors`.

The products over divisors in this file are stated for commutative monoids (commutative groups
for quotients), and each lemma `Nat.prod_…` or `TauCeti.prod_…` has an additive form `Nat.sum_…`
or `TauCeti.sum_…`.

`Nat.prod_divisors_filter_dvd` reindexes divisors divisible by a fixed `m ∣ n` as `m` times
the divisors of `n / m`.

`Nat.prod_divisorsAntidiagonal_ite_dvd` regroups a product over the factor pairs `(a, b)` of `n`,
restricted to `a ∣ m`, as a product over the divisors of `gcd(m, n)`.

`Int.mem_divisorsAntidiagonal_toNat` and `Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat`
identify the pairs of `n.toNat.divisorsAntidiagonal`, for an integer `n`, with the factorisations
of `n` into two positive integers.

`Nat.prod_divisorsAntidiagonal_filter_div` evaluates quotients over the factor pairs with
strictly increasing factors. `Nat.injOn_add_divisorsAntidiagonal_filter_lt` and
`Int.isSquare_sq_sub_four_mul_iff_exists_mem_divisorsAntidiagonal` identify those factor pairs
by their sum and by a positive square discriminant.

`Nat.prod_Ioc_prod_divisors` (and its additive form `Nat.sum_Ioc_sum_divisors`) regroups a
product over the divisors of `1, …, N` by divisor: `d` occurs `N / d` times.

For radical `P`, `Nat.pairwiseDisjoint_divisors_pow_filter_dvd` states that the families of
divisors of `d ^ M` divisible by `d` are pairwise disjoint as `d` ranges over the divisors of `P`.

`TauCeti.nontrivialDivisorEquiv` identifies divisors greater than one with the subtype of
`N.divisors` omitting the unit divisor. `TauCeti.pnatDvdEquivDivisors`,
`TauCeti.pnatMulDvdEquivSigma`, and `TauCeti.pnatMulDvdAndEquivSigma` identify positive divisors
`{M : ℕ+ // (M : ℕ) ∣ N}` with `N.divisors` and positive divisor pairs
`{p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}` (and its filtered subtypes) with sigma types over
`(N / M).divisors`, providing `Fintype` instances on these subtypes and collapsing sums that
depend only on `M` to `#(N / M).divisors`-weighted divisor sums
(`TauCeti.sum_pnatMulDvd_eq_sum_card_divisors_smul`,
`TauCeti.sum_pnatMulDvdAnd_eq_sum_dite_card_divisors_smul`, and the product forms
`TauCeti.prod_pnatMulDvd_eq_prod_pow_card_divisors`,
`TauCeti.prod_pnatMulDvdAnd_eq_prod_dite_pow_card_divisors`).
-/

public section

namespace Nat

variable {M : Type*} [CommMonoid M]

/-- The divisors of `n` divisible by `m ∣ n` are `m` times the divisors of `n / m`,
so a product over those divisors can be reindexed by division by `m`. -/
@[to_additive /-- The divisors of `n` divisible by `m ∣ n` are `m` times the divisors of
`n / m`, so a sum over those divisors can be reindexed by division by `m`. -/]
theorem prod_divisors_filter_dvd {m n : ℕ} (h : m ∣ n) (f : ℕ → M) :
    (∏ d ∈ n.divisors with m ∣ d, f d) = ∏ d ∈ (n / m).divisors, f (m * d) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  obtain ⟨k, rfl⟩ := h
  have hm : 0 < m := Nat.pos_of_ne_zero (left_ne_zero_of_mul hn)
  rw [Nat.mul_div_cancel_left k hm]
  -- Multiplication and division by `m` are inverse bijections between the two index sets.
  refine (Finset.prod_nbij' (m * ·) (· / m) (fun d hd ↦ ?_) (fun d hd ↦ ?_) (fun d _ ↦ ?_)
    (fun d hd ↦ ?_) fun _ _ ↦ rfl).symm
  · simp only [Finset.mem_filter, mem_divisors] at hd ⊢
    exact ⟨⟨Nat.mul_dvd_mul_left m hd.1, hn⟩, dvd_mul_right m d⟩
  · simp only [Finset.mem_filter, mem_divisors] at hd ⊢
    obtain ⟨⟨hdk, -⟩, e, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left e hm]
    exact ⟨Nat.dvd_of_mul_dvd_mul_left hm hdk, right_ne_zero_of_mul hn⟩
  · exact Nat.mul_div_cancel_left d hm
  · exact Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2

/-- The product over the divisors `d` of `N` of `f d` restricted to `a = N + d`. -/
@[to_additive /-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N + d`. -/]
theorem prod_divisors_ite_eq_add {N : ℕ} (hN : N ≠ 0) (a : ℕ) (f : ℕ → M) :
    ∏ d ∈ N.divisors, (if a = N + d then f d else 1) =
      if N < a ∧ a - N ∣ N then f (a - N) else 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single (a - N)]
    · rw [ite_eq_left (by omega)]
    · intro d _ hd
      rw [ite_eq_right (by omega)]
    · intro h'
      exact absurd (Nat.mem_divisors.mpr ⟨h.2, hN⟩) h'
  · refine Finset.prod_eq_one fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      omega
    · have had : a - N = d := by omega
      rw [had]
      exact Nat.dvd_of_mem_divisors hd

/-- The product over the divisors `d` of `N` of `f d` restricted to `a = N - d`. -/
@[to_additive /-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N - d`. -/]
theorem prod_divisors_ite_eq_sub {N : ℕ} (a : ℕ) (f : ℕ → M) :
    ∏ d ∈ N.divisors, (if a = N - d then f d else 1) =
      if a < N ∧ N - a ∣ a then f (N - a) else 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single (N - a)]
    · rw [ite_eq_left (by omega)]
    · intro d hd hne
      have := Nat.divisor_le hd
      rw [ite_eq_right (by omega)]
    · refine fun h' ↦ absurd (Nat.mem_divisors.mpr ⟨?_, by omega⟩) h'
      have h'' := Nat.dvd_add_self_right.mpr h.2
      rwa [Nat.add_sub_cancel' h.1.le] at h''
  · refine Finset.prod_eq_one fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      have := Nat.divisor_le hd
      omega
    · have := Nat.divisor_le hd
      have had : N - a = d := by omega
      have hN' : N = a + d := by omega
      rw [had]
      have h' := Nat.dvd_of_mem_divisors hd
      rwa [hN', Nat.dvd_add_self_right] at h'

/-- Regrouping a product over the factor pairs `(a, b)` of `n ≠ 0`, restricted to `a ∣ m`, by
the divisors `d` of `gcd(m, n)`: the pair `(d, n / d)` contributes `f d (m * n / d ^ 2)`, since
`(n / d) * (m / d) = m * n / d ^ 2`. -/
@[to_additive /-- Regrouping a sum over the factor pairs `(a, b)` of `n ≠ 0`, restricted to
`a ∣ m`, by the divisors `d` of `gcd(m, n)`: the pair `(d, n / d)` contributes
`f d (m * n / d ^ 2)`, since `(n / d) * (m / d) = m * n / d ^ 2`. -/]
theorem prod_divisorsAntidiagonal_ite_dvd {n : ℕ} (hn : n ≠ 0) (m : ℕ) (f : ℕ → ℕ → M) :
    ∏ p ∈ n.divisorsAntidiagonal, (if p.1 ∣ m then f p.1 (p.2 * (m / p.1)) else 1) =
      ∏ d ∈ (m.gcd n).divisors, f d (m * n / d ^ 2) := by
  rw [Nat.prod_divisorsAntidiagonal fun a b ↦ if a ∣ m then f a (b * (m / a)) else 1,
    ← Finset.prod_filter]
  have hs : {a ∈ n.divisors | a ∣ m} = (m.gcd n).divisors := by
    ext a
    simp [Nat.dvd_gcd_iff, hn, Nat.gcd_eq_zero_iff, and_comm]
  rw [hs]
  refine Finset.prod_congr rfl fun a ha ↦ ?_
  have ha' := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors ha)
  rw [Nat.div_mul_div_comm ha'.2 ha'.1, ← sq, mul_comm n m]

/-- On the factor pairs with increasing factors, dividing the value at the larger factor by that
at the smaller factor gives the full divisor product divided by the product at the minimum
factor. -/
@[to_additive /-- On the factor pairs with increasing factors, subtracting the value at the
smaller factor from that at the larger factor is the full divisor sum minus the sum at the
minimum factor. -/]
theorem prod_divisorsAntidiagonal_filter_div {G : Type*} [CommGroup G] (n : ℕ) (f : ℕ → G) :
    (∏ p ∈ n.divisorsAntidiagonal with p.1 < p.2, (f p.2 / f p.1)) =
      (∏ d ∈ n.divisors, f d) / ∏ p ∈ n.divisorsAntidiagonal, f (min p.1 p.2) := by
  rw [← prod_divisorsAntidiagonal' (fun _ d ↦ f d), ← Finset.prod_div_distrib,
    Finset.prod_filter]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  by_cases h : p.1 < p.2
  · simp [h, min_eq_left h.le]
  · simp [h, min_eq_right (by omega : p.2 ≤ p.1)]

/-- A factor pair with strictly increasing factors is determined by its sum. -/
theorem injOn_add_divisorsAntidiagonal_filter_lt (n : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2)
      ↑(n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)) := by
  intro p hp q hq hsum
  obtain ⟨hp, hplt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqlt⟩ := Finset.mem_filter.mp hq
  dsimp only at hsum
  have hmul : (p.1 : ℤ) * p.2 = (q.1 : ℤ) * q.2 := by
    exact_mod_cast (mem_divisorsAntidiagonal.mp hp).1.trans
      (mem_divisorsAntidiagonal.mp hq).1.symm
  have hprod : ((p.1 : ℤ) - q.1) * ((p.1 : ℤ) - q.2) = 0 := by nlinarith
  rcases _root_.mul_eq_zero.mp hprod with h | h
  · exact Prod.ext (by omega) (by omega)
  · omega

end Nat

namespace Int

variable {n : ℤ}

/-- The pairs of `n.toNat.divisorsAntidiagonal` are exactly the pairs of positive integers with
product `n`. -/
theorem mem_divisorsAntidiagonal_toNat {p : ℕ × ℕ} :
    p ∈ n.toNat.divisorsAntidiagonal ↔ 0 < (p.1 : ℤ) ∧ 0 < (p.2 : ℤ) ∧ (p.1 : ℤ) * p.2 = n := by
  rw [Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨h, h0⟩
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp (h ▸ h0)
    refine ⟨by omega, by omega, ?_⟩
    rw [← Nat.cast_mul, h]
    omega
  · rintro ⟨h1, h2, h⟩
    have hn : 0 < n := h ▸ mul_pos h1 h2
    refine ⟨?_, by omega⟩
    exact_mod_cast h.trans (Int.toNat_of_nonneg hn.le).symm

/-- A factorisation `n = u v` into positive integers is the pair `(u.toNat, v.toNat)` of
`n.toNat.divisorsAntidiagonal`. -/
theorem prodMk_toNat_mem_divisorsAntidiagonal_toNat {u v : ℤ} (hu : 0 < u) (hv : 0 < v)
    (h : u * v = n) : (u.toNat, v.toNat) ∈ n.toNat.divisorsAntidiagonal := by
  rw [mem_divisorsAntidiagonal_toNat, Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le]
  exact ⟨hu, hv, h⟩

/-- At positive discriminant and determinant, a square discriminant is equivalent to a
positive factorisation with increasing factors and sum equal to the absolute trace. -/
theorem isSquare_sq_sub_four_mul_iff_exists_mem_divisorsAntidiagonal
    (n : ℕ) (hn : 0 < n) (t : ℤ) (hD : 4 * (n : ℤ) < t ^ 2) :
    IsSquare (t ^ 2 - 4 * (n : ℤ)) ↔
      ∃ p ∈ n.divisorsAntidiagonal, p.1 < p.2 ∧ |t| = (p.1 : ℤ) + p.2 := by
  constructor
  · rintro ⟨u, hu⟩
    have hu' : t ^ 2 - 4 * (n : ℤ) = |u| ^ 2 := by nlinarith [sq_abs u]
    -- The trace and the square root have the same parity, so both roots are integral.
    have hpar : (|t| - |u|) % 2 = 0 := by
      have he : Even (|t| ^ 2 - |u| ^ 2) := ⟨2 * n, by nlinarith [sq_abs t]⟩
      have heq : Even |t| ↔ Even |u| := by
        simpa only [Int.even_pow' (by decide : (2 : ℕ) ≠ 0)] using Int.even_sub.mp he
      exact Int.even_iff.mp (Int.even_sub.mpr heq)
    let a := (|t| - |u|) / 2
    let d := (|t| + |u|) / 2
    have hprod : (|t| - |u|) * (|t| + |u|) = 4 * n := by nlinarith [sq_abs t]
    have htu : |u| < |t| := by nlinarith [abs_nonneg t, abs_nonneg u, sq_abs t]
    have hu0 : 0 < |u| := by nlinarith [abs_nonneg u]
    have ha : 0 < a := by dsimp [a]; omega
    have had : a < d := by dsimp [a, d]; omega
    have hadd : a + d = |t| := by dsimp [a, d]; omega
    have hmul : a * d = n := by
      have ha2 : 2 * a = |t| - |u| := by dsimp [a]; omega
      have hd2 : 2 * d = |t| + |u| := by dsimp [d]; omega
      nlinarith [hd2]
    refine ⟨(a.toNat, d.toNat), ?_, by omega, by omega⟩
    simpa only [Int.toNat_natCast] using
      prodMk_toNat_mem_divisorsAntidiagonal_toNat ha (by omega) hmul
  · rintro ⟨p, hp, _, ht⟩
    have hm : (p.1 : ℤ) * p.2 = n := by exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
    refine ⟨(p.2 : ℤ) - p.1, ?_⟩
    nlinarith [sq_abs t]

end Int

namespace TauCeti

open Finset

variable {N : ℕ} [NeZero N]

/-- Divisors greater than one correspond to positive divisors other than the unit divisor. -/
def nontrivialDivisorEquiv :
    {d : ℕ // 1 < d ∧ d ∣ N} ≃
      {d : N.divisors // d ≠ ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne N)⟩} where
  toFun d := ⟨⟨d.val, Nat.mem_divisors.mpr ⟨d.property.2, NeZero.ne N⟩⟩,
    fun h ↦ by have := congrArg Subtype.val h; simp at this; omega⟩
  invFun d := ⟨d.val.val, by
    have hdpos := Nat.pos_of_mem_divisors d.val.property
    have hdne : d.val.val ≠ 1 := fun h ↦ d.property (Subtype.ext h)
    exact ⟨by omega, Nat.dvd_of_mem_divisors d.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The divisor equivalence preserves the underlying natural number. -/
@[simp]
theorem nontrivialDivisorEquiv_apply_val (d : {d : ℕ // 1 < d ∧ d ∣ N}) :
    (nontrivialDivisorEquiv d).val.val = d.val := by rfl

/-- The inverse divisor equivalence preserves the underlying natural number. -/
@[simp]
theorem nontrivialDivisorEquiv_symm_apply_val
    (d : {d : N.divisors // d ≠ ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne N)⟩}) :
    (nontrivialDivisorEquiv.symm d).val = d.val.val := by rfl

/-- For `N ≠ 0`, positive integers dividing `N` correspond to `N.divisors`. -/
def pnatDvdEquivDivisors (N : ℕ) [NeZero N] : {M : ℕ+ // (M : ℕ) ∣ N} ≃ N.divisors where
  toFun M := ⟨M.val, Nat.mem_divisors.mpr ⟨M.property, NeZero.ne N⟩⟩
  invFun M := ⟨⟨M.val, Nat.pos_of_mem_divisors M.property⟩, Nat.dvd_of_mem_divisors M.property⟩
  left_inv _ := Subtype.ext (PNat.eq rfl)
  right_inv _ := Subtype.ext rfl

/-- `pnatDvdEquivDivisors` preserves the underlying natural number. -/
@[simp]
theorem coe_pnatDvdEquivDivisors_apply (M : {M : ℕ+ // (M : ℕ) ∣ N}) :
    ((pnatDvdEquivDivisors N M : N.divisors) : ℕ) = M.val :=
  (rfl)

/-- `(pnatDvdEquivDivisors N).symm` preserves the underlying natural number. -/
@[simp]
theorem coe_pnatDvdEquivDivisors_symm_apply (M : N.divisors) :
    (((pnatDvdEquivDivisors N).symm M).val : ℕ) = M :=
  (rfl)

/-- For `N ≠ 0`, the subtype of positive divisors of `N` is finite. -/
instance instFintypePNatDvd (N : ℕ) [NeZero N] : Fintype {M : ℕ+ // (M : ℕ) ∣ N} :=
  Fintype.ofEquiv N.divisors (pnatDvdEquivDivisors N).symm

/-- For `N ≠ 0`, pairs `(M, d)` of positive integers with `d * M ∣ N` correspond to a positive
divisor `M` of `N` together with a divisor `d` of `N / M`. -/
def pnatMulDvdEquivSigma (N : ℕ) [NeZero N] :
    {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N} ≃
      Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, (N / M.val).divisors where
  toFun p :=
    have hMN : (p.val.1 : ℕ) ∣ N := dvd_of_mul_left_dvd p.property
    ⟨⟨p.val.1, hMN⟩, ⟨p.val.2, Nat.mem_divisors.mpr
      ⟨(Nat.dvd_div_iff_mul_dvd hMN).mpr (mul_comm (p.val.2 : ℕ) p.val.1 ▸ p.property),
        Nat.div_ne_zero_iff.mpr ⟨p.val.1.ne_zero, Nat.le_of_dvd (NeZero.pos N) hMN⟩⟩⟩⟩
  invFun x := ⟨(x.1.val, ⟨x.2.val, Nat.pos_of_mem_divisors x.2.property⟩),
    mul_comm (x.1.val : ℕ) x.2.val ▸
      (Nat.dvd_div_iff_mul_dvd x.1.property).mp (Nat.dvd_of_mem_divisors x.2.property)⟩
  left_inv _ := Subtype.ext (Prod.ext rfl (PNat.eq rfl))
  right_inv x := by obtain ⟨_, ⟨_, _⟩⟩ := x; rfl

/-- The first component of `pnatMulDvdEquivSigma` preserves the positive divisor `M`. -/
@[simp]
theorem fst_val_pnatMulDvdEquivSigma_apply (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}) :
    (pnatMulDvdEquivSigma N p).1.val = p.val.1 :=
  (rfl)

/-- The second component of `pnatMulDvdEquivSigma` preserves the underlying natural number `d`. -/
@[simp]
theorem coe_snd_pnatMulDvdEquivSigma_apply (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}) :
    ((pnatMulDvdEquivSigma N p).2 : ℕ) = p.val.2 :=
  (rfl)

/-- The first factor of `(pnatMulDvdEquivSigma N).symm` is `x.1.1`. -/
@[simp]
theorem fst_val_pnatMulDvdEquivSigma_symm_apply
    (x : Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, (N / M.val).divisors) :
    ((pnatMulDvdEquivSigma N).symm x).val.1 = x.1.val :=
  (rfl)

/-- The second factor of `(pnatMulDvdEquivSigma N).symm` has underlying natural number `x.2`. -/
@[simp]
theorem coe_snd_val_pnatMulDvdEquivSigma_symm_apply
    (x : Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, (N / M.val).divisors) :
    (((pnatMulDvdEquivSigma N).symm x).val.2 : ℕ) = x.2 :=
  (rfl)

/-- For `N ≠ 0`, the subtype of positive divisor pairs `(M, d)` with `d * M ∣ N` is finite. -/
instance instFintypePNatMulDvd (N : ℕ) [NeZero N] :
    Fintype {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N} :=
  Fintype.ofEquiv _ (pnatMulDvdEquivSigma N).symm

/-- Multiplying a function of `M` over positive integer pairs `(M, d)` with `d * M ∣ N` raises
the factor at each positive divisor `M ∣ N` to the power `#(N / M).divisors`. -/
@[to_additive sum_pnatMulDvd_eq_sum_card_divisors_smul /-- Summing a function of `M` over
positive integer pairs `(M, d)` with `d * M ∣ N` weights each positive divisor `M ∣ N` by
`#(N / M).divisors`. -/]
theorem prod_pnatMulDvd_eq_prod_pow_card_divisors {A : Type*} [CommMonoid A] (F : ℕ+ → A) :
    (∏ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, F p.val.1) =
      ∏ M : {M : ℕ+ // (M : ℕ) ∣ N}, F M.val ^ #(N / M.val).divisors := by
  rw [← (pnatMulDvdEquivSigma N).symm.prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun M _ ↦ ?_
  exact (Finset.prod_congr rfl fun d _ ↦
    congrArg F (fst_val_pnatMulDvdEquivSigma_symm_apply ⟨M, d⟩)).trans (by simp)

/-- For `N ≠ 0` and a decidable predicate `P`, the subtype of positive divisor pairs `(M, d)` with
`d * M ∣ N` and `P (M, d)` is finite. -/
instance instFintypePNatMulDvdAnd (N : ℕ) [NeZero N] (P : ℕ+ × ℕ+ → Prop) [DecidablePred P] :
    Fintype {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ P p} :=
  Fintype.ofEquiv {p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N} // P p.val}
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun p : ℕ+ × ℕ+ ↦ (p.2 : ℕ) * p.1 ∣ N) P)

/-- For `N ≠ 0` and `P : ℕ+ → Prop`, pairs `(M, d)` of positive integers with `d * M ∣ N` and
`P M` correspond to a positive divisor `M` of `N` satisfying `P M` together with a divisor `d` of
`N / M`. -/
def pnatMulDvdAndEquivSigma (N : ℕ) [NeZero N] (P : ℕ+ → Prop) :
    {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ P p.1} ≃
      Σ M : {M : {M : ℕ+ // (M : ℕ) ∣ N} // P M.val}, (N / M.val.val).divisors :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun p : ℕ+ × ℕ+ ↦ (p.2 : ℕ) * p.1 ∣ N) (fun p ↦ P p.1)).symm.trans <|
    ((pnatMulDvdEquivSigma N).subtypeEquiv (q := fun x ↦ P x.1.val) fun _ ↦ by simp).trans <|
      Equiv.subtypeSigmaEquiv (fun M : {M : ℕ+ // (M : ℕ) ∣ N} ↦ ↥(N / M.val).divisors)
        (fun M ↦ P M.val)

/-- `pnatMulDvdAndEquivSigma` preserves the positive divisor `M`. -/
@[simp]
theorem fst_val_pnatMulDvdAndEquivSigma_apply {P : ℕ+ → Prop}
    (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ P p.1}) :
    (pnatMulDvdAndEquivSigma N P p).1.val.val = p.val.1 :=
  (rfl)

/-- The second component of `pnatMulDvdAndEquivSigma` preserves the underlying natural number
`d`. -/
@[simp]
theorem coe_snd_pnatMulDvdAndEquivSigma_apply {P : ℕ+ → Prop}
    (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ P p.1}) :
    ((pnatMulDvdAndEquivSigma N P p).2 : ℕ) = p.val.2 :=
  (rfl)

/-- The first factor of `(pnatMulDvdAndEquivSigma N P).symm` is `x.1.1.1`. -/
@[simp]
theorem fst_val_pnatMulDvdAndEquivSigma_symm_apply {P : ℕ+ → Prop}
    (x : Σ M : {M : {M : ℕ+ // (M : ℕ) ∣ N} // P M.val}, (N / M.val.val).divisors) :
    ((pnatMulDvdAndEquivSigma N P).symm x).val.1 = x.1.val.val :=
  (rfl)

/-- The second factor of `(pnatMulDvdAndEquivSigma N P).symm` has underlying natural number
`x.2`. -/
@[simp]
theorem coe_snd_val_pnatMulDvdAndEquivSigma_symm_apply {P : ℕ+ → Prop}
    (x : Σ M : {M : {M : ℕ+ // (M : ℕ) ∣ N} // P M.val}, (N / M.val.val).divisors) :
    (((pnatMulDvdAndEquivSigma N P).symm x).val.2 : ℕ) = x.2 :=
  (rfl)

/-- Multiplying a function of `(M, hM)` over positive integer pairs `(M, d)` with `d * M ∣ N` and
`P M` gives the `dite` product over positive divisors `M ∣ N` of the factors raised to the power
`#(N / M).divisors`. -/
@[to_additive sum_pnatMulDvdAnd_eq_sum_dite_card_divisors_smul /-- Summing a function of
`(M, hM)` over positive integer pairs `(M, d)` with `d * M ∣ N` and `P M` gives the `dite` sum over
positive divisors `M ∣ N` weighted by `#(N / M).divisors`. -/]
theorem prod_pnatMulDvdAnd_eq_prod_dite_pow_card_divisors {A : Type*} [CommMonoid A]
    (P : ℕ+ → Prop) [DecidablePred P] (F : ∀ M : ℕ+, P M → A) :
    (∏ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ P p.1}, F p.val.1 p.property.2) =
      ∏ M : {M : ℕ+ // (M : ℕ) ∣ N},
        if h : P M.val then F M.val h ^ #(N / M.val).divisors else 1 := by
  -- Extend `F` by `1` off `P`, so that the unrestricted product formula applies.
  have hG := prod_pnatMulDvd_eq_prod_pow_card_divisors (N := N)
    fun M ↦ if h : P M then F M h else 1
  rw [Finset.prod_dite, Finset.prod_const_one, mul_one] at hG
  refine Eq.trans ?_ (hG.trans (Finset.prod_congr rfl fun M _ ↦ ?_))
  · -- Reindex the conjunction subtype as the subtype of the filtered universe; these
    -- equivalences keep the underlying pair, so corresponding factors agree by `rfl`.
    exact Fintype.prod_equiv ((Equiv.subtypeSubtypeEquivSubtypeInter _
      fun p : ℕ+ × ℕ+ ↦ P p.1).symm.trans (Equiv.subtypeEquivRight fun _ ↦ by simp)) _ _
        fun _ ↦ rfl
  · split_ifs <;> simp

end TauCeti

namespace Nat

open Finset

/-- For radical `P`, the divisors of `d ^ M` divisible by `d` are disjoint as `d` ranges
through the divisors of `P`. This is the prime-support partition used by the Selberg sieve. -/
theorem pairwiseDisjoint_divisors_pow_filter_dvd {P : ℕ} (hP : IsRadical P) (M : ℕ) :
    (P.divisors : Set ℕ).PairwiseDisjoint
      (fun d ↦ (d ^ M).divisors.filter (d ∣ ·)) := by
  intro i hi j hj hij
  have hPsq := IsRadical.squarefree (Nat.ne_zero_of_mem_divisors hi) hP
  apply Finset.disjoint_left.mpr
  intro m hmi hmj
  obtain ⟨hmi, him⟩ := mem_filter.mp hmi
  obtain ⟨hmj, hjm⟩ := mem_filter.mp hmj
  have hij' : i ∣ j := (hPsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hi)).isRadical
    M j (him.trans (Nat.dvd_of_mem_divisors hmj))
  have hji' : j ∣ i := (hPsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hj)).isRadical
    M i (hjm.trans (Nat.dvd_of_mem_divisors hmi))
  exact hij (Nat.dvd_antisymm hij' hji')

/-- Regrouping a product over the divisors of `1, …, N` by divisor: each `d ≤ N` divides exactly
`N / d` of the integers `1, …, N`, so it contributes `f d ^ (N / d)`. -/
@[to_additive /-- Regrouping a sum over the divisors of `1, …, N` by divisor: each `d ≤ N`
divides exactly `N / d` of the integers `1, …, N`, so it contributes `(N / d) • f d`. -/]
theorem prod_Ioc_prod_divisors {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∏ i ∈ Ioc 0 N, ∏ d ∈ i.divisors, f d = ∏ d ∈ Ioc 0 N, f d ^ (N / d) := by
  rw [prod_comm' (t' := Ioc 0 N) (s' := fun d ↦ {i ∈ Ioc 0 N | d ∣ i})]
  · simp [Nat.Ioc_filter_dvd_card_eq_div]
  · intro i d
    simp only [mem_Ioc, mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨hi, hiN⟩, hdi, -⟩
      exact ⟨⟨⟨hi, hiN⟩, hdi⟩, Nat.pos_of_dvd_of_pos hdi hi, (Nat.le_of_dvd hi hdi).trans hiN⟩
    · rintro ⟨⟨⟨hi, hiN⟩, hdi⟩, -⟩
      exact ⟨⟨hi, hiN⟩, hdi, hi.ne'⟩

end Nat
