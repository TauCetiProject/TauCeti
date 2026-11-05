/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Divisor equivalences, factor pairs, and shifted-index sums

For `N ≠ 0`, the divisors `d` of `N` with `a = N + d` (respectively `a = N - d`) are at most one,
and such a divisor exists exactly when `a - N` divides `N` (respectively `N - a` divides `a`).
These lemmas evaluate the corresponding indicator sums over `N.divisors`.

`Nat.sum_divisorsAntidiagonal_ite_dvd` regroups a sum over the factor pairs `(a, b)` of `n`,
restricted to `a ∣ m`, as a sum over the divisors of `gcd(m, n)`.

`Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat` and
`Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat` identify the pairs of
`n.toNat.divisorsAntidiagonal`, for an integer `n`, with the factorisations of `n` into two positive
integers.

`Nat.sum_divisorsAntidiagonal_filter_sub` evaluates differences over the factor pairs with
strictly increasing factors. `Nat.injOn_add_divisorsAntidiagonal_filter_lt` and
`Int.isSquare_sq_sub_four_mul_iff_exists_mem_divisorsAntidiagonal` identify those factor pairs
by their sum and by a positive square discriminant.

`TauCeti.nontrivialDivisorEquiv` identifies divisors greater than one with the subtype of
`N.divisors` omitting the unit divisor.
-/

public section

namespace Nat

variable {M : Type*} [AddCommMonoid M]

/-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N + d`. -/
theorem sum_divisors_ite_eq_add {N : ℕ} (hN : N ≠ 0) (a : ℕ) (f : ℕ → M) :
    ∑ d ∈ N.divisors, (if a = N + d then f d else 0) =
      if N < a ∧ a - N ∣ N then f (a - N) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (a - N)]
    · rw [ite_eq_left (by omega)]
    · intro d _ hd
      rw [ite_eq_right (by omega)]
    · intro h'
      exact absurd (Nat.mem_divisors.mpr ⟨h.2, hN⟩) h'
  · refine Finset.sum_eq_zero fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      omega
    · have had : a - N = d := by omega
      rw [had]
      exact Nat.dvd_of_mem_divisors hd

/-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N - d`. -/
theorem sum_divisors_ite_eq_sub {N : ℕ} (hN : N ≠ 0) (a : ℕ) (f : ℕ → M) :
    ∑ d ∈ N.divisors, (if a = N - d then f d else 0) =
      if a < N ∧ N - a ∣ a then f (N - a) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (N - a)]
    · rw [ite_eq_left (by omega)]
    · intro d hd hne
      have := Nat.divisor_le hd
      rw [ite_eq_right (by omega)]
    · refine fun h' ↦ absurd (Nat.mem_divisors.mpr ⟨?_, hN⟩) h'
      have h'' := Nat.dvd_add_self_right.mpr h.2
      rwa [Nat.add_sub_cancel' h.1.le] at h''
  · refine Finset.sum_eq_zero fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      have := Nat.divisor_le hd
      omega
    · have := Nat.divisor_le hd
      have had : N - a = d := by omega
      have hN' : N = a + d := by omega
      rw [had]
      have h' := Nat.dvd_of_mem_divisors hd
      rwa [hN', Nat.dvd_add_self_right] at h'

/-- Regrouping a sum over the factor pairs `(a, b)` of `n ≠ 0`, restricted to `a ∣ m`, by the
divisors `d` of `gcd(m, n)`: the pair `(d, n / d)` contributes `f d (m * n / d ^ 2)`, since
`(n / d) * (m / d) = m * n / d ^ 2`. -/
theorem sum_divisorsAntidiagonal_ite_dvd {n : ℕ} (hn : n ≠ 0) (m : ℕ) (f : ℕ → ℕ → M) :
    ∑ p ∈ n.divisorsAntidiagonal, (if p.1 ∣ m then f p.1 (p.2 * (m / p.1)) else 0) =
      ∑ d ∈ (m.gcd n).divisors, f d (m * n / d ^ 2) := by
  rw [Nat.sum_divisorsAntidiagonal fun a b ↦ if a ∣ m then f a (b * (m / a)) else 0,
    ← Finset.sum_filter]
  have hs : {a ∈ n.divisors | a ∣ m} = (m.gcd n).divisors := by
    ext a
    simp [Nat.dvd_gcd_iff, hn, Nat.gcd_eq_zero_iff, and_comm]
  rw [hs]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha' := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors ha)
  rw [Nat.div_mul_div_comm ha'.2 ha'.1, ← sq, mul_comm n m]

/-- On the factor pairs with increasing factors, subtracting the value at the smaller factor
from that at the larger factor is the full divisor sum minus the sum at the minimum factor. -/
theorem sum_divisorsAntidiagonal_filter_sub {A : Type*} [AddCommGroup A]
    (n : ℕ) (f : ℕ → A) :
    (∑ p ∈ n.divisorsAntidiagonal with p.1 < p.2, (f p.2 - f p.1)) =
      (∑ d ∈ n.divisors, f d) - ∑ p ∈ n.divisorsAntidiagonal, f (min p.1 p.2) := by
  classical
  rw [← sum_divisorsAntidiagonal' (fun _ d ↦ f d), ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
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

/-- The factors of a pair in `n.toNat.divisorsAntidiagonal` are positive integers with product
`n`. -/
theorem pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat {p : ℕ × ℕ}
    (hp : p ∈ n.toNat.divisorsAntidiagonal) :
    0 < (p.1 : ℤ) ∧ 0 < (p.2 : ℤ) ∧ (p.1 : ℤ) * p.2 = n := by
  obtain ⟨h, h0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  obtain ⟨h1, h2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  refine ⟨by omega, by omega, ?_⟩
  rw [← Nat.cast_mul, h]
  omega

/-- A factorisation `n = u v` into positive integers is the pair `(u.toNat, v.toNat)` of
`n.toNat.divisorsAntidiagonal`. -/
theorem prodMk_toNat_mem_divisorsAntidiagonal_toNat {u v : ℤ} (hu : 0 < u) (hv : 0 < v)
    (h : u * v = n) : (u.toNat, v.toNat) ∈ n.toNat.divisorsAntidiagonal := by
  have hn : 0 < n := h ▸ mul_pos hu hv
  have h' : ((u.toNat * v.toNat : ℕ) : ℤ) = (n.toNat : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le, Int.toNat_of_nonneg hn.le, h]
  exact Nat.mem_divisorsAntidiagonal.mpr ⟨by exact_mod_cast h', by omega⟩

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

end TauCeti
