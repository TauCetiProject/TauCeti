/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring

/-!
# Divisor equivalences and sums picking out a shifted index

For `N ≠ 0`, the divisors `d` of `N` with `a = N + d` (respectively `a = N - d`) are at most one,
and such a divisor exists exactly when `a - N` divides `N` (respectively `N - a` divides `a`).
These lemmas evaluate the corresponding indicator sums over `N.divisors`.

`Nat.sum_divisorsAntidiagonal_ite_dvd` regroups a sum over the factor pairs `(a, b)` of `n`,
restricted to `a ∣ m`, as a sum over the divisors of `gcd(m, n)`.
`Nat.sum_divisorsAntidiagonal_filter_lt_sub` rewrites the sum of `f d - f a` over strictly ordered
factor pairs `a < d` of `n` as `∑_{d ∣ n} f d - ∑_{a d = n} f (min a d)`, and
`Nat.add_injOn_divisorsAntidiagonal_le` shows that ordered factor pairs `a ≤ d` of `n` are
determined by their sum `a + d`.

`Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat` and
`Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat` identify the pairs of
`n.toNat.divisorsAntidiagonal`, for an integer `n`, with the factorisations of `n` into two positive
integers; `Int.exists_mem_divisorsAntidiagonal_lt_add_eq_iff` characterises the sums `a + d` of
strictly ordered factor pairs `a < d` of `n ≠ 0` as the nonnegative integers `t` with `4 n < t²` and
`t² - 4 n` a square.

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

/-- Every factor pair `(a, d)` of `n` satisfies `a + d ≤ n + 1`, since `(a - 1) (d - 1) ≥ 0`. -/
theorem add_le_add_one_of_mem_divisorsAntidiagonal {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ n.divisorsAntidiagonal) : p.1 + p.2 ≤ n + 1 := by
  obtain ⟨hmul, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  obtain ⟨h1, h2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  obtain ⟨u, hu⟩ : ∃ u, p.1 = u + 1 := ⟨p.1 - 1, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, p.2 = v + 1 := ⟨p.2 - 1, by omega⟩
  rw [hu, hv] at hmul ⊢
  have huv : u + v + 1 ≤ (u + 1) * (v + 1) := by
    rw [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
    omega
  omega

/-- Ordered factor pairs `a ≤ d` of `n` are determined by their sum `a + d`. -/
theorem add_injOn_divisorsAntidiagonal_le (n : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) {p ∈ n.divisorsAntidiagonal | p.1 ≤ p.2} := by
  rintro ⟨a₁, d₁⟩ ⟨hp₁, hle₁⟩ ⟨a₂, d₂⟩ ⟨hp₂, hle₂⟩ (hsum : a₁ + d₁ = a₂ + d₂)
  dsimp only at hle₁ hle₂
  have hsum' : (a₁ : ℤ) + d₁ = (a₂ : ℤ) + d₂ := by exact_mod_cast hsum
  have hmul' : (a₁ : ℤ) * d₁ = (a₂ : ℤ) * d₂ := by
    exact_mod_cast
      (Nat.mem_divisorsAntidiagonal.mp hp₁).1.trans (Nat.mem_divisorsAntidiagonal.mp hp₂).1.symm
  have hdiff : (((d₁ : ℤ) - a₁) - ((d₂ : ℤ) - a₂)) * (((d₁ : ℤ) - a₁) + ((d₂ : ℤ) - a₂)) = 0 := by
    calc (((d₁ : ℤ) - a₁) - ((d₂ : ℤ) - a₂)) * (((d₁ : ℤ) - a₁) + ((d₂ : ℤ) - a₂))
        = ((a₁ : ℤ) + d₁) ^ 2 - 4 * ((a₁ : ℤ) * d₁) -
            (((a₂ : ℤ) + d₂) ^ 2 - 4 * ((a₂ : ℤ) * d₂)) := by ring
      _ = 0 := by rw [hsum', hmul', sub_self]
  rcases Int.mul_eq_zero.mp hdiff with h | h <;> exact Prod.ext (by omega) (by omega)

/-- Summing `f d - f a` over the strictly ordered factor pairs `a < d` of `n` equals
`∑_{d ∣ n} f d - ∑_{a d = n} f (min a d)`: pairs with `a ≥ d` have `min a d = d` and cancel. -/
theorem sum_divisorsAntidiagonal_filter_lt_sub {G : Type*} [AddCommGroup G] (n : ℕ) (f : ℕ → G) :
    ∑ p ∈ n.divisorsAntidiagonal with p.1 < p.2, (f p.2 - f p.1) =
      (∑ d ∈ n.divisors, f d) - ∑ p ∈ n.divisorsAntidiagonal, f (min p.1 p.2) := by
  rw [Finset.sum_filter, ← Nat.sum_divisorsAntidiagonal' fun _ d ↦ f d, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rcases lt_or_ge p.1 p.2 with h | h
  · rw [ite_eq_left h, min_eq_left h.le]
  · rw [ite_eq_right h.not_gt, min_eq_right h, sub_self]

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

/-- For `N ≠ 0`, an integer `t` is the sum `a + d` of a strictly ordered factor pair `a < d` of `N`
if and only if `0 ≤ t`, `4 N < t²` and `t² - 4 N` is a square: `a` and `d` are `(t ∓ s) / 2` where
`s > 0` satisfies `s² = t² - 4 N`. -/
theorem exists_mem_divisorsAntidiagonal_lt_add_eq_iff {N : ℕ} (hN : N ≠ 0) (t : ℤ) :
    (∃ p ∈ N.divisorsAntidiagonal, p.1 < p.2 ∧ (p.1 : ℤ) + p.2 = t) ↔
      0 ≤ t ∧ 4 * (N : ℤ) < t ^ 2 ∧ IsSquare (t ^ 2 - 4 * (N : ℤ)) := by
  constructor
  · rintro ⟨⟨a, d⟩, hp, had, rfl⟩
    dsimp only at had ⊢
    have hmul : (a : ℤ) * d = N := by exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hsub : 0 < (d : ℤ) - a := by omega
    have hdisc : ((a : ℤ) + d) ^ 2 - 4 * (N : ℤ) = ((d : ℤ) - a) * ((d : ℤ) - a) := by
      rw [← hmul]
      ring
    have hdisc_pos : 0 < ((a : ℤ) + d) ^ 2 - 4 * (N : ℤ) :=
      hdisc ▸ mul_pos hsub hsub
    exact ⟨by omega, by omega, ⟨(d : ℤ) - a, hdisc⟩⟩
  · rintro ⟨ht0, hlt, r, hr⟩
    obtain ⟨s, hs0, hs2⟩ : ∃ s : ℤ, 0 ≤ s ∧ s * s = t ^ 2 - 4 * (N : ℤ) :=
      ⟨if 0 ≤ r then r else -r, by split_ifs <;> omega, by rw [hr]; split_ifs <;> ring⟩
    have hs_pos : 0 < s := by
      rcases hs0.eq_or_lt with rfl | hs_pos
      · omega
      · exact hs_pos
    have hN_pos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hprod : (t - s) * (t + s) = 4 * (N : ℤ) := by
      calc (t - s) * (t + s) = t ^ 2 - s * s := by ring
      _ = 4 * (N : ℤ) := by omega
    have ht_pos : 0 < t := by
      rcases ht0.eq_or_lt with rfl | ht_pos
      · omega
      · exact ht_pos
    have hts_pos : 0 < t - s := by
      by_contra! hle
      have : (t - s) * (t + s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (by omega)
      omega
    have heven : (t - s) % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one (t - s) with h0 | h1
      · exact h0
      · exfalso
        have hmod := congrArg (· % 2) hprod
        have hts_eq : t + s = (t - s) + 2 * s := by ring
        rw [hts_eq, Int.mul_emod, Int.add_mul_emod_self_left, h1] at hmod
        omega
    set a : ℤ := (t - s) / 2
    set d : ℤ := (t + s) / 2
    have ha2 : 2 * a = t - s := Int.mul_ediv_cancel' (Int.dvd_iff_emod_eq_zero.mpr heven)
    have hd2 : 2 * d = t + s := by omega
    have ha_pos : 0 < a := by omega
    have hd_pos : 0 < d := by omega
    have had : a * d = N := by
      have : 4 * (a * d) = 4 * (N : ℤ) := by
        calc 4 * (a * d) = (2 * a) * (2 * d) := by ring
        _ = 4 * (N : ℤ) := by rw [ha2, hd2, hprod]
      omega
    have hmem : (a.toNat, d.toNat) ∈ N.divisorsAntidiagonal := by
      have := prodMk_toNat_mem_divisorsAntidiagonal_toNat ha_pos hd_pos had
      rwa [Int.toNat_natCast] at this
    exact ⟨(a.toNat, d.toNat), hmem, by omega, by omega⟩

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
