/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import TauCeti.NumberTheory.ArithmeticFunction.Misc

/-!
# Vaughan's identity

For a natural cutoff `V`, the *incomplete logarithm* is the arithmetic function
`λ_V(n) = ∑_{d ∣ n, V < d} Λ(d)`, the part of `log n = ∑_{d ∣ n} Λ(d)` coming from the divisors
above `V`. Its Möbius transform is the von Mangoldt function cut off below `V`:
`(μ * λ_V)(n) = Λ(n)` for `n > V`, and `0` for `n ≤ V`. Splitting the Möbius variable at a second
cutoff `U` gives Vaughan's identity

```text
Λ(n) = 1_{n ≤ V} Λ(n) + ∑_{b ∣ n, b ≤ U} μ(b) log(n/b)
         - ∑_{b ∣ n, b ≤ U} μ(b) ∑_{c ∣ n/b, c ≤ V} Λ(c) + ∑_{b ∣ n, U < b} μ(b) λ_V(n/b),
```

an exact identity for all natural `U`, `V` and `n`, with the boundary term `1_{n ≤ V} Λ(n)` kept.

Summed against an arbitrary weight `w`, it decomposes `∑_{n ≤ N} Λ(n) w(n)` into the short sum
`∑_{n ≤ min(N, V)} Λ(n) w(n)`, a sum of `μ(m)` on the small range `m ≤ U` against `λ_V(ℓ)`,
and a bilinear sum of `μ(m)` on `U < m` against `λ_V(ℓ)` on `V < ℓ` (of type II). The small-`m`
sum is not yet of type I: its inner coefficient is still `λ_V(ℓ)`, and it splits into the type I
sums of Vaughan's identity (a `log` sum and a sum over `md ≤ UV`) after rewriting `λ_V` with
`TauCeti.SieveVaughan.incompleteLog_eq_log_sub`, as in `TauCeti.SieveVaughan.vaughan_identity`.
This is the decomposition used to bound exponential sums over primes such as
`∑_{n ≤ N} Λ(n) e(nα)`, where `w(n) = e(nα)`. The coefficient energies
`∑ λ_V(ℓ)² ≤ (M - L) (log M)²` and `∑ μ(m)² ≤ M - L` over `L < m ≤ M` are what the
Cauchy–Schwarz step of the type II bound consumes.

## Main declarations

* `TauCeti.SieveVaughan.incompleteLog`: the incomplete logarithm `λ_V`.
* `TauCeti.SieveVaughan.moebius_mul_incompleteLog_apply`: `(μ * λ_V)(n) = 1_{V < n} Λ(n)`.
* `TauCeti.SieveVaughan.vaughan_identity`: Vaughan's identity with its boundary term.
* `TauCeti.SieveVaughan.sum_Ioc_vonMangoldt_smul_eq_add_sum_sum`: the weighted identity on the
  finite hyperbola `mℓ ≤ N`.
* `TauCeti.SieveVaughan.sum_Ioc_vonMangoldt_smul_eq_typeI_add_typeII`: the finite type I–type II
  decomposition.
* `TauCeti.SieveVaughan.sum_Ioc_incompleteLog_sq_le`: the coefficient energy of `λ_V`; the Möbius
  energy is `ArithmeticFunction.sum_Ioc_moebius_sq_le`.

The weighted hyperbola sum `ArithmeticFunction.sum_Ioc_mul_smul_eq_sum_sum`, the weighted form of
Mathlib's `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum` used here, is in
`TauCeti.NumberTheory.ArithmeticFunction.Misc`.

## References

* R. C. Vaughan, *Sommes trigonométriques sur les nombres premiers*, C. R. Acad. Sci. Paris
  Sér. A 285 (1977), 981–983.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §13.4.
* K. S. Kedlaya, *Notes on analytic number theory*, §18.2.
-/

public section

open Finset

namespace TauCeti.SieveVaughan

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The incomplete logarithm `λ_V(n) = ∑_{d ∣ n, V < d} Λ(d)`: the part of
`log n = ∑_{d ∣ n} Λ(d)` coming from the divisors of `n` above the cutoff `V`. It is a cutoff
divisor sum, not `log (n / V)`, and is not multiplicative. -/
noncomputable def incompleteLog (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ ∑ d ∈ n.divisors with V < d, Λ d, by simp⟩

variable {U V N L M m n ℓ : ℕ}

/-- The defining divisor sum of `λ_V`. -/
theorem incompleteLog_apply : incompleteLog V n = ∑ d ∈ n.divisors with V < d, Λ d :=
  (rfl)

/-- The incomplete logarithm is the logarithm minus the short von Mangoldt divisor sum. -/
theorem incompleteLog_eq_log_sub :
    incompleteLog V n = Real.log n - ∑ d ∈ n.divisors with d ≤ V, Λ d := by
  rw [incompleteLog_apply, ← vonMangoldt_sum,
    ← sum_filter_add_sum_filter_not n.divisors (fun d ↦ V < d)]
  simp only [not_lt]
  ring

/-- At cutoff `0` the incomplete logarithm is the full logarithm. -/
@[simp]
theorem incompleteLog_zero : incompleteLog 0 = log := by
  ext n
  rw [incompleteLog_eq_log_sub, log_apply, sub_eq_self]
  exact sum_eq_zero fun d hd ↦ by
    simp only [mem_filter, Nat.le_zero] at hd
    simp [hd.2]

/-- `λ_V(n) = 0` for `n ≤ V`: every divisor of `n` is at most `V`. -/
theorem incompleteLog_eq_zero_of_le (h : n ≤ V) : incompleteLog V n = 0 := by
  rw [incompleteLog_apply, sum_filter]
  exact sum_eq_zero fun d hd ↦ ite_eq_right (Nat.not_lt.2 ((Nat.divisor_le hd).trans h))

/-- The incomplete logarithm vanishes at and below its cutoff. -/
theorem lt_of_incompleteLog_ne_zero (h : incompleteLog V n ≠ 0) : V < n :=
  Nat.lt_of_not_le fun h' ↦ h (incompleteLog_eq_zero_of_le h')

@[simp]
theorem incompleteLog_nonneg : 0 ≤ incompleteLog V n := by
  rw [incompleteLog_apply]
  exact sum_nonneg fun _ _ ↦ vonMangoldt_nonneg

/-- `λ_V(n) ≤ log n`: the short divisor sum removed from `log n` is nonnegative. -/
theorem incompleteLog_le_log : incompleteLog V n ≤ Real.log n := by
  rw [incompleteLog_eq_log_sub]
  exact sub_le_self _ (sum_nonneg fun _ _ ↦ vonMangoldt_nonneg)

/-- Möbius inversion of the incomplete logarithm: `(μ * λ_V)(n)` is `Λ(n)` above the cutoff and
`0` at and below it. -/
theorem moebius_mul_incompleteLog_apply :
    ((μ : ArithmeticFunction ℝ) * incompleteLog V) n = if V < n then Λ n else 0 := by
  let h : ArithmeticFunction ℝ := ⟨fun n ↦ if V < n then Λ n else 0, by simp⟩
  have hh : incompleteLog V = h * ζ := by
    ext n
    rw [coe_mul_zeta_apply, incompleteLog_apply, sum_filter]
    simp only [h, coe_mk]
  rw [hh, mul_left_comm, coe_moebius_mul_coe_zeta, mul_one]
  simp only [h, coe_mk]

/-- `Λ(n)` is its boundary term `1_{n ≤ V} Λ(n)` plus `(μ * λ_V)(n)`. -/
theorem vonMangoldt_eq_add_moebius_mul_incompleteLog :
    Λ n = (if n ≤ V then Λ n else 0) + ((μ : ArithmeticFunction ℝ) * incompleteLog V) n := by
  rw [moebius_mul_incompleteLog_apply]
  by_cases h : n ≤ V
  · simp [h, Nat.not_lt.2 h]
  · simp [h, Nat.lt_of_not_le h]

/-- **Vaughan's identity**, with its boundary term `1_{n ≤ V} Λ(n)`:
`Λ(n) = 1_{n ≤ V} Λ(n) + ∑_{b ∣ n, b ≤ U} μ(b) log(n/b)
  - ∑_{b ∣ n, b ≤ U} μ(b) ∑_{c ∣ n/b, c ≤ V} Λ(c) + ∑_{b ∣ n, U < b} μ(b) ∑_{c ∣ n/b, V < c} Λ(c)`
for all natural `U`, `V` and `n`. -/
theorem vaughan_identity (U V n : ℕ) :
    Λ n = (if n ≤ V then Λ n else 0) +
      (∑ b ∈ n.divisors with b ≤ U, (μ b : ℝ) * Real.log (n / b : ℕ)) -
      (∑ b ∈ n.divisors with b ≤ U,
        (μ b : ℝ) * ∑ c ∈ (n / b).divisors with c ≤ V, Λ c) +
      (∑ b ∈ n.divisors with U < b,
        (μ b : ℝ) * ∑ c ∈ (n / b).divisors with V < c, Λ c) := by
  have hlow : ∑ b ∈ n.divisors with b ≤ U, (μ b : ℝ) * incompleteLog V (n / b) =
      (∑ b ∈ n.divisors with b ≤ U, (μ b : ℝ) * Real.log (n / b : ℕ)) -
        ∑ b ∈ n.divisors with b ≤ U, (μ b : ℝ) * ∑ c ∈ (n / b).divisors with c ≤ V, Λ c := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun b _ ↦ by rw [incompleteLog_eq_log_sub, mul_sub]
  conv_lhs =>
    rw [vonMangoldt_eq_add_moebius_mul_incompleteLog (V := V), ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun b c ↦ (μ : ArithmeticFunction ℝ) b * incompleteLog V c),
      ← sum_filter_add_sum_filter_not n.divisors (fun b ↦ b ≤ U)]
  simp only [intCoe_apply, not_le]
  rw [hlow]
  simp only [incompleteLog_apply]
  ring

/-- If `λ_V(ℓ) ≠ 0` and `mℓ ≤ N`, then `m ≤ N / (V + 1)`: the bilinear Vaughan term lives on
`m ≤ ⌊N / (V + 1)⌋`. -/
theorem le_div_of_incompleteLog_ne_zero (h : incompleteLog V ℓ ≠ 0) (hmℓ : m * ℓ ≤ N) :
    m ≤ N / (V + 1) :=
  (Nat.le_div_iff_mul_le V.succ_pos).2 <|
    (Nat.mul_le_mul_left m (lt_of_incompleteLog_ne_zero h)).trans hmℓ

section Weighted

variable {A : Type*} [AddCommMonoid A] [Module ℝ A]

/-- The weighted Vaughan identity on the finite hyperbola: for an arbitrary weight `w`,
`∑_{0 < n ≤ N} Λ(n) w(n) = ∑_{0 < n ≤ min(N, V)} Λ(n) w(n)
  + ∑_{0 < m ≤ N} μ(m) ∑_{0 < ℓ ≤ N/m} λ_V(ℓ) w(mℓ)`. -/
theorem sum_Ioc_vonMangoldt_smul_eq_add_sum_sum (V N : ℕ) (w : ℕ → A) :
    ∑ n ∈ Ioc 0 N, Λ n • w n =
      ∑ n ∈ Ioc 0 (min N V), Λ n • w n +
        ∑ m ∈ Ioc 0 N, (μ m : ℝ) • ∑ ℓ ∈ Ioc 0 (N / m), incompleteLog V ℓ • w (m * ℓ) := by
  have hfilter : {n ∈ Ioc 0 N | n ≤ V} = Ioc 0 (min N V) := by
    ext n
    simp only [mem_filter, mem_Ioc, le_min_iff]
    tauto
  have hsplit (n : ℕ) : Λ n • w n = (if n ≤ V then Λ n • w n else 0) +
      ((μ : ArithmeticFunction ℝ) * incompleteLog V) n • w n := by
    conv_lhs => rw [vonMangoldt_eq_add_moebius_mul_incompleteLog (V := V)]
    rw [add_smul, ite_smul, zero_smul]
  rw [sum_congr rfl fun n _ ↦ hsplit n, sum_add_distrib, ← sum_filter, hfilter,
    ArithmeticFunction.sum_Ioc_mul_smul_eq_sum_sum]
  simp only [intCoe_apply]

/-- **The finite type I–type II Vaughan decomposition.** With `B = ⌊N / (V + 1)⌋` and an
arbitrary weight `w`,
`∑_{0 < n ≤ N} Λ(n) w(n) = ∑_{0 < n ≤ min(N, V)} Λ(n) w(n)
  + ∑_{0 < m ≤ min(U, B)} μ(m) ∑_{V < ℓ ≤ N/m} λ_V(ℓ) w(mℓ)
  + ∑_{U < m ≤ B} μ(m) ∑_{V < ℓ ≤ N/m} λ_V(ℓ) w(mℓ)`.
The second sum has a small Möbius variable `m ≤ U`; its inner coefficient is still `λ_V(ℓ)`, and
it becomes the type I sums of Vaughan's identity only after rewriting `λ_V` with
`incompleteLog_eq_log_sub`, as in `vaughan_identity`. The third sum has both variables above their
cutoffs (type II). In both, the inner range still depends on `m`. -/
theorem sum_Ioc_vonMangoldt_smul_eq_typeI_add_typeII (U V N : ℕ) (w : ℕ → A) :
    ∑ n ∈ Ioc 0 N, Λ n • w n =
      ∑ n ∈ Ioc 0 (min N V), Λ n • w n +
        ∑ m ∈ Ioc 0 (min U (N / (V + 1))),
          (μ m : ℝ) • ∑ ℓ ∈ Ioc V (N / m), incompleteLog V ℓ • w (m * ℓ) +
        ∑ m ∈ Ioc U (N / (V + 1)),
          (μ m : ℝ) • ∑ ℓ ∈ Ioc V (N / m), incompleteLog V ℓ • w (m * ℓ) := by
  set B := N / (V + 1)
  -- The terms with `ℓ ≤ V` vanish, so the inner sums start above `V`.
  have hinner (m : ℕ) : ∑ ℓ ∈ Ioc 0 (N / m), incompleteLog V ℓ • w (m * ℓ) =
      ∑ ℓ ∈ Ioc V (N / m), incompleteLog V ℓ • w (m * ℓ) := by
    refine (sum_subset (Ioc_subset_Ioc_left V.zero_le) fun ℓ hℓ hℓ' ↦ ?_).symm
    simp only [mem_Ioc, not_and] at hℓ hℓ'
    rw [incompleteLog_eq_zero_of_le (Nat.le_of_not_lt fun h ↦ hℓ' h hℓ.2), zero_smul]
  -- The terms with `m > B` vanish, by the support of the bilinear term.
  have houter : ∑ m ∈ Ioc 0 N, (μ m : ℝ) • ∑ ℓ ∈ Ioc V (N / m), incompleteLog V ℓ • w (m * ℓ) =
      ∑ m ∈ Ioc 0 B, (μ m : ℝ) • ∑ ℓ ∈ Ioc V (N / m), incompleteLog V ℓ • w (m * ℓ) := by
    refine (sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self N _)) fun m hm hm' ↦ ?_).symm
    simp only [mem_Ioc, not_and, not_le] at hm hm'
    refine smul_eq_zero_of_right _ (sum_eq_zero fun ℓ hℓ ↦ ?_)
    by_cases h : incompleteLog V ℓ = 0
    · rw [h, zero_smul]
    · have hmℓ : m * ℓ ≤ N :=
        mul_comm m ℓ ▸ (Nat.le_div_iff_mul_le hm.1).1 (mem_Ioc.1 hℓ).2
      exact absurd (le_div_of_incompleteLog_ne_zero h hmℓ) (hm' hm.1).not_ge
  rw [sum_Ioc_vonMangoldt_smul_eq_add_sum_sum V, add_assoc]
  simp only [hinner]
  rw [houter, ← sum_Ioc_consecutive _ (Nat.zero_le (min U B)) (min_le_right U B)]
  rcases le_total U B with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Ioc_self, Ioc_eq_empty_of_le h, sum_empty]

end Weighted

/-- The incomplete-logarithm coefficient energy: `∑_{L < ℓ ≤ M} λ_V(ℓ)² ≤ (M - L) (log M)²`. -/
theorem sum_Ioc_incompleteLog_sq_le (V L M : ℕ) :
    ∑ ℓ ∈ Ioc L M, incompleteLog V ℓ ^ 2 ≤ ((M - L : ℕ) : ℝ) * Real.log M ^ 2 := by
  rw [← Nat.card_Ioc, ← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun ℓ hℓ ↦ ?_
  rw [mem_Ioc] at hℓ
  refine pow_le_pow_left₀ incompleteLog_nonneg (incompleteLog_le_log.trans ?_) 2
  exact Real.log_le_log (Nat.cast_pos.2 (hℓ.1.trans_le' L.zero_le)) (Nat.cast_le.2 hℓ.2)

/-! The cutoff is strict, and every prime-power divisor above it is kept. -/

example : incompleteLog 4 4 = 0 := incompleteLog_eq_zero_of_le le_rfl

example : incompleteLog 2 4 = Real.log 2 := by
  rw [incompleteLog_apply, show (4 : ℕ).divisors.filter (2 < ·) = {4} by decide, sum_singleton,
    show (4 : ℕ) = 2 ^ 2 by rfl, vonMangoldt_apply_pow two_ne_zero,
    vonMangoldt_apply_prime Nat.prime_two]
  norm_num

example : incompleteLog 2 12 = Real.log 2 + Real.log 3 := by
  rw [incompleteLog_apply, show (12 : ℕ).divisors.filter (2 < ·) = {3, 4, 6, 12} by decide,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton,
    vonMangoldt_apply_prime Nat.prime_three, show (4 : ℕ) = 2 ^ 2 by rfl,
    vonMangoldt_apply_pow two_ne_zero, vonMangoldt_apply_prime Nat.prime_two,
    vonMangoldt_eq_zero_iff.2 (by decide), vonMangoldt_eq_zero_iff.2 (by decide)]
  push_cast
  ring

end TauCeti.SieveVaughan
