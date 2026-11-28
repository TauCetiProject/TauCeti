/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist

/-!
# The remainders `R_q` of the one-sided prime sum bound

Let `d` be a prime, `χ_K = (· / d)` its Legendre symbol and `q` a natural number. This file
defines

* the weight `λ_q(n) = Λ(n) (1 - χ_K(n))` if `n ≡ 1 (mod q)` and `λ_q(n) = 0` otherwise
  (`primeWeight d q`);
* the product `ψ χ_K`, a Dirichlet character modulo `q d` (`quadraticTwist d ψ`);
* the mean of logarithmic derivatives
  `G_q(s) = φ(q)⁻¹ (Σ_ψ (E'_{ψχ_K} / E_{ψχ_K}(s) - E'_ψ / E_ψ(s)) - 1)`, the sum over all
  Dirichlet characters modulo `q`, where `E_ψ = DirichletCharacter.entireLFunction ψ` is `L(s, ψ)`
  if `ψ` is not principal and the entire continuation of `(s - 1) L(s, ψ)` if it is
  (`logDerivMean d q`);
* the remainder `R_q(y) = Σ_{1 ≤ n ≤ y} λ_q(n) (1/n - 1/y) - (log y) / φ(q) - c_q` with
  `c_q = Re G_q(1)` (`primeRemainder d q`),

and proves the elementary facts about them: `0 ≤ λ_q(n) ≤ 2 Λ(n)`; the positive-part identity
`Σ_{n=1}^{A} λ_q(n) (A/n - A/z)₊ = A (R_q(z) + (log z) / φ(q) + c_q)` for `0 < z` and an
integer `A ≥ ⌊z⌋`; and the Lipschitz-type bound `|R_q(z) - R_q(y)| ≤ 13 (z - y) / y` for
`0 < y ≤ z`. The value of `c_q` is not used: it cancels in each of these statements.

The remainder `R_q(y)` compares the smoothed sum of `λ_q` up to `y` with its expected size
`(log y) / φ(q) + c_q`. A one-sided bound for the zeros of Dirichlet `L`-functions is a bound on
`R_q(y)` from one side for all large `y`: the positive-part identity writes such sums at an
integer length `A`, and the Lipschitz-type bound passes from a real `y` to nearby real points.

## Main definitions

* `TauCeti.OneSidedBound.primeWeight`, `TauCeti.OneSidedBound.quadraticTwist`,
  `TauCeti.OneSidedBound.logDerivMean`, `TauCeti.OneSidedBound.primeRemainder`.

## Main results

* `TauCeti.OneSidedBound.primeWeight_nonneg`,
  `TauCeti.OneSidedBound.primeWeight_le_two_mul_vonMangoldt`: `0 ≤ λ_q(n) ≤ 2 Λ(n)`.
* `TauCeti.OneSidedBound.sum_primeWeight_le`: `Σ_{n ≤ z} λ_q(n) ≤ 2 (log 4 + 4) z`.
* `TauCeti.OneSidedBound.sum_primeWeight_mul_max_eq`: the positive-part identity.
* `TauCeti.OneSidedBound.abs_primeRemainder_sub_le`: `|R_q(z) - R_q(y)| ≤ 13 (z - y) / y`.

## References

* The definitions and statements follow the formal proof in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207:
  `New.lambdaKResidueClass`, `New.logDerivMean`, `New.primeRemainder`,
  `New.lambdaKResidueClass_le_two_mul_vonMangoldt`, `New.primeRemainder_eq_sum` and
  `New.abs_primeRemainder_sub_le`.
-/

public section

namespace TauCeti.OneSidedBound

open ArithmeticFunction

section Remainder

variable (d : ℕ) [Fact d.Prime] (q : ℕ)

/-- The weight `λ_q(n) = Λ(n) (1 - χ_K(n))` if `n ≡ 1 (mod q)` and `0` otherwise, with
`χ_K = (· / d)` the Legendre symbol of the prime `d`. -/
noncomputable def primeWeight (n : ℕ) : ℝ :=
  if (n : ZMod q) = 1 then Λ n * (1 - (legendreSym d n : ℝ)) else 0

/-- The definition of `primeWeight`. -/
theorem primeWeight_def (n : ℕ) :
    primeWeight d q n = if (n : ZMod q) = 1 then Λ n * (1 - (legendreSym d n : ℝ)) else 0 :=
  (rfl)

/-- The product `ψ χ_K` of a Dirichlet character `ψ` modulo `q` and the quadratic character
`χ_K = (· / d)`, a Dirichlet character modulo `q d`. The second factor is Mathlib's quadratic
character of `ZMod d` with values cast to `ℂ`, which is `TauCeti.jacobiChar ℂ d` by
`TauCeti.jacobiChar_eq_ringHomComp_quadraticChar`. -/
noncomputable def quadraticTwist {q : ℕ} (ψ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (q * d) :=
  DirichletCharacter.changeLevel (Dvd.intro d rfl) ψ *
    DirichletCharacter.changeLevel (Dvd.intro_left q rfl)
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))

/-- The definition of `quadraticTwist`. -/
theorem quadraticTwist_def {q : ℕ} (ψ : DirichletCharacter ℂ q) :
    quadraticTwist d ψ = DirichletCharacter.changeLevel (Dvd.intro d rfl) ψ *
      DirichletCharacter.changeLevel (Dvd.intro_left q rfl)
        ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) :=
  (rfl)

/-- The value of `ψ χ_K` at a unit `a` modulo `q d`: the product of `ψ` and `χ_K` at the
reductions of `a` modulo `q` and modulo `d`. -/
@[simp]
theorem quadraticTwist_apply {q : ℕ} (ψ : DirichletCharacter ℂ q) (a : (ZMod (q * d))ˣ) :
    quadraticTwist d ψ a =
      ψ (ZMod.cast (a : ZMod (q * d))) * quadraticChar (ZMod d) (ZMod.cast (a : ZMod (q * d))) := by
  simp [quadraticTwist_def, DirichletCharacter.changeLevel_eq_cast_of_dvd]

/-- The quadratic twist at level `q * d` is the Legendre twist by `d`. -/
theorem quadraticTwist_eq_legendreTwist {q : ℕ} (ψ : DirichletCharacter ℂ q) :
    quadraticTwist d ψ = ψ.legendreTwist d := by
  refine MulChar.ext fun a ↦ ?_
  rw [quadraticTwist_apply, ← ZMod.intCast_zmod_cast (a : ZMod (q * d)),
    DirichletCharacter.legendreTwist_apply]
  simp [legendreSym]

variable [NeZero q]

/-- The mean of logarithmic derivatives
`G_q(s) = φ(q)⁻¹ (Σ_ψ (E'_{ψχ_K} / E_{ψχ_K}(s) - E'_ψ / E_ψ(s)) - 1)`, the sum over all
Dirichlet characters `ψ` modulo `q`. -/
noncomputable def logDerivMean (s : ℂ) : ℂ :=
  (∑ ψ : DirichletCharacter ℂ q,
    (logDeriv (quadraticTwist d ψ).entireLFunction s - logDeriv ψ.entireLFunction s) - 1) /
      (Nat.totient q : ℂ)

/-- The definition of `logDerivMean`. -/
theorem logDerivMean_def (s : ℂ) :
    logDerivMean d q s =
      (∑ ψ : DirichletCharacter ℂ q,
        (logDeriv (quadraticTwist d ψ).entireLFunction s -
          logDeriv ψ.entireLFunction s) - 1) / (Nat.totient q : ℂ) :=
  (rfl)

/-- The remainder `R_q(y) = Σ_{1 ≤ n ≤ y} λ_q(n) (1/n - 1/y) - (log y) / φ(q) - c_q`, with
`c_q = Re G_q(1)` the real part of `logDerivMean d q 1`. -/
noncomputable def primeRemainder (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / (n : ℝ) - 1 / y) -
    Real.log y / (Nat.totient q : ℝ) - (logDerivMean d q 1).re

/-- The definition of `primeRemainder`. -/
theorem primeRemainder_def (y : ℝ) :
    primeRemainder d q y =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / (n : ℝ) - 1 / y) -
        Real.log y / (Nat.totient q : ℝ) - (logDerivMean d q 1).re :=
  (rfl)

end Remainder

section Bounds

variable (d : ℕ) [Fact d.Prime] (q : ℕ)

/-- The weight `λ_q` is nonnegative. -/
theorem primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight d q n := by
  rw [primeWeight_def]
  split_ifs
  · refine mul_nonneg vonMangoldt_nonneg (sub_nonneg.2 ?_)
    -- the Legendre symbol takes the values `0`, `1` and `-1`
    rcases quadraticChar_isQuadratic (ZMod d) (n : ZMod d) with h | h | h <;>
      norm_num [legendreSym, h]
  · exact le_rfl

/-- The weight `λ_q` is at most twice the von Mangoldt function. -/
theorem primeWeight_le_two_mul_vonMangoldt (n : ℕ) : primeWeight d q n ≤ 2 * Λ n := by
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  rw [primeWeight_def]
  split_ifs
  · rw [mul_comm 2]
    refine mul_le_mul_of_nonneg_left ?_ hΛ
    -- the Legendre symbol takes the values `0`, `1` and `-1`
    rcases quadraticChar_isQuadratic (ZMod d) (n : ZMod d) with h | h | h <;>
      norm_num [legendreSym, h]
  · linarith

/-- Chebyshev's bound for the weight: `Σ_{1 ≤ n ≤ z} λ_q(n) ≤ 2 (log 4 + 4) z` for `z ≥ 0`,
from `λ_q ≤ 2 Λ` and `Chebyshev.psi_le_const_mul_self`. -/
theorem sum_primeWeight_le {z : ℝ} (hz : 0 ≤ z) :
    ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, primeWeight d q n ≤ 2 * (Real.log 4 + 4) * z := by
  have hψ : ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, Λ n = Chebyshev.psi z := by
    rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  calc ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, primeWeight d q n
      ≤ ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, 2 * Λ n :=
        Finset.sum_le_sum fun n _ ↦ primeWeight_le_two_mul_vonMangoldt d q n
    _ = 2 * Chebyshev.psi z := by rw [← Finset.mul_sum, hψ]
    _ ≤ 2 * (Real.log 4 + 4) * z := by
        linarith [Chebyshev.psi_le_const_mul_self hz]

/-- For `0 < y` and `⌊y⌋ ≤ N`, a sum against `(1/n - 1/y)₊` over `1 ≤ n ≤ N` is the sum
against `1/n - 1/y` over `1 ≤ n ≤ y`. -/
private lemma sum_mul_max_eq (f : ℕ → ℝ) {y : ℝ} (hy : 0 < y) {N : ℕ} (hN : ⌊y⌋₊ ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, f n * max (1 / (n : ℝ) - 1 / y) 0 =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n * (1 / (n : ℝ) - 1 / y) := by
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hN) ?_]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.1 hn
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn₁
    rw [max_eq_left (sub_nonneg.2 (one_div_le_one_div_of_le hn₀
      ((Nat.le_floor_iff hy.le).1 hn₂)))]
  · intro n hn hn'
    have hyn : y < n := (Nat.floor_lt hy.le).1 <|
      Nat.lt_of_not_le fun h ↦ hn' (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn).1, h⟩)
    rw [max_eq_right (sub_nonpos.2 (one_div_le_one_div_of_le hy hyn.le)), mul_zero]

/-- **The positive-part identity.** For `0 < z` and a natural number `A ≥ ⌊z⌋` (in particular
for `0 < z ≤ A`), `Σ_{n=1}^{A} λ_q(n) (A/n - A/z)₊ = A (R_q(z) + (log z) / φ(q) + c_q)`. -/
theorem sum_primeWeight_mul_max_eq [NeZero q] {z : ℝ} (hz : 0 < z) {A : ℕ} (hA : ⌊z⌋₊ ≤ A) :
    ∑ n ∈ Finset.Icc 1 A, primeWeight d q n * max ((A : ℝ) / n - A / z) 0 =
      A * (primeRemainder d q z + Real.log z / (Nat.totient q : ℝ) +
        (logDerivMean d q 1).re) := by
  have hA₀ : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have h : ∀ n : ℕ, primeWeight d q n * max ((A : ℝ) / n - A / z) 0 =
      A * (primeWeight d q n * max (1 / (n : ℝ) - 1 / z) 0) := fun n ↦ by
    have hA' : (A : ℝ) / n - A / z = A * (1 / n - 1 / z) := by ring
    have hmax : max ((A : ℝ) * (1 / n - 1 / z)) 0 = A * max (1 / (n : ℝ) - 1 / z) 0 := by
      rw [mul_max_of_nonneg _ _ hA₀, mul_zero]
    rw [hA', hmax]
    ring
  simp only [h]
  rw [← Finset.mul_sum, sum_mul_max_eq _ hz hA, primeRemainder_def]
  ring

/-- The smoothed sums at `y ≤ z` differ by at most `(1/y - 1/z) Σ_{n ≤ z} f(n)` for `f ≥ 0`. -/
private lemma sum_sub_sum_mem_Icc (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {y z : ℝ} (hy : 0 < y)
    (hyz : y ≤ z) :
    0 ≤ ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, f n * (1 / (n : ℝ) - 1 / z) -
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n * (1 / (n : ℝ) - 1 / y) ∧
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, f n * (1 / (n : ℝ) - 1 / z) -
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n * (1 / (n : ℝ) - 1 / y) ≤
      (∑ n ∈ Finset.Icc 1 ⌊z⌋₊, f n) * (1 / y - 1 / z) := by
  rw [← sum_mul_max_eq f hy (Nat.floor_le_floor hyz), ← sum_mul_max_eq f (hy.trans_le hyz) le_rfl,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  have hyz' : 1 / z ≤ 1 / y := one_div_le_one_div_of_le hy hyz
  constructor
  · refine Finset.sum_nonneg fun n _ ↦ ?_
    rw [← mul_sub]
    exact mul_nonneg (hf n) (sub_nonneg.2 (max_le_max (by linarith) le_rfl))
  · refine Finset.sum_le_sum fun n _ ↦ ?_
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hf n)
    rw [sub_le_iff_le_add]
    exact max_le (by linarith [le_max_left (1 / (n : ℝ) - 1 / y) 0])
      (by linarith [le_max_right (1 / (n : ℝ) - 1 / y) 0])

/-- **The Lipschitz-type bound** `|R_q(z) - R_q(y)| ≤ 13 (z - y) / y` for `0 < y ≤ z`. -/
theorem abs_primeRemainder_sub_le [NeZero q] {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    |primeRemainder d q z - primeRemainder d q y| ≤ 13 * (z - y) / y := by
  -- No integrals: with `t = (z - y) / y`, the smoothed sums differ by a quantity in
  -- `[0, (1/y - 1/z) Σ_{n ≤ z} λ_q(n)] ⊆ [0, 2 (log 4 + 4) t]` (`sum_sub_sum_mem_Icc` and
  -- Chebyshev's bound), the logarithmic terms by `log (z / y) / φ(q) ∈ [0, t]`, and `c_q` cancels.
  have hz : 0 < z := hy.trans_le hyz
  obtain ⟨h₀, h₁⟩ := sum_sub_sum_mem_Icc _ (primeWeight_nonneg d q) hy hyz
  have hS := sum_primeWeight_le d q hz.le
  have ht : (1 / y - 1 / z) * z = (z - y) / y := by field_simp
  have hD : (∑ n ∈ Finset.Icc 1 ⌊z⌋₊, primeWeight d q n) * (1 / y - 1 / z) ≤
      2 * (Real.log 4 + 4) * ((z - y) / y) :=
    calc _ ≤ 2 * (Real.log 4 + 4) * z * (1 / y - 1 / z) :=
          mul_le_mul_of_nonneg_right hS (sub_nonneg.2 (one_div_le_one_div_of_le hy hyz))
      _ = 2 * (Real.log 4 + 4) * ((z - y) / y) := by rw [← ht]; ring
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hlog : Real.log z - Real.log y ≤ (z - y) / y := by
    have hzy : z / y - 1 = (z - y) / y := by field_simp
    rw [← Real.log_div hz.ne' hy.ne', ← hzy]
    exact Real.log_le_sub_one_of_pos (div_pos hz hy)
  have hlog₀ : 0 ≤ Real.log z - Real.log y := sub_nonneg.2 (Real.log_le_log hy hyz)
  have hL := div_le_self hlog₀ hφ
  have hL₀ := div_nonneg hlog₀ (zero_le_one.trans hφ)
  have h4 : Real.log 4 ≤ 2 := by
    have h2 := Real.log_le_sub_one_of_pos (two_pos (α := ℝ))
    have h22 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h22, Real.log_pow]
    push_cast
    linarith
  have h4t := mul_le_mul_of_nonneg_right h4 (div_nonneg (sub_nonneg.2 hyz) hy.le)
  have hLsub : Real.log z / Nat.totient q - Real.log y / Nat.totient q =
      (Real.log z - Real.log y) / Nat.totient q := by ring
  rw [primeRemainder_def, primeRemainder_def, mul_div_assoc, abs_le]
  constructor <;> linarith

end Bounds

end TauCeti.OneSidedBound
