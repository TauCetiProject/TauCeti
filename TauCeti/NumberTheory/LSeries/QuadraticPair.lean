/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.ZetaMul
public import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction

/-!
# Nonnegative coefficients for a pair of quadratic characters

For quadratic characters `χ` and `ψ`, possibly of different levels, the product
`ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` has nonnegative real Dirichlet coefficients.
The product character is kept at the least common multiple of the levels, not replaced by
its primitive character: thus no Euler factors at primes dividing either level are discarded.
No primitivity, nontriviality, or distinctness assumption is needed.

The local argument pairs `ζ * χ` with its twist by `ψ`. If `χ(p) = -1`, the first factor
vanishes at odd powers of `p`, and twisting its even-power coefficients preserves positivity.
Interchange the characters when `ψ(p) = -1`. In the remaining cases all four local character
values are nonnegative. Multiplicativity then gives positivity at every integer.

This is the coefficient positivity used in the two-character argument for Siegel's theorem;
no uniform lower bound or zero-free estimate is asserted here.

## References

* H. Davenport, *Multiplicative Number Theory*, chapter on Siegel's theorem.
-/

public section

open ArithmeticFunction
open scoped ComplexOrder

namespace DirichletCharacter

variable {M N : ℕ}

/-- The Dirichlet coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)`, with the product
character at the least common multiple of the two levels. -/
noncomputable def quadraticPairCoeffs (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  (χ.zetaMul * toArithmeticFunction (ψ ·)) * toArithmeticFunction (χ.mul ψ ·)

/-- The four Dirichlet-convolution factors defining `quadraticPairCoeffs`. -/
theorem quadraticPairCoeffs_def (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) :
    χ.quadraticPairCoeffs ψ =
      (χ.zetaMul * toArithmeticFunction (ψ ·)) * toArithmeticFunction (χ.mul ψ ·) := (rfl)

/-- Pairing the first two factors with their character twist gives the four-factor product. -/
theorem quadraticPairCoeffs_eq_zetaMul_mul_pmul (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) :
    χ.quadraticPairCoeffs ψ = χ.zetaMul * (toArithmeticFunction (ψ ·)).pmul χ.zetaMul := by
  rw [quadraticPairCoeffs, zetaMul, toArithmeticFunction_pmul_mul,
    ArithmeticFunction.pmul_zeta, toArithmeticFunction_mul,
    ArithmeticFunction.pmul_comm (toArithmeticFunction (ψ ·)), mul_assoc]

/-- The four-factor coefficient function is symmetric in the characters. -/
theorem quadraticPairCoeffs_comm (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) :
    χ.quadraticPairCoeffs ψ = ψ.quadraticPairCoeffs χ := by
  simp only [quadraticPairCoeffs, zetaMul, toArithmeticFunction_mul]
  rw [ArithmeticFunction.pmul_comm (toArithmeticFunction (χ ·))]
  ring

/-- The coefficients of the four-factor product are multiplicative. -/
@[arith_mult] theorem isMultiplicative_quadraticPairCoeffs (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : (χ.quadraticPairCoeffs ψ).IsMultiplicative :=
  (χ.isMultiplicative_zetaMul.mul ψ.isMultiplicative_toArithmeticFunction).mul
    (χ.mul ψ).isMultiplicative_toArithmeticFunction

/-- The coefficient at `1` of the four-factor product is `1`. -/
@[simp] theorem quadraticPairCoeffs_one (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : χ.quadraticPairCoeffs ψ 1 = 1 :=
  (χ.isMultiplicative_quadraticPairCoeffs ψ).map_one

private theorem twist_zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hψ : ψ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hχ : χ p = -1) (k : ℕ) :
    0 ≤ (toArithmeticFunction (ψ ·)).pmul χ.zetaMul (p ^ k) := by
  rw [ArithmeticFunction.pmul_apply, zetaMul_prime_pow_of_eq_neg_one hp hχ]
  split_ifs with hk
  · rw [mul_one, ← ψ.apply_eq_toArithmeticFunction_apply (pow_ne_zero _ hp.ne_zero),
      Nat.cast_pow, map_pow]
    rcases hψ p with h | h | h
    · simp [h, pow_nonneg]
    · simp [h]
    · simp [h, hk.neg_one_pow]
  · simp

private theorem quadraticPairCoeffs_prime_pow_nonneg_of_eq_neg_one
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hχp : χ p = -1) (k : ℕ) : 0 ≤ χ.quadraticPairCoeffs ψ (p ^ k) := by
  rw [quadraticPairCoeffs_eq_zetaMul_mul_pmul, mul_apply]
  refine Finset.sum_nonneg fun d hd ↦ ?_
  have hdn := (Nat.mem_divisorsAntidiagonal.mp hd).1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (show d.1 ∣ p ^ k from ⟨d.2, hdn.symm⟩)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp
    (show d.2 ∣ p ^ k from ⟨d.1, hdn.symm.trans (mul_comm _ _)⟩)
  rw [hi, hj]
  exact mul_nonneg (zetaMul_prime_pow_nonneg (MulChar.isQuadratic_iff_sq_eq_one.mp hχ) hp i)
    (twist_zetaMul_prime_pow_nonneg hψ hp hχp j)

/-- At every prime, including primes dividing either level, the coefficients of the
four-factor product of quadratic characters are nonnegative real numbers. -/
theorem quadraticPairCoeffs_prime_pow_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ χ.quadraticPairCoeffs ψ (p ^ k) := by
  by_cases hχp : χ p = -1
  · exact quadraticPairCoeffs_prime_pow_nonneg_of_eq_neg_one hχ hψ hp hχp k
  by_cases hψp : ψ p = -1
  · rw [quadraticPairCoeffs_comm]
    exact quadraticPairCoeffs_prime_pow_nonneg_of_eq_neg_one hψ hχ hp hψp k
  have hψ0 : 0 ≤ ψ p := by rcases hψ p with h | h | h <;> simp_all
  rw [quadraticPairCoeffs_eq_zetaMul_mul_pmul, mul_apply]
  refine Finset.sum_nonneg fun d hd ↦ ?_
  have hdn := (Nat.mem_divisorsAntidiagonal.mp hd).1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp
    (show d.2 ∣ p ^ k from ⟨d.1, hdn.symm.trans (mul_comm _ _)⟩)
  rw [ArithmeticFunction.pmul_apply]
  refine mul_nonneg (zetaMul_nonneg (MulChar.isQuadratic_iff_sq_eq_one.mp hχ) _) ?_
  refine mul_nonneg ?_ (zetaMul_nonneg (MulChar.isQuadratic_iff_sq_eq_one.mp hχ) _)
  rw [hj, ← ψ.apply_eq_toArithmeticFunction_apply (pow_ne_zero _ hp.ne_zero), Nat.cast_pow,
    map_pow]
  exact pow_nonneg hψ0 _

/-- All Dirichlet coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` are nonnegative
real numbers for quadratic characters, without any conductor or distinctness restriction. -/
theorem quadraticPairCoeffs_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (n : ℕ) :
    0 ≤ χ.quadraticPairCoeffs ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [(χ.isMultiplicative_quadraticPairCoeffs ψ).multiplicative_factorization _ hn]
  exact Finset.prod_nonneg fun p hp ↦
    quadraticPairCoeffs_prime_pow_nonneg hχ hψ (Nat.prime_of_mem_primeFactors hp) _

/-- On `Re s > 1` the four-factor product is the absolutely convergent Dirichlet series
of `quadraticPairCoeffs`. The fourth L-function is that of the actual product character,
with its imprimitive Euler factors retained. -/
theorem LSeriesHasSum_quadraticPairCoeffs [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    have : NeZero (Nat.lcm M N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
    LSeriesHasSum (χ.quadraticPairCoeffs ψ) s
      (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) := by
  have : NeZero (Nat.lcm M N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  have hL {A : ℕ} [NeZero A] (φ : DirichletCharacter ℂ A) :
      LSeriesHasSum (toArithmeticFunction (φ ·)) s (φ.LFunction s) := by
    rw [φ.LFunction_eq_LSeries hs]
    exact (LSeriesHasSum_congr s _ φ.apply_eq_toArithmeticFunction_apply).mp
      (ZMod.LSeriesSummable_of_one_lt_re φ hs).LSeriesHasSum
  have hζχ : LSeriesHasSum χ.zetaMul s (riemannZeta s * χ.LFunction s) := by
    rw [← LSeries_zetaMul χ hs]
    exact (χ.LSeriesSummable_zetaMul hs).LSeriesHasSum
  exact ArithmeticFunction.LSeriesHasSum_mul
    (ArithmeticFunction.LSeriesHasSum_mul hζχ (hL ψ)) (hL (χ.mul ψ))

end DirichletCharacter
