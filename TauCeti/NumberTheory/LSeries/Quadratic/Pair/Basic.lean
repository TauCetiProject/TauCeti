/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.GCD
public import TauCeti.NumberTheory.LSeries.ZetaMul
public import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction

/-!
# Four-factor coefficients for a pair of Dirichlet characters

`DirichletCharacter.zetaMulPairCoeffs` is defined for arbitrary characters. Its coefficients
are multiplicative and its L-series is the four-factor product on `Re s > 1`.
For quadratic characters `χ` and `ψ`, possibly of different levels, the product
`ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` has nonnegative real Dirichlet coefficients.
The fourth factor is the L-function of the product character at the least common multiple
of the levels, not of its primitive character. Its Euler factors at primes dividing that
least common multiple are trivial.
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
noncomputable def zetaMulPairCoeffs (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  (χ.zetaMul * toArithmeticFunction (ψ ·)) * toArithmeticFunction (χ.mul ψ ·)

/-- The four Dirichlet-convolution factors defining `zetaMulPairCoeffs`. -/
theorem zetaMulPairCoeffs_def (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) :
    χ.zetaMulPairCoeffs ψ =
      (χ.zetaMul * toArithmeticFunction (ψ ·)) * toArithmeticFunction (χ.mul ψ ·) := (rfl)

/-- Pairing the first two factors with their character twist gives the four-factor product. -/
theorem zetaMulPairCoeffs_eq_zetaMul_mul_pmul (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) :
    χ.zetaMulPairCoeffs ψ = χ.zetaMul * (toArithmeticFunction (ψ ·)).pmul χ.zetaMul := by
  rw [zetaMulPairCoeffs, zetaMul, toArithmeticFunction_pmul_mul,
    ArithmeticFunction.pmul_zeta, toArithmeticFunction_mul,
    ArithmeticFunction.pmul_comm (toArithmeticFunction (ψ ·)), mul_assoc]

/-- The prime-power coefficients are the convolution of `zetaMul` with its character twist. -/
theorem zetaMulPairCoeffs_prime_pow (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    χ.zetaMulPairCoeffs ψ (p ^ k) = ∑ i ∈ Finset.range (k + 1),
      χ.zetaMul (p ^ i) * (toArithmeticFunction (ψ ·)).pmul χ.zetaMul (p ^ (k - i)) := by
  rw [zetaMulPairCoeffs_eq_zetaMul_mul_pmul, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b ↦
      χ.zetaMul a * (toArithmeticFunction (ψ ·)).pmul χ.zetaMul b),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [← pow_sub_mul_pow p (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
    Nat.mul_div_cancel _ (pow_pos hp.pos _)]

/-- The four-factor coefficient function is symmetric in the characters. -/
theorem zetaMulPairCoeffs_comm (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) :
    χ.zetaMulPairCoeffs ψ = ψ.zetaMulPairCoeffs χ := by
  simp only [zetaMulPairCoeffs, zetaMul, toArithmeticFunction_mul]
  rw [ArithmeticFunction.pmul_comm (toArithmeticFunction (χ ·))]
  ring

/-- The coefficients of the four-factor product are multiplicative. -/
@[arith_mult] theorem isMultiplicative_zetaMulPairCoeffs (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : (χ.zetaMulPairCoeffs ψ).IsMultiplicative :=
  (χ.isMultiplicative_zetaMul.mul ψ.isMultiplicative_toArithmeticFunction).mul
    (χ.mul ψ).isMultiplicative_toArithmeticFunction

/-- The coefficient at `1` of the four-factor product is `1`. -/
@[simp] theorem zetaMulPairCoeffs_one (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) : χ.zetaMulPairCoeffs ψ 1 = 1 :=
  (χ.isMultiplicative_zetaMulPairCoeffs ψ).map_one

private theorem twist_zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hψ : ψ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hχ : χ p = -1) (k : ℕ) :
    0 ≤ (toArithmeticFunction (ψ ·)).pmul χ.zetaMul (p ^ k) := by
  rw [ArithmeticFunction.pmul_apply, zetaMul_prime_pow_of_eq_neg_one hp hχ]
  split_ifs with hk
  · rw [mul_one, toArithmeticFunction_apply_pow ψ hp.ne_zero]
    rcases hψ p with h | h | h
    · simp [h, pow_nonneg]
    · simp [h]
    · simp [h, hk.neg_one_pow]
  · simp

private theorem zetaMulPairCoeffs_prime_pow_nonneg_of_eq_neg_one
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hχp : χ p = -1) (k : ℕ) : 0 ≤ χ.zetaMulPairCoeffs ψ (p ^ k) := by
  rw [zetaMulPairCoeffs_prime_pow χ ψ hp]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  exact mul_nonneg (zetaMul_prime_pow_nonneg (MulChar.isQuadratic_iff_sq_eq_one.mp hχ) hp i)
    (twist_zetaMul_prime_pow_nonneg hψ hp hχp (k - i))

/-- At every prime, including primes dividing either level, the coefficients of the
four-factor product of quadratic characters are nonnegative real numbers. -/
theorem zetaMulPairCoeffs_prime_pow_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ χ.zetaMulPairCoeffs ψ (p ^ k) := by
  by_cases hχp : χ p = -1
  · exact zetaMulPairCoeffs_prime_pow_nonneg_of_eq_neg_one hχ hψ hp hχp k
  by_cases hψp : ψ p = -1
  · rw [zetaMulPairCoeffs_comm]
    exact zetaMulPairCoeffs_prime_pow_nonneg_of_eq_neg_one hψ hχ hp hψp k
  have hψ0 : 0 ≤ ψ p := by rcases hψ p with h | h | h <;> simp_all
  have hχsq := MulChar.isQuadratic_iff_sq_eq_one.mp hχ
  rw [zetaMulPairCoeffs_prime_pow χ ψ hp]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [ArithmeticFunction.pmul_apply, toArithmeticFunction_apply_pow ψ hp.ne_zero]
  exact mul_nonneg (zetaMul_nonneg hχsq _)
    (mul_nonneg (pow_nonneg hψ0 _) (zetaMul_nonneg hχsq _))

/-- All Dirichlet coefficients of `ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` are nonnegative
real numbers for quadratic characters, without any conductor or distinctness restriction. -/
theorem zetaMulPairCoeffs_nonneg {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (n : ℕ) :
    0 ≤ χ.zetaMulPairCoeffs ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [(χ.isMultiplicative_zetaMulPairCoeffs ψ).multiplicative_factorization _ hn]
  exact Finset.prod_nonneg fun p hp ↦
    zetaMulPairCoeffs_prime_pow_nonneg hχ hψ (Nat.prime_of_mem_primeFactors hp) _

/-- On `Re s > 1` the four-factor product is the absolutely convergent Dirichlet series
of `zetaMulPairCoeffs`. The fourth L-function is `(χ.mul ψ).LFunction` at level
`Nat.lcm M N`, not the L-function of its primitive character. -/
theorem LSeriesHasSum_zetaMulPairCoeffs [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (χ.zetaMulPairCoeffs ψ) s
      (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) := by
  exact ArithmeticFunction.LSeriesHasSum_mul
    (ArithmeticFunction.LSeriesHasSum_mul (χ.LSeriesHasSum_zetaMul hs)
      (ψ.LSeriesHasSum_toArithmeticFunction hs))
    ((χ.mul ψ).LSeriesHasSum_toArithmeticFunction hs)

end DirichletCharacter
