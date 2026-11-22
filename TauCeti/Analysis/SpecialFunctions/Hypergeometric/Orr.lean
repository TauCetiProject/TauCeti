/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.Binomial
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.RingTheory.Binomial
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Orr's product formula for Gauss hypergeometric series

Define coefficients `Aₛ` by the generating function

`(1 - z)^(a + b - c) F(2a, 2b; 2c - 1; z) = ∑ₛ Aₛ zˢ`  (DLMF 15.16.2),

so that `Aₛ = ∑_{i + j = s} (2a)ᵢ (2b)ᵢ / ((2c - 1)ᵢ i!) · (c - a - b)ⱼ / j!`. Orr's product
formula (DLMF 15.16.1) expresses a product of two Gauss series through the same coefficients:

`F(a, b; c - 1/2; z) F(c - a, c - b; c + 1/2; z) = ∑ₛ (c)ₛ / (c + 1/2)ₛ Aₛ zˢ`,  `|z| < 1`.

Here `F` is Mathlib's `ordinaryHypergeometric`. The formula holds whenever `2c - 1` is not a
nonpositive integer, which is exactly when the three lower parameters `c - 1/2`, `c + 1/2` and
`2c - 1` avoid the poles `0, -1, -2, …`. Comparing coefficients, it is the finite identity
`∑_{i + j = n} fᵢ gⱼ = (c)ₙ / (c + 1/2)ₙ Aₙ` between the coefficients `fᵢ`, `gⱼ` of the two
factors, which holds over any field of characteristic zero.

## Main definitions

* `TauCeti.orrCoefficient a b c s`: the coefficient `Aₛ` of DLMF 15.16.2.

## Main results

* `TauCeti.mk_orrCoefficient`: the formal generating function of the `Aₛ` (DLMF 15.16.2).
* `TauCeti.hasSum_orrCoefficient_mul_pow`: the generating function of the `Aₛ` on the open unit
  disk (DLMF 15.16.2).
* `TauCeti.sum_antidiagonal_ordinaryHypergeometricCoefficient_mul_eq_mul_orrCoefficient`: the
  coefficient form of Orr's formula.
* `TauCeti.hasSum_mul_orrCoefficient_smul_pow`: Orr's formula on the open unit ball of a complete
  normed division algebra over `ℝ` or `ℂ` (DLMF 15.16.1).

## Implementation notes

Write `θ = X * d⁄dX` for the Euler operator on formal power series, which multiplies the
coefficient of `Xⁿ` by `n`. Both factors satisfy the hypergeometric equation
(`TauCeti.mk_ordinaryHypergeometricCoefficient_gaussEquation`), and from the two equations their
product satisfies the fourth-order equation `L₀(θ) Y + X L₁(θ) Y + X² L₂(θ) Y = 0` with
`L₀(θ) = θ (θ + 2c - 2) (2θ + 2c - 3) (2θ + 2c - 1)`; the proof is an explicit
`linear_combination` of the two equations and their derivatives. The series of
`(1 - X)^(a + b - c)` satisfies a first-order equation, so the generating function of the `Aₛ`
satisfies a second-order equation, and multiplying its coefficients by `(c)ₛ / (c + 1/2)ₛ` turns
the recurrence of that equation into the recurrence of the fourth-order one. The two coefficient
sequences therefore obey the same three-term recurrence, whose leading coefficient `L₀(n)` does
not vanish for `n ≥ 1`, and they agree at `n = 0`.

## References

* W. McF. Orr, *Theorems relating to the product of two hypergeometric series*, Transactions of the
  Cambridge Philosophical Society **17** (1899).
* J. L. Burchnall and T. W. Chaundy, *The hypergeometric identities of Cayley, Orr, and Bailey*,
  Proceedings of the London Mathematical Society (2) **50** (1948).
* NIST Digital Library of Mathematical Functions, §15.16, equations 15.16.1 and 15.16.2,
  <https://dlmf.nist.gov/15.16>.
-/

public section

noncomputable section

open Finset PowerSeries
open scoped Nat

namespace TauCeti

section Formal

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient `Aₛ` of DLMF 15.16.2: the coefficient of `zˢ` in
`(1 - z)^(a + b - c) F(2a, 2b; 2c - 1; z)`, the Cauchy product of the coefficients
`(2a)ᵢ (2b)ᵢ / ((2c - 1)ᵢ i!)` of the Gauss series and the coefficients `(c - a - b)ⱼ / j!` of
`(1 - z)^(a + b - c)`. These are the coefficients of Orr's product formula
(`TauCeti.hasSum_mul_orrCoefficient_smul_pow`). -/
def orrCoefficient (a b c : K) (s : ℕ) : K :=
  ∑ p ∈ antidiagonal s,
    ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) p.1 *
      Ring.multichoose (c - a - b) p.2

/-- `Aₛ` as the Cauchy product of `(2a)ᵢ (2b)ᵢ / ((2c - 1)ᵢ i!)` and `(c - a - b)ⱼ / j!`. -/
theorem orrCoefficient_def (a b c : K) (s : ℕ) :
    orrCoefficient a b c s =
      ∑ p ∈ antidiagonal s,
        ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) p.1 *
          Ring.multichoose (c - a - b) p.2 := (rfl)

/-- The constant term of the generating function of the `Aₛ` is `A₀ = 1`. -/
@[simp]
theorem orrCoefficient_zero (a b c : K) : orrCoefficient a b c 0 = 1 := by
  simp [orrCoefficient_def, ordinaryHypergeometricCoefficient]

/-- The formal generating function of the `Aₛ` (DLMF 15.16.2): it is the product of the series of
`F(2a, 2b; 2c - 1; X)` and the series `∑ⱼ (c - a - b)ⱼ / j! Xʲ` of `(1 - X)^(a + b - c)`. -/
theorem mk_orrCoefficient (a b c : K) :
    PowerSeries.mk (orrCoefficient a b c) =
      mk (ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1)) *
        mk (Ring.multichoose (c - a - b)) := by
  ext
  simp [coeff_mul, orrCoefficient_def]

omit [CharZero K] in
/-- The coefficient of `X` in `p + X q + X² r` is `p₁ + q₀`. -/
private theorem coeff_one_add_X_mul_add_X_mul_X_mul (p q r : K⟦X⟧) :
    coeff 1 (p + X * q + X * (X * r)) = coeff 1 p + coeff 0 q := by
  simp [coeff_succ_X_mul]

omit [CharZero K] in
/-- The coefficient of `Xⁿ⁺²` in `p + X q + X² r` is `pₙ₊₂ + qₙ₊₁ + rₙ`. These two lemmas turn an
equation `p + X q + X² r = 0` into the three-term recurrence of its coefficients. -/
private theorem coeff_add_two_add_X_mul_add_X_mul_X_mul (p q r : K⟦X⟧) (n : ℕ) :
    coeff (n + 2) (p + X * q + X * (X * r)) = coeff (n + 2) p + coeff (n + 1) q + coeff n r := by
  simp only [map_add, coeff_succ_X_mul]

/-- If `f` and `g` satisfy the hypergeometric equations with parameters `(a, b; c - 1/2)` and
`(c - a, c - b; c + 1/2)`, their product `Y = f * g` satisfies the fourth-order equation
`L₀(θ) Y + X L₁(θ) Y + X² L₂(θ) Y = 0` of Orr's formula, where `θ = X * d⁄dX`,
`L₀(θ) = θ (θ + 2c - 2) (2θ + 2c - 3) (2θ + 2c - 1)` and each `Lⱼ(θ)` is expanded in powers
of `θ`. -/
private theorem orr_equation_mul_of_gaussEquation {a b c : K} {f g : K⟦X⟧}
    (hf : X * (1 - X) * d⁄dX (d⁄dX f) + (C (c - 1 / 2) - C (a + b + 1) * X) * d⁄dX f =
      C (a * b) * f)
    (hg : X * (1 - X) * d⁄dX (d⁄dX g) + (C (c + 1 / 2) - C (c - a + (c - b) + 1) * X) * d⁄dX g =
      C ((c - a) * (c - b)) * g) :
    (2 * (c - 1) * (2 * c - 3) * (2 * c - 1) : K) • (X * d⁄dX (f * g)) +
        (20 * c ^ 2 - 40 * c + 19 : K) • (X * d⁄dX (X * d⁄dX (f * g))) +
        (16 * (c - 1) : K) • (X * d⁄dX (X * d⁄dX (X * d⁄dX (f * g)))) +
        (4 : K) • (X * d⁄dX (X * d⁄dX (X * d⁄dX (X * d⁄dX (f * g))))) +
      X * ((-2 * c * (2 * c - 1) * (4 * a * b - 2 * a * c + a - 2 * b * c + b + 2 * c ^ 2 - c) :
            K) • (f * g) +
          (-2 * (16 * a * b * c - 4 * a * b - 8 * a * c ^ 2 + 6 * a * c - a - 8 * b * c ^ 2 +
            6 * b * c - b + 16 * c ^ 3 - 14 * c ^ 2 + 3 * c) : K) • (X * d⁄dX (f * g)) +
          (-4 * (4 * a * b - 2 * a * c + a - 2 * b * c + b + 12 * c ^ 2 - 8 * c + 1) : K) •
            (X * d⁄dX (X * d⁄dX (f * g))) +
          (-4 * (8 * c - 3) : K) • (X * d⁄dX (X * d⁄dX (X * d⁄dX (f * g)))) +
          (-8 : K) • (X * d⁄dX (X * d⁄dX (X * d⁄dX (X * d⁄dX (f * g)))))) +
      X * (X * ((-4 * c * (c + 1) * (a - b - c) * (a - b + c) : K) • (f * g) +
          (-4 * (2 * a ^ 2 * c + a ^ 2 - 4 * a * b * c - 2 * a * b + 2 * b ^ 2 * c + b ^ 2 -
            4 * c ^ 3 - 3 * c ^ 2) : K) • (X * d⁄dX (f * g)) +
          (-4 * (a ^ 2 - 2 * a * b + b ^ 2 - 6 * c ^ 2 - 3 * c) : K) •
            (X * d⁄dX (X * d⁄dX (f * g))) +
          (4 * (4 * c + 1) : K) • (X * d⁄dX (X * d⁄dX (X * d⁄dX (f * g)))) +
          (4 : K) • (X * d⁄dX (X * d⁄dX (X * d⁄dX (X * d⁄dX (f * g))))))) = 0 := by
  have hw : (2 : K⟦X⟧) * C (1 / 2 : K) = 1 := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  have hf₁ := congrArg d⁄dX hf
  have hf₂ := congrArg d⁄dX hf₁
  have hg₁ := congrArg d⁄dX hg
  have hg₂ := congrArg d⁄dX hg₁
  -- The certificate is the reduction of the equation modulo the two hypergeometric equations and
  -- their first two derivatives, in which `C (1 / 2)` is cleared by `hw`.
  simp only [smul_eq_C_mul, Derivation.leibniz,
    Derivation.map_one_eq_zero, derivative_X, derivative_C, smul_eq_mul, map_add, map_sub,
    map_mul, map_neg, map_one, map_ofNat, map_pow, mul_one, mul_zero, add_zero, zero_sub,
    neg_zero] at hf hf₁ hf₂ hg hg₁ hg₂ ⊢
  linear_combination
    (-2 * g * X ^ 4 + 2 * g * X ^ 3) * (2 * hf₂ + d⁄dX (d⁄dX (d⁄dX f)) * hw) +
    (2 * g * X ^ 3 * C a + 2 * g * X ^ 3 * C b - 8 * g * X ^ 3 * C c - 4 * g * X ^ 3 +
      6 * g * X ^ 2 * C c + g * X ^ 2 - 8 * d⁄dX g * X ^ 4 + 8 * d⁄dX g * X ^ 3) *
      (2 * hf₁ + d⁄dX (d⁄dX f) * hw) +
    (-6 * g * X ^ 2 * C a * C b + 8 * g * X ^ 2 * C a * C c + 2 * g * X ^ 2 * C a +
      8 * g * X ^ 2 * C b * C c + 2 * g * X ^ 2 * C b - 12 * g * X ^ 2 * C c ^ 2 -
      6 * g * X ^ 2 * C c + 4 * g * X * C c ^ 2 - g * X + 8 * d⁄dX g * X ^ 3 * C a +
      8 * d⁄dX g * X ^ 3 * C b - 24 * d⁄dX g * X ^ 3 * C c - 18 * d⁄dX g * X ^ 3 +
      16 * d⁄dX g * X ^ 2 * C c + 8 * d⁄dX g * X ^ 2 - 12 * d⁄dX (d⁄dX g) * X ^ 4 +
      12 * d⁄dX (d⁄dX g) * X ^ 3) * (2 * hf + d⁄dX f * hw) +
    (-2 * f * X ^ 4 + 2 * f * X ^ 3) * (2 * hg₂ - d⁄dX (d⁄dX (d⁄dX g)) * hw) +
    (-2 * f * X ^ 3 * C a - 2 * f * X ^ 3 * C b - 4 * f * X ^ 3 * C c - 4 * f * X ^ 3 +
      6 * f * X ^ 2 * C c - f * X ^ 2 - 8 * d⁄dX f * X ^ 4 + 8 * d⁄dX f * X ^ 3) *
      (2 * hg₁ - d⁄dX (d⁄dX g) * hw) +
    (6 * f * X ^ 2 * C a * C b - 2 * f * X ^ 2 * C a * C c - 2 * f * X ^ 2 * C a -
      2 * f * X ^ 2 * C b * C c - 2 * f * X ^ 2 * C b - 2 * f * X ^ 2 * C c ^ 2 -
      2 * f * X ^ 2 * C c + 4 * f * X * C c ^ 2 - 4 * f * X * C c + f * X +
      4 * d⁄dX f * X ^ 3 * C a + 4 * d⁄dX f * X ^ 3 * C b - 8 * d⁄dX f * X ^ 3 * C c -
      6 * d⁄dX f * X ^ 3 + 4 * d⁄dX f * X ^ 2 * C c + 6 * d⁄dX f * X ^ 2) *
      (2 * hg - d⁄dX g * hw)

/-- If `f` and `g` satisfy the hypergeometric equations with parameters `(a, b; c - 1/2)` and
`(c - a, c - b; c + 1/2)`, the coefficients `yₙ` of `f * g` satisfy the three-term recurrence
`L₀(n + 2) yₙ₊₂ + L₁(n + 1) yₙ₊₁ + L₂(n) yₙ = 0` of the fourth-order equation
`L₀(θ) Y + X L₁(θ) Y + X² L₂(θ) Y = 0` of Orr's theorem, where `θ = X * d⁄dX` and
`L₀(θ) = θ (θ + 2c - 2) (2θ + 2c - 3) (2θ + 2c - 1)`. -/
private theorem coeff_mul_recurrence_of_gaussEquation {a b c : K} {f g : K⟦X⟧}
    (hf : X * (1 - X) * d⁄dX (d⁄dX f) + (C (c - 1 / 2) - C (a + b + 1) * X) * d⁄dX f =
      C (a * b) * f)
    (hg : X * (1 - X) * d⁄dX (d⁄dX g) + (C (c + 1 / 2) - C (c - a + (c - b) + 1) * X) * d⁄dX g =
      C ((c - a) * (c - b)) * g) :
    (2 * c - 1) ^ 2 * (2 * c + 1) * coeff 1 (f * g) +
        2 * (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c) * c * (2 * c - 1) *
          coeff 0 (f * g) = 0 ∧
    ∀ n : ℕ, ((n : K) + 2) * (n + 2 * c) * (2 * n + 2 * c + 1) * (2 * n + 2 * c + 3) *
          coeff (n + 2) (f * g) +
        2 * (-2 * (n + 1) ^ 2 + (2 - 4 * c) * (n + 1) +
          (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c)) * (n + 1 + c) *
          (2 * n + 2 * c + 1) * coeff (n + 1) (f * g) +
        4 * (n + c - a + b) * (n + c + a - b) * (n + c) * (n + c + 1) * coeff n (f * g) = 0 := by
  have hode := orr_equation_mul_of_gaussEquation hf hg
  refine ⟨?_, fun n ↦ ?_⟩
  · have h := congrArg (coeff 1) hode
    rw [coeff_one_add_X_mul_add_X_mul_X_mul] at h
    simp only [map_add, coeff_smul, smul_eq_mul, coeff_X_mul_derivative, map_zero] at h
    push_cast at h
    linear_combination h
  · have h := congrArg (coeff (n + 2)) hode
    rw [coeff_add_two_add_X_mul_add_X_mul_X_mul] at h
    simp only [map_add, coeff_smul, smul_eq_mul, coeff_X_mul_derivative, map_zero] at h
    push_cast at h
    linear_combination h

omit [CharZero K] in
/-- If `f` satisfies the hypergeometric equation with parameters `(2a, 2b; 2c - 1)` and `g`
satisfies `(1 - X) g' = (c - a - b) g`, the coefficients `Aₙ` of `f * g` satisfy the three-term
recurrence `M₀(n + 2) Aₙ₊₂ + M₁(n + 1) Aₙ₊₁ + M₂(n) Aₙ = 0` of the second-order equation
`M₀(θ) H + X M₁(θ) H + X² M₂(θ) H = 0`, where `θ = X * d⁄dX` and `M₀(θ) = θ (θ + 2c - 2)`. -/
private theorem coeff_mul_recurrence_of_gaussEquation_of_one_sub {a b c : K} {f g : K⟦X⟧}
    (hf : X * (1 - X) * d⁄dX (d⁄dX f) + (C (2 * c - 1) - C (2 * a + 2 * b + 1) * X) * d⁄dX f =
      C (2 * a * (2 * b)) * f)
    (hg : (1 - X) * d⁄dX g = C (c - a - b) * g) :
    (2 * c - 1) * coeff 1 (f * g) +
        (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c) * coeff 0 (f * g) = 0 ∧
    ∀ n : ℕ, ((n : K) + 2) * (n + 2 * c) * coeff (n + 2) (f * g) +
        (-2 * (n + 1) ^ 2 + (2 - 4 * c) * (n + 1) +
          (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c)) * coeff (n + 1) (f * g) +
        (n + c - a + b) * (n + c + a - b) * coeff n (f * g) = 0 := by
  have hg₁ := congrArg d⁄dX hg
  set H₁ := X * d⁄dX (f * g) with hH₁
  set H₂ := X * d⁄dX H₁ with hH₂
  -- The equation `M₀(θ) H + X M₁(θ) H + X² M₂(θ) H = 0` for `H = f * g`, expanded in the powers
  -- `Hₖ = θᵏ H`. The certificate is its reduction modulo the hypergeometric equation of `f` and
  -- the first-order equation of `g` with its derivative.
  have hode :
      (2 * (c - 1) : K) • H₁ + H₂ +
        X * ((-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c : K) • (f * g) +
          (-2 * (2 * c - 1) : K) • H₁ + (-2 : K) • H₂) +
        X * (X * ((-(a - b - c) * (a - b + c) : K) • (f * g) + (2 * c : K) • H₁ + H₂)) = 0 := by
    simp only [hH₁, hH₂, smul_eq_C_mul, Derivation.leibniz, Derivation.map_one_eq_zero,
      derivative_X, derivative_C, smul_eq_mul, map_add, map_sub, map_mul, map_neg, map_one,
      map_ofNat, map_pow, mul_one, mul_zero, add_zero, zero_sub, neg_zero] at hf hg hg₁ ⊢
    linear_combination
      (-g * X ^ 2 + g * X) * hf + (-f * X ^ 3 + f * X ^ 2) * hg₁ +
      (-f * X ^ 2 * C a - f * X ^ 2 * C b - f * X ^ 2 * C c + 2 * f * X * C c - f * X -
        2 * d⁄dX f * X ^ 3 + 2 * d⁄dX f * X ^ 2) * hg
  refine ⟨?_, fun n ↦ ?_⟩
  · have h := congrArg (coeff 1) hode
    rw [coeff_one_add_X_mul_add_X_mul_X_mul] at h
    simp only [hH₁, hH₂, map_add, coeff_smul, smul_eq_mul, coeff_X_mul_derivative, map_zero] at h
    push_cast at h
    linear_combination h
  · have h := congrArg (coeff (n + 2)) hode
    rw [coeff_add_two_add_X_mul_add_X_mul_X_mul] at h
    simp only [hH₁, hH₂, map_add, coeff_smul, smul_eq_mul, coeff_X_mul_derivative, map_zero] at h
    push_cast at h
    linear_combination h

/-- The ratio `Bₘ = (c)ₘ / (c + 1/2)ₘ` satisfies `(2 (c + m) + 1) Bₘ₊₁ = 2 (c + m) Bₘ` when `2c - 1`
is not a nonpositive integer. -/
private theorem two_mul_add_one_mul_ascPochhammer_div_succ {c : K}
    (hc : ∀ k : ℕ, 2 * c - 1 ≠ -k) (m : ℕ) :
    (2 * (c + m) + 1) *
        ((ascPochhammer K (m + 1)).eval c / (ascPochhammer K (m + 1)).eval (c + 1 / 2)) =
      2 * (c + m) * ((ascPochhammer K m).eval c / (ascPochhammer K m).eval (c + 1 / 2)) := by
  have h₁ : (ascPochhammer K m).eval (c + 1 / 2) ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩
    exact hc (2 * k + 2) (by push_cast; linear_combination 2 * hk)
  have h₂ : 2 * (c + m) + 1 ≠ 0 := fun h ↦ hc (2 * m + 2) (by push_cast; linear_combination h)
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  generalize (ascPochhammer K m).eval c = u
  generalize (ascPochhammer K m).eval (c + 1 / 2) = v at h₁ ⊢
  rw [show c + 1 / 2 + m = (2 * (c + m) + 1) / 2 by ring]
  generalize 2 * (c + m) + 1 = w at h₂ ⊢
  field_simp

/-- The recurrences of `coeff_mul_recurrence_of_gaussEquation` and
`coeff_mul_recurrence_of_gaussEquation_of_one_sub` determine a sequence from its first term:
if `y` satisfies the first and `A` the second, with `y 0 = A 0 = 1`, then
`y n = (c)ₙ / (c + 1/2)ₙ A n`, provided `2c - 1` is not a nonpositive integer. -/
private theorem eq_ascPochhammer_div_mul_of_recurrence {a b c : K}
    (hc : ∀ k : ℕ, 2 * c - 1 ≠ -k) {y A : ℕ → K} (hy₀ : y 0 = 1) (hA₀ : A 0 = 1)
    (hy₁ : (2 * c - 1) ^ 2 * (2 * c + 1) * y 1 +
        2 * (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c) * c * (2 * c - 1) *
          y 0 = 0)
    (hy : ∀ m : ℕ, ((m : K) + 2) * (m + 2 * c) * (2 * m + 2 * c + 1) * (2 * m + 2 * c + 3) *
          y (m + 2) +
        2 * (-2 * (m + 1) ^ 2 + (2 - 4 * c) * (m + 1) +
          (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c)) * (m + 1 + c) *
          (2 * m + 2 * c + 1) * y (m + 1) +
        4 * (m + c - a + b) * (m + c + a - b) * (m + c) * (m + c + 1) * y m = 0)
    (hA₁ : (2 * c - 1) * A 1 + (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c) *
      A 0 = 0)
    (hA : ∀ m : ℕ, ((m : K) + 2) * (m + 2 * c) * A (m + 2) +
        (-2 * (m + 1) ^ 2 + (2 - 4 * c) * (m + 1) +
          (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c)) * A (m + 1) +
        (m + c - a + b) * (m + c + a - b) * A m = 0)
    (n : ℕ) :
    y n = (ascPochhammer K n).eval c / (ascPochhammer K n).eval (c + 1 / 2) * A n := by
  set B := fun m : ℕ ↦ (ascPochhammer K m).eval c / (ascPochhammer K m).eval (c + 1 / 2)
    with hB_def
  have hB (m : ℕ) : (2 * (c + m) + 1) * B (m + 1) = 2 * (c + m) * B m :=
    two_mul_add_one_mul_ascPochhammer_div_succ hc m
  have hB₀ : B 0 = 1 := by simp [hB_def]
  -- the leading coefficients of the recurrence of `y` do not vanish
  have hq₁ : (2 * c - 1) ^ 2 * (2 * c + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (by simpa using hc 0))
      fun h ↦ hc 2 (by push_cast; linear_combination h)
  have hq : ∀ m : ℕ,
      ((m : K) + 2) * (m + 2 * c) * (2 * m + 2 * c + 1) * (2 * m + 2 * c + 3) ≠ 0 := fun m ↦ by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    · have h : ((m + 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at h
      exact h
    · exact fun h ↦ hc (m + 1) (by push_cast; linear_combination h)
    · exact fun h ↦ hc (2 * m + 2) (by push_cast; linear_combination h)
    · exact fun h ↦ hc (2 * m + 4) (by push_cast; linear_combination h)
  -- `B * A` satisfies the recurrence of `y`: by `hB`, the recurrence of `y` at `B * A` is
  -- `4 (c + m) (c + m + 1) B m` times the recurrence of `A`
  have key : ∀ m, y m = B m * A m ∧ y (m + 1) = B (m + 1) * A (m + 1) := by
    intro m
    induction m with
    | zero =>
      have h := hB 0
      push_cast at h
      refine ⟨by simp [hy₀, hB₀, hA₀], mul_left_cancel₀ hq₁ ?_⟩
      linear_combination hy₁ - (2 * c - 1) ^ 2 * A 1 * h - 2 * c * (2 * c - 1) * B 0 * hA₁ +
        2 * (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c) * c * (2 * c - 1) *
          (A 0 * hB₀ + hA₀ - hy₀)
    | succ m ih =>
      have h := hB (m + 1)
      push_cast at h
      refine ⟨ih.2, ?_⟩
      rw [show m + 1 + 1 = m + 2 by omega]
      refine mul_left_cancel₀ (hq m) ?_
      linear_combination hy m -
        2 * (-2 * (m + 1) ^ 2 + (2 - 4 * c) * (m + 1) +
          (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c)) * (m + 1 + c) *
          (2 * m + 2 * c + 1) * ih.2 -
        4 * (m + c - a + b) * (m + c + a - b) * (m + c) * (m + c + 1) * ih.1 -
        4 * (c + m) * (c + m + 1) * B m * hA m -
        ((m : K) + 2) * (m + 2 * c) * (2 * m + 2 * c + 1) * A (m + 2) * h -
        (((m : K) + 2) * (m + 2 * c) * (2 * (c + m + 1)) * A (m + 2) +
          2 * (-2 * (m + 1) ^ 2 + (2 - 4 * c) * (m + 1) +
            (-4 * a * b + 2 * a * c - a + 2 * b * c - b - 2 * c ^ 2 + c)) * (m + 1 + c) *
            A (m + 1)) * hB m
  exact (key n).1

/-- **Orr's theorem**, coefficient form (DLMF 15.16.1–15.16.2): when `2c - 1` is not a
nonpositive integer, the Cauchy product of the coefficients of `F(a, b; c - 1/2; ·)` and
`F(c - a, c - b; c + 1/2; ·)` is `(c)ₙ / (c + 1/2)ₙ Aₙ`, with `Aₙ = orrCoefficient a b c n`. -/
theorem sum_antidiagonal_ordinaryHypergeometricCoefficient_mul_eq_mul_orrCoefficient {a b c : K}
    (hc : ∀ k : ℕ, 2 * c - 1 ≠ -k) (n : ℕ) :
    ∑ p ∈ antidiagonal n, ordinaryHypergeometricCoefficient a b (c - 1 / 2) p.1 *
        ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) p.2 =
      (ascPochhammer K n).eval c / (ascPochhammer K n).eval (c + 1 / 2) *
        orrCoefficient a b c n := by
  have hc₁ : ∀ k : ℕ, (k : K) ≠ -(c - 1 / 2) := fun k hk ↦
    hc (2 * k) (by push_cast; linear_combination 2 * hk)
  have hc₂ : ∀ k : ℕ, (k : K) ≠ -(c + 1 / 2) := fun k hk ↦
    hc (2 * k + 2) (by push_cast; linear_combination 2 * hk)
  have hc₃ : ∀ k : ℕ, (k : K) ≠ -(2 * c - 1) := fun k hk ↦ hc k (by linear_combination hk)
  -- the series `(1 - X)^(a + b - c)` satisfies `(1 - X) P' = (c - a - b) P`
  have hP : (1 - X) * d⁄dX (mk (Ring.multichoose (c - a - b))) =
      C (c - a - b) * mk (Ring.multichoose (c - a - b)) := by
    ext m
    rw [sub_mul, one_mul, map_sub, coeff_X_mul_derivative, coeff_derivative, coeff_C_mul]
    simp only [coeff_mk]
    have h := Ring.add_one_nsmul_multichoose_add_one (c - a - b) m
    rw [nsmul_eq_mul] at h
    push_cast at h ⊢
    linear_combination h
  obtain ⟨hy₁, hy⟩ := coeff_mul_recurrence_of_gaussEquation
    (mk_ordinaryHypergeometricCoefficient_gaussEquation a b (c - 1 / 2) hc₁)
    (mk_ordinaryHypergeometricCoefficient_gaussEquation (c - a) (c - b) (c + 1 / 2) hc₂)
  obtain ⟨hA₁, hA⟩ := coeff_mul_recurrence_of_gaussEquation_of_one_sub
    (mk_ordinaryHypergeometricCoefficient_gaussEquation (2 * a) (2 * b) (2 * c - 1) hc₃) hP
  simp only [← mk_orrCoefficient, coeff_mk] at hA₁ hA
  have h := eq_ascPochhammer_div_mul_of_recurrence hc (y := fun m ↦ coeff m
    (mk (ordinaryHypergeometricCoefficient a b (c - 1 / 2)) *
      mk (ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2))))
    (by simp [ordinaryHypergeometricCoefficient]) (orrCoefficient_zero a b c) hy₁ hy hA₁ hA n
  simpa [coeff_mul] using h

end Formal

section Analytic

/-- **The generating function of Orr's coefficients** (DLMF 15.16.2): on the open unit disk,
`(1 - z)^(a + b - c) F(2a, 2b; 2c - 1; z) = ∑ₛ Aₛ zˢ` with `Aₛ = orrCoefficient a b c s`, for all
complex parameters, the power being principal. -/
theorem hasSum_orrCoefficient_mul_pow (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n ↦ orrCoefficient a b c n * z ^ n)
      ((1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z) := by
  set f := fun n ↦ ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) n * z ^ n
  set g := fun n ↦ Ring.multichoose (c - a - b) n * z ^ n
  have hf : HasSum f (₂F₁ (2 * a) (2 * b) (2 * c - 1) z) := by
    simpa only [f, smul_eq_mul] using hasSum_ordinaryHypergeometric (2 * a) (2 * b) (2 * c - 1) hz
  have hg : HasSum g (1 / (1 - z) ^ (c - a - b)) :=
    hasSum_multichoose_mul_geometric_complex_of_norm_lt_one hz
  have hfn : Summable fun n ↦ ‖f n‖ := by
    simpa only [f, smul_eq_mul] using
      summable_norm_ordinaryHypergeometricCoefficient_smul_pow (2 * a) (2 * b) (2 * c - 1) hz
  have hgn : Summable fun n ↦ ‖g n‖ := hg.summable.norm
  have hterm (n : ℕ) :
      ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 = orrCoefficient a b c n * z ^ n := by
    rw [orrCoefficient_def, sum_mul]
    refine sum_congr rfl fun kl hkl ↦ ?_
    rw [← mem_antidiagonal.mp hkl, pow_add]
    ring
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn, hf.tsum_eq,
    hg.tsum_eq] at h
  simp only [hterm] at h
  rwa [one_div, ← Complex.cpow_neg, show -(c - a - b) = a + b - c by ring, mul_comm] at h

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **Orr's theorem** (DLMF 15.16.1): on the open unit ball, when `2c - 1` is not a nonpositive
integer,
`F(a, b; c - 1/2; x) F(c - a, c - b; c + 1/2; x) = ∑ₛ (c)ₛ / (c + 1/2)ₛ Aₛ xˢ`, where the
`Aₛ = orrCoefficient a b c s` are the coefficients of `(1 - z)^(a + b - c) F(2a, 2b; 2c - 1; z)`
(`TauCeti.hasSum_orrCoefficient_mul_pow`). -/
theorem hasSum_mul_orrCoefficient_smul_pow {a b c : 𝕂} (hc : ∀ k : ℕ, 2 * c - 1 ≠ -k) {x : 𝔸}
    (hx : ‖x‖ < 1) :
    HasSum (fun n ↦ ((ascPochhammer 𝕂 n).eval c / (ascPochhammer 𝕂 n).eval (c + 1 / 2) *
        orrCoefficient a b c n) • x ^ n)
      (₂F₁ a b (c - 1 / 2) x * ₂F₁ (c - a) (c - b) (c + 1 / 2) x) := by
  have hfn := summable_norm_ordinaryHypergeometricCoefficient_smul_pow a b (c - 1 / 2) hx
  have hgn := summable_norm_ordinaryHypergeometricCoefficient_smul_pow (c - a) (c - b)
    (c + 1 / 2) hx
  have hterm (n : ℕ) :
      ∑ kl ∈ antidiagonal n,
          ordinaryHypergeometricCoefficient a b (c - 1 / 2) kl.1 • x ^ kl.1 *
            ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) kl.2 • x ^ kl.2 =
        ((ascPochhammer 𝕂 n).eval c / (ascPochhammer 𝕂 n).eval (c + 1 / 2) *
          orrCoefficient a b c n) • x ^ n := by
    rw [← sum_antidiagonal_ordinaryHypergeometricCoefficient_mul_eq_mul_orrCoefficient hc n,
      sum_smul]
    refine sum_congr rfl fun kl hkl ↦ ?_
    rw [← mem_antidiagonal.mp hkl, pow_add, smul_mul_smul_comm]
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn,
    (hasSum_ordinaryHypergeometric a b (c - 1 / 2) hx).tsum_eq,
    (hasSum_ordinaryHypergeometric (c - a) (c - b) (c + 1 / 2) hx).tsum_eq] at h
  simpa only [hterm] using h

end Analytic

end TauCeti
