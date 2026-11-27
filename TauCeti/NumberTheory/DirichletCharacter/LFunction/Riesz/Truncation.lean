/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder

/-!
# Truncating the logarithmic derivative at one

A finite difference of the compensated first Riesz sum controls the approximation of
`L′/L(1, χ)` by a sharp von Mangoldt sum with weight `χ(n)/n`. Only prime powers between
the two cutoffs contribute to the smoothing error. This is the finite-difference step of
L. Alpöge's zero-free-box argument in his formalization of the Riemann hypothesis for
Dirichlet L-functions (https://github.com/leanprover-community/riemann-hypothesis).
-/

public section

open ArithmeticFunction Finset Real TauCeti

namespace DirichletCharacter

/-- A bound `B` on a compensated Riesz increment over `(z,y]` bounds the error in truncating
`L′/L(1, χ)` at `z`. The additional error is due to the integers in `(z,y]`. This is
`Chebyshev.norm_add_sum_div_le_of_norm_rieszSum_sub_add_le` for `c(n) = χ(n) Λ(n)`, so it also
holds with the totalized logarithmic derivative for the principal character. -/
theorem norm_logDeriv_add_sum_vonMangoldt_div_le_of_norm_rieszSum_sub_add_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z y B : ℝ} (hz : 0 < z) (hzy : z < y) (hy : 1 ≤ y)
    (hinc : ‖rieszSum (fun n ↦ χ n * Λ n) y - rieszSum (fun n ↦ χ n * Λ n) z +
      ((y - z : ℝ) : ℂ) * logDeriv χ.LFunction 1‖ ≤ B) :
    ‖logDeriv χ.LFunction 1 + ∑ n ∈ Icc 1 ⌊z⌋₊, χ n * Λ n / (n : ℂ)‖ ≤
      B / (y - z) + (y - z + 1) * (log y / z) :=
  Chebyshev.norm_add_sum_div_le_of_norm_rieszSum_sub_add_le χ.norm_mul_vonMangoldt_le _ hz hzy hy
    hinc

/-- With `z = x^(1/δ₀)` and relative width `η = x⁻²`, the smoothed zero-free-box increment
bound gives a sharp truncation error of at most `(2K + 2) x^(-1 + δ/δ₀) (log Q)²`. This
separates the finite-difference argument from the contour estimate supplying the increment;
it is `Chebyshev.norm_add_sum_div_le_at_rpow` for `c(n) = χ(n) Λ(n)`. -/
theorem norm_logDeriv_add_sum_vonMangoldt_div_le_at_rpow {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x Q δ₀ δ K : ℝ} (hx : 2 ≤ x) (hδ₀ : 0 < δ₀)
    (hδ₀' : δ₀ ≤ 1) (hδ : 0 ≤ δ) (hQ : x ^ (1 / δ₀ + 3) ≤ Q)
    (hinc : ‖rieszSum (fun n ↦ χ n * Λ n) (x ^ (1 / δ₀) * (1 + x ^ (-2 : ℝ))) -
        rieszSum (fun n ↦ χ n * Λ n) (x ^ (1 / δ₀)) +
        ((x ^ (1 / δ₀) * x ^ (-2 : ℝ) : ℝ) : ℂ) * logDeriv χ.LFunction 1‖ ≤
      K * log Q * (x ^ (-2 : ℝ) * (x ^ (1 / δ₀)) ^ (1 - δ₀ + δ) * log Q +
        (x ^ (1 / δ₀)) ^ 2 / Q)) :
    ‖logDeriv χ.LFunction 1 + ∑ n ∈ Icc 1 ⌊x ^ (1 / δ₀)⌋₊, χ n * Λ n / (n : ℂ)‖ ≤
      (2 * K + 2) * x ^ (-1 + δ / δ₀) * log Q ^ 2 :=
  Chebyshev.norm_add_sum_div_le_at_rpow χ.norm_mul_vonMangoldt_le _ hx hδ₀ hδ₀' hδ hQ hinc

end DirichletCharacter
