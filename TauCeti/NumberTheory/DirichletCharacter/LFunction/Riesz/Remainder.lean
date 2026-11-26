/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.Chebyshev.RieszRemainder

/-!
# Lipschitz and size bounds for the Riesz remainder of a Dirichlet character

For a Dirichlet character `χ` the *Riesz remainder* is
`G_χ(y) = ∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)`, with the sum written as
`TauCeti.rieszSum (fun n ↦ χ n * Λ n) y` and `(L′/L)(1, χ)` as
`logDeriv (LFunction χ) 1`. Since `‖χ(n) Λ(n)‖ ≤ Λ(n)`
(`DirichletCharacter.norm_mul_vonMangoldt_le`), the bounds of
`TauCeti.NumberTheory.Chebyshev.RieszRemainder` for coefficients dominated by `Λ` give, for
`a ≥ 0`, `w, w' > 0` and `y, z` with `max y z ≥ 1`, resp. `y ≥ 1`,
* `‖w G_χ(a / w) - w' G_χ(a / w')‖ ≤ 3 (a / min w w') |w - w'|`;
* `‖G_χ(y) - G_χ(z)‖ ≤ |y - z| (log (max y z) + log 4 + 4 + ‖(L′/L)(1, χ)‖)`;
* `‖G_χ(y)‖ ≤ y (log y + log 4 + 4 + ‖(L′/L)(1, χ)‖)`.

The statements carry no hypothesis on `χ`: for a nonprincipal `χ` they bound the Riesz remainder,
while for a principal `χ` the function `L(·, χ)` has a pole at `1` and the constant is Mathlib's
junk value of `logDeriv (LFunction χ) 1`. The Mellin side of the Riesz remainder is treated in
`TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin`.

## Main results

* `DirichletCharacter.norm_mul_vonMangoldt_le`: `‖χ(n) Λ(n)‖ ≤ Λ(n)`.
* `DirichletCharacter.norm_mul_rieszSum_div_add_mul_logDeriv_sub_le`,
  `DirichletCharacter.norm_rieszSum_add_mul_logDeriv_sub_le`,
  `DirichletCharacter.norm_rieszSum_add_mul_logDeriv_le`: the three bounds for `G_χ`.

## References

* The Riesz remainder `G_χ` and these bounds, in the form with an absolute constant, are those of
  the formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open ArithmeticFunction TauCeti

namespace DirichletCharacter

variable {q : ℕ} (χ : DirichletCharacter ℂ q)

/-- A Dirichlet character twist of the von Mangoldt function is dominated by it:
`‖χ(n) Λ(n)‖ ≤ Λ(n)`. -/
theorem norm_mul_vonMangoldt_le (n : ℕ) : ‖χ n * (Λ n : ℂ)‖ ≤ Λ n := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one n)

variable [NeZero q]

/-- **Lipschitz bound in the weight for the Riesz remainder of a Dirichlet character.**
Let `G_χ(y) = ∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)`. For
`a ≥ 0` and `w, w' > 0`, `‖w G_χ(a / w) - w' G_χ(a / w')‖ ≤ 3 (a / min w w') |w - w'|`. For a
nonprincipal `χ`, `G_χ` is the Riesz remainder; for a principal `χ` the constant is Mathlib's junk
value of `logDeriv (LFunction χ) 1` at the pole
(`Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le` holds for every constant). -/
theorem norm_mul_rieszSum_div_add_mul_logDeriv_sub_le {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w)
    (hw' : 0 < w') :
    ‖(w : ℂ) * (rieszSum (fun n ↦ χ n * Λ n) (a / w) +
          ((a / w : ℝ) : ℂ) * logDeriv (LFunction χ) 1) -
        (w' : ℂ) * (rieszSum (fun n ↦ χ n * Λ n) (a / w') +
          ((a / w' : ℝ) : ℂ) * logDeriv (LFunction χ) 1)‖ ≤
      3 * (a / min w w') * |w - w'| :=
  Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le χ.norm_mul_vonMangoldt_le _ ha hw hw'

/-- **Lipschitz bound for the Riesz remainder of a Dirichlet character.**
Let `G_χ(y) = ∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)`. If `max y z ≥ 1`, then
`‖G_χ(y) - G_χ(z)‖ ≤ |y - z| (log (max y z) + log 4 + 4 + ‖(L′/L)(1, χ)‖)`. For a principal `χ`
the constant `(L′/L)(1, χ)` is Mathlib's junk value at the pole. -/
theorem norm_rieszSum_add_mul_logDeriv_sub_le {y z : ℝ} (h : 1 ≤ max y z) :
    ‖(rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv (LFunction χ) 1) -
        (rieszSum (fun n ↦ χ n * Λ n) z + z * logDeriv (LFunction χ) 1)‖ ≤
      |y - z| * (Real.log (max y z) + (Real.log 4 + 4) + ‖logDeriv (LFunction χ) 1‖) :=
  Chebyshev.norm_rieszSum_add_mul_sub_le χ.norm_mul_vonMangoldt_le _ h

/-- **Size bound for the Riesz remainder of a Dirichlet character.** For
`y ≥ 1`, `‖∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)‖ ≤
y (log y + log 4 + 4 + ‖(L′/L)(1, χ)‖)`. For a principal `χ` the constant `(L′/L)(1, χ)` is
Mathlib's junk value at the pole. -/
theorem norm_rieszSum_add_mul_logDeriv_le {y : ℝ} (hy : 1 ≤ y) :
    ‖rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv (LFunction χ) 1‖ ≤
      y * (Real.log y + (Real.log 4 + 4) + ‖logDeriv (LFunction χ) 1‖) :=
  Chebyshev.norm_rieszSum_add_mul_le χ.norm_mul_vonMangoldt_le _ hy

end DirichletCharacter
