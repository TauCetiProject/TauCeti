/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import TauCeti.Data.Nat.GCD
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# The sign of the four-factor product to the left of `1`

For quadratic characters `χ` and `ψ`, the product
`F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` has nonnegative Dirichlet coefficients
(`DirichletCharacter.zetaMulPairCoeffs_nonneg`) and a pole at `1`. Siegel's theorem, in Goldfeld's
form, bounds its residue at `1` from below in terms of `1 - β` at any real point `β < 1` where
`F(β) ≤ 0`. This file supplies that sign condition.

Let `0 < β < 1`. Then `ζ(β)` is a negative real number (`TauCeti.riemannZeta_lt_zero`). If none
of the three L-functions vanishes on `(β, 1)`, each of them is a nonnegative real number at `β`
(`DirichletCharacter.LFunction_nonneg_of_forall_ne_zero`), so `F(β) ≤ 0`. If one of them vanishes
at `β` itself, then `F(β) = 0` trivially. These are the two alternatives of the argument: either
no character has a real zero close to `1`, or a fixed character has one.

The product character must be nonprincipal. If `χ.mul ψ` is principal, for instance if `χ = ψ`,
the fourth factor is `ζ` times finitely many Euler factors that are positive on `(0, 1)`, so it
has the same sign as `ζ` there and this argument gives no sign for `F(β)`. The product character
`χ.mul ψ` lives at the common level and is usually imprimitive, but on `(0, 1)` its L-function has
the same zeros as that of its primitive character
(`DirichletCharacter.LFunction_changeLevel_eq_zero_iff`).

## Main results

* `DirichletCharacter.pair_nonpos_of_forall_ne_zero`: if the three L-functions have no zero on
  `(β, 1)` with `0 < β < 1`, then `F(β) ≤ 0`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
-/

public section

open Complex
open scoped ComplexOrder

namespace DirichletCharacter

variable {M N : ℕ} [NeZero M] [NeZero N] {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}

/-- Let `χ`, `ψ` be nonprincipal quadratic characters with nonprincipal product, and
`0 < β < 1`. If none of `L(s, χ)`, `L(s, ψ)` and `L(s, χ.mul ψ)` vanishes on `(β, 1)`, then the
four-factor product `ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)` is a nonpositive real number. -/
theorem pair_nonpos_of_forall_ne_zero (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1)
    (hψ₁ : ψ ≠ 1) (hχψ₁ : χ.mul ψ ≠ 1) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (h : ∀ σ ∈ Set.Ioo β 1,
      χ.LFunction σ ≠ 0 ∧ ψ.LFunction σ ≠ 0 ∧ (χ.mul ψ).LFunction σ ≠ 0) :
    riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (TauCeti.riemannZeta_lt_zero hβ₀ hβ₁).le
      (LFunction_nonneg_of_forall_ne_zero hχ hχ₁ fun σ hσ ↦ (h σ hσ).1))
      (LFunction_nonneg_of_forall_ne_zero hψ hψ₁ fun σ hσ ↦ (h σ hσ).2.1))
      (LFunction_nonneg_of_forall_ne_zero (isQuadratic_mul hχ hψ) hχψ₁
        fun σ hσ ↦ (h σ hσ).2.2)

end DirichletCharacter
