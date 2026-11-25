/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.Derivation.Basic
import TauCeti.RingTheory.Derivation.Bol

/-!
# Bol's identity for formal power series

This file specializes Bol's identity for derivations (`TauCeti.RingTheory.Derivation.Bol`) to
formal power series over a field `K`, with the derivation `d⁄dX`, `N = a X + b` and
`L = c X + d`. Then `D (D N) = 0 = D (D L)` and `D N * L - N * D L = a d - b c`. When `d = 0`,
`L⁻¹ = 0` and both sides of each identity vanish, so the statements hold for all `a, b, c, d`.

## Main results

* `TauCeti.PowerSeries.iterate_derivative_pow_add_mul_inv_pow_add_one`: Bol's identity
  `D^r (N ^ (j + r) * L⁻¹ ^ (j + 1)) =
  (j + r) ⋯ (j + 1) • (a d - b c) ^ r * N ^ j * L⁻¹ ^ (j + r + 1)`.
* `TauCeti.PowerSeries.iterate_derivative_pow_mul_aeval`: Bol's identity for polynomials
  composed with `N L⁻¹`.

## References

* K. Buzzard, *On p-adic families of automorphic forms*, in *Modular curves and abelian
  varieties*, Progr. Math. 224, Birkhäuser, 2004, §7.
-/

public section

open scoped Polynomial

open PowerSeries

namespace TauCeti.PowerSeries

variable {K : Type*} [Field K]

/-- The second derivative of an affine power series `a X + b` vanishes. -/
private theorem derivative_derivative_C_mul_X_add_C (a b : K) :
    d⁄dX (d⁄dX (C a * X + C b)) = 0 := by
  simp

/-- The Wronskian-type expression `D N * L - N * D L` for `N = a X + b` and `L = c X + d` is the
constant `a d - b c`. -/
private theorem derivative_mul_sub_mul_derivative (a b c d : K) :
    d⁄dX (C a * X + C b) * (C c * X + C d) - (C a * X + C b) * d⁄dX (C c * X + C d) =
      C (a * d - b * c) := by
  simp only [map_add, derivative_C_mul_X, derivative_C, add_zero, map_sub, map_mul]
  ring

/-- **Bol's identity** for formal power series over a field: with `N = a X + b` and
`L = c X + d`, `D^r (N ^ (j + r) * L⁻¹ ^ (j + 1)) =
(j + r) ⋯ (j + 1) • (a d - b c) ^ r * N ^ j * L⁻¹ ^ (j + r + 1)`. When `d = 0` both sides vanish,
because `L⁻¹ = 0`. -/
theorem iterate_derivative_pow_add_mul_inv_pow_add_one (a b c d : K) (j r : ℕ) :
    d⁄dX^[r] ((C a * X + C b) ^ (j + r) * (C c * X + C d)⁻¹ ^ (j + 1)) =
      (j + r).descFactorial r •
        (C (a * d - b * c) ^ r * (C a * X + C b) ^ j * (C c * X + C d)⁻¹ ^ (j + r + 1)) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [iterate_map_zero]
  · have hLM : (C c * X + C d) * (C c * X + C d)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simpa)
    rw [(d⁄dX).iterate_apply_pow_add_mul_pow_add_one (derivative_derivative_C_mul_X_add_C a b)
      (derivative_derivative_C_mul_X_add_C c d) hLM, derivative_mul_sub_mul_derivative]

/-- **Bol's identity for polynomials**, over formal power series over a field: with
`N = a X + b` and `L = c X + d`, for every polynomial `f` and every `n : ℕ`,
`D^(n + 1) (L ^ n * f (N L⁻¹)) = (a d - b c) ^ (n + 1) * L⁻¹ ^ (n + 2) * f^(n + 1) (N L⁻¹)`. -/
theorem iterate_derivative_pow_mul_aeval (a b c d : K) (n : ℕ) (f : K[X]) :
    d⁄dX^[n + 1]
        ((C c * X + C d) ^ n * Polynomial.aeval ((C a * X + C b) * (C c * X + C d)⁻¹) f) =
      C (a * d - b * c) ^ (n + 1) * (C c * X + C d)⁻¹ ^ (n + 2) *
        Polynomial.aeval ((C a * X + C b) * (C c * X + C d)⁻¹)
          (Polynomial.derivative^[n + 1] f) := by
  rcases eq_or_ne d 0 with rfl | hd
  · have h : (C c * X + C (0 : K))⁻¹ = 0 := PowerSeries.inv_eq_zero.2 (by simp)
    -- `f (N L⁻¹) = f (0)` is a constant and `D^(n + 1)` kills `L ^ n`.
    have hf : d⁄dX (Polynomial.aeval (0 : K⟦X⟧) f) = 0 := by
      rw [← Polynomial.coeff_zero_eq_aeval_zero', Derivation.map_algebraMap]
    rw [h, mul_zero, mul_comm ((C c * X + C 0) ^ n),
      Derivation.iterate_apply_mul_of_apply_eq_zero _ hf,
      Derivation.iterate_apply_pow_of_apply_apply_eq_zero _
        (derivative_derivative_C_mul_X_add_C c 0)]
    simp
  · have hLM : (C c * X + C d) * (C c * X + C d)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simpa)
    rw [(d⁄dX).iterate_apply_pow_mul_aeval (derivative_derivative_C_mul_X_add_C a b)
      (derivative_derivative_C_mul_X_add_C c d) hLM, derivative_mul_sub_mul_derivative]

end TauCeti.PowerSeries
