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

/-!
# Bol's identity

Let `D` be a derivation of a commutative ring `A`, and let `N, L ∈ A` be *linear* for `D`, in
the sense that `D (D N) = 0` and `D (D L) = 0`; the model case is `N = a z + b` and `L = c z + d`
with `D = d/dz`. If `L` has an inverse `M`, write `Δ = D N * L - N * D L`, which is `ad - bc` in
the model case. **Bol's identity** says that for all `j, r : ℕ`,

`D^r (N ^ (j + r) * M ^ (j + 1)) = (j + r) (j + r - 1) ⋯ (j + 1) • Δ ^ r * N ^ j * M ^ (j + r + 1)`.

Equivalently, for every polynomial `f` and every `n : ℕ`,

`D^(n + 1) (L ^ n * f (N / L)) = Δ ^ (n + 1) * L ^ (-(n + 2)) * f^(n + 1) (N / L)`.

For `γ = !![a, b; c, d]` the left-hand side is the `(n + 1)`-st derivative of the weight `-n`
slash `L ^ n * f (γ z)` of `f`, and the right-hand side is `det γ ^ (n + 1)` times the weight
`n + 2` slash of `f^(n + 1)`. So `D^(n + 1)` intertwines these two slash actions of `GL₂`. This
is the algebraic input to the theta operators on overconvergent modular forms, and hence to
classicality of overconvergent forms of small slope.

## Main results

* `Derivation.iterate_apply_pow_add_mul_pow_add_one`: Bol's identity.
* `Derivation.iterate_apply_pow_mul_aeval`: Bol's identity for polynomials composed with `N / L`.
* `TauCeti.PowerSeries.iterate_derivative_pow_add_mul_inv_pow_add_one` and
  `TauCeti.PowerSeries.iterate_derivative_pow_mul_aeval`: the same identities for formal power
  series over a field, with `N = a X + b` and `L = c X + d`.

## References

* K. Buzzard, *On p-adic families of automorphic forms*, in *Modular curves and abelian
  varieties*, Progr. Math. 224, Birkhäuser, 2004, §7.
* G. Bol, *Invarianten linearer Differentialgleichungen*, Abh. Math. Sem. Univ. Hamburg 16
  (1949), 1–28.
-/

public section

open scoped Polynomial

namespace Derivation

open Polynomial

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] (D : Derivation R A A)

/-- **Bol's identity.** Let `N, L` satisfy `D (D N) = 0` and `D (D L) = 0`, and let `M` be an
inverse of `L`. Then
`D^r (N ^ (j + r) * M ^ (j + 1)) = (j + r) ⋯ (j + 1) • Δ ^ r * N ^ j * M ^ (j + r + 1)` with
`Δ = D N * L - N * D L`. For `N = a z + b`, `L = c z + d` and `D = d/dz`, `Δ = ad - bc`. -/
theorem iterate_apply_pow_add_mul_pow_add_one {N L M : A} (hN : D (D N) = 0)
    (hL : D (D L) = 0) (hLM : L * M = 1) (j r : ℕ) :
    D^[r] (N ^ (j + r) * M ^ (j + 1)) =
      (j + r).descFactorial r • ((D N * L - N * D L) ^ r * N ^ j * M ^ (j + r + 1)) := by
  have hM : D M = -(M ^ 2 * D L) := by
    simpa [smul_eq_mul] using
      (D.restrictScalars ℤ).leibniz_of_mul_eq_one ((mul_comm M L).trans hLM)
  induction r generalizing j with
  | zero => simp
  | succ r ih =>
    have hcN : D ((j + r + 1 : ℕ) * D N) = 0 := by simp [leibniz, hN]
    have hcL : D ((j + 1 : ℕ) * D L) = 0 := by simp [leibniz, hL]
    -- One derivative splits the product into the two shapes covered by the induction hypothesis.
    have hstep : D (N ^ (j + (r + 1)) * M ^ (j + 1)) =
        (j + r + 1 : ℕ) * D N * (N ^ (j + r) * M ^ (j + 1)) -
          (j + 1 : ℕ) * D L * (N ^ (j + 1 + r) * M ^ (j + 1 + 1)) := by
      rw [leibniz, leibniz_pow, leibniz_pow, hM, show j + (r + 1) - 1 = j + r by omega,
        Nat.add_sub_cancel]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [Function.iterate_succ_apply, hstep, iterate_map_sub,
      iterate_apply_mul_of_apply_eq_zero D hcN, iterate_apply_mul_of_apply_eq_zero D hcL, ih, ih]
    have h₁ : (j + (r + 1)).descFactorial (r + 1) = (j + r + 1) * (j + r).descFactorial r := by
      rw [← add_assoc, Nat.succ_descFactorial_succ]
    have h₂ : (j + (r + 1)).descFactorial (r + 1) = (j + 1) * (j + 1 + r).descFactorial r := by
      rw [Nat.descFactorial_succ, show j + (r + 1) - r = j + 1 by omega,
        show j + (r + 1) = j + 1 + r by omega]
    have h₂' : ((j + (r + 1)).descFactorial (r + 1) : A) =
        (j + 1 : ℕ) * ((j + 1 + r).descFactorial r : A) := by
      rw [h₂, Nat.cast_mul]
    simp only [nsmul_eq_mul]
    rw [h₁, Nat.cast_mul] at h₂' ⊢
    linear_combination -(((j + r + 1 : ℕ) : A) * ((j + r).descFactorial r : A) *
      (D N * L - N * D L) ^ r * N ^ j * M ^ (j + r + 1) * D N) * hLM +
      (D L * (D N * L - N * D L) ^ r * N ^ (j + 1) * M ^ (j + 1 + r + 1)) * h₂'

/-- **Bol's identity for polynomials.** Let `N, L` satisfy `D (D N) = 0` and `D (D L) = 0`, and
let `M` be an inverse of `L`. For every polynomial `f` and every `n : ℕ`,
`D^(n + 1) (L ^ n * f (N M)) = Δ ^ (n + 1) * M ^ (n + 2) * f^(n + 1) (N M)` with
`Δ = D N * L - N * D L`. For `N = a z + b` and `L = c z + d` this says that `D^(n + 1)` carries
the weight `-n` slash of `f` by `!![a, b; c, d]` to `(ad - bc) ^ (n + 1)` times the weight
`n + 2` slash of `f^(n + 1)`. -/
theorem iterate_apply_pow_mul_aeval {N L M : A} (hN : D (D N) = 0) (hL : D (D L) = 0)
    (hLM : L * M = 1) (n : ℕ) (f : R[X]) :
    D^[n + 1] (L ^ n * aeval (N * M) f) =
      (D N * L - N * D L) ^ (n + 1) * M ^ (n + 2) * aeval (N * M) (derivative^[n + 1] f) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, iterate_map_add, mul_add, hf, hg]
  | monomial m r =>
    rw [← C_mul_X_pow_eq_monomial, iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
    simp only [map_mul, aeval_C, aeval_X_pow]
    rw [mul_left_comm, iterate_apply_mul_of_apply_eq_zero D (D.map_algebraMap r)]
    rcases le_or_gt m n with hmn | hmn
    · -- For `m ≤ n` both sides vanish: `L ^ n * (N M) ^ m = N ^ m * L ^ (n - m)`.
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have hprod : L ^ (m + k) * (N * M) ^ m = N ^ m * L ^ k := by
        rw [show L ^ (m + k) * (N * M) ^ m = N ^ m * L ^ k * (L * M) ^ m by ring, hLM,
          one_pow, mul_one]
      rw [hprod, iterate_apply_pow_mul_pow_eq_zero D hN hL (by omega),
        Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]
      simp
    · -- For `m = j + n + 1`, `L ^ n * (N M) ^ m = N ^ (j + (n + 1)) * M ^ (j + 1)`.
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hmn
      have hprod : L ^ n * (N * M) ^ (n + j + 1) = N ^ (j + (n + 1)) * M ^ (j + 1) := by
        rw [show L ^ n * (N * M) ^ (n + j + 1) =
            N ^ (j + (n + 1)) * M ^ (j + 1) * (L * M) ^ n by ring, hLM, one_pow, mul_one]
      rw [hprod, iterate_apply_pow_add_mul_pow_add_one D hN hL hLM,
        show n + j + 1 = j + (n + 1) by omega, show j + (n + 1) - (n + 1) = j by omega]
      simp only [nsmul_eq_mul, _root_.map_natCast]
      ring

end Derivation

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
      Derivation.iterate_apply_pow _ (derivative_derivative_C_mul_X_add_C c 0)]
    simp
  · have hLM : (C c * X + C d) * (C c * X + C d)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simpa)
    rw [(d⁄dX).iterate_apply_pow_mul_aeval (derivative_derivative_C_mul_X_add_C a b)
      (derivative_derivative_C_mul_X_add_C c d) hLM, derivative_mul_sub_mul_derivative]

end TauCeti.PowerSeries
