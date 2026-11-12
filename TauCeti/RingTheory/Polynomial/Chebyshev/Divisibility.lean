/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Addition and divisibility for the rescaled Chebyshev polynomials of the second kind

Mathlib's rescaled Chebyshev polynomial of the second kind `Polynomial.Chebyshev.S R n` satisfies
`(u - u⁻¹) Sₙ(u + u⁻¹) = uⁿ⁺¹ - u⁻ⁿ⁻¹`, so `Sₙ₋₁` is the symmetric quantum integer `[n]` as a
polynomial in `u + u⁻¹`. This file proves, over an arbitrary commutative ring and for all integer
indices, the polynomial identities behind the arithmetic of quantum integers:

* the addition formula `S_{m+n} = Sₘ Sₙ - S_{m-1} S_{n-1}`, which is
  `[m + n + 1] = [m + 1] [n + 1] - [m] [n]`;
* the product with the rescaled Chebyshev polynomial of the first kind,
  `Cₘ Sₙ = S_{n+m} + S_{n-m}`, the analogue of Mathlib's `Polynomial.Chebyshev.C_mul_C`;
* the multiplication formula `S_{mn-1} = S_{m-1} · (S_{n-1} ∘ Cₘ)`, which is
  `[mn]_u = [m]_u [n]_{uᵐ}`, since `Cₘ(u + u⁻¹) = uᵐ + u⁻ᵐ`;
* hence the divisibility `S_{m-1} ∣ S_{n-1}` whenever `m ∣ n`, that is `[m] ∣ [n]`.

Being identities of polynomials, they specialize to every evaluation, in particular to quantum
integers at an arbitrary loop parameter `δ = u + u⁻¹`.

## Main results

* `Polynomial.Chebyshev.S_add`: `S_{m+n} = Sₘ Sₙ - S_{m-1} S_{n-1}`.
* `Polynomial.Chebyshev.C_mul_S`: `Cₘ Sₙ = S_{n+m} + S_{n-m}`.
* `Polynomial.Chebyshev.S_mul_sub_one`: `S_{mn-1} = S_{m-1} · (S_{n-1} ∘ Cₘ)`.
* `Polynomial.Chebyshev.S_sub_one_dvd_S_sub_one`: `m ∣ n → S_{m-1} ∣ S_{n-1}`.

## References

* J. C. Mason and D. C. Handscomb, *Chebyshev Polynomials*, Chapman & Hall/CRC, 2003, for the
  product and composition identities of the Chebyshev polynomials.
-/

public section

namespace Polynomial.Chebyshev

variable (R : Type*) [CommRing R]

/-- **Addition formula** for the rescaled Chebyshev polynomials of the second kind:
`S_{m+n} = Sₘ Sₙ - S_{m-1} S_{n-1}`. In quantum-integer form this is
`[m + n + 1] = [m + 1] [n + 1] - [m] [n]`. -/
theorem S_add (m n : ℤ) : S R (m + n) = S R m * S R n - S R (m - 1) * S R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp [S_add_one, mul_comm]
  | add_two n ih1 ih2 =>
    have h₁ := S_add_two R (m + n)
    have h₂ := S_add_two R n
    have h₃ := S_add_two R (n - 1)
    linear_combination (norm := ring_nf)
      h₁ - S R m * h₂ + S R (m - 1) * h₃ + (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_add_two R (m - n - 1)
    have h₂ := S_add_two R (-n - 1)
    have h₃ := S_add_two R (-n - 2)
    linear_combination (norm := ring_nf)
      h₁ - S R m * h₂ + S R (m - 1) * h₃ + (X : R[X]) * ih1 - ih2

/-- The product of a rescaled Chebyshev polynomial of the first kind with one of the second kind:
`Cₘ Sₙ = S_{n+m} + S_{n-m}`. -/
theorem C_mul_S (m n : ℤ) : C R m * S R n = S R (n + m) + S R (n - m) := by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => rw [C_one, S_add_one]; ring
  | add_two m ih1 ih2 =>
    have h₁ := C_add_two R m
    have h₂ := S_add_two R (n + m)
    have h₃ := S_sub_two R (n - m)
    linear_combination (norm := ring_nf) S R n * h₁ - h₂ - h₃ + (X : R[X]) * ih1 - ih2
  | neg_add_one m ih1 ih2 =>
    have h₁ := C_add_two R (-m - 1)
    have h₂ := S_add_two R (n - m - 1)
    have h₃ := S_sub_two R (n + m + 1)
    linear_combination (norm := ring_nf) S R n * h₁ - h₂ - h₃ + (X : R[X]) * ih1 - ih2

/-- **Multiplication formula** for the rescaled Chebyshev polynomials of the second kind:
`S_{mn-1} = S_{m-1} · (S_{n-1} ∘ Cₘ)`. In quantum-integer form, since
`Cₘ(u + u⁻¹) = uᵐ + u⁻ᵐ`, this is `[mn]_u = [m]_u [n]_{uᵐ}`. -/
theorem S_mul_sub_one (m n : ℤ) : S R (m * n - 1) = S R (m - 1) * (S R (n - 1)).comp (C R m) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := congr(comp $(S_add_two R (n - 1)) (C R m))
    simp only [sub_comp, mul_comp, X_comp] at h₁
    have h₂ := C_mul_S R m (m * (n + 1) - 1)
    linear_combination (norm := ring_nf) -S R (m - 1) * h₁ - h₂ + C R m * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := congr(comp $(S_add_two R (-n - 2)) (C R m))
    simp only [sub_comp, mul_comp, X_comp] at h₁
    have h₂ := C_mul_S R m (-(m * n) - 1)
    linear_combination (norm := ring_nf) -S R (m - 1) * h₁ - h₂ + C R m * ih1 - ih2

/-- **Divisibility** of the rescaled Chebyshev polynomials of the second kind: if `m ∣ n` then
`S_{m-1} ∣ S_{n-1}`. In quantum-integer form, `[m] ∣ [n]` whenever `m ∣ n`. -/
theorem S_sub_one_dvd_S_sub_one {m n : ℤ} (h : m ∣ n) : S R (m - 1) ∣ S R (n - 1) := by
  obtain ⟨k, rfl⟩ := h
  exact Dvd.intro _ (S_mul_sub_one R m k).symm

end Polynomial.Chebyshev
