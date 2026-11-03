/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Orthogonality of the sine system on `[0, π]`

The functions `θ ↦ sin (k θ)`, for `k` a positive natural number, are pairwise orthogonal on the
interval `[0, π]`, each of square norm `π / 2`:

`∫₀^π sin (m θ) · sin (n θ) dθ = (π / 2) · δ_{mn}`.

This file proves that identity for all integer frequencies, where the sign-reversed mode `-m`
contributes a second Kronecker delta, and its normalized form, in which the system
`√(2/π) · sin (k ·)` is orthonormal. The key computation is the single-mode integral
`∫₀^π cos (k θ) dθ = 0` for a nonzero integer `k`, combined with the product-to-sum identity
`2 sin x sin y = cos (x - y) - cos (x + y)`.

The cosine counterpart is recorded in the Chebyshev vocabulary, as
`TauCeti.integral_chebyshevCosine_mul_chebyshevCosine_eq_ite`
(`TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Cosine/Transfer.lean`), whose
single-mode integrals are read off `TauCeti.integral_cos_int_mul` below. The two families are
stated separately because the sine system has square norm `π / 2` in *every* degree, while the
degree-`0` cosine mode has square norm `π`.

## Main results

* `TauCeti.integral_cos_int_mul`: `∫₀^π cos (k θ) dθ` is `π` when the integer `k` is zero and `0`
  otherwise.
* `TauCeti.integral_sin_int_mul_mul_sin_int_mul`: the orthogonality relation
  `∫₀^π sin (m θ) sin (n θ) dθ = (π / 2) · (δ_{m,n} - δ_{m,-n})` for all integers `m` and `n`.
* `TauCeti.integral_sin_succ_mul_sin_succ`: the same relation indexed by the positive frequencies
  `m + 1`, where the right-hand side is a plain Kronecker delta, and
  `TauCeti.two_div_pi_mul_integral_sin_succ_mul_sin_succ`, its normalized restatement
  `(2/π) ∫₀^π sin ((m+1) θ) sin ((n+1) θ) dθ = δ_{mn}`, to which the character orthonormality
  of `SU(2)` reduces (`TauCeti/RepresentationTheory/SU2/Weyl/Orthogonality.lean`).

## References

The sine system on `[0, π]` is the classical Fourier sine basis; see for instance
E. M. Stein, R. Shakarchi, *Fourier Analysis: An Introduction*, Princeton (2003), Chapter 2.
-/

public section

namespace TauCeti

/-- `∫₀^π cos (k θ) dθ` for an integer `k`: it is `π` in degree `0`, and vanishes otherwise. -/
theorem integral_cos_int_mul (k : ℤ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * θ) = if k = 0 then Real.pi else 0 := by
  split_ifs with hk
  · simp [hk]
  · simp [intervalIntegral.integral_comp_mul_left _ (Int.cast_ne_zero.mpr hk : (k : ℝ) ≠ 0),
      Real.sin_int_mul_pi]

/-- **Orthogonality of the sine system on `[0, π]`.** For integers `m` and `n`,
`∫₀^π sin (m θ) sin (n θ) dθ = (π / 2) · (δ_{m,n} - δ_{m,-n})`.

Since `θ ↦ sin (k θ)` is odd in `k`, the frequencies `m` and `-m` give the same mode up to sign;
for `m = n = 0` the two Kronecker deltas cancel, matching the identically vanishing integrand. -/
theorem integral_sin_int_mul_mul_sin_int_mul (m n : ℤ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ)
      = (if m = n then Real.pi / 2 else 0) - if m = -n then Real.pi / 2 else 0 := by
  -- Product to sum: `2 sin (m θ) sin (n θ) = cos ((m - n) θ) - cos ((m + n) θ)`.
  have hprod (θ : ℝ) : Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ)
      = Real.cos (((m - n : ℤ) : ℝ) * θ) / 2 - Real.cos (((m + n : ℤ) : ℝ) * θ) / 2 := by
    push_cast
    rw [sub_mul, add_mul, ← sub_div, ← Real.two_mul_sin_mul_sin]
    ring
  simp only [hprod]
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _)
      ((by fun_prop : Continuous _).intervalIntegrable _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_cos_int_mul, integral_cos_int_mul]
  simp only [sub_eq_zero, add_eq_zero_iff_eq_neg]
  split_ifs <;> ring

/-- The sine system indexed by its positive frequencies `m + 1`, where the sign-reversed mode of
`TauCeti.integral_sin_int_mul_mul_sin_int_mul` is out of range and the right-hand side is a plain
Kronecker delta: `∫₀^π sin ((m+1) θ) sin ((n+1) θ) dθ = (π / 2) · δ_{mn}`. -/
theorem integral_sin_succ_mul_sin_succ (m n : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = if m = n then Real.pi / 2 else 0 := by
  have h := integral_sin_int_mul_mul_sin_int_mul (m + 1) (n + 1)
  push_cast at h
  rw [h, ite_eq_right (by omega : ¬((m : ℤ) + 1 = -((n : ℤ) + 1))), sub_zero]
  exact if_congr (by omega) rfl rfl

/-- **The sine system, normalized.** With the `2/π` normalization the family
`√(2/π) · sin ((m+1) ·)` is orthonormal on `[0, π]`:
`(2/π) ∫₀^π sin ((m+1) θ) sin ((n+1) θ) dθ = δ_{mn}`.

This is the form the character orthonormality of `SU(2)` reduces to, and
`TauCeti.SU2.character_symPower_orthonormal_torusExp`
(`TauCeti/RepresentationTheory/SU2/Weyl/Orthogonality.lean`) is proved by rewriting with it. -/
theorem two_div_pi_mul_integral_sin_succ_mul_sin_succ (m n : ℕ) :
    2 / Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = if m = n then 1 else 0 := by
  rw [integral_sin_succ_mul_sin_succ]
  split_ifs <;> simp [field]

end TauCeti
