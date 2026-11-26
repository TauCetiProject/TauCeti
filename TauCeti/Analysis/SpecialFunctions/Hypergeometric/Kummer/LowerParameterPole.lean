/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Transformation

/-!
# The regularized Kummer function at a nonpositive integer lower parameter

Olver's regularized Kummer function `𝐌(a, b, z) = ∑ (a)ₖ zᵏ / (k! Γ(b + k))` is Mathlib's
`Complex.regularizedHGFun {a} {b} z`. With Mathlib's convention `(Γ(-m))⁻¹ = 0`, it is defined at
every lower parameter `b`, including the poles `b = -n` of `Γ(b)`, where the unregularized function
`M(a, b, z) = Γ(b) 𝐌(a, b, z)` is not. There the first `n + 1` terms of the series vanish, and the
remaining ones reassemble into a second Kummer function (DLMF 13.2.5):

`𝐌(a, -n, z) = (a)ₙ₊₁ zⁿ⁺¹ 𝐌(a + n + 1, n + 2, z)`

for every natural `n` and all complex `a`, `z`. DLMF states the left side as the limit of
`M(a, b, z) / Γ(b)` as `b → -n`; that limit is the value at `-n` of the function `𝐌(a, ·, z)`, which
is continuous because it is entire in `b`.

This identity is what makes Tricomi's bracket
`𝐌(a, b, z) / Γ(a - b + 1) - z^{1 - b} 𝐌(a - b + 1, 2 - b, z) / Γ(a)` vanish at integer `b`,
so that Tricomi's function `U(a, b, z)` extends holomorphically across the integers.

## Main results

* `Complex.regularizedHGFun_singleton_neg_natCast_right` — DLMF 13.2.5.
* `Complex.regularizedHGFun_one_singleton_zero` — its case `a = 1`, `n = 0`:
  `𝐌(1, 0, z) = z e^z`.

## References

* NIST Digital Library of Mathematical Functions, 13.2.5, <https://dlmf.nist.gov/13.2.E5>.
* R. Beals and R. Wong, *Special Functions: A Graduate Text*, Cambridge University Press, 2010,
  (6.3.1).
-/

public section

noncomputable section

open Finset Polynomial
open scoped Nat

namespace Complex

/-- The coefficient identity behind DLMF 13.2.5: the `(m + n + 1)`-th coefficient of the series of
`𝐌(a, -n, ·)` is `(a)ₙ₊₁` times the `m`-th coefficient of the series of `𝐌(a + n + 1, n + 2, ·)`. -/
private theorem regularizedHGFunCoeff_singleton_neg_natCast_add (a : ℂ) (n m : ℕ) :
    regularizedHGFunCoeff {a} {-(n : ℂ)} (m + (n + 1)) =
      (ascPochhammer ℂ (n + 1)).eval a * regularizedHGFunCoeff {a + n + 1} {(n : ℂ) + 2} m := by
  have hpoch : (ascPochhammer ℂ (m + (n + 1))).eval a =
      (ascPochhammer ℂ (n + 1)).eval a * (ascPochhammer ℂ m).eval (a + n + 1) := by
    rw [add_comm m, ← ascPochhammer_mul]
    simp [add_assoc]
  have hl : -(n : ℂ) + ((m + (n + 1) : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hr : (n : ℂ) + 2 + (m : ℂ) = ((m + (n + 1) : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton, hl, hr, hpoch,
    Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
  ring

/-- **DLMF 13.2.5.** At the pole `b = -n` of `Γ(b)`, the regularized Kummer function is
`𝐌(a, -n, z) = (a)ₙ₊₁ zⁿ⁺¹ 𝐌(a + n + 1, n + 2, z)`, for every natural `n` and all complex `a`
and `z`. -/
theorem regularizedHGFun_singleton_neg_natCast_right (a z : ℂ) (n : ℕ) :
    regularizedHGFun {a} {-(n : ℂ)} z =
      (ascPochhammer ℂ (n + 1)).eval a * z ^ (n + 1) *
        regularizedHGFun {a + n + 1} {(n : ℂ) + 2} z := by
  have h := hasSum_regularizedHGFun (a := {a}) (b := {-(n : ℂ)}) (by simp) z
  rw [← hasSum_nat_add_iff' (n + 1)] at h
  -- The first `n + 1` terms vanish, since `Γ(-n + k)` has a pole for `k ≤ n`.
  have hzero : ∑ k ∈ range (n + 1), regularizedHGFunCoeff {a} {-(n : ℂ)} k * z ^ k = 0 :=
    sum_eq_zero fun k hk => by
      rw [regularizedHGFunCoeff_eq_zero_right {a} {-(n : ℂ)} k (n - k)
        (by
          rw [Multiset.mem_singleton, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
          ring), zero_mul]
  rw [hzero, sub_zero] at h
  refine h.unique ?_
  convert (hasSum_regularizedHGFun (a := {a + n + 1}) (b := {(n : ℂ) + 2}) (by simp)
    z).mul_left ((ascPochhammer ℂ (n + 1)).eval a * z ^ (n + 1)) using 2 with m
  rw [regularizedHGFunCoeff_singleton_neg_natCast_add, pow_add]
  ring

/-- The case `a = 1`, `n = 0` of DLMF 13.2.5: `𝐌(1, 0, z) = z e^z`. Here
`𝐌(1, 0, z) = ∑_{k ≥ 1} zᵏ / (k - 1)!`, whose `k = 0` term vanishes. -/
@[simp]
theorem regularizedHGFun_one_singleton_zero (z : ℂ) :
    regularizedHGFun {1} {0} z = z * exp z := by
  have h : regularizedHGFun {1} {0} z = z * regularizedHGFun {2} {2} z := by
    simpa [one_add_one_eq_two] using regularizedHGFun_singleton_neg_natCast_right 1 z 0
  rw [h, regularizedHGFun_singleton_self]
  simp

end Complex
