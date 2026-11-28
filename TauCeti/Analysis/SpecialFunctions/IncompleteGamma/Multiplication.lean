/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower

/-!
# The multiplication theorem of the lower incomplete Gamma function

The multiplication theorem DLMF 8.15.1,
`γ(a, λx) = λ^a ∑ₖ γ(a + k, x) (1 − λ)ᵏ / k!`. It follows from its entire counterpart for
Tricomi's function `γ*` (`Complex.hasSum_tricomiIncompleteGamma_mul`), the Taylor expansion of
the entire function `γ*(a, ·)`, through `γ(a, z) = Γ(a) z^a γ*(a, z)`.

## Main results

* `Complex.hasSum_lowerIncompleteGamma_mul`: **DLMF 8.15.1**,
  `γ(a, λx) = λ^a ∑ₖ γ(a + k, x) (1 − λ)ᵏ / k!` with the principal power, for `a ∉ −ℕ`,
  real `x ≥ 0` and every complex `λ`.

## Implementation notes

The multiplier `λ` of DLMF is the variable `t` here, since `λ` is reserved in Lean. DLMF
states 8.15.1 for `λ` in the slit plane and `x > 0`. With the principal power the identity holds
for every complex `λ` and every `x ≥ 0`, since `(λx)^a = λ^a x^a` for real `x ≥ 0`; the series
converges for every `λ` because `γ*(a, ·)` is entire. The hypothesis `a ∉ −ℕ` cannot be dropped:
at `a = −n` the left side is Mathlib's junk value `0`, while the terms with `k > n` on the right
are not.

## References

* NIST Digital Library of Mathematical Functions, §8.15, <https://dlmf.nist.gov/8.15>.

The proof follows lean-DLMF's `lowerIncompleteGamma_multiplication_hasSum` (file
`DLMF/IncompleteGamma/IntegralTransforms.lean` of <https://github.com/bjbraams/lean-DLMF>), the
Taylor expansion of `γ*(a, ·)`, restated with principal powers in place of lean-DLMF's
logarithmic coordinates.
-/

public section

noncomputable section

open scoped Nat

namespace Complex

/-- **DLMF 8.15.1**, the multiplication theorem for the lower incomplete Gamma function:
`γ(a, tx) = t^a ∑ₖ γ(a + k, x) (1 − t)ᵏ / k!` with the principal power `t^a`, for `a ∉ −ℕ`,
real `x ≥ 0` and every complex `t` (DLMF's `λ`). -/
theorem hasSum_lowerIncompleteGamma_mul {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) {x : ℝ} (hx : 0 ≤ x)
    (t : ℂ) :
    HasSum (fun k : ℕ => t ^ a * lowerIncompleteGamma (a + k) x * (1 - t) ^ k / k !)
      (lowerIncompleteGamma a (t * x)) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have h := (hasSum_tricomiIncompleteGamma_mul a x t).mul_left (Gamma a * t ^ a * (x : ℂ) ^ a)
  have hp : (t * x) ^ a = t ^ a * (x : ℂ) ^ a := by
    rw [mul_comm, ofReal_mul_cpow hx.le, mul_comm]
  rw [lowerIncompleteGamma_def, regularizedGamma_def, hp, ← mul_assoc, ← mul_assoc]
  refine h.congr_fun fun k => ?_
  rw [lowerIncompleteGamma_def, regularizedGamma_def,
    Gamma_add_natCast_eq_ascPochhammer_eval_mul ha, cpow_add _ _ hx0, cpow_natCast]
  ring

end Complex
