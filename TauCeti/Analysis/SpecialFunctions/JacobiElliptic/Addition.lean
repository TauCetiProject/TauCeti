/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.JacobiElliptic.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination

/-!
# The addition theorem for the Jacobi elliptic functions

For a modulus `k` with `k ^ 2 < 1`, we prove the addition theorem for the real Jacobi elliptic
functions (DLMF 22.8.1–22.8.3): writing `D = 1 - k² sn²(u) sn²(v)`,

* `sn(u + v) = (sn u · cn v · dn v + sn v · cn u · dn u) / D`;
* `cn(u + v) = (cn u · cn v - sn u · dn u · sn v · dn v) / D`;
* `dn(u + v) = (dn u · dn v - k² · sn u · cn u · sn v · cn v) / D`,

together with the positivity of the common denominator `D`.

## Implementation notes

The proof is Euler's: fix `a = u + v` and regard each right-hand side as a function of `t = u`,
with `v = a - t`. The derivatives `sn′ = cn dn`, `cn′ = -sn dn`, `dn′ = -k² sn cn` and the
identities `sn² + cn² = 1`, `dn² + k² sn² = 1` show that its derivative vanishes, so it is
constant in `t`; its value at `t = 0` is the left-hand side.

## References

* NIST *Digital Library of Mathematical Functions*, §22.8, <https://dlmf.nist.gov/22.8>.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §22.2.
-/

public section

namespace TauCeti.Real

open _root_.Real

/-- The denominator `1 - k² sn²(u) sn²(v)` of the addition theorem is positive for `k ^ 2 < 1`. -/
theorem one_sub_sq_mul_jacobiSn_sq_mul_jacobiSn_sq_pos {k : ℝ} (hk : k ^ 2 < 1) (u v : ℝ) :
    0 < 1 - k ^ 2 * jacobiSn k u ^ 2 * jacobiSn k v ^ 2 := by
  have h : k ^ 2 * jacobiSn k u ^ 2 * jacobiSn k v ^ 2 ≤ k ^ 2 := by
    rw [mul_assoc, jacobiSn_def, jacobiSn_def]
    exact mul_le_of_le_one_right (sq_nonneg k)
      ((mul_le_of_le_one_left (sq_nonneg _) (sin_sq_le_one _)).trans (sin_sq_le_one _))
  linarith

/-! ### Euler's argument -/

section Euler

variable {k : ℝ} (hk : k ^ 2 < 1) (a : ℝ)

include hk

private theorem hasDerivAt_jacobiSn_const_sub (t : ℝ) :
    HasDerivAt (fun t ↦ jacobiSn k (a - t)) (-(jacobiCn k (a - t) * jacobiDn k (a - t))) t :=
  (hasDerivAt_jacobiSn hk (a - t)).comp_const_sub a t

private theorem hasDerivAt_jacobiCn_const_sub (t : ℝ) :
    HasDerivAt (fun t ↦ jacobiCn k (a - t)) (-(-jacobiSn k (a - t) * jacobiDn k (a - t))) t :=
  (hasDerivAt_jacobiCn hk (a - t)).comp_const_sub a t

private theorem hasDerivAt_jacobiDn_const_sub (t : ℝ) :
    HasDerivAt (fun t ↦ jacobiDn k (a - t))
      (-(-k ^ 2 * jacobiSn k (a - t) * jacobiCn k (a - t))) t :=
  (hasDerivAt_jacobiDn hk (a - t)).comp_const_sub a t

/-- Euler's argument: let `N` be a differentiable function of `t` whose derivative `N'` satisfies
`N' D = N D'`, where `D(t) = 1 - k² sn²(t) sn²(a - t)`. Then `N / D` is constant, equal to its
value `N 0` at `t = 0`. -/
private theorem div_eq_of_hasDerivAt {N N' : ℝ → ℝ} (hN : ∀ t, HasDerivAt N (N' t) t)
    (h : ∀ t, N' t * (1 - k ^ 2 * jacobiSn k t ^ 2 * jacobiSn k (a - t) ^ 2) =
      N t * (-2 * k ^ 2 * jacobiSn k t * jacobiSn k (a - t) *
        (jacobiSn k (a - t) * jacobiCn k t * jacobiDn k t -
          jacobiSn k t * jacobiCn k (a - t) * jacobiDn k (a - t))))
    (t : ℝ) :
    N t / (1 - k ^ 2 * jacobiSn k t ^ 2 * jacobiSn k (a - t) ^ 2) = N 0 := by
  have hD : ∀ t, HasDerivAt (fun t ↦ 1 - k ^ 2 * jacobiSn k t ^ 2 * jacobiSn k (a - t) ^ 2)
      (-2 * k ^ 2 * jacobiSn k t * jacobiSn k (a - t) *
        (jacobiSn k (a - t) * jacobiCn k t * jacobiDn k t -
          jacobiSn k t * jacobiCn k (a - t) * jacobiDn k (a - t))) t := fun t ↦ by
    have := ((((hasDerivAt_jacobiSn hk t).fun_pow 2).const_mul (k ^ 2)).fun_mul
      ((hasDerivAt_jacobiSn_const_sub hk a t).fun_pow 2)).const_sub 1
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have hQ : ∀ t, HasDerivAt (fun t ↦ N t / (1 - k ^ 2 * jacobiSn k t ^ 2 *
      jacobiSn k (a - t) ^ 2)) 0 t := fun t ↦ by
    have := (hN t).fun_div (hD t) (one_sub_sq_mul_jacobiSn_sq_mul_jacobiSn_sq_pos hk t _).ne'
    rwa [h t, sub_self, zero_div] at this
  have := is_const_of_deriv_eq_zero (fun t ↦ (hQ t).differentiableAt) (fun t ↦ (hQ t).deriv) t 0
  simpa using this

end Euler

/-! ### The addition theorem -/

/-- **The addition theorem for `sn`** (DLMF 22.8.1):
`sn(u + v) = (sn u · cn v · dn v + sn v · cn u · dn u) / (1 - k² sn²(u) sn²(v))`. -/
theorem jacobiSn_add {k : ℝ} (hk : k ^ 2 < 1) (u v : ℝ) :
    jacobiSn k (u + v) =
      (jacobiSn k u * jacobiCn k v * jacobiDn k v + jacobiSn k v * jacobiCn k u * jacobiDn k u) /
        (1 - k ^ 2 * jacobiSn k u ^ 2 * jacobiSn k v ^ 2) := by
  set a := u + v
  have h := div_eq_of_hasDerivAt hk a (N := fun t ↦
      jacobiSn k t * jacobiCn k (a - t) * jacobiDn k (a - t) +
        jacobiSn k (a - t) * jacobiCn k t * jacobiDn k t)
    (fun t ↦ (((hasDerivAt_jacobiSn hk t).fun_mul (hasDerivAt_jacobiCn_const_sub hk a t)).fun_mul
      (hasDerivAt_jacobiDn_const_sub hk a t)).fun_add
      (((hasDerivAt_jacobiSn_const_sub hk a t).fun_mul (hasDerivAt_jacobiCn hk t)).fun_mul
        (hasDerivAt_jacobiDn hk t)))
    (fun t ↦ by
      have hc₁ := jacobiSn_sq_add_jacobiCn_sq k t
      have hd₁ := jacobiDn_sq_add_sq_mul_jacobiSn_sq hk.le t
      have hc₂ := jacobiSn_sq_add_jacobiCn_sq k (a - t)
      have hd₂ := jacobiDn_sq_add_sq_mul_jacobiSn_sq hk.le (a - t)
      generalize jacobiSn k t = s₁, jacobiCn k t = c₁, jacobiDn k t = d₁,
        jacobiSn k (a - t) = s₂, jacobiCn k (a - t) = c₂, jacobiDn k (a - t) = d₂ at *
      linear_combination s₁ * s₂ *
        ((1 - k ^ 2 * s₁ ^ 2 * s₂ ^ 2 - 2 * k ^ 2 * s₁ ^ 2 * c₂ ^ 2) * hd₂ +
          k ^ 2 * (1 - k ^ 2 * s₁ ^ 2 * s₂ ^ 2 - 2 * s₁ ^ 2 * (1 - k ^ 2 * s₂ ^ 2)) * hc₂ -
          (1 - k ^ 2 * s₁ ^ 2 * s₂ ^ 2 - 2 * k ^ 2 * s₂ ^ 2 * c₁ ^ 2) * hd₁ -
          k ^ 2 * (1 - k ^ 2 * s₁ ^ 2 * s₂ ^ 2 - 2 * s₂ ^ 2 * (1 - k ^ 2 * s₁ ^ 2)) * hc₁))
    u
  simp only [a, add_sub_cancel_left, sub_zero, jacobiSn_zero, jacobiCn_zero, jacobiDn_zero,
    zero_mul, mul_one, zero_add] at h
  exact h.symm

/-- **The addition theorem for `cn`** (DLMF 22.8.2):
`cn(u + v) = (cn u · cn v - sn u · dn u · sn v · dn v) / (1 - k² sn²(u) sn²(v))`. -/
theorem jacobiCn_add {k : ℝ} (hk : k ^ 2 < 1) (u v : ℝ) :
    jacobiCn k (u + v) =
      (jacobiCn k u * jacobiCn k v - jacobiSn k u * jacobiDn k u * jacobiSn k v * jacobiDn k v) /
        (1 - k ^ 2 * jacobiSn k u ^ 2 * jacobiSn k v ^ 2) := by
  set a := u + v
  have h := div_eq_of_hasDerivAt hk a (N := fun t ↦
      jacobiCn k t * jacobiCn k (a - t) -
        jacobiSn k t * jacobiDn k t * jacobiSn k (a - t) * jacobiDn k (a - t))
    (fun t ↦ ((hasDerivAt_jacobiCn hk t).fun_mul (hasDerivAt_jacobiCn_const_sub hk a t)).fun_sub
      ((((hasDerivAt_jacobiSn hk t).fun_mul (hasDerivAt_jacobiDn hk t)).fun_mul
        (hasDerivAt_jacobiSn_const_sub hk a t)).fun_mul (hasDerivAt_jacobiDn_const_sub hk a t)))
    (fun t ↦ by
      have hc₁ := jacobiSn_sq_add_jacobiCn_sq k t
      have hd₁ := jacobiDn_sq_add_sq_mul_jacobiSn_sq hk.le t
      have hc₂ := jacobiSn_sq_add_jacobiCn_sq k (a - t)
      have hd₂ := jacobiDn_sq_add_sq_mul_jacobiSn_sq hk.le (a - t)
      generalize jacobiSn k t = s₁, jacobiCn k t = c₁, jacobiDn k t = d₁,
        jacobiSn k (a - t) = s₂, jacobiCn k (a - t) = c₂, jacobiDn k (a - t) = d₂ at *
      linear_combination
        (1 + k ^ 2 * s₁ ^ 2 * s₂ ^ 2) * (s₁ * c₂ * d₁ * hd₂ - s₂ * c₁ * d₂ * hd₁) +
          2 * k ^ 2 * s₁ * s₂ ^ 2 * c₂ * d₁ * hc₁ - 2 * k ^ 2 * s₁ ^ 2 * s₂ * c₁ * d₂ * hc₂)
    u
  simp only [a, add_sub_cancel_left, sub_zero, jacobiSn_zero, jacobiCn_zero, jacobiDn_zero,
    zero_mul, mul_one, one_mul] at h
  exact h.symm

/-- **The addition theorem for `dn`** (DLMF 22.8.3):
`dn(u + v) = (dn u · dn v - k² · sn u · cn u · sn v · cn v) / (1 - k² sn²(u) sn²(v))`. -/
theorem jacobiDn_add {k : ℝ} (hk : k ^ 2 < 1) (u v : ℝ) :
    jacobiDn k (u + v) =
      (jacobiDn k u * jacobiDn k v -
          k ^ 2 * jacobiSn k u * jacobiCn k u * jacobiSn k v * jacobiCn k v) /
        (1 - k ^ 2 * jacobiSn k u ^ 2 * jacobiSn k v ^ 2) := by
  set a := u + v
  have h := div_eq_of_hasDerivAt hk a (N := fun t ↦
      jacobiDn k t * jacobiDn k (a - t) -
        k ^ 2 * jacobiSn k t * jacobiCn k t * jacobiSn k (a - t) * jacobiCn k (a - t))
    (fun t ↦ ((hasDerivAt_jacobiDn hk t).fun_mul (hasDerivAt_jacobiDn_const_sub hk a t)).fun_sub
      (((((hasDerivAt_jacobiSn hk t).const_mul (k ^ 2)).fun_mul (hasDerivAt_jacobiCn hk t)).fun_mul
        (hasDerivAt_jacobiSn_const_sub hk a t)).fun_mul (hasDerivAt_jacobiCn_const_sub hk a t)))
    (fun t ↦ by
      have hc₁ := jacobiSn_sq_add_jacobiCn_sq k t
      have hd₁ := jacobiDn_sq_add_sq_mul_jacobiSn_sq hk.le t
      have hc₂ := jacobiSn_sq_add_jacobiCn_sq k (a - t)
      have hd₂ := jacobiDn_sq_add_sq_mul_jacobiSn_sq hk.le (a - t)
      generalize jacobiSn k t = s₁, jacobiCn k t = c₁, jacobiDn k t = d₁,
        jacobiSn k (a - t) = s₂, jacobiCn k (a - t) = c₂, jacobiDn k (a - t) = d₂ at *
      linear_combination
        k ^ 2 * (1 + k ^ 2 * s₁ ^ 2 * s₂ ^ 2) * (s₁ * c₁ * d₂ * hc₂ - s₂ * c₂ * d₁ * hc₁) +
          2 * k ^ 2 * s₁ * s₂ ^ 2 * c₁ * d₂ * hd₁ - 2 * k ^ 2 * s₁ ^ 2 * s₂ * c₂ * d₁ * hd₂)
    u
  simp only [a, add_sub_cancel_left, sub_zero, jacobiSn_zero, jacobiCn_zero, jacobiDn_zero,
    zero_mul, mul_zero, mul_one, one_mul] at h
  exact h.symm

end TauCeti.Real
