/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.JointAnalytic
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Connection

/-!
# The integral of the first kind as a function of `sin φ`

For a complex modulus `k`, Carlson's form of the incomplete integral of the first kind as a
function of `x = sin φ` is

`g(x) = x R_F(1 - x², 1 - k² x², 1)`,

defined on the domain `D_k = {x | 1 - x² ∈ slitPlane, 1 - k² x² ∈ slitPlane}`. For real
`|φ| ≤ π / 2` and `k² sin² φ < 1`, `g(sin φ) = F(φ, k)`
(`TauCeti.Real.ofReal_legendreF_eq_carlsonRF`). This file proves that `g` is a primitive of
`(1 - x²)^(-1/2) (1 - k² x²)^(-1/2)` on `D_k` (DLMF 19.25.33 with `p = n`, and 22.15.11 for real
arguments), which is the differential equation of the inverse of Jacobi's `sn(·, k)`, and that
`D_k` is open and star-shaped about `0`, the setting for the identity theorem on `D_k`.

By the chain rule `HasDerivAt.carlsonRF`, `g′(x)` is `R_F(1 - x², 1 - k² x², 1)` plus `1/3` of
`S = x² (R_D(1 - k² x², 1, 1 - x²) + k² R_D(1 - x², 1, 1 - k² x²))`. The connection formula
`Complex.sub_mul_carlsonRD_add_sub_mul_carlsonRD` (DLMF 19.21.8) at `(1 - x², 1, 1 - k² x²)`
evaluates `S` as `3 (1 - x²)^(-1/2) (1 - k² x²)^(-1/2) - 3 R_F(1 - x², 1 - k² x², 1)`.

## Main results

* `Complex.hasDerivAt_mul_carlsonRF`: `g′(x) = (1 - x²)^(-1/2) (1 - k² x²)^(-1/2)` on `D_k`.
* `Complex.analyticOnNhd_mul_carlsonRF`: `g` is holomorphic on `D_k`.
* `Complex.isOpen_setOf_one_sub_sq_mem_slitPlane_and_one_sub_mul_sq_mem_slitPlane`,
  `Complex.starConvex_setOf_one_sub_sq_mem_slitPlane_and_one_sub_mul_sq_mem_slitPlane`: `D_k` is
  open and star-shaped about `0`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.25(v) and §22.15(ii),
  <https://dlmf.nist.gov/19.25.v> and <https://dlmf.nist.gov/22.15.ii>.
* D. F. Lawden, *Elliptic Functions and Applications*, Springer, 1989, §8.14.
-/

public section

open Set

namespace Complex

/-- **The integral of the first kind as a function of `sin φ`** has derivative
`(1 - x²)^(-1/2) (1 - k² x²)^(-1/2)` (DLMF 19.25.33 with `p = n`): for every complex `k` and every
`x` with `1 - x²` and `1 - k² x²` in the slit plane, `x ↦ x R_F(1 - x², 1 - k² x², 1)` has this
derivative at `x`. -/
theorem hasDerivAt_mul_carlsonRF {k x : ℂ} (hx : 1 - x ^ 2 ∈ slitPlane)
    (hkx : 1 - k ^ 2 * x ^ 2 ∈ slitPlane) :
    HasDerivAt (fun y ↦ y * carlsonRF (1 - y ^ 2) (1 - k ^ 2 * y ^ 2) 1)
      ((1 - x ^ 2) ^ (-1 / 2 : ℂ) * (1 - k ^ 2 * x ^ 2) ^ (-1 / 2 : ℂ)) x := by
  have ha : HasDerivAt (fun y : ℂ ↦ 1 - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have hb : HasDerivAt (fun y : ℂ ↦ 1 - k ^ 2 * y ^ 2) (-(k ^ 2 * (2 * x))) x := by
    simpa using (((hasDerivAt_pow 2 x).const_mul (k ^ 2)).const_sub 1)
  have hR := (hasDerivAt_id x).mul
    (ha.carlsonRF hb (hasDerivAt_const x (1 : ℂ)) hx hkx one_mem_slitPlane)
  refine hR.congr_deriv ?_
  have hconn := sub_mul_carlsonRD_add_sub_mul_carlsonRD hx (Or.inl one_mem_slitPlane) hkx
  rw [carlsonRF_comm_right, carlsonRD_comm 1, one_cpow, one_mul] at hconn
  have hexp : (-1 / 2 : ℂ) = -(1 / 2) := by norm_num
  rw [hexp]
  simp only [id_eq, one_mul]
  linear_combination (-1 / 3 : ℂ) * hconn

/-- The domain `{x | 1 - x² ∈ slitPlane, 1 - k² x² ∈ slitPlane}` of
`x ↦ x R_F(1 - x², 1 - k² x², 1)` is open. -/
theorem isOpen_setOf_one_sub_sq_mem_slitPlane_and_one_sub_mul_sq_mem_slitPlane (k : ℂ) :
    IsOpen {x : ℂ | 1 - x ^ 2 ∈ slitPlane ∧ 1 - k ^ 2 * x ^ 2 ∈ slitPlane} :=
  (isOpen_slitPlane.preimage (by fun_prop)).inter (isOpen_slitPlane.preimage (by fun_prop))

/-- The domain `{x | 1 - x² ∈ slitPlane, 1 - k² x² ∈ slitPlane}` of
`x ↦ x R_F(1 - x², 1 - k² x², 1)` is star-shaped about `0`: if `x² ∉ [1, ∞)` and
`k² x² ∉ [1, ∞)`, the same holds for `t x` with `0 ≤ t ≤ 1`. -/
theorem starConvex_setOf_one_sub_sq_mem_slitPlane_and_one_sub_mul_sq_mem_slitPlane (k : ℂ) :
    StarConvex ℝ 0 {x : ℂ | 1 - x ^ 2 ∈ slitPlane ∧ 1 - k ^ 2 * x ^ 2 ∈ slitPlane} := by
  rw [starConvex_zero_iff]
  rintro x ⟨hx, hkx⟩ t ht₀ ht₁
  have ht : t ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg t, pow_le_one₀ ht₀ ht₁⟩
  have hsq : (t • x) ^ 2 = x ^ 2 * ((t ^ 2 : ℝ) : ℂ) := by
    rw [real_smul, ofReal_pow]
    ring
  refine ⟨?_, ?_⟩
  · rw [Set.mem_ofPred_eq, hsq]
    exact one_sub_mul_ofReal_mem_slitPlane hx ht
  · rw [hsq, ← mul_assoc]
    exact one_sub_mul_ofReal_mem_slitPlane hkx ht

/-- The integral of the first kind as a function of `sin φ`,
`x ↦ x R_F(1 - x², 1 - k² x², 1)`, is holomorphic on its domain
`{x | 1 - x² ∈ slitPlane, 1 - k² x² ∈ slitPlane}`. -/
theorem analyticOnNhd_mul_carlsonRF (k : ℂ) :
    AnalyticOnNhd ℂ (fun y ↦ y * carlsonRF (1 - y ^ 2) (1 - k ^ 2 * y ^ 2) 1)
      {x : ℂ | 1 - x ^ 2 ∈ slitPlane ∧ 1 - k ^ 2 * x ^ 2 ∈ slitPlane} :=
  DifferentiableOn.analyticOnNhd (fun _ hx ↦
    (hasDerivAt_mul_carlsonRF hx.1 hx.2).differentiableAt.differentiableWithinAt)
    (isOpen_setOf_one_sub_sq_mem_slitPlane_and_one_sub_mul_sq_mem_slitPlane k)

end Complex
