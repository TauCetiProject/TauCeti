/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The complex lower incomplete Gamma function

The regularized lower incomplete Gamma function `P(a, z) = z^a γ*(a, z)` (DLMF 8.2.6), with the
principal power, and the lower incomplete Gamma function `γ(a, z) = Γ(a) P(a, z)` (DLMF 8.2.4),
both defined through Tricomi's entire function `γ*` of
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi`.

## Main results

* `Complex.lowerIncompleteGamma_eq_integral`: DLMF 8.2.1, `γ(a, z) = z^a ∫₀¹ s^{a−1} e^{−zs} ds`
  for `0 < Re a`;
* `TauCeti.intervalIntegral_cpow_mul_exp_neg_mul`: DLMF 8.2.1 rescaled,
  `∫₀ˣ t^{a−1} e^{−rt} dt = r^{−a} γ(a, rx)` for `0 < Re a`, `r ≠ 0`, `0 ≤ x`;
* `Complex.tendsto_mul_lowerIncompleteGamma`: for `z ≠ 0`, `γ(·, z)` has simple poles at
  `a = −n` with residue `(−1)ⁿ/n!`, from the residue of `Γ`
  (`Complex.tendsto_add_natCast_mul_Gamma`);
* `Complex.differentiable_regularizedGamma_left`: for `z ≠ 0`, `P(·, z)` is entire;
* `Complex.differentiableAt_lowerIncompleteGamma_left`: `γ(·, z)` is holomorphic off `−ℕ`;
* `Complex.regularizedGamma_one_left`, `Complex.regularizedGamma_neg_natCast`,
  `Complex.regularizedGammaQ_neg_natCast`: `P(1, z) = 1 − e^{−z}`, and `P(−n, z) = 1`,
  `Q(−n, z) = 0` for `z ≠ 0` (DLMF 8.2.5, 8.4.12).

## Implementation notes

The functions live in the root `Complex` namespace, beside `Complex.tricomiIncompleteGamma`.
At the poles `a ∈ −ℕ`, `γ(a, z)` takes the value given by Mathlib's junk value `Γ(−n) = 0`.

## References

* NIST Digital Library of Mathematical Functions, §§8.2, 8.4, <https://dlmf.nist.gov/8.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/IncompleteGamma/ContinuedProperties.lean`, and restated on Tricomi's `γ*`.
The rescaled integral `TauCeti.intervalIntegral_cpow_mul_exp_neg_mul` has a new proof.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Topology

namespace Complex

/-- The regularized lower incomplete Gamma function `P(a, z) = z^a γ*(a, z)` (DLMF 8.2.6), with
the principal power. For fixed `z ≠ 0` it is entire in `a`. -/
def regularizedGamma (a z : ℂ) : ℂ :=
  z ^ a * tricomiIncompleteGamma a z

/-- The lower incomplete Gamma function `γ(a, z) = Γ(a) P(a, z)` (DLMF 8.2.4). At the poles
`a ∈ −ℕ` it takes Mathlib's junk value `Γ(−n) = 0`. -/
def lowerIncompleteGamma (a z : ℂ) : ℂ :=
  Gamma a * regularizedGamma a z

/-- The regularized upper incomplete Gamma function `Q(a, z) = 1 − P(a, z)` (DLMF 8.2.5). -/
def regularizedGammaQ (a z : ℂ) : ℂ :=
  1 - regularizedGamma a z

/-- DLMF 8.2.6: `P(a, z) = z^a γ*(a, z)`. -/
theorem regularizedGamma_def (a z : ℂ) :
    regularizedGamma a z = z ^ a * tricomiIncompleteGamma a z := (rfl)

/-- DLMF 8.2.4: `γ(a, z) = Γ(a) P(a, z)`. -/
theorem lowerIncompleteGamma_def (a z : ℂ) :
    lowerIncompleteGamma a z = Gamma a * regularizedGamma a z := (rfl)

/-- DLMF 8.2.5: `Q(a, z) = 1 − P(a, z)`. -/
theorem regularizedGammaQ_def (a z : ℂ) :
    regularizedGammaQ a z = 1 - regularizedGamma a z := (rfl)

/-- DLMF 8.2.5: `P(a, z) + Q(a, z) = 1`. -/
theorem regularizedGamma_add_regularizedGammaQ (a z : ℂ) :
    regularizedGamma a z + regularizedGammaQ a z = 1 := by
  rw [regularizedGammaQ]
  ring

/-- **DLMF 8.2.1**: `γ(a, z) = z^a ∫₀¹ s^{a−1} e^{−zs} ds` for `0 < Re a` and every `z`. -/
theorem lowerIncompleteGamma_eq_integral {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    lowerIncompleteGamma a z =
      z ^ a * ∫ s in (0 : ℝ)..1, (s : ℂ) ^ (a - 1) * cexp (-(z * s)) := by
  rw [lowerIncompleteGamma_def, regularizedGamma_def, tricomiIncompleteGamma_eq_integral ha]
  have hG := Gamma_ne_zero_of_re_pos ha
  field_simp

/-- For `z ≠ 0`, `P(·, z)` is entire. -/
theorem differentiable_regularizedGamma_left {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ fun a => regularizedGamma a z := fun a =>
  (differentiableAt_id.const_cpow (Or.inl hz)).mul
    (differentiable_tricomiIncompleteGamma_left z a)

/-- `γ(a, 0) = 0` for every `a`; at `a = 0` this is Mathlib's junk value `Γ(0) = 0`. -/
@[simp]
theorem lowerIncompleteGamma_zero_right (a : ℂ) : lowerIncompleteGamma a 0 = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [lowerIncompleteGamma_def]
  · simp [lowerIncompleteGamma_def, regularizedGamma_def, zero_cpow ha]

/-- `γ(·, z)` is holomorphic off the nonpositive integers. -/
theorem differentiableAt_lowerIncompleteGamma_left {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) (z : ℂ) :
    DifferentiableAt ℂ (fun a => lowerIncompleteGamma a z) a := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [lowerIncompleteGamma_zero_right]
    exact differentiableAt_const _
  · exact (differentiableAt_Gamma a ha).mul (differentiable_regularizedGamma_left hz a)

/-- `P(−n, z) = 1` for `z ≠ 0` (DLMF 8.4.12). -/
@[simp]
theorem regularizedGamma_neg_natCast (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGamma (-n) z = 1 := by
  rw [regularizedGamma_def, tricomiIncompleteGamma_neg_natCast, cpow_neg, cpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hz)]

/-- `Q(−n, z) = 0` for `z ≠ 0` (DLMF 8.2.5 and 8.4.12). -/
@[simp]
theorem regularizedGammaQ_neg_natCast (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGammaQ (-n) z = 0 := by
  rw [regularizedGammaQ_def, regularizedGamma_neg_natCast n hz, sub_self]

/-- `P(1, z) = 1 − e^{−z}` for every `z` (DLMF 8.4.1). -/
@[simp]
theorem regularizedGamma_one_left (z : ℂ) : regularizedGamma 1 z = 1 - cexp (-z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [regularizedGamma_def]
  · rw [regularizedGamma_def, tricomiIncompleteGamma_one_left hz, cpow_one]
    field_simp

/-- **The poles of `γ(·, z)`**: for `z ≠ 0`, `(a + n) γ(a, z) → (−1)ⁿ/n!` as `a → −n`. -/
theorem tendsto_mul_lowerIncompleteGamma (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun a => (a + n) * lowerIncompleteGamma a z) (𝓝[≠] (-n : ℂ))
      (𝓝 ((-1) ^ n / (n ! : ℂ))) := by
  have hP : Tendsto (fun a => regularizedGamma a z) (𝓝[≠] (-(n : ℂ))) (𝓝 1) := by
    rw [← regularizedGamma_neg_natCast n hz]
    exact ((differentiable_regularizedGamma_left hz).continuous.tendsto _).mono_left
      nhdsWithin_le_nhds
  simpa [lowerIncompleteGamma_def, mul_assoc] using (tendsto_add_natCast_mul_Gamma n).mul hP

end Complex

namespace TauCeti

open Complex Set

/-- DLMF 8.2.1 rescaled: `∫₀ˣ t^{a−1} e^{−rt} dt = r^{−a} γ(a, rx)` for `0 < Re a`, `r ≠ 0` and
`0 ≤ x`. -/
theorem intervalIntegral_cpow_mul_exp_neg_mul {a r : ℂ} (ha : 0 < a.re) (hr : r ≠ 0) {x : ℝ}
    (hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (a - 1) * cexp (-(r * t)) =
      r ^ (-a) * lowerIncompleteGamma a (r * x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hra : r ^ a ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
    (fun h => by simp [h] at ha)).mpr hr
  have hrx : (r * x) ^ a = r ^ a * (x : ℂ) ^ a := by
    rw [mul_comm, TauCeti.ofReal_mul_cpow hx.le, mul_comm]
  rw [lowerIncompleteGamma_eq_integral ha, hrx, ← mul_assoc, ← mul_assoc, cpow_neg,
    inv_mul_cancel₀ hra, one_mul]
  have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (f := fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(r * t))) x
  rw [mul_zero, mul_one] at h
  rw [← h, real_smul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le zero_le_one] at hu
  rw [ofReal_mul, ofReal_mul_cpow hx.le, cpow_sub _ _ hx0, cpow_one]
  field_simp

end TauCeti
