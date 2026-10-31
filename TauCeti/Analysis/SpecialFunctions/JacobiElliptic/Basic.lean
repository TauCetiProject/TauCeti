/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Jacobi elliptic functions of a real variable

For a modulus `k` with `k ^ 2 < 1`, the integral of the first kind `φ ↦ F(φ, k)` is an order
isomorphism of `ℝ` (`TauCeti.Real.legendreFOrderIso`). This file defines its inverse, the
**Jacobi amplitude** `jacobiAm k`, and the three basic Jacobi elliptic functions
(DLMF §22.16(i))

* `jacobiSn k u = sin (jacobiAm k u)`;
* `jacobiCn k u = cos (jacobiAm k u)`;
* `jacobiDn k u = √(1 - k ^ 2 * jacobiSn k u ^ 2)`,

as functions `ℝ → ℝ` with the modulus as first argument. For `k ^ 2 ≥ 1` the amplitude is the junk
value `id`; theorems that need `k ^ 2 < 1` say so.

We prove the basic theory:

* the amplitude inverts `F`, is odd, continuous and strictly increasing, satisfies
  `am(u + 2 n K) = am(u) + n π` and `am(K) = π / 2`, and has derivative `dn`;
* the identities `sn² + cn² = 1` and `dn² + k² sn² = 1`, positivity of `dn`, and the parities of
  `sn`, `cn` and `dn` in the argument and in the modulus;
* the derivatives `sn′ = cn dn`, `cn′ = -sn dn`, `dn′ = -k² sn cn`, and the first-order
  differential equation `(sn′)² = (1 - sn²)(1 - k² sn²)`;
* the antiperiods `2K` of `sn` and `cn`, hence their period `4K`, the period `2K` of `dn`, and the
  values at `u = K`;
* the degeneration at modulus `0`: `am = id`, `sn = sin`, `cn = cos`, `dn = 1`.

Here `K = legendreK k` is the complete integral of the first kind.

## References

* NIST *Digital Library of Mathematical Functions*, Chapter 22, <https://dlmf.nist.gov/22>.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, Chapter XXII.
-/

public section

noncomputable section

namespace TauCeti.Real

open _root_.Real Filter Set

/-! ### Definitions -/

/-- **The Jacobi amplitude** `am(u, k)` (DLMF §22.16(i)): for `k ^ 2 < 1`, the inverse of the
integral of the first kind `φ ↦ F(φ, k)`, so that `F(am(u, k), k) = u`. For `k ^ 2 ≥ 1` it is the
junk value `id`. -/
def jacobiAm (k : ℝ) : ℝ → ℝ :=
  if hk : k ^ 2 < 1 then (legendreFOrderIso hk).symm else id

/-- **The Jacobi elliptic function** `sn(u, k) = sin (am(u, k))`. -/
def jacobiSn (k u : ℝ) : ℝ := sin (jacobiAm k u)

/-- **The Jacobi elliptic function** `cn(u, k) = cos (am(u, k))`. -/
def jacobiCn (k u : ℝ) : ℝ := cos (jacobiAm k u)

/-- **The Jacobi elliptic function** `dn(u, k) = √(1 - k² sn²(u, k))`. -/
def jacobiDn (k u : ℝ) : ℝ := √(1 - k ^ 2 * jacobiSn k u ^ 2)

theorem jacobiSn_def (k u : ℝ) : jacobiSn k u = sin (jacobiAm k u) := (rfl)

theorem jacobiCn_def (k u : ℝ) : jacobiCn k u = cos (jacobiAm k u) := (rfl)

theorem jacobiDn_def (k u : ℝ) : jacobiDn k u = √(1 - k ^ 2 * jacobiSn k u ^ 2) := (rfl)

/-! ### The amplitude -/

/-- For `k ^ 2 < 1`, the inverse of the order isomorphism `φ ↦ F(φ, k)` is the amplitude. -/
@[simp]
theorem coe_legendreFOrderIso_symm {k : ℝ} (hk : k ^ 2 < 1) :
    ⇑(legendreFOrderIso hk).symm = jacobiAm k := by
  simp only [jacobiAm, hk, ↓reduceDIte]

/-- For `k ^ 2 ≥ 1` the amplitude is the junk value `id`. -/
theorem jacobiAm_of_one_le_sq {k : ℝ} (hk : 1 ≤ k ^ 2) : jacobiAm k = id := by
  simp only [jacobiAm, hk.not_gt, ↓reduceDIte]

@[simp]
theorem legendreF_jacobiAm {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) : legendreF (jacobiAm k u) k = u := by
  simpa using (legendreFOrderIso hk).apply_symm_apply u

@[simp]
theorem jacobiAm_legendreF {k : ℝ} (hk : k ^ 2 < 1) (φ : ℝ) : jacobiAm k (legendreF φ k) = φ := by
  simpa using (legendreFOrderIso hk).symm_apply_apply φ

/-- For `k ^ 2 < 1`, `am(u, k) = φ` exactly when `F(φ, k) = u`. -/
theorem jacobiAm_eq_iff {k : ℝ} (hk : k ^ 2 < 1) {u φ : ℝ} :
    jacobiAm k u = φ ↔ legendreF φ k = u := by
  have h := (legendreFOrderIso hk).symm_apply_eq (x := φ) (y := u)
  simp only [coe_legendreFOrderIso_symm, coe_legendreFOrderIso] at h
  rw [h, eq_comm]

/-- The amplitude is strictly increasing, for every modulus. -/
theorem strictMono_jacobiAm (k : ℝ) : StrictMono (jacobiAm k) := by
  by_cases hk : k ^ 2 < 1
  · rw [← coe_legendreFOrderIso_symm hk]
    exact (legendreFOrderIso hk).symm.strictMono
  · rw [jacobiAm_of_one_le_sq (not_lt.1 hk)]
    exact strictMono_id

/-- The amplitude is continuous, for every modulus. -/
theorem continuous_jacobiAm (k : ℝ) : Continuous (jacobiAm k) := by
  by_cases hk : k ^ 2 < 1
  · rw [← coe_legendreFOrderIso_symm hk]
    exact (legendreFOrderIso hk).symm.continuous
  · rw [jacobiAm_of_one_le_sq (not_lt.1 hk)]
    exact continuous_id

@[simp]
theorem jacobiAm_zero (k : ℝ) : jacobiAm k 0 = 0 := by
  by_cases hk : k ^ 2 < 1
  · rw [jacobiAm_eq_iff hk, legendreF_zero]
  · rw [jacobiAm_of_one_le_sq (not_lt.1 hk), id]

/-- The amplitude is odd: `am(-u, k) = -am(u, k)`. -/
@[simp]
theorem jacobiAm_neg (k u : ℝ) : jacobiAm k (-u) = -jacobiAm k u := by
  by_cases hk : k ^ 2 < 1
  · rw [jacobiAm_eq_iff hk, legendreF_neg, legendreF_jacobiAm hk]
  · simp [jacobiAm_of_one_le_sq (not_lt.1 hk)]

/-- The amplitude is even in the modulus. -/
@[simp]
theorem jacobiAm_neg_modulus (k : ℝ) : jacobiAm (-k) = jacobiAm k := by
  by_cases hk : k ^ 2 < 1
  · ext u
    rw [jacobiAm_eq_iff (by rwa [neg_sq]), legendreF_neg_modulus, legendreF_jacobiAm hk]
  · rw [jacobiAm_of_one_le_sq (by rw [neg_sq]; exact not_lt.1 hk),
      jacobiAm_of_one_le_sq (not_lt.1 hk)]

/-- At modulus `0` the amplitude is the identity. -/
@[simp]
theorem jacobiAm_zero_modulus : jacobiAm 0 = id := by
  ext u
  rw [jacobiAm_eq_iff (by norm_num), id, legendreF_zero_modulus]

/-- **Quasi-periodicity of the amplitude**: `am(u + 2 n K, k) = am(u, k) + n π` for every integer
`n`. -/
theorem jacobiAm_add_two_mul_int_mul_legendreK {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) (n : ℤ) :
    jacobiAm k (u + 2 * n * legendreK k) = jacobiAm k u + n * π := by
  rw [jacobiAm_eq_iff hk, legendreF_add_int_mul_pi hk, legendreF_jacobiAm hk]

theorem jacobiAm_add_two_mul_legendreK {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) :
    jacobiAm k (u + 2 * legendreK k) = jacobiAm k u + π := by
  simpa using jacobiAm_add_two_mul_int_mul_legendreK hk u 1

/-- The amplitude at a quarter period is `π / 2`: `am(K, k) = π / 2`. -/
@[simp]
theorem jacobiAm_legendreK {k : ℝ} (hk : k ^ 2 < 1) : jacobiAm k (legendreK k) = π / 2 := by
  rw [jacobiAm_eq_iff hk, legendreK_def]

/-! ### Algebraic identities -/

@[simp]
theorem jacobiSn_sq_add_jacobiCn_sq (k u : ℝ) : jacobiSn k u ^ 2 + jacobiCn k u ^ 2 = 1 :=
  sin_sq_add_cos_sq _

/-- For `k ^ 2 ≤ 1`, the radicand defining `dn` is nonnegative. -/
theorem one_sub_sq_mul_jacobiSn_sq_nonneg {k : ℝ} (hk : k ^ 2 ≤ 1) (u : ℝ) :
    0 ≤ 1 - k ^ 2 * jacobiSn k u ^ 2 :=
  (sub_nonneg.2 hk).trans (one_sub_sq_le_one_sub_sq_mul_sin_sq k _)

/-- For `k ^ 2 < 1`, the radicand defining `dn` is positive. -/
theorem one_sub_sq_mul_jacobiSn_sq_pos {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) :
    0 < 1 - k ^ 2 * jacobiSn k u ^ 2 :=
  one_sub_mul_sin_sq_pos hk _

theorem jacobiDn_sq {k : ℝ} (hk : k ^ 2 ≤ 1) (u : ℝ) :
    jacobiDn k u ^ 2 = 1 - k ^ 2 * jacobiSn k u ^ 2 :=
  sq_sqrt (one_sub_sq_mul_jacobiSn_sq_nonneg hk u)

theorem jacobiDn_sq_add_sq_mul_jacobiSn_sq {k : ℝ} (hk : k ^ 2 ≤ 1) (u : ℝ) :
    jacobiDn k u ^ 2 + k ^ 2 * jacobiSn k u ^ 2 = 1 := by
  rw [jacobiDn_sq hk]
  ring

theorem jacobiDn_nonneg (k u : ℝ) : 0 ≤ jacobiDn k u := sqrt_nonneg _

theorem jacobiDn_pos {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) : 0 < jacobiDn k u :=
  sqrt_pos.2 (one_sub_sq_mul_jacobiSn_sq_pos hk u)

theorem jacobiDn_le_one (k u : ℝ) : jacobiDn k u ≤ 1 :=
  sqrt_le_one.2 (one_sub_sq_mul_sin_sq_le_one k _)

/-! ### Values at zero and parity -/

@[simp]
theorem jacobiSn_zero (k : ℝ) : jacobiSn k 0 = 0 := by simp [jacobiSn_def]

@[simp]
theorem jacobiCn_zero (k : ℝ) : jacobiCn k 0 = 1 := by simp [jacobiCn_def]

@[simp]
theorem jacobiDn_zero (k : ℝ) : jacobiDn k 0 = 1 := by simp [jacobiDn_def]

/-- `sn` is odd. -/
@[simp]
theorem jacobiSn_neg (k u : ℝ) : jacobiSn k (-u) = -jacobiSn k u := by
  simp [jacobiSn_def]

/-- `cn` is even. -/
@[simp]
theorem jacobiCn_neg (k u : ℝ) : jacobiCn k (-u) = jacobiCn k u := by
  simp [jacobiCn_def]

/-- `dn` is even. -/
@[simp]
theorem jacobiDn_neg (k u : ℝ) : jacobiDn k (-u) = jacobiDn k u := by
  simp [jacobiDn_def]

@[simp]
theorem jacobiSn_neg_modulus (k : ℝ) : jacobiSn (-k) = jacobiSn k := by
  ext u
  simp [jacobiSn_def]

@[simp]
theorem jacobiCn_neg_modulus (k : ℝ) : jacobiCn (-k) = jacobiCn k := by
  ext u
  simp [jacobiCn_def]

@[simp]
theorem jacobiDn_neg_modulus (k : ℝ) : jacobiDn (-k) = jacobiDn k := by
  ext u
  simp [jacobiDn_def]

/-! ### The degenerate modulus `k = 0` -/

@[simp]
theorem jacobiSn_zero_modulus : jacobiSn 0 = sin := by
  ext u
  simp [jacobiSn_def]

@[simp]
theorem jacobiCn_zero_modulus : jacobiCn 0 = cos := by
  ext u
  simp [jacobiCn_def]

@[simp]
theorem jacobiDn_zero_modulus : jacobiDn 0 = 1 := by
  ext u
  simp [jacobiDn_def]

/-! ### Continuity and derivatives -/

theorem continuous_jacobiSn (k : ℝ) : Continuous (jacobiSn k) :=
  continuous_sin.comp (continuous_jacobiAm k)

theorem continuous_jacobiCn (k : ℝ) : Continuous (jacobiCn k) :=
  continuous_cos.comp (continuous_jacobiAm k)

theorem continuous_jacobiDn (k : ℝ) : Continuous (jacobiDn k) :=
  (continuous_const.sub (continuous_const.mul ((continuous_jacobiSn k).pow 2))).sqrt

/-- The derivative of the amplitude is `dn`: `am′(u, k) = dn(u, k)` (DLMF §22.16(i)). -/
theorem hasDerivAt_jacobiAm {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (jacobiAm k) (jacobiDn k u) u := by
  have hF := hasDerivAt_legendreF hk (jacobiAm k u)
  rw [legendreF_integrand_eq_inv_sqrt] at hF
  have h := hF.of_local_left_inverse (continuous_jacobiAm k).continuousAt
    (inv_ne_zero (jacobiDn_pos hk u).ne') (Eventually.of_forall (legendreF_jacobiAm hk))
  rwa [inv_inv] at h

/-- `sn′ = cn · dn` (DLMF §22.13(i)). -/
theorem hasDerivAt_jacobiSn {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (jacobiSn k) (jacobiCn k u * jacobiDn k u) u := by
  rw [show jacobiSn k = fun v ↦ sin (jacobiAm k v) from funext (jacobiSn_def k), jacobiCn_def]
  exact (hasDerivAt_jacobiAm hk u).sin

/-- `cn′ = -sn · dn` (DLMF §22.13(i)). -/
theorem hasDerivAt_jacobiCn {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (jacobiCn k) (-jacobiSn k u * jacobiDn k u) u := by
  rw [show jacobiCn k = fun v ↦ cos (jacobiAm k v) from funext (jacobiCn_def k), jacobiSn_def]
  exact (hasDerivAt_jacobiAm hk u).cos

/-- `dn′ = -k² · sn · cn` (DLMF §22.13(i)). -/
theorem hasDerivAt_jacobiDn {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) :
    HasDerivAt (jacobiDn k) (-k ^ 2 * jacobiSn k u * jacobiCn k u) u := by
  have h := (((hasDerivAt_jacobiSn hk u).pow 2).const_mul (k ^ 2)).const_sub 1 |>.sqrt
    (one_sub_sq_mul_jacobiSn_sq_pos hk u).ne'
  convert h using 1
  · exact funext fun v ↦ by rw [jacobiDn_def, Pi.pow_apply]
  · rw [Pi.pow_apply, ← jacobiDn_def]
    field_simp [(jacobiDn_pos hk u).ne']
    norm_num
    ring

/-- **The first-order differential equation of `sn`** (DLMF §22.13(ii)):
`(sn′)² = (1 - sn²)(1 - k² sn²)`. -/
theorem deriv_jacobiSn_sq {k : ℝ} (hk : k ^ 2 < 1) (u : ℝ) :
    deriv (jacobiSn k) u ^ 2 = (1 - jacobiSn k u ^ 2) * (1 - k ^ 2 * jacobiSn k u ^ 2) := by
  rw [(hasDerivAt_jacobiSn hk u).deriv, mul_pow, jacobiDn_sq hk.le,
    ← jacobiSn_sq_add_jacobiCn_sq k u]
  ring

/-! ### Periods and values at the quarter period -/

/-- `sn` changes sign under a shift by `2K`: `sn(u + 2K) = -sn(u)` (DLMF §22.4(iii)). -/
theorem jacobiSn_antiperiodic {k : ℝ} (hk : k ^ 2 < 1) :
    Function.Antiperiodic (jacobiSn k) (2 * legendreK k) := fun u ↦ by
  rw [jacobiSn_def, jacobiAm_add_two_mul_legendreK hk, sin_add_pi, jacobiSn_def]

/-- `cn` changes sign under a shift by `2K`: `cn(u + 2K) = -cn(u)` (DLMF §22.4(iii)). -/
theorem jacobiCn_antiperiodic {k : ℝ} (hk : k ^ 2 < 1) :
    Function.Antiperiodic (jacobiCn k) (2 * legendreK k) := fun u ↦ by
  rw [jacobiCn_def, jacobiAm_add_two_mul_legendreK hk, cos_add_pi, jacobiCn_def]

/-- `sn` has period `4K`. -/
theorem jacobiSn_periodic {k : ℝ} (hk : k ^ 2 < 1) :
    Function.Periodic (jacobiSn k) (4 * legendreK k) := by
  have h := (jacobiSn_antiperiodic hk).periodic_two_mul
  rwa [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] at h

/-- `cn` has period `4K`. -/
theorem jacobiCn_periodic {k : ℝ} (hk : k ^ 2 < 1) :
    Function.Periodic (jacobiCn k) (4 * legendreK k) := by
  have h := (jacobiCn_antiperiodic hk).periodic_two_mul
  rwa [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] at h

/-- `dn` has period `2K`. -/
theorem jacobiDn_periodic {k : ℝ} (hk : k ^ 2 < 1) :
    Function.Periodic (jacobiDn k) (2 * legendreK k) := fun u ↦ by
  rw [jacobiDn_def, jacobiSn_antiperiodic hk, neg_sq, jacobiDn_def]

@[simp]
theorem jacobiSn_legendreK {k : ℝ} (hk : k ^ 2 < 1) : jacobiSn k (legendreK k) = 1 := by
  rw [jacobiSn_def, jacobiAm_legendreK hk, sin_pi_div_two]

@[simp]
theorem jacobiCn_legendreK {k : ℝ} (hk : k ^ 2 < 1) : jacobiCn k (legendreK k) = 0 := by
  rw [jacobiCn_def, jacobiAm_legendreK hk, cos_pi_div_two]

/-- `dn(K, k) = √(1 - k²)`, the complementary modulus. -/
@[simp]
theorem jacobiDn_legendreK {k : ℝ} (hk : k ^ 2 < 1) : jacobiDn k (legendreK k) = √(1 - k ^ 2) := by
  rw [jacobiDn_def, jacobiSn_legendreK hk, one_pow, mul_one]

end TauCeti.Real
