/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Legendre's elliptic integrals

This file defines Legendre's incomplete elliptic integrals of the first, second and third kinds
(DLMF 19.2.4, 19.2.5, 19.2.7), as functions of a real amplitude `φ`, a real modulus `k` and a real
characteristic `α2` (written `α²` in prose; it may be negative):

* `TauCeti.Real.legendreF φ k = ∫ θ in 0..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2)`;
* `TauCeti.Real.legendreE φ k = ∫ θ in 0..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2)`;
* `TauCeti.Real.legendrePi φ k α2` is the integral over `[0, φ]` of
  `(1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2)`;

together with the complete integrals `legendreK k`, `legendreEc k` and `legendrePic k α2`, their
values at `φ = π / 2`. The powers are `Real.rpow`. These are total functions of their real
arguments; their values are meaningful for `k ^ 2 < 1` and `α2 < 1`, under which every integrand
is continuous and bounded between two positive constants, and every theorem below states the
hypotheses it needs. The integral of the second kind needs no hypothesis at all for the bounds on
its integrand, nor for continuity, differentiability, positivity and quasi-periodicity in `φ`, and
it is strictly increasing in `φ` for `k ^ 2 ≤ 1`.

We prove the basic theory in the amplitude:

* the integrands are continuous, positive, bounded by explicit constants and interval integrable;
* the fundamental theorem of calculus
  `HasDerivAt (legendreF · k) ((1 - k ^ 2 * sin φ ^ 2) ^ (-1 / 2)) φ` and its analogues, so the
  three integrals are continuous and strictly increasing in `φ`, and positive for `φ > 0`; in
  particular the complete integrals are positive;
* the integrals are odd in `φ` and even in `k`;
* quasi-periodicity: `legendreF (φ + n * π) k = legendreF φ k + 2 * n * legendreK k` for integers
  `n`, and likewise for the other two kinds;
* `legendreFOrderIso`: for `k ^ 2 < 1`, the map `φ ↦ legendreF φ k` is an order isomorphism of `ℝ`,
  whose inverse is the Jacobi amplitude;
* the degenerate modulus `k = 0`: `legendreF φ 0 = legendreE φ 0 = φ`, and
  `legendreK 0 = legendreEc 0 = π / 2`.

The conventions (modulus rather than parameter, argument order `(φ, k)` and `(φ, k, α2)`) are
those of DLMF Chapter 19 and of B. Braams' `lean-codes` formalization of B. C. Carlson's
*Special Functions of Applied Mathematics*, so that the two developments stay interoperable.

## References

* NIST *Digital Library of Mathematical Functions*, §19.2, <https://dlmf.nist.gov/19.2>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
-/

public section

noncomputable section

namespace TauCeti.Real

open _root_.Real Filter MeasureTheory intervalIntegral Set
open scoped Topology

/-! ### Definitions -/

/-- **Legendre's incomplete elliptic integral of the first kind** (DLMF 19.2.4),
`F(φ, k) = ∫₀^φ (1 - k² sin² θ)^(-1/2) dθ`, with amplitude `φ` and modulus `k`. It is meaningful
for `k ^ 2 < 1`. -/
def legendreF (φ k : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)

/-- **Legendre's incomplete elliptic integral of the second kind** (DLMF 19.2.5),
`E(φ, k) = ∫₀^φ (1 - k² sin² θ)^(1/2) dθ`, with amplitude `φ` and modulus `k`. It is meaningful
for `k ^ 2 ≤ 1`. -/
def legendreE (φ k : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ)

/-- **Legendre's incomplete elliptic integral of the third kind** (DLMF 19.2.7),
`Π(φ, k, α²) = ∫₀^φ (1 - α² sin² θ)⁻¹ (1 - k² sin² θ)^(-1/2) dθ`, with amplitude `φ`, modulus `k`
and characteristic `α2`, which may be negative. It is meaningful for `k ^ 2 < 1` and `α2 < 1`. -/
def legendrePi (φ k α2 : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)

/-- **The complete elliptic integral of the first kind**, `K(k) = F(π/2, k)`. -/
def legendreK (k : ℝ) : ℝ := legendreF (π / 2) k

/-- **The complete elliptic integral of the second kind**, `E(k) = E(π/2, k)`. -/
def legendreEc (k : ℝ) : ℝ := legendreE (π / 2) k

/-- **The complete elliptic integral of the third kind**, `Π(k, α²) = Π(π/2, k, α²)`. -/
def legendrePic (k α2 : ℝ) : ℝ := legendrePi (π / 2) k α2

theorem legendreF_def (φ k : ℝ) :
    legendreF φ k = ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) := (rfl)

theorem legendreE_def (φ k : ℝ) :
    legendreE φ k = ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) := (rfl)

theorem legendrePi_def (φ k α2 : ℝ) :
    legendrePi φ k α2 =
      ∫ θ in (0 : ℝ)..φ, (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) := (rfl)

theorem legendreK_def (k : ℝ) : legendreK k = legendreF (π / 2) k := (rfl)

theorem legendreEc_def (k : ℝ) : legendreEc k = legendreE (π / 2) k := (rfl)

theorem legendrePic_def (k α2 : ℝ) : legendrePic k α2 = legendrePi (π / 2) k α2 := (rfl)

/-! ### The integrands -/

/-! #### The first kind -/

theorem continuous_legendreF_integrand {k : ℝ} (hk : k ^ 2 < 1) :
    Continuous fun θ ↦ (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) :=
  (continuous_const.sub (continuous_const.mul (continuous_sin.pow 2))).rpow_const fun θ ↦
    Or.inl (one_sub_mul_sin_sq_pos hk θ).ne'

/-- The integrand of the first kind is at least `1`. -/
theorem one_le_legendreF_integrand {k : ℝ} (hk : k ^ 2 < 1) (θ : ℝ) :
    1 ≤ (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) :=
  one_le_rpow_of_pos_of_le_one_of_nonpos (one_sub_mul_sin_sq_pos hk θ)
    (one_sub_sq_mul_sin_sq_le_one k θ) (by norm_num)

/-- The integrand of the first kind is at most `(1 - k²)^(-1/2)`. -/
theorem legendreF_integrand_le {k : ℝ} (hk : k ^ 2 < 1) (θ : ℝ) :
    (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) ≤ (1 - k ^ 2) ^ (-1 / 2 : ℝ) :=
  rpow_le_rpow_of_nonpos (by linarith) (one_sub_sq_le_one_sub_sq_mul_sin_sq k θ) (by norm_num)

theorem intervalIntegrable_legendreF_integrand {k : ℝ} (hk : k ^ 2 < 1) (a b : ℝ) :
    IntervalIntegrable (fun θ ↦ (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) volume a b :=
  (continuous_legendreF_integrand hk).intervalIntegrable a b

/-! #### The second kind -/

/-- The integrand of the second kind is continuous for every modulus. -/
theorem continuous_legendreE_integrand (k : ℝ) :
    Continuous fun θ ↦ (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) :=
  (continuous_const.sub (continuous_const.mul (continuous_sin.pow 2))).rpow_const fun _ ↦
    Or.inr (by norm_num)

theorem legendreE_integrand_pos {k : ℝ} (hk : k ^ 2 < 1) (θ : ℝ) :
    0 < (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) :=
  rpow_pos_of_pos (one_sub_mul_sin_sq_pos hk θ) _

/-- The integrand of the second kind is nonnegative, for every modulus. -/
theorem legendreE_integrand_nonneg (k θ : ℝ) : 0 ≤ (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [← sqrt_eq_rpow]
  exact sqrt_nonneg _

/-- The integrand of the second kind is at least `(1 - k²)^(1/2)`, for every modulus. -/
theorem le_legendreE_integrand (k θ : ℝ) :
    (1 - k ^ 2) ^ (1 / 2 : ℝ) ≤ (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [← sqrt_eq_rpow, ← sqrt_eq_rpow]
  exact sqrt_le_sqrt (one_sub_sq_le_one_sub_sq_mul_sin_sq k θ)

/-- The integrand of the second kind is at most `1`, for every modulus. -/
theorem legendreE_integrand_le_one (k θ : ℝ) : (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) ≤ 1 := by
  rw [← sqrt_eq_rpow]
  exact (sqrt_le_sqrt (one_sub_sq_mul_sin_sq_le_one k θ)).trans_eq sqrt_one

theorem intervalIntegrable_legendreE_integrand (k a b : ℝ) :
    IntervalIntegrable (fun θ ↦ (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ)) volume a b :=
  (continuous_legendreE_integrand k).intervalIntegrable a b

/-! #### The third kind -/

theorem continuous_legendrePi_integrand {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    Continuous fun θ ↦ (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) :=
  ((continuous_const.sub (continuous_const.mul (continuous_sin.pow 2))).inv₀ fun θ ↦
    (one_sub_mul_sin_sq_pos hα θ).ne').mul (continuous_legendreF_integrand hk)

/-- The integrand of the third kind is at least `(max 1 (1 - α²))⁻¹`. -/
theorem inv_max_le_legendrePi_integrand {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (θ : ℝ) :
    (max 1 (1 - α2))⁻¹ ≤ (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) := by
  have hpos := one_sub_mul_sin_sq_pos hα θ
  have hle : 1 - α2 * sin θ ^ 2 ≤ max 1 (1 - α2) := by
    have h₀ := sq_nonneg (sin θ)
    have h₁ := sin_sq_le_one θ
    rcases le_or_gt α2 0 with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  calc (max 1 (1 - α2))⁻¹ ≤ (1 - α2 * sin θ ^ 2)⁻¹ := inv_anti₀ hpos hle
    _ = (1 - α2 * sin θ ^ 2)⁻¹ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_legendreF_integrand hk θ) (inv_nonneg.2 hpos.le)

theorem legendrePi_integrand_pos {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (θ : ℝ) :
    0 < (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) :=
  lt_of_lt_of_le (inv_pos.2 (lt_max_of_lt_left one_pos)) (inv_max_le_legendrePi_integrand hk hα θ)

/-- The integrand of the third kind is at most `(min 1 (1 - α²))⁻¹ (1 - k²)^(-1/2)`. -/
theorem legendrePi_integrand_le {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (θ : ℝ) :
    (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) ≤
      (min 1 (1 - α2))⁻¹ * (1 - k ^ 2) ^ (-1 / 2 : ℝ) := by
  have hmin : 0 < min 1 (1 - α2) := lt_min one_pos (by linarith)
  have hle : min 1 (1 - α2) ≤ 1 - α2 * sin θ ^ 2 := by
    have h₀ := sq_nonneg (sin θ)
    have h₁ := sin_sq_le_one θ
    rcases le_or_gt α2 0 with h | h
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
  exact mul_le_mul (inv_anti₀ hmin hle) (legendreF_integrand_le hk θ)
    (rpow_nonneg (one_sub_mul_sin_sq_pos hk θ).le _) (inv_nonneg.2 hmin.le)

theorem intervalIntegrable_legendrePi_integrand {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1)
    (a b : ℝ) :
    IntervalIntegrable
      (fun θ ↦ (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) volume a b :=
  (continuous_legendrePi_integrand hk hα).intervalIntegrable a b

/-! ### The integral of the first kind -/

@[simp]
theorem legendreF_zero (k : ℝ) : legendreF 0 k = 0 := integral_same

/-- The integral of the first kind is a primitive of its integrand. -/
theorem hasDerivAt_legendreF {k : ℝ} (hk : k ^ 2 < 1) (φ : ℝ) :
    HasDerivAt (legendreF · k) ((1 - k ^ 2 * sin φ ^ 2) ^ (-1 / 2 : ℝ)) φ :=
  integral_hasDerivAt_right (intervalIntegrable_legendreF_integrand hk 0 φ)
    ((continuous_legendreF_integrand hk).stronglyMeasurableAtFilter _ _)
    (continuous_legendreF_integrand hk).continuousAt

/-- For `k ^ 2 < 1`, `F(φ, k)` is continuous in the amplitude `φ`. -/
theorem continuous_legendreF {k : ℝ} (hk : k ^ 2 < 1) : Continuous (legendreF · k) :=
  continuous_iff_continuousAt.2 fun φ ↦ (hasDerivAt_legendreF hk φ).continuousAt

/-- For `k ^ 2 < 1`, `F(φ, k)` is strictly increasing in the amplitude `φ`. -/
theorem strictMono_legendreF {k : ℝ} (hk : k ^ 2 < 1) : StrictMono (legendreF · k) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_legendreF hk) fun φ ↦
    one_pos.trans_le (one_le_legendreF_integrand hk φ)

/-- For `k ^ 2 < 1`, `F(φ, k)` is positive for positive amplitude `φ`. -/
theorem legendreF_pos {φ k : ℝ} (hk : k ^ 2 < 1) (hφ : 0 < φ) : 0 < legendreF φ k := by
  simpa using strictMono_legendreF hk hφ

/-- For nonnegative amplitude, `φ ≤ F(φ, k)`, since the integrand is at least `1`. -/
theorem self_le_legendreF {φ k : ℝ} (hk : k ^ 2 < 1) (hφ : 0 ≤ φ) : φ ≤ legendreF φ k := by
  have h := integral_mono_on hφ intervalIntegrable_const
    (intervalIntegrable_legendreF_integrand hk 0 φ) fun θ _ ↦ one_le_legendreF_integrand hk θ
  simpa [legendreF_def] using h

/-- `F(φ, k)` is odd in the amplitude. -/
@[simp]
theorem legendreF_neg (φ k : ℝ) : legendreF (-φ) k = -legendreF φ k :=
  integral_comp_sin_sq_neg (fun s ↦ (1 - k ^ 2 * s) ^ (-1 / 2 : ℝ)) φ

/-- `F(φ, k)` is even in the modulus. -/
@[simp]
theorem legendreF_neg_modulus (φ k : ℝ) : legendreF φ (-k) = legendreF φ k := by
  simp only [legendreF_def, neg_sq]

/-- For nonpositive amplitude, `F(φ, k) ≤ φ`. -/
theorem legendreF_le_self {φ k : ℝ} (hk : k ^ 2 < 1) (hφ : φ ≤ 0) : legendreF φ k ≤ φ := by
  have h := self_le_legendreF hk (neg_nonneg.2 hφ)
  rw [legendreF_neg] at h
  linarith

/-- **Quasi-periodicity of `F`**: `F(φ + nπ, k) = F(φ, k) + 2 n K(k)` for every integer `n`. -/
theorem legendreF_add_int_mul_pi {k : ℝ} (hk : k ^ 2 < 1) (φ : ℝ) (n : ℤ) :
    legendreF (φ + n * π) k = legendreF φ k + 2 * n * legendreK k :=
  integral_comp_sin_sq_add_int_mul_pi (fun s ↦ (1 - k ^ 2 * s) ^ (-1 / 2 : ℝ))
    (continuous_legendreF_integrand hk) φ n

theorem legendreF_add_pi {k : ℝ} (hk : k ^ 2 < 1) (φ : ℝ) :
    legendreF (φ + π) k = legendreF φ k + 2 * legendreK k := by
  simpa using legendreF_add_int_mul_pi hk φ 1

theorem legendreF_int_mul_pi {k : ℝ} (hk : k ^ 2 < 1) (n : ℤ) :
    legendreF (n * π) k = 2 * n * legendreK k := by
  simpa using legendreF_add_int_mul_pi hk 0 n

/-- For `k ^ 2 < 1`, `F(φ, k)` tends to `+∞` as the amplitude `φ` tends to `+∞`. -/
theorem tendsto_legendreF_atTop {k : ℝ} (hk : k ^ 2 < 1) :
    Tendsto (legendreF · k) atTop atTop :=
  tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun _ hφ ↦ self_le_legendreF hk hφ)
    tendsto_id

/-- For `k ^ 2 < 1`, `F(φ, k)` tends to `-∞` as the amplitude `φ` tends to `-∞`. -/
theorem tendsto_legendreF_atBot {k : ℝ} (hk : k ^ 2 < 1) :
    Tendsto (legendreF · k) atBot atBot :=
  tendsto_atBot_mono' atBot ((eventually_le_atBot 0).mono fun _ hφ ↦ legendreF_le_self hk hφ)
    tendsto_id

/-- For `k ^ 2 < 1`, the integral of the first kind `φ ↦ F(φ, k)` as an order isomorphism of `ℝ`.
Its inverse is the Jacobi amplitude `u ↦ am(u, k)`. -/
def legendreFOrderIso {k : ℝ} (hk : k ^ 2 < 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (legendreF · k) (strictMono_legendreF hk)
    ((continuous_legendreF hk).surjective (tendsto_legendreF_atTop hk)
      (tendsto_legendreF_atBot hk))

@[simp]
theorem coe_legendreFOrderIso {k : ℝ} (hk : k ^ 2 < 1) :
    ⇑(legendreFOrderIso hk) = (legendreF · k) := (rfl)

/-- At modulus `0` the integral of the first kind is the identity: `F(φ, 0) = φ`. -/
@[simp]
theorem legendreF_zero_modulus (φ : ℝ) : legendreF φ 0 = φ := by
  simp [legendreF_def]

/-- For `k ^ 2 < 1`, the complete integral of the first kind `K(k)` is positive. -/
theorem legendreK_pos {k : ℝ} (hk : k ^ 2 < 1) : 0 < legendreK k :=
  legendreF_pos hk (by positivity)

@[simp]
theorem legendreK_neg (k : ℝ) : legendreK (-k) = legendreK k := legendreF_neg_modulus _ k

@[simp]
theorem legendreK_zero : legendreK 0 = π / 2 := legendreF_zero_modulus _

/-! ### The integral of the second kind -/

@[simp]
theorem legendreE_zero (k : ℝ) : legendreE 0 k = 0 := integral_same

/-- The integral of the second kind is a primitive of its integrand, for every modulus. -/
theorem hasDerivAt_legendreE (k φ : ℝ) :
    HasDerivAt (legendreE · k) ((1 - k ^ 2 * sin φ ^ 2) ^ (1 / 2 : ℝ)) φ :=
  integral_hasDerivAt_right (intervalIntegrable_legendreE_integrand k 0 φ)
    ((continuous_legendreE_integrand k).stronglyMeasurableAtFilter _ _)
    (continuous_legendreE_integrand k).continuousAt

/-- For every modulus `k`, `E(φ, k)` is continuous in the amplitude `φ`. -/
theorem continuous_legendreE (k : ℝ) : Continuous (legendreE · k) :=
  continuous_iff_continuousAt.2 fun φ ↦ (hasDerivAt_legendreE k φ).continuousAt

/-- For `k ^ 2 ≤ 1`, `E(φ, k)` is strictly increasing in the amplitude `φ`. -/
theorem strictMono_legendreE {k : ℝ} (hk : k ^ 2 ≤ 1) : StrictMono (legendreE · k) := by
  intro a b hab
  -- The integrand is positive wherever `cos θ ≠ 0`, which holds off a countable set.
  have hZ : {θ : ℝ | cos θ = 0}.Countable := by
    refine (countable_range fun n : ℤ ↦ (2 * n + 1) * π / 2).mono fun θ hθ ↦ ?_
    obtain ⟨n, hn⟩ := cos_eq_zero_iff.1 hθ
    exact ⟨n, hn.symm⟩
  have hne : volume (Ioo a b \ {θ : ℝ | cos θ = 0}) ≠ 0 := by
    rw [measure_sdiff_null (hZ.measure_zero volume)]
    exact ((Measure.measure_Ioo_pos _).2 hab).ne'
  obtain ⟨c, hc, hcos⟩ := nonempty_of_measure_ne_zero hne
  have hc_pos : 0 < (1 - k ^ 2 * sin c ^ 2) ^ (1 / 2 : ℝ) := by
    have : 0 < cos c ^ 2 := (sq_nonneg _).lt_of_ne (pow_ne_zero 2 hcos).symm
    exact rpow_pos_of_pos (by nlinarith [sin_sq_add_cos_sq c, sq_nonneg (sin c)]) _
  have hint := intervalIntegrable_legendreE_integrand k
  rw [← sub_pos]
  simp only [legendreE_def]
  rw [integral_interval_sub_left (hint 0 b) (hint 0 a)]
  exact intervalIntegral.integral_pos hab (continuous_legendreE_integrand k).continuousOn
    (fun θ _ ↦ legendreE_integrand_nonneg k θ) ⟨c, Ioo_subset_Icc_self hc, hc_pos⟩

/-- For every modulus `k`, `E(φ, k)` is positive for positive amplitude `φ`. -/
theorem legendreE_pos {φ k : ℝ} (hφ : 0 < φ) : 0 < legendreE φ k :=
  intervalIntegral.integral_pos hφ (continuous_legendreE_integrand k).continuousOn
    (fun θ _ ↦ legendreE_integrand_nonneg k θ) ⟨0, left_mem_Icc.2 hφ.le, by simp⟩

/-- `E(φ, k)` is odd in the amplitude. -/
@[simp]
theorem legendreE_neg (φ k : ℝ) : legendreE (-φ) k = -legendreE φ k :=
  integral_comp_sin_sq_neg (fun s ↦ (1 - k ^ 2 * s) ^ (1 / 2 : ℝ)) φ

/-- `E(φ, k)` is even in the modulus. -/
@[simp]
theorem legendreE_neg_modulus (φ k : ℝ) : legendreE φ (-k) = legendreE φ k := by
  simp only [legendreE_def, neg_sq]

/-- **Quasi-periodicity of `E`**: `E(φ + nπ, k) = E(φ, k) + 2 n E(k)` for every integer `n` and
every modulus. -/
theorem legendreE_add_int_mul_pi (φ k : ℝ) (n : ℤ) :
    legendreE (φ + n * π) k = legendreE φ k + 2 * n * legendreEc k :=
  integral_comp_sin_sq_add_int_mul_pi (fun s ↦ (1 - k ^ 2 * s) ^ (1 / 2 : ℝ))
    (continuous_legendreE_integrand k) φ n

theorem legendreE_add_pi (φ k : ℝ) : legendreE (φ + π) k = legendreE φ k + 2 * legendreEc k := by
  simpa using legendreE_add_int_mul_pi φ k 1

theorem legendreE_int_mul_pi (k : ℝ) (n : ℤ) : legendreE (n * π) k = 2 * n * legendreEc k := by
  simpa using legendreE_add_int_mul_pi 0 k n

/-- At modulus `0` the integral of the second kind is the identity: `E(φ, 0) = φ`. -/
@[simp]
theorem legendreE_zero_modulus (φ : ℝ) : legendreE φ 0 = φ := by
  simp [legendreE_def]

/-- For every modulus `k`, the complete integral of the second kind `E(k)` is positive. -/
theorem legendreEc_pos (k : ℝ) : 0 < legendreEc k :=
  legendreE_pos (by positivity)

@[simp]
theorem legendreEc_neg (k : ℝ) : legendreEc (-k) = legendreEc k := legendreE_neg_modulus _ k

@[simp]
theorem legendreEc_zero : legendreEc 0 = π / 2 := legendreE_zero_modulus _

/-! ### The integral of the third kind -/

@[simp]
theorem legendrePi_zero (k α2 : ℝ) : legendrePi 0 k α2 = 0 := integral_same

/-- The integral of the third kind is a primitive of its integrand. -/
theorem hasDerivAt_legendrePi {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (φ : ℝ) :
    HasDerivAt (legendrePi · k α2)
      ((1 - α2 * sin φ ^ 2)⁻¹ * (1 - k ^ 2 * sin φ ^ 2) ^ (-1 / 2 : ℝ)) φ :=
  integral_hasDerivAt_right (intervalIntegrable_legendrePi_integrand hk hα 0 φ)
    ((continuous_legendrePi_integrand hk hα).stronglyMeasurableAtFilter _ _)
    (continuous_legendrePi_integrand hk hα).continuousAt

/-- For `k ^ 2 < 1` and `α2 < 1`, `Π(φ, k, α²)` is continuous in the amplitude `φ`. -/
theorem continuous_legendrePi {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    Continuous (legendrePi · k α2) :=
  continuous_iff_continuousAt.2 fun φ ↦ (hasDerivAt_legendrePi hk hα φ).continuousAt

/-- For `k ^ 2 < 1` and `α2 < 1`, `Π(φ, k, α²)` is strictly increasing in the amplitude `φ`. -/
theorem strictMono_legendrePi {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    StrictMono (legendrePi · k α2) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_legendrePi hk hα) (legendrePi_integrand_pos hk hα)

/-- For `k ^ 2 < 1` and `α2 < 1`, `Π(φ, k, α²)` is positive for positive amplitude `φ`. -/
theorem legendrePi_pos {φ k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (hφ : 0 < φ) :
    0 < legendrePi φ k α2 := by
  simpa using strictMono_legendrePi hk hα hφ

/-- `Π(φ, k, α²)` is odd in the amplitude. -/
@[simp]
theorem legendrePi_neg (φ k α2 : ℝ) : legendrePi (-φ) k α2 = -legendrePi φ k α2 :=
  integral_comp_sin_sq_neg (fun s ↦ (1 - α2 * s)⁻¹ * (1 - k ^ 2 * s) ^ (-1 / 2 : ℝ)) φ

/-- `Π(φ, k, α²)` is even in the modulus. -/
@[simp]
theorem legendrePi_neg_modulus (φ k α2 : ℝ) : legendrePi φ (-k) α2 = legendrePi φ k α2 := by
  simp only [legendrePi_def, neg_sq]

/-- **Quasi-periodicity of `Π`**: `Π(φ + nπ, k, α²) = Π(φ, k, α²) + 2 n Π(k, α²)` for every
integer `n`. -/
theorem legendrePi_add_int_mul_pi {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (φ : ℝ) (n : ℤ) :
    legendrePi (φ + n * π) k α2 = legendrePi φ k α2 + 2 * n * legendrePic k α2 :=
  integral_comp_sin_sq_add_int_mul_pi (fun s ↦ (1 - α2 * s)⁻¹ * (1 - k ^ 2 * s) ^ (-1 / 2 : ℝ))
    (continuous_legendrePi_integrand hk hα) φ n

theorem legendrePi_add_pi {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (φ : ℝ) :
    legendrePi (φ + π) k α2 = legendrePi φ k α2 + 2 * legendrePic k α2 := by
  simpa using legendrePi_add_int_mul_pi hk hα φ 1

theorem legendrePi_int_mul_pi {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) (n : ℤ) :
    legendrePi (n * π) k α2 = 2 * n * legendrePic k α2 := by
  simpa using legendrePi_add_int_mul_pi hk hα 0 n

/-- For `k ^ 2 < 1` and `α2 < 1`, the complete integral of the third kind `Π(k, α²)` is
positive. -/
theorem legendrePic_pos {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) : 0 < legendrePic k α2 :=
  legendrePi_pos hk hα (by positivity)

@[simp]
theorem legendrePic_neg_modulus (k α2 : ℝ) : legendrePic (-k) α2 = legendrePic k α2 :=
  legendrePi_neg_modulus _ k α2

end TauCeti.Real
