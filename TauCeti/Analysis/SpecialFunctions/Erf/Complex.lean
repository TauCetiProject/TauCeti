/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf.Basic
public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The complex error functions and Fresnel integrals

This file defines the complex error functions and the Fresnel integrals as entire functions,
with the integrals from `0` to `z` taken along the straight segment (DLMF §7.2):

* `TauCeti.Complex.erf z = (2/√π) ∫₀¹ z e^{−(sz)²} ds` (DLMF 7.2.1) and
  `TauCeti.Complex.erfc z = 1 − erf z` (DLMF 7.2.2);
* the Faddeeva function `TauCeti.faddeeva z = e^{−z²} erfc(−iz)` (DLMF 7.2.3);
* the Fresnel integrals `TauCeti.fresnelC z = ∫₀¹ z cos(π(sz)²/2) ds` and
  `TauCeti.fresnelS z = ∫₀¹ z sin(π(sz)²/2) ds` (DLMF 7.2.7–7.2.8);
* `TauCeti.fresnelTail z = (1 + i)/2 − (C(z) + i S(z))` (`ℱ`, DLMF 7.5.2) and the auxiliary
  functions `TauCeti.fresnelAuxF`, `TauCeti.fresnelAuxG` (DLMF 7.2.10–7.2.11).

## Main results

* `TauCeti.Complex.hasDerivAt_erf`, `TauCeti.hasDerivAt_fresnelC`, `TauCeti.hasDerivAt_fresnelS`:
  `erf′ = (2/√π) e^{−z²}`, `C′ = cos(πz²/2)`, `S′ = sin(πz²/2)`, with value `0` at `0`; all the
  functions above are entire.
* `TauCeti.Complex.erf_ofReal`: the complex `erf` restricts to `TauCeti.Real.erf`.
* `TauCeti.Complex.erf_conj`, `TauCeti.faddeeva_neg_conj`, `TauCeti.fresnelC_conj`,
  `TauCeti.fresnelS_conj`: the conjugation symmetries.
* `TauCeti.Complex.erf_sqrt_pi_mul`: `2 ∫₀ʷ e^{−πt²} dt = erf(√π w)` along the segment.
* The Checks of the roadmap: `erf` is odd, `w(0) = 1`, `w(iy) = e^{y²} erfc y` for real `y`,
  `ℱ(0) = (1 + i)/2`, `ℱ(z) + ℱ(−z) = 1 + i`, and `f(0) = g(0) = ½`.

## Implementation notes

A segment integral `z ∫₀¹ f(sz) ds` of an entire function `f` is `g(z) − g(0)` for any primitive
`g` of `f`, by the fundamental theorem of calculus along the segment, and a primitive exists by
Mathlib's `Differentiable.isExactOn_univ`. This gives the derivatives without differentiating
under the integral sign.

The definitions and the segment-primitive argument are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMF/ErrorFunctions/Basic/Functions.lean`,
`DLMF/Confluent/Basic/ErrorFunctions.lean` and
`DLMFMathlib/Analysis/Complex/SegmentPrimitive.lean`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §7.2, <https://dlmf.nist.gov/7.2>.
-/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory

open scoped Real ComplexConjugate

namespace TauCeti

/-- Integrating a complex derivative along the straight segment from `0` to `z` recovers the
endpoint difference. -/
private theorem mul_integral_comp_mul_eq_sub {f g : ℂ → ℂ}
    (hg : ∀ z, HasDerivAt g (f z) z) (z : ℂ) :
    z * (∫ t : ℝ in 0..1, f (t * z)) = g z - g 0 := by
  have hgd : Differentiable ℂ g := fun w => (hg w).differentiableAt
  have he : deriv g = f := funext fun w => (hg w).deriv
  have hf : Continuous f := he ▸ hgd.deriv.continuous
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => g (u * z)) (z * f (t * z)) t := by
    simpa [mul_comm] using
      ((hg (t * z)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => z * f (t * z)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => z * f (t * z))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [intervalIntegral.integral_const_mul] using h

/-- The straight-segment integral `w ↦ ∫₀¹ w f(tw) dt` of an entire function `f` is a primitive
of `f`. -/
private theorem hasDerivAt_integral_mul_comp_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z : ℂ) : HasDerivAt (fun w : ℂ => ∫ t : ℝ in 0..1, w * f (t * w)) (f z) z := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hg' (w : ℂ) := hg w (mem_univ w)
  have he : (fun w : ℂ => ∫ t : ℝ in 0..1, w * f (t * w)) = fun w => g w - g 0 := by
    funext w
    rw [intervalIntegral.integral_const_mul, mul_integral_comp_mul_eq_sub hg']
  rw [he]
  exact (hg' z).sub_const _

/-- The segment integral of an odd-in-`z` integrand: `∫₀¹ (−z) f(t(−z)) dt = −∫₀¹ z f(tz) dt` for
even `f`. -/
private theorem integral_mul_comp_mul_neg {f : ℂ → ℂ} (hf : ∀ u, f (-u) = f u) (z : ℂ) :
    ∫ t : ℝ in 0..1, -z * f (t * -z) = -∫ t : ℝ in 0..1, z * f (t * z) := by
  simp only [mul_neg, hf, neg_mul, intervalIntegral.integral_neg]

/-- Conjugation commutes with the integral over `[0, 1]`. -/
private theorem intervalIntegral_conj (f : ℝ → ℂ) :
    ∫ s in (0 : ℝ)..1, conj (f s) = conj (∫ s in (0 : ℝ)..1, f s) := by
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_conj]

namespace Complex

/-- The error function `erf z = (2/√π) ∫₀¹ z e^{−(sz)²} ds`, the integral `(2/√π) ∫₀^z e^{−t²} dt`
along the straight segment from `0` to `z` (DLMF 7.2.1). -/
def erf (z : ℂ) : ℂ :=
  2 / (Real.sqrt π : ℂ) * ∫ s in (0 : ℝ)..1, z * cexp (-((s : ℂ) * z) ^ 2)

/-- The complementary error function `erfc z = 1 − erf z` (DLMF 7.2.2). -/
def erfc (z : ℂ) : ℂ :=
  1 - erf z

theorem erf_def (z : ℂ) :
    erf z = 2 / (Real.sqrt π : ℂ) * ∫ s in (0 : ℝ)..1, z * cexp (-((s : ℂ) * z) ^ 2) := (rfl)

theorem erfc_def (z : ℂ) : erfc z = 1 - erf z := (rfl)

/-- `erf′(z) = (2/√π) e^{−z²}`. -/
theorem hasDerivAt_erf (z : ℂ) :
    HasDerivAt erf (2 / (Real.sqrt π : ℂ) * cexp (-z ^ 2)) z :=
  (hasDerivAt_integral_mul_comp_mul (f := fun u : ℂ => cexp (-u ^ 2)) (by fun_prop) z).const_mul _

/-- `erf` is entire. -/
theorem differentiable_erf : Differentiable ℂ erf := fun z => (hasDerivAt_erf z).differentiableAt

/-- `erfc′(z) = −(2/√π) e^{−z²}`. -/
theorem hasDerivAt_erfc (z : ℂ) :
    HasDerivAt erfc (-(2 / (Real.sqrt π : ℂ) * cexp (-z ^ 2))) z := by
  exact (hasDerivAt_erf z).const_sub 1

/-- `erfc` is entire. -/
theorem differentiable_erfc : Differentiable ℂ erfc :=
  fun z => (hasDerivAt_erfc z).differentiableAt

@[simp]
theorem erf_zero : erf 0 = 0 := by simp [erf_def]

@[simp]
theorem erfc_zero : erfc 0 = 1 := by simp [erfc_def]

/-- `erf` is odd. -/
theorem erf_neg (z : ℂ) : erf (-z) = -erf z := by
  rw [erf_def, erf_def, integral_mul_comp_mul_neg (f := fun u : ℂ => cexp (-u ^ 2)) (by simp)]
  ring

/-- `erfc(−z) = 2 − erfc z`. -/
theorem erfc_neg (z : ℂ) : erfc (-z) = 2 - erfc z := by
  rw [erfc_def, erfc_def, erf_neg]
  ring

/-- The complex error function restricts to Tau Ceti's real one. -/
theorem erf_ofReal (x : ℝ) : erf x = (TauCeti.Real.erf x : ℂ) := by
  have hpt (s : ℝ) :
      (x : ℂ) * cexp (-((s : ℂ) * x) ^ 2) = ((x * Real.exp (-(s * x) ^ 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  simp_rw [erf_def, hpt]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, Real.erf_def]
  have h := intervalIntegral.smul_integral_comp_mul_right (fun t => Real.exp (-t ^ 2)) x
    (a := 0) (b := 1)
  simp only [smul_eq_mul, zero_mul, one_mul] at h
  rw [← h]
  push_cast
  rfl

/-- The complementary error function restricts to Tau Ceti's real one. -/
theorem erfc_ofReal (x : ℝ) : erfc x = (TauCeti.Real.erfc x : ℂ) := by
  rw [erfc_def, erf_ofReal, Real.erfc_def]
  push_cast
  rfl

/-- `erf(z̄) = conj (erf z)`. -/
theorem erf_conj (z : ℂ) : erf (conj z) = conj (erf z) := by
  have hpt (s : ℝ) : conj z * cexp (-((s : ℂ) * conj z) ^ 2) =
      conj (z * cexp (-((s : ℂ) * z) ^ 2)) := by
    rw [map_mul, ← exp_conj]
    simp [map_pow, map_neg, map_mul, conj_ofReal]
  rw [erf_def, erf_def, funext hpt, intervalIntegral_conj, map_mul]
  congr 1
  simp [map_div₀, conj_ofReal, map_ofNat]

/-- `erfc(z̄) = conj (erfc z)`. -/
theorem erfc_conj (z : ℂ) : erfc (conj z) = conj (erfc z) := by
  simp [erfc_def, erf_conj]

/-- `2 ∫₀¹ w e^{−π(sw)²} ds`, the integral `2 ∫₀ʷ e^{−πt²} dt` along the segment, is
`erf(√π w)`. -/
theorem erf_sqrt_pi_mul (w : ℂ) :
    2 * ∫ s in (0 : ℝ)..1, w * cexp (-π * ((s : ℂ) * w) ^ 2) = erf (Real.sqrt π * w) := by
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hsq : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpt (s : ℝ) : (Real.sqrt π : ℂ) * w * cexp (-((s : ℂ) * ((Real.sqrt π : ℂ) * w)) ^ 2) =
      (Real.sqrt π : ℂ) * (w * cexp (-π * ((s : ℂ) * w) ^ 2)) := by
    rw [show ((s : ℂ) * ((Real.sqrt π : ℂ) * w)) ^ 2 = (Real.sqrt π : ℂ) ^ 2 * ((s : ℂ) * w) ^ 2
      by ring, hsq]
    ring_nf
  rw [erf_def, funext hpt, intervalIntegral.integral_const_mul (Real.sqrt π : ℂ)
    (fun s : ℝ => w * cexp (-π * ((s : ℂ) * w) ^ 2)), ← mul_assoc, div_mul_cancel₀ _ hpi]

end Complex

/-- The Faddeeva function `w(z) = e^{−z²} erfc(−iz)` (DLMF 7.2.3). -/
def faddeeva (z : ℂ) : ℂ :=
  cexp (-z ^ 2) * Complex.erfc (-I * z)

/-- The Fresnel integral `C(z) = ∫₀¹ z cos(π(sz)²/2) ds`, the integral `∫₀^z cos(πt²/2) dt`
along the segment (DLMF 7.2.7). -/
def fresnelC (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, z * Complex.cos (π * ((s : ℂ) * z) ^ 2 / 2)

/-- The Fresnel integral `S(z) = ∫₀¹ z sin(π(sz)²/2) ds`, the integral `∫₀^z sin(πt²/2) dt`
along the segment (DLMF 7.2.8). -/
def fresnelS (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, z * Complex.sin (π * ((s : ℂ) * z) ^ 2 / 2)

/-- `ℱ(z) = (1 + i)/2 − (C(z) + i S(z))` (DLMF 7.5.2). -/
def fresnelTail (z : ℂ) : ℂ :=
  (1 + I) / 2 - (fresnelC z + I * fresnelS z)

/-- The auxiliary function `f(z) = (½ − S(z)) cos(πz²/2) − (½ − C(z)) sin(πz²/2)`
(DLMF 7.2.10). -/
def fresnelAuxF (z : ℂ) : ℂ :=
  (1 / 2 - fresnelS z) * Complex.cos (π * z ^ 2 / 2) -
    (1 / 2 - fresnelC z) * Complex.sin (π * z ^ 2 / 2)

/-- The auxiliary function `g(z) = (½ − C(z)) cos(πz²/2) + (½ − S(z)) sin(πz²/2)`
(DLMF 7.2.11). -/
def fresnelAuxG (z : ℂ) : ℂ :=
  (1 / 2 - fresnelC z) * Complex.cos (π * z ^ 2 / 2) +
    (1 / 2 - fresnelS z) * Complex.sin (π * z ^ 2 / 2)

/-- `w(z) = e^{−z²} erfc(−iz)`. -/
theorem faddeeva_def (z : ℂ) : faddeeva z = cexp (-z ^ 2) * Complex.erfc (-I * z) := (rfl)

/-- The Faddeeva function is entire. -/
theorem differentiable_faddeeva : Differentiable ℂ faddeeva := by
  unfold faddeeva
  exact (by fun_prop : Differentiable ℂ fun z : ℂ => cexp (-z ^ 2)).mul
    (Complex.differentiable_erfc.comp (by fun_prop))

/-- `w(0) = 1`. -/
@[simp]
theorem faddeeva_zero : faddeeva 0 = 1 := by simp [faddeeva_def]

/-- `w(iy) = e^{y²} erfc y` for real `y`, with `TauCeti.Real.erfc`. -/
theorem faddeeva_I_mul (y : ℝ) :
    faddeeva (I * y) = (Real.exp (y ^ 2) : ℂ) * (TauCeti.Real.erfc y : ℂ) := by
  have h1 : -I * (I * y) = (y : ℂ) := by
    ring_nf
    rw [I_sq]
    ring
  have h2 : -(I * (y : ℂ)) ^ 2 = ((y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [faddeeva_def, h1, h2, Complex.erfc_ofReal, ofReal_exp]

/-- `w(−z̄) = conj (w z)`. -/
theorem faddeeva_neg_conj (z : ℂ) : faddeeva (-conj z) = conj (faddeeva z) := by
  have h : -I * -conj z = conj (-I * z) := by simp [conj_I]
  rw [faddeeva_def, faddeeva_def, h, Complex.erfc_conj, map_mul, ← exp_conj]
  simp [map_neg, map_pow]

/-- `C′(z) = cos(πz²/2)`. -/
theorem hasDerivAt_fresnelC (z : ℂ) :
    HasDerivAt fresnelC (Complex.cos (π * z ^ 2 / 2)) z :=
  hasDerivAt_integral_mul_comp_mul (f := fun u : ℂ => Complex.cos (π * u ^ 2 / 2))
    (by fun_prop) z

/-- `S′(z) = sin(πz²/2)`. -/
theorem hasDerivAt_fresnelS (z : ℂ) :
    HasDerivAt fresnelS (Complex.sin (π * z ^ 2 / 2)) z :=
  hasDerivAt_integral_mul_comp_mul (f := fun u : ℂ => Complex.sin (π * u ^ 2 / 2))
    (by fun_prop) z

/-- `C` is entire. -/
theorem differentiable_fresnelC : Differentiable ℂ fresnelC :=
  fun z => (hasDerivAt_fresnelC z).differentiableAt

/-- `S` is entire. -/
theorem differentiable_fresnelS : Differentiable ℂ fresnelS :=
  fun z => (hasDerivAt_fresnelS z).differentiableAt

/-- `ℱ` is entire. -/
theorem differentiable_fresnelTail : Differentiable ℂ fresnelTail := by
  unfold fresnelTail
  exact (differentiable_const _).sub
    (differentiable_fresnelC.add ((differentiable_const _).mul differentiable_fresnelS))

/-- The auxiliary function `f` is entire. -/
theorem differentiable_fresnelAuxF : Differentiable ℂ fresnelAuxF := by
  unfold fresnelAuxF
  have := differentiable_fresnelC
  have := differentiable_fresnelS
  fun_prop

/-- The auxiliary function `g` is entire. -/
theorem differentiable_fresnelAuxG : Differentiable ℂ fresnelAuxG := by
  unfold fresnelAuxG
  have := differentiable_fresnelC
  have := differentiable_fresnelS
  fun_prop

@[simp]
theorem fresnelC_zero : fresnelC 0 = 0 := by simp [fresnelC]

@[simp]
theorem fresnelS_zero : fresnelS 0 = 0 := by simp [fresnelS]

/-- `C` is odd. -/
theorem fresnelC_neg (z : ℂ) : fresnelC (-z) = -fresnelC z :=
  integral_mul_comp_mul_neg (f := fun u : ℂ => Complex.cos (π * u ^ 2 / 2)) (by simp) z

/-- `S` is odd. -/
theorem fresnelS_neg (z : ℂ) : fresnelS (-z) = -fresnelS z :=
  integral_mul_comp_mul_neg (f := fun u : ℂ => Complex.sin (π * u ^ 2 / 2)) (by simp) z

/-- `C(z̄) = conj (C z)`. -/
theorem fresnelC_conj (z : ℂ) : fresnelC (conj z) = conj (fresnelC z) := by
  have hpt (s : ℝ) : conj z * Complex.cos (π * ((s : ℂ) * conj z) ^ 2 / 2) =
      conj (z * Complex.cos (π * ((s : ℂ) * z) ^ 2 / 2)) := by
    rw [map_mul, ← cos_conj]
    simp [map_pow, map_mul, map_div₀, conj_ofReal, map_ofNat]
  rw [fresnelC, fresnelC, funext hpt, intervalIntegral_conj]

/-- `S(z̄) = conj (S z)`. -/
theorem fresnelS_conj (z : ℂ) : fresnelS (conj z) = conj (fresnelS z) := by
  have hpt (s : ℝ) : conj z * Complex.sin (π * ((s : ℂ) * conj z) ^ 2 / 2) =
      conj (z * Complex.sin (π * ((s : ℂ) * z) ^ 2 / 2)) := by
    rw [map_mul, ← sin_conj]
    simp [map_pow, map_mul, map_div₀, conj_ofReal, map_ofNat]
  rw [fresnelS, fresnelS, funext hpt, intervalIntegral_conj]

/-- `ℱ(0) = (1 + i)/2`. -/
@[simp]
theorem fresnelTail_zero : fresnelTail 0 = (1 + I) / 2 := by simp [fresnelTail]

/-- `ℱ(z) + ℱ(−z) = 1 + i`. -/
theorem fresnelTail_add_fresnelTail_neg (z : ℂ) : fresnelTail z + fresnelTail (-z) = 1 + I := by
  rw [fresnelTail, fresnelTail, fresnelC_neg, fresnelS_neg]
  ring

/-- `f(0) = ½`. -/
@[simp]
theorem fresnelAuxF_zero : fresnelAuxF 0 = 1 / 2 := by simp [fresnelAuxF]

/-- `g(0) = ½`. -/
@[simp]
theorem fresnelAuxG_zero : fresnelAuxG 0 = 1 / 2 := by simp [fresnelAuxG]

end TauCeti
