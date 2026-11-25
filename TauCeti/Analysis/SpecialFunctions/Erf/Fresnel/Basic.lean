/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HasPrimitives.Basic
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Fresnel integrals

This file defines the Fresnel integrals as entire functions, with the integral from `0` to `z`
taken along the straight segment (DLMF §7.2):

* `TauCeti.fresnelC z = ∫₀¹ z cos(π(sz)²/2) ds` and `TauCeti.fresnelS z = ∫₀¹ z sin(π(sz)²/2) ds`
  (DLMF 7.2.7–7.2.8);
* `TauCeti.fresnelTail z = (1 + i)/2 − (C(z) + i S(z))` (`ℱ`, DLMF 7.5.2) and the auxiliary
  functions `TauCeti.fresnelAuxF`, `TauCeti.fresnelAuxG` (DLMF 7.2.10–7.2.11).

## Main results

* `TauCeti.hasDerivAt_fresnelC`, `TauCeti.hasDerivAt_fresnelS`, `TauCeti.deriv_fresnelC`,
  `TauCeti.deriv_fresnelS`: `C′ = cos(πz²/2)` and `S′ = sin(πz²/2)`, with value `0` at `0`; all
  the functions above are entire.
* `TauCeti.fresnelC_conj`, `TauCeti.fresnelS_conj`: the conjugation symmetries.
* Special values and symmetry identities: `C` and `S` are odd, `ℱ(0) = (1 + i)/2`,
  `ℱ(z) + ℱ(−z) = 1 + i`, and `f(0) = g(0) = ½`.

## Implementation notes

A segment integral `z ∫₀¹ f(sz) ds` of an entire function `f` is a primitive of `f`
(`Differentiable.hasDerivAt_integral_mul_comp_mul`). This gives the derivatives without
differentiating under the integral sign. Oddness and the conjugation symmetry come from
`TauCeti.intervalIntegral.integral_mul_comp_mul_neg` and
`TauCeti.intervalIntegral.integral_mul_comp_mul_conj`.

The definitions and proofs are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/ErrorFunctions/Basic/Functions.lean`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §7.2, <https://dlmf.nist.gov/7.2>.
-/

public section

noncomputable section

open Complex Set MeasureTheory

open scoped Real ComplexConjugate

namespace TauCeti

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

theorem fresnelC_def (z : ℂ) :
    fresnelC z = ∫ s in (0 : ℝ)..1, z * Complex.cos (π * ((s : ℂ) * z) ^ 2 / 2) := (rfl)

theorem fresnelS_def (z : ℂ) :
    fresnelS z = ∫ s in (0 : ℝ)..1, z * Complex.sin (π * ((s : ℂ) * z) ^ 2 / 2) := (rfl)

theorem fresnelTail_def (z : ℂ) : fresnelTail z = (1 + I) / 2 - (fresnelC z + I * fresnelS z) :=
  (rfl)

theorem fresnelAuxF_def (z : ℂ) :
    fresnelAuxF z = (1 / 2 - fresnelS z) * Complex.cos (π * z ^ 2 / 2) -
      (1 / 2 - fresnelC z) * Complex.sin (π * z ^ 2 / 2) := (rfl)

theorem fresnelAuxG_def (z : ℂ) :
    fresnelAuxG z = (1 / 2 - fresnelC z) * Complex.cos (π * z ^ 2 / 2) +
      (1 / 2 - fresnelS z) * Complex.sin (π * z ^ 2 / 2) := (rfl)

/-- `C′(z) = cos(πz²/2)`. -/
theorem hasDerivAt_fresnelC (z : ℂ) :
    HasDerivAt fresnelC (Complex.cos (π * z ^ 2 / 2)) z :=
  Differentiable.hasDerivAt_integral_mul_comp_mul (f := fun u : ℂ => Complex.cos (π * u ^ 2 / 2))
    (by fun_prop) z

/-- `S′(z) = sin(πz²/2)`. -/
theorem hasDerivAt_fresnelS (z : ℂ) :
    HasDerivAt fresnelS (Complex.sin (π * z ^ 2 / 2)) z :=
  Differentiable.hasDerivAt_integral_mul_comp_mul (f := fun u : ℂ => Complex.sin (π * u ^ 2 / 2))
    (by fun_prop) z

/-- `C` is entire. -/
@[fun_prop]
theorem differentiable_fresnelC : Differentiable ℂ fresnelC :=
  fun z => (hasDerivAt_fresnelC z).differentiableAt

/-- `S` is entire. -/
@[fun_prop]
theorem differentiable_fresnelS : Differentiable ℂ fresnelS :=
  fun z => (hasDerivAt_fresnelS z).differentiableAt

/-- `C′ = cos(πz²/2)`, as a function. -/
@[simp]
theorem deriv_fresnelC : deriv fresnelC = fun z => Complex.cos (π * z ^ 2 / 2) :=
  funext fun z => (hasDerivAt_fresnelC z).deriv

/-- `S′ = sin(πz²/2)`, as a function. -/
@[simp]
theorem deriv_fresnelS : deriv fresnelS = fun z => Complex.sin (π * z ^ 2 / 2) :=
  funext fun z => (hasDerivAt_fresnelS z).deriv

/-- `ℱ` is entire. -/
@[fun_prop]
theorem differentiable_fresnelTail : Differentiable ℂ fresnelTail := by
  rw [funext fresnelTail_def]
  fun_prop

/-- The auxiliary function `f` is entire. -/
@[fun_prop]
theorem differentiable_fresnelAuxF : Differentiable ℂ fresnelAuxF := by
  rw [funext fresnelAuxF_def]
  fun_prop

/-- The auxiliary function `g` is entire. -/
@[fun_prop]
theorem differentiable_fresnelAuxG : Differentiable ℂ fresnelAuxG := by
  rw [funext fresnelAuxG_def]
  fun_prop

@[simp]
theorem fresnelC_zero : fresnelC 0 = 0 := by simp [fresnelC_def]

@[simp]
theorem fresnelS_zero : fresnelS 0 = 0 := by simp [fresnelS_def]

/-- `C` is odd. -/
@[simp]
theorem fresnelC_neg (z : ℂ) : fresnelC (-z) = -fresnelC z := by
  rw [fresnelC_def, fresnelC_def, TauCeti.intervalIntegral.integral_mul_comp_mul_neg
    (f := fun u : ℂ => Complex.cos (π * u ^ 2 / 2)) (by simp)]

/-- `S` is odd. -/
@[simp]
theorem fresnelS_neg (z : ℂ) : fresnelS (-z) = -fresnelS z := by
  rw [fresnelS_def, fresnelS_def, TauCeti.intervalIntegral.integral_mul_comp_mul_neg
    (f := fun u : ℂ => Complex.sin (π * u ^ 2 / 2)) (by simp)]

/-- `C(conj z) = conj (C z)`. -/
theorem fresnelC_conj (z : ℂ) : fresnelC (conj z) = conj (fresnelC z) := by
  rw [fresnelC_def, fresnelC_def, TauCeti.intervalIntegral.integral_mul_comp_mul_conj
    (f := fun u : ℂ => Complex.cos (π * u ^ 2 / 2)) (fun u => by simp [← cos_conj, map_ofNat])]

/-- `S(conj z) = conj (S z)`. -/
theorem fresnelS_conj (z : ℂ) : fresnelS (conj z) = conj (fresnelS z) := by
  rw [fresnelS_def, fresnelS_def, TauCeti.intervalIntegral.integral_mul_comp_mul_conj
    (f := fun u : ℂ => Complex.sin (π * u ^ 2 / 2)) (fun u => by simp [← sin_conj, map_ofNat])]

/-- `ℱ(0) = (1 + i)/2`. -/
@[simp]
theorem fresnelTail_zero : fresnelTail 0 = (1 + I) / 2 := by simp [fresnelTail_def]

/-- `ℱ(z) + ℱ(−z) = 1 + i`. -/
theorem fresnelTail_add_fresnelTail_neg (z : ℂ) : fresnelTail z + fresnelTail (-z) = 1 + I := by
  rw [fresnelTail_def, fresnelTail_def, fresnelC_neg, fresnelS_neg]
  ring

/-- `f(0) = ½`. -/
@[simp]
theorem fresnelAuxF_zero : fresnelAuxF 0 = 1 / 2 := by simp [fresnelAuxF_def]

/-- `g(0) = ½`. -/
@[simp]
theorem fresnelAuxG_zero : fresnelAuxG 0 = 1 / 2 := by simp [fresnelAuxG_def]

end TauCeti
