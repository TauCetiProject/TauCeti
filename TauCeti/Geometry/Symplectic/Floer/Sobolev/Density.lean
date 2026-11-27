/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The `W^{1,2}` energy density of a section

For a map `ξ : ℝ × ℝ → V` into a normed space, the `W^{1,2}` energy density
`‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` (`TauCeti.Floer.sobolevDensity`) is the integrand of the squared
`W^{1,2}` norm of `ξ` in the coordinates `(s, t)`, the derivatives being taken along the coordinate
vectors `TauCeti.stdComplexLineReal` and `TauCeti.stdComplexLineImag`. It is the energy that the
semi-Fredholm and other linear estimates of the linearized Floer operator control. The file also
records the derivatives of a section cut off by a function of `s`.

## Main results

* `TauCeti.Floer.sobolevDensity_nonneg`: the density is nonnegative.
* `TauCeti.Floer.continuous_sobolevDensity`, `TauCeti.Floer.continuousAt_sobolevDensity`: the
  density of a `C¹` map is continuous, and that of a map `C¹` at a point is continuous there.
* `TauCeti.Floer.sobolevDensity_congr_of_eventuallyEq`: the density at `z` depends only on the
  germ of the map at `z`.
* `TauCeti.Floer.integrableOn_sobolevDensity_of_eventuallyEq_zero`: a map with continuous density
  that vanishes beyond some `N` in `s` has integrable density over every half-cylinder
  `(a, ∞) × [0, 1]`.
* `TauCeti.Floer.fderiv_smul_fst_apply_stdComplexLineReal`,
  `TauCeti.Floer.fderiv_smul_fst_apply_stdComplexLineImag`: the derivatives of a section cut off
  by a function `β(s)` are `∂s (β ξ) = β ∂s ξ + β' ξ` and `∂t (β ξ) = β ∂t ξ`.
* `TauCeti.Floer.sobolevDensity_add_le`: the density of `ξ₁ + ξ₂` is at most twice the sum of the
  densities of `ξ₁` and `ξ₂`.
* `TauCeti.Floer.setLIntegral_le_ofReal_mul_setIntegral_sobolevDensity`: on a compact set where a
  conformal weight `ρ` is at most `B`, the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` is at
  most `B + 1` times the `W^{1,2}` energy.
* `TauCeti.Floer.setIntegral_norm_sq_le_setIntegral_sobolevDensity`: the density bounds `‖ξ‖²`, so
  on a compact set where a `C¹` map `g` equals `η`, the energy of `g` bounds the `L²` norm of `η`.
* `TauCeti.Floer.setIntegral_sobolevDensity_le_of_eventuallyEq_one`: if `β = 1` near every point
  of `s` and `s ⊆ t` with `t` compact, the energy of `ξ` on `s` is at most that of `β ξ` on `t`.
-/

public section

open MeasureTheory Set ContinuousLinearMap
open scoped Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The `W^{1,2}` energy density `‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` of a map `ξ : ℝ × ℝ → V`. -/
noncomputable def sobolevDensity (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ :=
  ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2

theorem sobolevDensity_apply (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    sobolevDensity ξ z =
      ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
        ‖ξ z‖ ^ 2 :=
  (rfl)

theorem sobolevDensity_nonneg (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : 0 ≤ sobolevDensity ξ z := by
  rw [sobolevDensity_apply]
  positivity

/-- The zero map has zero energy density. -/
@[simp]
theorem sobolevDensity_zero (z : ℝ × ℝ) : sobolevDensity (0 : ℝ × ℝ → V) z = 0 := by
  simp [sobolevDensity_apply]

/-- The `W^{1,2}` energy density of a map that is `C¹` at `z` is continuous at `z`. -/
theorem continuousAt_sobolevDensity {ξ : ℝ × ℝ → V} {z : ℝ × ℝ} (hξ : ContDiffAt ℝ 1 ξ z) :
    ContinuousAt (sobolevDensity ξ) z := by
  have := hξ.continuousAt_fderiv one_ne_zero
  have := hξ.continuousAt
  simp only [funext (sobolevDensity_apply ξ)]
  fun_prop

/-- The `W^{1,2}` energy density of a `C¹` map is continuous. -/
theorem continuous_sobolevDensity {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) :
    Continuous (sobolevDensity ξ) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_sobolevDensity hξ.contDiffAt

/-- Two maps that agree near `z` have the same energy density at `z`. -/
theorem sobolevDensity_congr_of_eventuallyEq {ξ η : ℝ × ℝ → V} {z : ℝ × ℝ}
    (h : ξ =ᶠ[𝓝 z] η) :
    sobolevDensity ξ z = sobolevDensity η z := by
  rw [sobolevDensity_apply, sobolevDensity_apply, h.fderiv_eq, h.eq_of_nhds]

/-- A map with continuous `W^{1,2}` energy density (for instance a `C¹` map,
`continuous_sobolevDensity`) that vanishes near every point beyond `N` in the longitudinal
coordinate has integrable density over every half-cylinder `(a, ∞) × [0, 1]`. -/
theorem integrableOn_sobolevDensity_of_eventuallyEq_zero {g : ℝ × ℝ → V}
    (hg : Continuous (sobolevDensity g)) {N : ℝ} (hzero : ∀ ζ : ℝ × ℝ, N < ζ.1 → g =ᶠ[𝓝 ζ] 0)
    (a : ℝ) : IntegrableOn (sobolevDensity g) (Ioi a ×ˢ Icc 0 1) := by
  have hK : IsCompact (Icc a N ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  refine (hg.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
  have hζN : N < ζ.1 := by
    by_contra! h
    exact hζ.2 ⟨⟨le_of_lt hζ.1.1, h⟩, hζ.1.2⟩
  rw [sobolevDensity_congr_of_eventuallyEq (hzero ζ hζN), sobolevDensity_zero]

/-- The `s`-derivative of a section cut off by a function `β(s)`: `∂s (β ξ) = β ∂s ξ + β' ξ`. -/
theorem fderiv_smul_fst_apply_stdComplexLineReal {ξ : ℝ × ℝ → V} {β : ℝ → ℝ} {β' : ℝ}
    {z : ℝ × ℝ} (hβ : HasDerivAt β β' z.1) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal =
      β z.1 • fderiv ℝ ξ z stdComplexLineReal + β' • ξ z := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1 • ξ w) _ z :=
    (hβ.hasFDerivAt.comp z hasFDerivAt_fst).smul hξ.hasFDerivAt
  rw [hd.fderiv]
  simp [stdComplexLineReal_eq, add_comm]

/-- The `t`-derivative of a section cut off by a function `β(s)`: `∂t (β ξ) = β ∂t ξ`. -/
theorem fderiv_smul_fst_apply_stdComplexLineImag {ξ : ℝ × ℝ → V} {β : ℝ → ℝ} {z : ℝ × ℝ}
    (hβ : DifferentiableAt ℝ β z.1) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag =
      β z.1 • fderiv ℝ ξ z stdComplexLineImag := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1 • ξ w) _ z :=
    (hβ.hasDerivAt.hasFDerivAt.comp z hasFDerivAt_fst).smul hξ.hasFDerivAt
  rw [hd.fderiv]
  simp [stdComplexLineImag_eq]

/-- The `W^{1,2}` energy density of a section splits over a sum: the density of `ξ₁ + ξ₂` is at
most twice the sum of the densities of `ξ₁` and `ξ₂`. -/
theorem sobolevDensity_add_le {ξ₁ ξ₂ : ℝ × ℝ → V} {z : ℝ × ℝ} (h₁ : DifferentiableAt ℝ ξ₁ z)
    (h₂ : DifferentiableAt ℝ ξ₂ z) :
    sobolevDensity (ξ₁ + ξ₂) z ≤ 2 * sobolevDensity ξ₁ z + 2 * sobolevDensity ξ₂ z := by
  have hsq (x y : V) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2).trans add_sq_le
  simp only [sobolevDensity_apply]
  rw [fderiv_add h₁ h₂]
  simp only [add_apply, Pi.add_apply]
  linarith [hsq (fderiv ℝ ξ₁ z stdComplexLineReal) (fderiv ℝ ξ₂ z stdComplexLineReal),
    hsq (fderiv ℝ ξ₁ z stdComplexLineImag) (fderiv ℝ ξ₂ z stdComplexLineImag), hsq (ξ₁ z) (ξ₂ z)]

/-- If a `C¹` map `g` agrees with `η` on a compact set `s`, the `L²` norm of `η` on `s` is at most
the `W^{1,2}` energy of `g` there. -/
theorem setIntegral_norm_sq_le_setIntegral_sobolevDensity {η g : ℝ × ℝ → V} {s : Set (ℝ × ℝ)}
    (hs : IsCompact s) (hηi : IntegrableOn (fun z ↦ ‖η z‖ ^ 2) s) (hg : ContDiff ℝ 1 g)
    (hgη : EqOn g η s) :
    ∫ z in s, ‖η z‖ ^ 2 ≤ ∫ z in s, sobolevDensity g z :=
  setIntegral_mono_on hηi ((continuous_sobolevDensity hg).continuousOn.integrableOn_compact hs)
    hs.measurableSet fun z hz ↦ by
      rw [sobolevDensity_apply, ← hgη hz]
      have := sq_nonneg ‖fderiv ℝ g z stdComplexLineReal‖
      have := sq_nonneg ‖fderiv ℝ g z stdComplexLineImag‖
      linarith

/-- **Comparing with a cut-off map.** If `β = 1` near every point of a measurable set `s`, and `s`
lies in a compact set `t`, then the `W^{1,2}` energy of `ξ` on `s` is at most the energy of the
`C¹` map `β ξ` on `t`. -/
theorem setIntegral_sobolevDensity_le_of_eventuallyEq_one {ξ : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ}
    {s t : Set (ℝ × ℝ)} (hs : MeasurableSet s) (ht : IsCompact t) (hst : s ⊆ t)
    (hβ1 : ∀ z ∈ s, β =ᶠ[𝓝 z] 1) (hβξ : ContDiff ℝ 1 fun z ↦ β z • ξ z) :
    ∫ z in s, sobolevDensity ξ z ≤ ∫ z in t, sobolevDensity (fun z ↦ β z • ξ z) z := by
  refine le_of_eq_of_le (setIntegral_congr_fun hs fun z hz ↦ ?_)
    (setIntegral_mono_set ((continuous_sobolevDensity hβξ).continuousOn.integrableOn_compact ht)
      (ae_of_all _ fun z ↦ sobolevDensity_nonneg _ z) (ae_of_all _ hst))
  -- Near `s` the cut-off map agrees with `ξ`.
  refine (sobolevDensity_congr_of_eventuallyEq ((hβ1 z hz).mono fun z' h ↦ ?_)).symm
  simp [h]

/-- **The weighted energy on a compact set.** On a compact set `K` where a weight `ρ` is at most
`B ≥ 0`, the weighted energy `∫_K (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of a `C¹` section is at most `B + 1`
times its `W^{1,2}` energy on `K`. -/
theorem setLIntegral_le_ofReal_mul_setIntegral_sobolevDensity {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {ρ : ℝ × ℝ → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z ∈ K, ρ z ≤ B)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) :
    ∫⁻ z in K, ENNReal.ofReal (ρ z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal ((B + 1) * ∫ z in K, sobolevDensity ξ z) := by
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
    (((continuous_sobolevDensity hξ).continuousOn.integrableOn_compact hK).const_mul _)
    (ae_of_all _ fun z ↦ mul_nonneg (by positivity) (sobolevDensity_nonneg ξ z))]
  refine setLIntegral_mono' hK.measurableSet fun z hz ↦ ENNReal.ofReal_le_ofReal ?_
  rw [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  nlinarith [mul_le_mul_of_nonneg_right (hB z hz) (sq_nonneg ‖ξ z‖),
    sq_nonneg ‖fderiv ℝ ξ z (1, 0)‖, sq_nonneg ‖fderiv ℝ ξ z (0, 1)‖, sq_nonneg ‖ξ z‖]

end TauCeti.Floer
