/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Background
public import TauCeti.Analysis.PDE.Regularity.PlanarPoisson
public import TauCeti.Analysis.PDE.Regularity.Semilinear
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Smoothness of weak solutions of the reduced vortex equation

Let `f` be holomorphic on an open set `U ⊆ ℂ`, for instance a polynomial `P` on `U = ℂ`. Taubes's
reduced vortex equation for a correction `w` of the background amplitude
`u₀ = -log (1 + |f|²) / 2` (`TauCeti.Vortex.backgroundAmplitude`) is

`Δw = (exp(2w) h - 1) / 8 + g`,    `h = |f|² / (1 + |f|²)`,    `g = 2 |f'|² / (1 + |f|²)²`,

with `h = TauCeti.Vortex.backgroundWeight f`. Variational methods produce `w` only as a weak
solution. This file shows that a weak solution that is continuous is smooth, and that the field
reconstructed from it is a classical vortex.

If `w` is continuous on `U` and solves the reduced equation in the sense of distributions,
`∫ Δφ · w = ∫ φ ((exp(2w) h - 1) / 8 + g)` for every test function `φ` on `U`, then `w` is smooth
on `U`. The right side is a smooth function of the position and of the value of `w`, so this is
the planar semilinear bootstrap `TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`.
The field `amplitudeField (u₀ + w) f`, with section `exp(u₀ + w) f`, then solves the vortex
equation at every point of `U`, by
`TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff`.

For a monic polynomial `P` of degree `m ≥ 1` and `U = ℂ`, such a field has the degree-`m` end
framing exactly when `w → 0` at infinity
(`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff`). Since
`exp(u₀ + w)` has no zeros, its section `exp(u₀ + w) P` vanishes exactly at the roots of `P`.

Taubes's existence proof minimizes `TauCeti.Vortex.taubesFunctional` over `H¹`, so it produces a
weak solution `u ∈ H¹(Ω)` of `Δw = h (exp (2w) - 1) / 8 + k` in the energy form
`∫_Ω ⟨∇u, ∇v⟩ = -∫_Ω (h (exp (2w) - 1) / 8 + k) v` for every `v ∈ H¹₀(Ω)`, for coefficients `h`
and `k` smooth on an open subset `Ω` of `EuclideanSpace ℝ (Fin 2)`. If `u` agrees almost
everywhere with a function `w` continuous on `Ω`, then `w` is smooth on `Ω`: this is the case
`a = 1`, `A = -h / 8`, `Φ(t) = exp (2t)`, `C = h / 8 - k` of the semilinear bootstrap
`TauCeti.PDE.UniformlyEllipticOn.contDiffOn_of_energyFormH1_eq`.

## Main results

All in the namespace `TauCeti.Vortex`:

* `contDiffOn_of_forall_integral_laplacian_mul_eq_reduced`: a continuous weak solution of the
  reduced equation is smooth.
* `equation_amplitudeField_backgroundAmplitude_add_eq_zero_of_forall_integral_laplacian_mul_eq`:
  the field reconstructed from it solves the vortex equation.
* `contDiff_amplitudeField_backgroundAmplitude_add_of_forall_integral_laplacian_mul_eq`: for
  entire `f` and `U = ℂ`, that field is smooth on the plane.
* `contDiffOn_of_energyFormH1_eq_neg`: a continuous `H¹` weak solution of the reduced equation, in
  the energy form, is smooth.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, §4.
-/

public section

namespace TauCeti.Vortex

open InnerProductSpace Laplacian MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

variable {U : Opens ℂ} {f : ℂ → ℂ} {w : ℂ → ℝ}

/-- The right side of the reduced vortex equation is a smooth function of the position and of the
value of the correction, on the open set where `f` is holomorphic. -/
private theorem contDiffOn_reducedRightSide (hf : AnalyticOnNhd ℂ f U) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℝ ↦ (Real.exp (2 * p.2) * backgroundWeight f p.1 - 1) / 8 +
      2 * ‖deriv f p.1‖ ^ 2 / (1 + ‖f p.1‖ ^ 2) ^ 2) (U ×ˢ univ) := by
  have hf' : ContDiffOn ℝ ∞ f U := (hf.contDiffOn (n := ∞) U.isOpen.uniqueDiffOn).restrict_scalars ℝ
  have hdf : ContDiffOn ℝ ∞ (deriv f) U :=
    (hf.deriv.contDiffOn (n := ∞) U.isOpen.uniqueDiffOn).restrict_scalars ℝ
  have hfst : MapsTo (fun p : ℂ × ℝ ↦ p.1) (U ×ˢ univ) U := fun p hp ↦ hp.1
  have hfp : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ ↦ f p.1) (U ×ˢ univ) := hf'.comp contDiffOn_fst hfst
  have hdfp : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ ↦ deriv f p.1) (U ×ˢ univ) :=
    hdf.comp contDiffOn_fst hfst
  have hnorm : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ ↦ 1 + ‖f p.1‖ ^ 2) (U ×ˢ univ) :=
    contDiffOn_const.add (hfp.norm_sq ℝ)
  have hweight : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ ↦ backgroundWeight f p.1) (U ×ˢ univ) := by
    simp only [backgroundWeight_def]
    exact (hfp.norm_sq ℝ).div hnorm fun p _ ↦ by positivity
  refine (((Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul contDiffOn_snd)).mul
    hweight).sub contDiffOn_const).div_const _ |>.add ?_
  exact (contDiffOn_const.mul (hdfp.norm_sq ℝ)).div (hnorm.pow 2) fun p _ ↦ by positivity

/-- **Weak solutions of the reduced vortex equation are smooth.** Let `f` be holomorphic on the open
set `U ⊆ ℂ`, and let `w` be continuous on `U` and solve the reduced vortex equation
`Δw = (exp(2w) h - 1) / 8 + 2 |f'|² / (1 + |f|²)²`, `h = TauCeti.Vortex.backgroundWeight f`, in the
sense of distributions on `U`. Then `w` is smooth on `U`. -/
theorem contDiffOn_of_forall_integral_laplacian_mul_eq_reduced (hf : AnalyticOnNhd ℂ f U)
    (hw : ContinuousOn w U)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ x, Δ (φ : ℂ → ℝ) x * w x = ∫ x, φ x *
      ((Real.exp (2 * w x) * backgroundWeight f x - 1) / 8 +
        2 * ‖deriv f x‖ ^ 2 / (1 + ‖f x‖ ^ 2) ^ 2)) :
    ContDiffOn ℝ ∞ w U := by
  simpa using contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp (k := ⊤)
    (contDiffOn_reducedRightSide hf) hw h

/-- **Weak solutions of the reduced vortex equation give classical vortices.** Let `f` be
holomorphic on the open set `U ⊆ ℂ`, and let `w` be continuous on `U` and solve the reduced vortex
equation in the sense of distributions on `U`. Then the field reconstructed from the amplitude
`u₀ + w`, `u₀ = TauCeti.Vortex.backgroundAmplitude f`, with section `exp(u₀ + w) f`, solves the
vortex equation at every point of `U`. -/
theorem equation_amplitudeField_backgroundAmplitude_add_eq_zero_of_forall_integral_laplacian_mul_eq
    (hf : AnalyticOnNhd ℂ f U) (hw : ContinuousOn w U)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ x, Δ (φ : ℂ → ℝ) x * w x = ∫ x, φ x *
      ((Real.exp (2 * w x) * backgroundWeight f x - 1) / 8 +
        2 * ‖deriv f x‖ ^ 2 / (1 + ‖f x‖ ^ 2) ^ 2))
    {z : ℂ} (hz : z ∈ U) :
    equation (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) z = 0 := by
  have hreg := contDiffOn_reducedRightSide hf
  rw [equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff (hf z hz)
    (((contDiffOn_of_forall_integral_laplacian_mul_eq_reduced hf hw h).of_le (by simp)).contDiffAt
      (U.isOpen.mem_nhds hz))]
  exact eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp (hreg.of_le (by simp)) hw h hz

/-- **A continuous weak solution of the reduced equation on the plane gives a smooth vortex.** Let
`f` be entire, for instance a polynomial, and let `w` be continuous on `ℂ` and solve the reduced
vortex equation in the sense of distributions on `ℂ`. Then the field reconstructed from the
amplitude `u₀ + w`, `u₀ = TauCeti.Vortex.backgroundAmplitude f`, is smooth on `ℂ`; it solves the
vortex equation everywhere by the preceding theorem. -/
theorem contDiff_amplitudeField_backgroundAmplitude_add_of_forall_integral_laplacian_mul_eq
    (hf : Differentiable ℂ f) (hw : Continuous w)
    (h : ∀ φ : 𝓓((⊤ : Opens ℂ), ℝ), ∫ x, Δ (φ : ℂ → ℝ) x * w x = ∫ x, φ x *
      ((Real.exp (2 * w x) * backgroundWeight f x - 1) / 8 +
        2 * ‖deriv f x‖ ^ 2 / (1 + ‖f x‖ ^ 2) ^ 2)) :
    ContDiff ℝ ∞ (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) := by
  have hfa : AnalyticOnNhd ℂ f (⊤ : Opens ℂ) := fun z _ ↦ hf.analyticAt z
  have hwc : ContDiff ℝ ∞ w := by
    rw [← contDiffOn_univ]
    simpa using contDiffOn_of_forall_integral_laplacian_mul_eq_reduced hfa hw.continuousOn h
  have hfc : ContDiff ℝ ∞ f := (hf.contDiff (n := ∞)).restrict_scalars ℝ
  exact contDiff_amplitudeField (n := ⊤)
    (((contDiff_backgroundAmplitude hfc).add hwc).of_le (by simp)) hfc

/-- **Continuous `H¹` weak solutions of Taubes's reduced vortex equation are smooth.** Let `h` and
`k` be smooth on an open subset `Ω` of the plane. If `u ∈ H¹(Ω)` agrees almost everywhere on `Ω`
with a function `w` continuous on `Ω`, and weakly solves `Δw = h (exp (2w) - 1) / 8 + k`, in the
sense that `∫_Ω ⟨∇u, ∇v⟩ = -∫_Ω (h (exp (2w) - 1) / 8 + k) v` for every `v ∈ H¹₀(Ω)`, then `w` is
smooth on `Ω`. -/
theorem contDiffOn_of_energyFormH1_eq_neg {Omega : Opens (EuclideanSpace ℝ (Fin 2))}
    {h k : EuclideanSpace ℝ (Fin 2) → ℝ} (hh : ContDiffOn ℝ ∞ h Omega)
    (hk : ContDiffOn ℝ ∞ k Omega) {u : W1p volume Omega 2} {w : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hw : ContinuousOn w Omega)
    (huw : (W1p.value u : EuclideanSpace ℝ (Fin 2) → ℝ) =ᵐ[volume.restrict (Omega : Set _)] w)
    (hu : ∀ v : W1p0 volume Omega 2, PDE.energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
      -∫ x in Omega, (h x * (Real.exp (2 * w x) - 1) / 8 + k x) *
        W1p.value (v : W1p volume Omega 2) x) :
    ContDiffOn ℝ ∞ w Omega := by
  refine (PDE.uniformlyEllipticOn_const_one_one _).contDiffOn_of_energyFormH1_eq (by simp)
    (fun _ _ => contDiffOn_const) (hh.neg.div_const 8) ((hh.div_const 8).sub hk)
    (Φ := fun t => Real.exp (2 * t)) (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
    hw huw fun v => ?_
  rw [hu v, ← integral_neg]
  congr 1
  ext x
  ring

end TauCeti.Vortex
