/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Regularity.PlanarPoisson
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Smoothness of `H²` solutions of the stationary Schrödinger equation in the plane

Let `P` and `g` be smooth real functions on the plane. If `h ∈ H²(ℂ)` solves the stationary
Schrödinger equation `-Δh + P h = g` weakly, `∫ h (-Δφ + P φ) = ∫ g φ` for every compactly
supported `C²` function `φ`, then `h` agrees almost everywhere with a smooth function that solves
the equation pointwise.

Since `2 > dim ℂ / 2`, the Sobolev embedding gives a continuous representative `w` of `h`
(`TemperedDistribution.MemSobolev.exists_contDiff_ae_eq`). It solves `Δw = P w - g` in the sense of
distributions, whose right side is a smooth function of the position and of the value of `w`, so
the planar semilinear bootstrap `TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`
makes `w` smooth. Green's identity then turns the weak equation into a pointwise one.

No sign or decay condition on `P` is needed: these are interior regularity statements. The
solvability of the equation in `H²(E)`, which does use such conditions, is
`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`.

## Main results

* `TauCeti.exists_contDiff_ae_eq_and_neg_laplacian_add_mul_eq`: a weak `H²` solution of
  `-Δh + P h = g` with smooth `P` and `g` has a smooth representative solving the equation at every
  point.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8 (interior regularity of weak solutions).
-/

public section

namespace TauCeti

open MeasureTheory TemperedDistribution Module
open scoped ContDiff Laplacian Distributions

/-- **Smooth solutions of the stationary Schrödinger equation in the plane.** Let `P` and `g` be
smooth real functions on `ℂ`, and let `h ∈ H²(ℂ)` solve `-Δh + P h = g` weakly:
`∫ h (-Δφ + P φ) = ∫ g φ` for every compactly supported `C²` function `φ`. Then `h` agrees almost
everywhere with a smooth function `w` with `-Δw + P w = g` at every point. -/
theorem exists_contDiff_ae_eq_and_neg_laplacian_add_mul_eq {P g h : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hg : ContDiff ℝ ∞ g) (hh : h ∈ realSobolevFunctions ℂ 2 2)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, h z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ h =ᵐ[volume] w ∧ ∀ z, -Δ w z + P z * w z = g z := by
  -- A continuous representative, by the Sobolev embedding `H² ⊆ C⁰` in the plane.
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hh
  obtain ⟨G, hG, huG⟩ := hS.exists_contDiff_ae_eq (k := 0)
    (by rw [Complex.finrank_real_complex]; norm_num)
  set w : ℂ → ℝ := fun z ↦ (G z).re
  have hwc : Continuous w := Complex.continuous_re.comp hG.continuous
  have hhw : h =ᵐ[volume] w := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u, hu, huG] with z h₁ h₂ h₃
    simp only [w, ← h₃, h₁, ← h₂, Complex.ofRealCLM_apply, Complex.ofReal_re]
  -- The weak equation for `w`, for test functions on the plane, in the form `Δw = P w - g`.
  have hweak' (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ)) :
      ∫ z, Δ (φ : ℂ → ℝ) z * w z = ∫ z, φ z * (P z * w z - g z) := by
    have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
    have hΔc : HasCompactSupport (Δ (φ : ℂ → ℝ)) := φ.hasCompactSupport.laplacian
    have i₁ : Integrable (fun z ↦ Δ (φ : ℂ → ℝ) z * w z) volume :=
      (hφ2.continuous_laplacian.mul hwc).integrable_of_hasCompactSupport hΔc.mul_right
    have i₂ : Integrable (fun z ↦ φ z * (P z * w z)) volume :=
      (φ.continuous.mul (hP.continuous.mul hwc)).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_right
    have i₃ : Integrable (fun z ↦ φ z * g z) volume :=
      (φ.continuous.mul hg.continuous).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_right
    have hw := hweak φ hφ2 φ.hasCompactSupport
    have e₁ : ∫ z, h z * (-Δ (φ : ℂ → ℝ) z + P z * φ z) =
        ∫ z, (φ z * (P z * w z) - Δ (φ : ℂ → ℝ) z * w z) :=
      integral_congr_ae (by filter_upwards [hhw] with z hz; rw [hz]; ring)
    have e₂ : ∫ z, g z * φ z = ∫ z, φ z * g z :=
      integral_congr_ae (ae_of_all _ fun z ↦ mul_comm _ _)
    rw [e₁, e₂, integral_sub i₂ i₁] at hw
    calc ∫ z, Δ (φ : ℂ → ℝ) z * w z = (∫ z, φ z * (P z * w z)) - ∫ z, φ z * g z := by
          linarith
      _ = ∫ z, φ z * (P z * w z - g z) := by
        rw [← integral_sub i₂ i₃]
        exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)
  -- The semilinear bootstrap makes `w` smooth.
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ ↦ P p.1 * p.2 - g p.1)
      ((⊤ : TopologicalSpace.Opens ℂ) ×ˢ Set.univ) :=
    (((hP.comp contDiff_fst).mul contDiff_snd).sub (hg.comp contDiff_fst)).contDiffOn
  have hwsm : ContDiff ℝ ∞ w := by
    have := contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp hF hwc.continuousOn hweak'
    simpa [contDiffOn_univ] using this
  refine ⟨w, hwsm, hhw, fun z ↦ ?_⟩
  -- Green's identity gives `∫ φ (Δw - P w + g) = 0` for every test function `φ`.
  have hw2 : ContDiff ℝ 2 w := hwsm.of_le (by simp)
  have hcont : Continuous fun z ↦ -Δ w z + P z * w z - g z :=
    (hw2.continuous_laplacian.neg.add (hP.continuous.mul hwc)).sub hg.continuous
  have hzero : ∀ᵐ z ∂volume, -Δ w z + P z * w z - g z = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    let ψ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ) := ⟨φ, hφ, hφc, by simp⟩
    have hG := hw2.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian
      (Ω := ⊤) (μ := volume) ψ
    have hE := hweak' ψ
    simp only [smul_eq_mul] at hG
    have i₁ : Integrable (fun z ↦ φ z * Δ w z) volume :=
      (hφ.continuous.mul hw2.continuous_laplacian).integrable_of_hasCompactSupport hφc.mul_right
    have i₂ : Integrable (fun z ↦ φ z * (P z * w z - g z)) volume :=
      (hφ.continuous.mul ((hP.continuous.mul hwc).sub
        hg.continuous)).integrable_of_hasCompactSupport hφc.mul_right
    have : ∫ z, φ z * Δ w z = ∫ z, φ z * (P z * w z - g z) := hG.symm.trans hE
    calc ∫ z, φ z • (-Δ w z + P z * w z - g z)
        = ∫ z, (φ z * (P z * w z - g z) - φ z * Δ w z) :=
          integral_congr_ae (ae_of_all _ fun z ↦ by simp only [smul_eq_mul]; ring)
      _ = 0 := by rw [integral_sub i₂ i₁, this, sub_self]
  have hfun := (hcont.ae_eq_iff_eq volume continuous_const).1 hzero
  linarith [congrFun hfun z]

end TauCeti
