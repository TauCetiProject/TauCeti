/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Functional
public import TauCeti.Analysis.PDE.Vortex.Variational
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Sobolev.W1p.Exponential
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# `H²` regularity of weak solutions of the reduced vortex equation

Let `P` be a complex polynomial of degree `m ≥ 1` and put

`h = ‖P‖² / (1 + ‖P‖²)`,    `g = 2 ‖P'‖² / (1 + ‖P‖²)²`.

A plane vortex with zero divisor `P` is reconstructed from a solution `w` of the reduced equation

`Δw = (exp (2w) h - 1) / 8 + g`,    `w → 0` at infinity

(`TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff` and
`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff`). Taubes obtains
`w` as the minimizer in `H¹(ℂ)` of the functional `TauCeti.Vortex.sobolevReducedFunctional`, which
makes `w` a weak solution: `∫ ⟪∇w, ∇φ⟫ + ∫ ((exp (2w) h - 1) / 8 + g) φ = 0` for every compactly
supported smooth `φ`. This file proves the first regularity step for such weak solutions.

The right-hand side `TauCeti.Vortex.reducedSource P w` is square integrable for every
`w ∈ H¹(ℂ)` (`TauCeti.Vortex.memLp_reducedSource`). Writing it as
`h (exp (2w) - 1) / 8 + (g - (1 + ‖P‖²)⁻¹ / 8)`, the first term is square integrable because
`exp (2w) - 1 ∈ L²(ℂ)` for `w ∈ H¹(ℂ)` (`TauCeti.W1p.memLp_exp_value_sub_one`) and `0 ≤ h ≤ 1`,
and the second by `TauCeti.Vortex.memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight`.

A weak solution `w ∈ H¹(ℂ)` therefore satisfies `-Δw + w = w - reducedSource P w ∈ L²(ℂ)` as
tempered distributions, and the resolvent of the Laplacian
(`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`) puts `w` in `H²(ℂ)`
(`TauCeti.Vortex.exists_wkp_value_ae_eq_of_forall_integral_reducedSource`). Since `H²(ℂ)`
embeds in the continuous functions vanishing at infinity (`TauCeti.Wkp.toZeroAtInfty`), the weak
solution agrees almost everywhere with a continuous function `w` with `w → 0` at infinity
(`TauCeti.Vortex.exists_zeroAtInftyContinuousMap_ae_eq_of_forall_integral_reducedSource`).
This is the decay at infinity that gives the reconstructed vortex its degree-`m` end framing; the
`C²` regularity needed to reconstruct the vortex itself is not treated here.

## Main definitions

* `TauCeti.Vortex.reducedSource P w`: the right-hand side `(exp (2w) h - 1) / 8 + g` of the
  reduced equation.

## Main results

* `TauCeti.Vortex.memLp_reducedSource`: `reducedSource P w ∈ L²(ℂ)` for `w ∈ H¹(ℂ)`.
* `TauCeti.Vortex.exists_wkp_value_ae_eq_of_forall_integral_reducedSource`: a weak solution in
  `H¹(ℂ)` of the reduced equation lies in `H²(ℂ)`.
* `TauCeti.Vortex.exists_zeroAtInftyContinuousMap_ae_eq_of_forall_integral_reducedSource`: it
  has a continuous representative vanishing at infinity.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TemperedDistribution Filter Module
open scoped SchwartzMap RealInnerProductSpace Gradient Laplacian Distributions ZeroAtInfty
  ContDiff

/-- The right-hand side `(exp (2w) h - 1) / 8 + g` of the reduced vortex equation for the zero
divisor of `P`, where `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. It is written as
`h (exp (2w) - 1) / 8 + k`, with `h = TauCeti.Vortex.backgroundWeight` and
`k = (h - 1) / 8 + g = TauCeti.Vortex.backgroundSource` its value at `w = 0`. -/
def reducedSource (P : Polynomial ℂ) (w : ℂ → ℝ) (z : ℂ) : ℝ :=
  backgroundWeight (P.eval ·) z * (Real.exp (2 * w z) - 1) / 8 + backgroundSource (P.eval ·) z

/-- The defining formula of `TauCeti.Vortex.reducedSource`. -/
theorem reducedSource_def (P : Polynomial ℂ) (w : ℂ → ℝ) (z : ℂ) :
    reducedSource P w z =
      backgroundWeight (P.eval ·) z * (Real.exp (2 * w z) - 1) / 8 +
        backgroundSource (P.eval ·) z := (rfl)

variable {P : Polynomial ℂ}

/-- **The source of the reduced equation is square integrable.** For a polynomial `P` of positive
degree and `w ∈ H¹(ℂ)`, `(exp (2w) h - 1) / 8 + g ∈ L²(ℂ)`. -/
theorem memLp_reducedSource (hm : 0 < P.natDegree) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (reducedSource P (W1p.value u)) 2 volume := by
  have hE : finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  set h : ℂ → ℝ := backgroundWeight (P.eval ·)
  have hh0 (z : ℂ) : 0 ≤ h z := backgroundWeight_nonneg _ z
  have hh1 (z : ℂ) : h z ≤ 1 := by
    rw [show h z = _ from backgroundWeight_def _ z]
    exact div_le_one_of_le₀ (by linarith) (by positivity)
  have hhc : Continuous h := continuous_backgroundWeight P.continuous
  -- `exp (2w) - 1 ∈ L²`, from the value of `2 • u`.
  have h2u : (W1p.value ((2 : ℝ) • u) : ℂ → ℝ) =ᵐ[volume] fun z ↦ 2 * W1p.value u z := by
    have h := W1p.value_smul_ae (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2) 2 u
    simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    exact h.mono fun z hz ↦ by rw [hz, Pi.smul_apply, smul_eq_mul]
  have hexp : MemLp (fun z ↦ Real.exp (2 * W1p.value u z) - 1) 2 volume :=
    (W1p.memLp_exp_value_sub_one volume hE ((2 : ℝ) • u)).ae_eq
      (h2u.mono fun z hz ↦ by simp only [hz])
  have htop : MemLp h ⊤ volume :=
    memLp_top_of_bound hhc.aestronglyMeasurable 1 (Eventually.of_forall fun z ↦ by
      rw [Real.norm_of_nonneg (hh0 z)]; exact hh1 z)
  have hfirst := (htop.mul (r := 2) hexp).const_mul (1 / 8)
  refine (hfirst.add (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm)).ae_eq
    (Eventually.of_forall fun z ↦ ?_)
  simp only [Pi.add_apply, Pi.mul_apply, reducedSource_def, backgroundSource_def,
    backgroundWeight_def, Polynomial.deriv, h]
  field_simp
  ring

/-- **Weak solutions of the reduced vortex equation lie in `H²`.** Let `P` be a polynomial of
positive degree and let `w ∈ H¹(ℂ)` be a weak solution of `Δw = (exp (2w) h - 1) / 8 + g`, that is
`∫ ⟪∇w, ∇φ⟫ + ∫ ((exp (2w) h - 1) / 8 + g) φ = 0` for every compactly supported smooth `φ`. Then
`w` is the value of an element of `W^{2,2}(ℂ)`. -/
theorem exists_wkp_value_ae_eq_of_forall_integral_reducedSource (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) + ∫ z, reducedSource P (W1p.value u) z * φ z = 0) :
    ∃ W : Wkp (volume : Measure ℂ) ⊤ 2 2,
      (Wkp.value 2 W : ℂ → ℝ) =ᵐ[volume] W1p.value u := by
  set f : ℂ → ℝ := ⇑(W1p.value u)
  have hf : MemLp f 2 volume := W1p.memLp_value u
  have hS : MemLp (reducedSource P f) 2 volume := memLp_reducedSource hm u
  have hR : MemLp (f - reducedSource P f) 2 volume := hf.sub hS
  set T : 𝓢'(ℂ, ℂ) := Lp.toTemperedDistribution (ofRealCLM.compLp (hf.toLp f))
  -- Pairing a real Schwartz function with the distribution of a real `L²` function.
  have hpair {g : ℂ → ℝ} (hg : MemLp g 2 volume) (φ : 𝓢(ℂ, ℝ)) :
      Lp.toTemperedDistribution (ofRealCLM.compLp (hg.toLp g)) (φ.postcompCLM ofRealCLM) =
        ((∫ z, φ z * g z : ℝ) : ℂ) := by
    rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      integral_congr_ae (hg.coeFn_toLp.mono fun z hz ↦ by rw [hz])]
  -- The weak equation, after integrating the gradient term by parts once more.
  have hweak (φ : 𝓢(ℂ, ℝ)) (hφ : HasCompactSupport φ) :
      ∫ z, Δ (φ : ℂ → ℝ) z * f z = ∫ z, φ z * reducedSource P f z := by
    let φ' : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ) :=
      ⟨φ, φ.smooth ⊤, hφ, by simp only [TopologicalSpace.Opens.coe_top, Set.subset_univ]⟩
    have hcoe : (φ' : ℂ → ℝ) = φ := TestFunction.coe_mk
    have hibp := (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ'
    simp only [TopologicalSpace.Opens.coe_top, smul_eq_mul, hcoe] at hibp
    have h := hu φ (φ.smooth ⊤) hφ
    have h1 : ∫ z, ⟪W1p.gradient u z, ∇ (φ : ℂ → ℝ) z⟫ =
        ∫ z, ⟪∇ (φ : ℂ → ℝ) z, W1p.gradient u z⟫ :=
      integral_congr_ae (Eventually.of_forall fun z ↦ real_inner_comm _ _)
    have h2 : ∫ z, reducedSource P f z * φ z = ∫ z, φ z * reducedSource P f z :=
      integral_congr_ae (Eventually.of_forall fun z ↦ mul_comm _ _)
    rw [h1, h2] at h
    rw [hibp]
    linarith
  -- Hence `-Δw + w = w - reducedSource P w` as tempered distributions.
  have hT : -Δ T + (1 : ℝ) • T = Lp.toTemperedDistribution (ofRealCLM.compLp (hR.toLp _)) := by
    refine ext_real fun φ hφ ↦ ?_
    have hφ2 := φ.memLp 2 (μ := volume)
    rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, TauCeti.laplacian_postcompCLM,
      hpair hf, hpair hf, hpair hR, one_smul]
    simp only [SchwartzMap.laplacian_apply]
    rw [hweak φ hφ]
    simp_rw [Pi.sub_apply, mul_sub]
    rw [integral_sub (f := fun z ↦ φ z * f z) (g := fun z ↦ φ z * reducedSource P f z)
      (hφ2.integrable_mul hf) (hφ2.integrable_mul hS)]
    push_cast
    ring
  have hT2 : MemSobolev ((2 : ℕ) : ℝ) 2 T := by
    have h := (memSobolev_add_two_iff_neg_laplacian_add_smul (s := 0) (c := 1) one_pos).2
      (by rw [hT]; exact memSobolev_zero_iff.2 ⟨_, rfl⟩)
    rwa [zero_add, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
  obtain ⟨W, hW⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq (by norm_num) (by norm_num) 2
    (hf.toLp f)).1 hT2
  exact ⟨W, hW.trans hf.coeFn_toLp⟩

/-- **Weak solutions of the reduced vortex equation are continuous and vanish at infinity.** A
weak solution `w ∈ H¹(ℂ)` of `Δw = (exp (2w) h - 1) / 8 + g`, for a polynomial `P` of positive
degree, agrees almost everywhere with a continuous function tending to zero at infinity. -/
theorem exists_zeroAtInftyContinuousMap_ae_eq_of_forall_integral_reducedSource
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) + ∫ z, reducedSource P (W1p.value u) z * φ z = 0) :
    ∃ v : C₀(ℂ, ℝ), (W1p.value u : ℂ → ℝ) =ᵐ[volume] v := by
  obtain ⟨W, hW⟩ := exists_wkp_value_ae_eq_of_forall_integral_reducedSource hm hu
  have hk : finrank ℝ ℂ < 2 * 2 := by rw [Complex.finrank_real_complex]; norm_num
  exact ⟨Wkp.toZeroAtInfty hk W, hW.symm.trans (Wkp.value_ae_eq_toZeroAtInfty hk W)⟩

end TauCeti.Vortex
