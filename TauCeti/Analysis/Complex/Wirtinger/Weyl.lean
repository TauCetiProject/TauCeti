/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Weak
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Weyl's lemma for the conjugate Wirtinger derivative

A locally integrable distributional solution of `\bar∂u=0` on an open subset of the plane has an
almost-everywhere equal holomorphic representative. The proof first applies the conjugate real
first-order operator on test functions to obtain weak harmonicity. The harmonic Weyl theorem
supplies smooth representatives of the real and imaginary parts. The weak equation passes to
the representative and agrees with the classical Cauchy–Riemann equation there.

Finite-dimensional complex coefficients follow by coordinates. No real weak first derivatives
of the original function, or a Sobolev exponent, are assumed.

## Main results

* `HasWeakConjWirtingerDerivOn.integral_laplacian_smul_eq`: since `Δ = 4 ∂ \bar∂`, a solution of
  `\bar∂u = g` has distributional Laplacian `4 ∂g`.
* `HasWeakConjWirtingerDerivOn.integral_laplacian_mul_re_eq`: the real part of a solution of
  `\bar∂u = k` solves `Δ (Re u) = 2 (∂ₛ (Re k) + ∂ₜ (Im k))` weakly.
* `HasWeakConjWirtingerDerivOn.weaklyHarmonicOn`: the distributional first-order equation
  implies weak harmonicity, with arbitrary complex Banach coefficients.
* `HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq`: Weyl's lemma for finite-dimensional
  complex coefficients.
* `HasWeakConjWirtingerDerivOn.differentiableOn`: a continuous solution is itself holomorphic.
The converse for holomorphic maps and the elementary conjugation counterexample live in
`Wirtinger.Weak`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace InnerProductSpace Laplacian LineDeriv
open scoped ContDiff Distributions ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure ℂ} {Ω : Opens ℂ} {u g : ℂ → F}

/-- **The distributional Laplacian of a solution of `\bar∂u = g`.** Since `Δ = 4 ∂ \bar∂`, the
distributional Laplacian of `u` is `4 ∂g`, where `∂ = (∂ₛ - I ∂ₜ)/2`. Against a real test
function this reads `∫ Δφ • u = -2 • (∫ ∂ₛφ • g - I • ∫ ∂ₜφ • g)`. -/
theorem HasWeakConjWirtingerDerivOn.integral_laplacian_smul_eq
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • u z ∂μ =
      -(2 : ℂ) • ((∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • g z ∂μ) -
        I • ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • g z ∂μ) := by
  have hs := h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul (∂_{(1 : ℂ)} φ)
  have ht := h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul (∂_{I} φ)
  simp only [← TestFunction.lineDerivOp_apply] at hs ht ⊢
  rw [TestFunction.lineDerivOp_comm φ I 1] at hs
  have hΔ (z : ℂ) : Δ (φ : ℂ → ℝ) z =
      (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ)) z + (∂_{I} (∂_{I} φ)) z := by
    rw [← TestFunction.laplacianCLM_apply]
    simp [laplacianCLM_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]
  simp_rw [hΔ, add_smul]
  rw [integral_add
    ((∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ)).integrable_smul h.locallyIntegrableOn)
    ((∂_{I} (∂_{I} φ)).integrable_smul h.locallyIntegrableOn)]
  calc
    _ = ((∫ z, (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ)) z • u z ∂μ) +
          I • (∫ z, (∂_{(1 : ℂ)} (∂_{I} φ)) z • u z ∂μ)) -
        I • ((∫ z, (∂_{(1 : ℂ)} (∂_{I} φ)) z • u z ∂μ) +
          I • (∫ z, (∂_{I} (∂_{I} φ)) z • u z ∂μ)) := by
      simp only [smul_add, smul_smul, I_mul_I, neg_one_smul]
      abel
    _ = _ := by rw [hs, ht, smul_sub, smul_comm I]

/-- **The real part of a solution of `\bar∂u = k` solves a divergence-form Laplace equation.**
Since `Δ = 4 ∂ \bar∂` and `2 Re ∂k = ∂ₛ (Re k) + ∂ₜ (Im k)`, the distributional Laplacian of `Re u`
is `2 (∂ₛ (Re k) + ∂ₜ (Im k))`:
`∫ Δφ * Re u = -2 ∫ (∂ₛφ * Re k + ∂ₜφ * Im k)` for every real test function `φ`. -/
theorem HasWeakConjWirtingerDerivOn.integral_laplacian_mul_re_eq {u k : ℂ → ℂ}
    (h : HasWeakConjWirtingerDerivOn μ Ω u k) (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z * (u z).re ∂μ =
      -2 * ∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 * (k z).re +
        fderiv ℝ (φ : ℂ → ℝ) z I * (k z).im) ∂μ := by
  have hk := h.locallyIntegrableOn_deriv
  have hderiv (z v : ℂ) : lineDeriv ℝ (φ : ℂ → ℝ) z v = fderiv ℝ (φ : ℂ → ℝ) z v := by
    rw [← TestFunction.lineDerivOp_apply, TestFunction.lineDerivOp_apply_eq_fderiv]
  have e := congrArg re (h.integral_laplacian_smul_eq φ)
  simp only [hderiv] at e
  have hre (v : ℂ) : (∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • k z ∂μ).re =
      ∫ z, fderiv ℝ (φ : ℂ → ℝ) z v * (k z).re ∂μ := by
    rw [← reCLM_apply,
      ← reCLM.integral_comp_comm (integrable_fderiv_smul_of_locallyIntegrableOn hk φ v)]
    simp
  have him (v : ℂ) : (∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • k z ∂μ).im =
      ∫ z, fderiv ℝ (φ : ℂ → ℝ) z v * (k z).im ∂μ := by
    rw [← imCLM_apply,
      ← imCLM.integral_comp_comm (integrable_fderiv_smul_of_locallyIntegrableOn hk φ v)]
    simp
  rw [← reCLM_apply, ← reCLM.integral_comp_comm (by
    simpa only [TestFunction.laplacianCLM_apply] using
      (laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) φ).integrable_smul h.locallyIntegrableOn)] at e
  rw [integral_add (by simpa using (integrable_fderiv_smul_of_locallyIntegrableOn hk φ 1).re)
    (by simpa using (integrable_fderiv_smul_of_locallyIntegrableOn hk φ I).im)]
  simp only [reCLM_apply, smul_re, smul_eq_mul, sub_re, mul_re, re_ofNat, im_ofNat, I_re, I_im,
    neg_re, neg_im] at e
  rw [e, ← hre, ← him]
  ring

/-- A distributional solution of `\bar∂u=0` is weakly harmonic, with arbitrary complex Banach
coefficients. -/
theorem HasWeakConjWirtingerDerivOn.weaklyHarmonicOn
    (h : HasWeakConjWirtingerDerivOn μ Ω u 0) : WeaklyHarmonicOn μ Ω u :=
  weaklyHarmonicOn_iff.2 ⟨h.locallyIntegrableOn, fun φ ↦ by
    simpa using h.integral_laplacian_smul_eq φ⟩

private theorem exists_differentiableOn_ae_eq_scalar {u : ℂ → ℂ} [μ.IsAddHaarMeasure]
    (h : HasWeakConjWirtingerDerivOn μ Ω u 0) :
    ∃ v : ℂ → ℂ, DifferentiableOn ℂ v Ω ∧ u =ᵐ[μ.restrict Ω] v := by
  have hh := h.weaklyHarmonicOn
  obtain ⟨a, ha, hua⟩ := (hh.clm_comp Complex.reCLM).exists_harmonicOnNhd_ae_eq
  obtain ⟨b, hb, hub⟩ := (hh.clm_comp Complex.imCLM).exists_harmonicOnNhd_ae_eq
  let v : ℂ → ℂ := fun z ↦ (a z : ℂ) + (b z : ℂ) * I
  have hae : u =ᵐ[μ.restrict Ω] v := by
    filter_upwards [hua, hub] with z hz₁ hz₂
    rw [Complex.reCLM_apply] at hz₁
    rw [Complex.imCLM_apply] at hz₂
    calc
      u z = ((u z).re : ℂ) + ((u z).im : ℂ) * I := (Complex.re_add_im _).symm
      _ = v z := by rw [hz₁, hz₂]
  have ha' : ContDiffOn ℝ 1 (fun z ↦ (a z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (ha.contDiffOn.of_le (by simp))
  have hb' : ContDiffOn ℝ 1 (fun z ↦ (b z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hb.contDiffOn.of_le (by simp))
  have hv : ContDiffOn ℝ 1 v Ω := ha'.add (hb'.mul contDiffOn_const)
  exact ⟨v, (hasWeakConjWirtingerDerivOn_zero_iff_of_contDiffOn hv).1 (h.congr_ae hae), hae⟩

/-- **Weyl's lemma for `\bar∂`.** A distributional solution with finite-dimensional complex
coefficients agrees almost everywhere on its domain with a holomorphic function. -/
theorem HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq
    [FiniteDimensional ℂ F] [μ.IsAddHaarMeasure]
    (h : HasWeakConjWirtingerDerivOn μ Ω u 0) :
    ∃ v : ℂ → F, DifferentiableOn ℂ v Ω ∧ u =ᵐ[μ.restrict Ω] v := by
  let e : F ≃L[ℂ] (Fin (Module.finrank ℂ F) → ℂ) :=
    (Module.finBasis ℂ F).equivFun.toContinuousLinearEquiv
  let π (i : Fin (Module.finrank ℂ F)) : F →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hc (i : Fin (Module.finrank ℂ F)) :
      HasWeakConjWirtingerDerivOn μ Ω (fun z ↦ π i (u z)) 0 := by
    simpa only [Pi.zero_apply, map_zero, Pi.zero_def] using h.clm_comp (π i)
  choose v hv huv using fun i ↦ exists_differentiableOn_ae_eq_scalar (hc i)
  refine ⟨fun z ↦ e.symm (fun i ↦ v i z), ?_, ?_⟩
  · exact e.symm.differentiable.comp_differentiableOn (differentiableOn_pi.2 hv)
  · filter_upwards [Filter.eventually_all.2 huv] with z hz
    apply e.injective
    ext i
    simpa [π] using hz i

/-- A continuous distributional solution is itself holomorphic; no representative change is
needed. -/
theorem HasWeakConjWirtingerDerivOn.differentiableOn
    [FiniteDimensional ℂ F] [μ.IsAddHaarMeasure]
    (h : HasWeakConjWirtingerDerivOn μ Ω u 0) (hu : ContinuousOn u Ω) :
    DifferentiableOn ℂ u Ω := by
  obtain ⟨v, hv, huv⟩ := h.exists_differentiableOn_ae_eq
  exact hv.congr (Measure.eqOn_open_of_ae_eq huv Ω.isOpen hu hv.continuousOn)

/-- The distributional equation is equivalent to existence of an almost-everywhere equal
holomorphic representative. -/
theorem hasWeakConjWirtingerDerivOn_zero_iff_exists_differentiableOn_ae_eq
    [FiniteDimensional ℂ F] [μ.IsAddHaarMeasure] :
    HasWeakConjWirtingerDerivOn μ Ω u 0 ↔
      ∃ v : ℂ → F, DifferentiableOn ℂ v Ω ∧ u =ᵐ[μ.restrict Ω] v := by
  have := FiniteDimensional.completeSpace ℂ F
  refine ⟨HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq, ?_⟩
  rintro ⟨v, hv, huv⟩
  exact hv.hasWeakConjWirtingerDerivOn_zero.congr_ae huv.symm

/-- For continuous finite-dimensional complex-valued maps, the distributional equation is
precisely holomorphy. -/
theorem hasWeakConjWirtingerDerivOn_zero_iff_of_continuousOn
    [FiniteDimensional ℂ F] [μ.IsAddHaarMeasure] (hu : ContinuousOn u Ω) :
    HasWeakConjWirtingerDerivOn μ Ω u 0 ↔ DifferentiableOn ℂ u Ω := by
  have := FiniteDimensional.completeSpace ℂ F
  exact ⟨fun h ↦ h.differentiableOn hu, DifferentiableOn.hasWeakConjWirtingerDerivOn_zero⟩


end TauCeti
