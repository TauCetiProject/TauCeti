/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Complex conjugation on `H^s(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space. An `L²` function `u : E → ℂ` lying in
the Bessel-potential space `H^s` has complex conjugate `conj u` in `H^s` again, with the same norm,
for every real order `s`. Consequently the real and imaginary parts of `u` lie in the real Sobolev
functions `TemperedDistribution.realSobolevFunctions E s 2`. These are the facts needed to pass
between complex `H^s` functions, such as the coordinate `u - 1` of a circle-valued gauge, and the
pairs of real `H^s` functions that define them.

The proof is on the Fourier side. Membership of `u` in `H^s` says that the weighted Fourier
transform `(1 + ‖ξ‖ ^ 2) ^ (s / 2) 𝓕 u` is an `L²` function `g`. Conjugating the Fourier integral
and substituting `ξ ↦ -ξ` gives `conj (𝓕 φ x) = 𝓕 (ξ ↦ conj (φ (-ξ))) x`
(`Real.conj_fourier_apply`); since the weight is real and even, pairing against Schwartz
functions shows that the weighted Fourier transform of `conj u` is the `L²` function
`ξ ↦ conj (g (-ξ))`, which has the same `L²` norm as `g`.

The statements are for Lebesgue measure `volume`, the measure of Mathlib's Bessel-potential
spaces.

## Main declarations

* `TemperedDistribution.MemSobolev.of_ae_eq_conj`: the conjugate of an `L²` function in `H^s`
  lies in `H^s`.
* `TemperedDistribution.MemSobolev.norm_toBesselPotentialSpace_of_ae_eq_conj`: it has the same
  `H^s` norm.
* `TemperedDistribution.re_mem_realSobolevFunctions`,
  `TemperedDistribution.im_mem_realSobolevFunctions`: the real and imaginary parts of an `L²`
  function in `H^s` are real `H^s` functions.
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory
open scoped FourierTransform SchwartzMap

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TemperedDistribution

/-- The Fourier side of the conjugate of an `L²` function `u`: if the weighted Fourier transform
of `u` is the `L²` function `g`, that of `conj u` is the `L²` function `ξ ↦ conj (g (-ξ))`. -/
private theorem smulLeftCLM_fourier_of_ae_eq_conj {s : ℝ} {u u' : Lp ℂ 2 (volume : Measure E)}
    (hu' : u' =ᵐ[volume] fun x ↦ conj (u x)) {g : Lp ℂ 2 (volume : Measure E)}
    (hg : smulLeftCLM ℂ (fun ξ : E ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 (u : 𝓢'(E, ℂ))) = g) :
    smulLeftCLM ℂ (fun ξ : E ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 (u' : 𝓢'(E, ℂ))) =
      (((Lp.memLp g).comp_measurePreserving (Measure.measurePreserving_neg volume)).star.toLp _ :
        Lp ℂ 2 (volume : Measure E)) := by
  set w : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  ext φ
  -- The Schwartz function `ψ ξ = conj (φ (-ξ))`; the weight is real and even, so the Fourier
  -- transform of the weighted `ψ` is the conjugate of that of the weighted `φ`.
  set ψ : 𝓢(E, ℂ) := SchwartzMap.postcompCLM (conjCLE : ℂ →L[ℝ] ℂ)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (LinearIsometryEquiv.neg ℝ (E := E)) φ)
  have hψ (ξ : E) : ψ ξ = conj (φ (-ξ)) := by
    simp [ψ, SchwartzMap.postcompCLM_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have key (x : E) : 𝓕 (SchwartzMap.smulLeftCLM ℂ w ψ) x =
      conj (𝓕 (SchwartzMap.smulLeftCLM ℂ w φ) x) := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.conj_fourier_apply]
    refine congrArg (fun f : E → ℂ ↦ 𝓕 f x) (funext fun ξ ↦ ?_)
    simp [SchwartzMap.smulLeftCLM_apply_apply hw, hψ, w, norm_neg]
  have hgψ := congrArg (fun T : 𝓢'(E, ℂ) ↦ T ψ) hg
  simp only [smulLeftCLM_apply_apply, fourier_apply, Lp.toTemperedDistribution_apply] at hgψ ⊢
  calc ∫ x, 𝓕 (SchwartzMap.smulLeftCLM ℂ w φ) x • u' x
      = conj (∫ x, 𝓕 (SchwartzMap.smulLeftCLM ℂ w ψ) x • u x) := by
        rw [← integral_conj]
        refine integral_congr_ae ?_
        filter_upwards [hu'] with x hx
        simp [hx, key]
    _ = ∫ ξ, φ (-ξ) • conj (g ξ) := by
        rw [hgψ, ← integral_conj]
        simp [hψ]
    _ = ∫ ξ, φ ξ • conj (g (-ξ)) := by
        rw [← integral_neg_eq_self]
        simp
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [((Lp.memLp g).comp_measurePreserving
          (Measure.measurePreserving_neg volume)).star.coeFn_toLp] with ξ hξ
        simp [hξ]

/-- **`H^s` is closed under complex conjugation.** If an `L²` function `u` lies in `H^s`, so does
every `L²` function agreeing almost everywhere with `conj u`. -/
theorem MemSobolev.of_ae_eq_conj {s : ℝ} {u u' : Lp ℂ 2 (volume : Measure E)}
    (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) (hu' : u' =ᵐ[volume] fun x ↦ conj (u x)) :
    MemSobolev s 2 (u' : 𝓢'(E, ℂ)) := by
  obtain ⟨g, hg⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.1 hu
  exact memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨_, smulLeftCLM_fourier_of_ae_eq_conj hu' hg⟩

/-- **Complex conjugation is an isometry of `H^s`.** Let `u` be an `L²` function in `H^s`, and `u'`
an `L²` function agreeing almost everywhere with `conj u`. Then `u'` has the same `H^s` norm as
`u`. -/
theorem MemSobolev.norm_toBesselPotentialSpace_of_ae_eq_conj {s : ℝ}
    {u u' : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    (hu' : u' =ᵐ[volume] fun x ↦ conj (u x)) (hu'' : MemSobolev s 2 (u' : 𝓢'(E, ℂ))) :
    ‖hu''.toBesselPotentialSpace‖ = ‖hu.toBesselPotentialSpace‖ := by
  obtain ⟨g, hg⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.1 hu
  rw [BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq (u := hu''.toBesselPotentialSpace)
      (by rw [hu''.toBesselPotentialSpace_toDistr, smulLeftCLM_fourier_of_ae_eq_conj hu' hg]),
    BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq (u := hu.toBesselPotentialSpace)
      (by rw [hu.toBesselPotentialSpace_toDistr, hg]),
    Lp.norm_toLp, Lp.norm_def, eLpNorm_star,
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable g)
      (Measure.measurePreserving_neg volume)]

/-- **The real part of an `H^s` function.** The real part of an `L²` function in `H^s` is a real
`H^s` function. -/
theorem re_mem_realSobolevFunctions {s : ℝ} {u : Lp ℂ 2 (volume : Measure E)}
    (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) :
    (fun x ↦ (u x).re) ∈ realSobolevFunctions E s 2 := by
  set u' : Lp ℂ 2 (volume : Measure E) := (Lp.memLp u).star.toLp _
  have hu' : u' =ᵐ[volume] fun x ↦ conj (u x) := (Lp.memLp u).star.coeFn_toLp
  refine mem_realSobolevFunctions_of_ae_eq_ofReal
    ((hu.toTemperedDistribution_add (hu.of_ae_eq_conj hu')).toTemperedDistribution_smul
      (2⁻¹ : ℂ)) ?_
  filter_upwards [Lp.coeFn_smul (2⁻¹ : ℂ) (u + u'), Lp.coeFn_add u u', hu'] with x h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, Pi.add_apply, h₃, smul_eq_mul, Complex.add_conj]
  push_cast
  ring

/-- **The imaginary part of an `H^s` function.** The imaginary part of an `L²` function in `H^s`
is a real `H^s` function. -/
theorem im_mem_realSobolevFunctions {s : ℝ} {u : Lp ℂ 2 (volume : Measure E)}
    (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) :
    (fun x ↦ (u x).im) ∈ realSobolevFunctions E s 2 := by
  set u' : Lp ℂ 2 (volume : Measure E) := (Lp.memLp u).star.toLp _
  have hu' : u' =ᵐ[volume] fun x ↦ conj (u x) := (Lp.memLp u).star.coeFn_toLp
  refine mem_realSobolevFunctions_of_ae_eq_ofReal
    ((hu.toTemperedDistribution_sub (hu.of_ae_eq_conj hu')).toTemperedDistribution_smul
      (-I / 2)) ?_
  filter_upwards [Lp.coeFn_smul (-I / 2) (u - u'), Lp.coeFn_sub u u', hu'] with x h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, smul_eq_mul, Complex.sub_conj]
  push_cast
  linear_combination (-((u x).im : ℂ)) * I_sq

end TemperedDistribution
