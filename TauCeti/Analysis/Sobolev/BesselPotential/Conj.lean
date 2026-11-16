/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Complex conjugation on `H^s(ℝⁿ)`, `s > n / 2`

Let `E` be a finite-dimensional real inner product space of dimension `n`. An `L²` function
`u : E → ℂ` lying in the Bessel-potential space `H^s`, `2s > n`, has complex conjugate `conj u`
in `H^s` again, with the same norm. Consequently the real and imaginary parts of `u` lie in the
real Sobolev functions `TemperedDistribution.realSobolevFunctions E s 2`. These are the facts
needed to pass between complex `H^s` functions, such as the coordinate `u - 1` of a circle-valued
gauge, and the pairs of real `H^s` functions that define them.

The proof is on the Fourier side. Since `2s > n`, the Fourier transform of `u` is an integrable
function `v` (`TemperedDistribution.MemSobolev.fourier_memL1`), and `u = 𝓕⁻ v` almost everywhere.
Conjugating the Fourier integral and substituting `ξ ↦ -ξ` gives

`conj (𝓕⁻ v x) = 𝓕⁻ v' x`,  `v' ξ = conj (v (-ξ))`

(`Real.conj_fourierInv_apply`), so the Fourier transform of `conj u` is the integrable function
`v'`. The weight `(1 + ‖ξ‖ ^ 2) ^ (s / 2)` is real and even, so `(1 + ‖ξ‖ ^ 2) ^ (s / 2) v'` has
the same `L²` norm as `(1 + ‖ξ‖ ^ 2) ^ (s / 2) v`, which is the `H^s` norm of `u`
(`MemSobolev.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace`).

The statements are for Lebesgue measure `volume`, the measure of Mathlib's Bessel-potential
spaces, and for orders `s > n / 2`, where the Fourier transform is integrable.

## Main declarations

* `Real.conj_fourierInv_apply`: `conj (𝓕⁻ v x) = 𝓕⁻ (fun ξ ↦ conj (v (-ξ))) x`.
* `TemperedDistribution.MemSobolev.of_ae_eq_conj`: the conjugate of an `L²` function in `H^s`,
  `2s > n`, lies in `H^s`.
* `TemperedDistribution.MemSobolev.norm_toBesselPotentialSpace_of_ae_eq_conj`: it has the same
  `H^s` norm.
* `TemperedDistribution.re_mem_realSobolevFunctions`,
  `TemperedDistribution.im_mem_realSobolevFunctions`: the real and imaginary parts of an `L²`
  function in `H^s`, `2s > n`, are real `H^s` functions.
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory Module
open scoped FourierTransform SchwartzMap

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace Real

/-- **The inverse Fourier transform of a conjugate.** Conjugating the inverse Fourier integral
of `v` gives the inverse Fourier integral of `ξ ↦ conj (v (-ξ))`. -/
theorem conj_fourierInv_apply (v : E → ℂ) (x : E) :
    conj (𝓕⁻ v x) = 𝓕⁻ (fun ξ ↦ conj (v (-ξ))) x := by
  rw [fourierInv_eq', fourierInv_eq', ← integral_conj, ← integral_neg_eq_self]
  congr 1
  ext ξ
  simp [← exp_conj, inner_neg_left, map_ofNat]

end Real

namespace TemperedDistribution

/-- The Fourier side of the conjugate of an `L²` function `u ∈ H^s`, `2s > n`: the Fourier
transforms of `u` and of its conjugate are `L¹` functions `v` and `v'`, and their weighted `L²`
norms agree. -/
private theorem exists_fourier_eq_of_ae_eq_conj {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u u' : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    (hu' : u' =ᵐ[volume] fun x ↦ conj (u x)) :
    ∃ v v' : Lp ℂ 1 (volume : Measure E), 𝓕 (u : 𝓢'(E, ℂ)) = v ∧ 𝓕 (u' : 𝓢'(E, ℂ)) = v' ∧
      eLpNorm (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v' ξ) 2 volume =
        eLpNorm (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v ξ) 2 volume := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 hs
  have hint : Integrable fun ξ ↦ conj (v (-ξ)) :=
    memLp_one_iff_integrable.1 (memLp_one_iff_integrable.2 (L1.integrable_coeFn v).comp_neg).star
  refine ⟨v, hint.toL1 _, hv, ?_, ?_⟩
  · -- `conj u = conj (𝓕⁻ v) = 𝓕⁻ v'` almost everywhere, so `𝓕 (conj u) = v'`.
    have hu'' : (u' : 𝓢'(E, ℂ)) = 𝓕⁻ ((hint.toL1 _ : Lp ℂ 1 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
      ext φ
      rw [Lp.fourierInv_toTemperedDistribution_apply _ hint hint.coeFn_toL1,
        Lp.toTemperedDistribution_apply]
      refine integral_congr_ae ?_
      filter_upwards [hu', Lp.ae_eq_fourierInv_of_fourier_eq hv] with x hx hx'
      rw [hx, hx', Real.conj_fourierInv_apply]
    rw [hu'', FourierTransform.fourier_fourierInv_eq]
  -- The weight is real and even, so the weighted `v'` is the conjugate of the weighted `v`
  -- composed with `ξ ↦ -ξ`.
  set f : E → ℂ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v ξ
  have hae : (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) • (hint.toL1 _ : E → ℂ) ξ) =ᵐ[volume]
      star (f ∘ fun ξ ↦ -ξ) := by
    filter_upwards [hint.coeFn_toL1] with ξ hξ
    rw [hξ]
    simp [f, norm_neg]
  have hwc : Continuous fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) :=
    (by fun_prop : Continuous fun ξ : E ↦ 1 + ‖ξ‖ ^ 2).rpow_const fun ξ ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  rw [eLpNorm_congr_ae hae, eLpNorm_star]
  exact eLpNorm_comp_measurePreserving
    (hwc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable v))
    (Measure.measurePreserving_neg volume)

/-- **`H^s` is closed under complex conjugation, `2s > n`.** If an `L²` function `u` lies in
`H^s` with `2s > dim E`, so does every `L²` function agreeing almost everywhere with `conj u`. -/
theorem MemSobolev.of_ae_eq_conj {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u u' : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    (hu' : u' =ᵐ[volume] fun x ↦ conj (u x)) : MemSobolev s 2 (u' : 𝓢'(E, ℂ)) := by
  obtain ⟨v, v', hv, hv', heq⟩ := exists_fourier_eq_of_ae_eq_conj hs hu hu'
  have hw : (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hmem : MemLp (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v' ξ) 2 volume := by
    rw [memLp_iff, heq]
    exact hu.memLp_one_add_norm_sq_rpow_smul hv
  refine memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨hmem.toLp _, ?_⟩
  ext φ
  rw [hv', Lp.smulLeftCLM_toTemperedDistribution_apply hw, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with ξ hξ
  rw [hξ, Complex.coe_smul]

/-- **Complex conjugation is an isometry of `H^s`, `2s > n`.** Let `u` be an `L²` function in
`H^s`, `2s > dim E`, and `u'` an `L²` function agreeing almost everywhere with `conj u`. Then `u'`
has the same `H^s` norm as `u`. -/
theorem MemSobolev.norm_toBesselPotentialSpace_of_ae_eq_conj {s : ℝ}
    (hs : finrank ℝ E < 2 * s) {u u' : Lp ℂ 2 (volume : Measure E)}
    (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) (hu' : u' =ᵐ[volume] fun x ↦ conj (u x))
    (hu'' : MemSobolev s 2 (u' : 𝓢'(E, ℂ))) :
    ‖hu''.toBesselPotentialSpace‖ = ‖hu.toBesselPotentialSpace‖ := by
  obtain ⟨v, v', hv, hv', heq⟩ := exists_fourier_eq_of_ae_eq_conj hs hu hu'
  rw [← toReal_eNorm, ← toReal_eNorm,
    ← hu''.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace hv',
    ← hu.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace hv, heq]

/-- **The real part of an `H^s` function, `2s > n`.** The real part of an `L²` function in `H^s`,
`2s > dim E`, is a real `H^s` function. -/
theorem re_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) :
    (fun x ↦ (u x).re) ∈ realSobolevFunctions E s 2 := by
  set u' : Lp ℂ 2 (volume : Measure E) := (Lp.memLp u).star.toLp _
  have hu' : u' =ᵐ[volume] fun x ↦ conj (u x) := (Lp.memLp u).star.coeFn_toLp
  refine mem_realSobolevFunctions_of_ae_eq_ofReal
    ((hu.toTemperedDistribution_add (hu.of_ae_eq_conj hs hu')).toTemperedDistribution_smul
      (2⁻¹ : ℂ)) ?_
  filter_upwards [Lp.coeFn_smul (2⁻¹ : ℂ) (u + u'), Lp.coeFn_add u u', hu'] with x h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, Pi.add_apply, h₃, smul_eq_mul, Complex.add_conj]
  push_cast
  ring

/-- **The imaginary part of an `H^s` function, `2s > n`.** The imaginary part of an `L²` function
in `H^s`, `2s > dim E`, is a real `H^s` function. -/
theorem im_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) :
    (fun x ↦ (u x).im) ∈ realSobolevFunctions E s 2 := by
  set u' : Lp ℂ 2 (volume : Measure E) := (Lp.memLp u).star.toLp _
  have hu' : u' =ᵐ[volume] fun x ↦ conj (u x) := (Lp.memLp u).star.coeFn_toLp
  refine mem_realSobolevFunctions_of_ae_eq_ofReal
    ((hu.toTemperedDistribution_sub (hu.of_ae_eq_conj hs hu')).toTemperedDistribution_smul
      (-I / 2)) ?_
  filter_upwards [Lp.coeFn_smul (-I / 2) (u - u'), Lp.coeFn_sub u u', hu'] with x h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, smul_eq_mul, Complex.sub_conj]
  push_cast
  linear_combination (-((u x).im : ℂ)) * I_sq

end TemperedDistribution
