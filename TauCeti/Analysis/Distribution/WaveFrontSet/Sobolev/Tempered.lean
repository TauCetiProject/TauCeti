/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction

/-!
# Local Sobolev regularity on Bessel-potential spaces

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`, and `φ` a complex test function on `Ω`. The localized Fourier transform
`η ↦ T (φ e_η)` of `Distribution.localFourier`, with `e_η x = 𝐞 (-⟪x, η⟫)`, is the Fourier
transform of the tempered distribution `φ T` of `Distribution.cutoffTempered`:

`𝓕 (φ T) ψ = ∫ ψ η • T (φ e_η) dη`

for every compactly supported Schwartz function `ψ` (`Distribution.fourier_cutoffTempered_apply`),
and these determine `𝓕 (φ T)` since they are dense. Indeed `φ 𝓕ψ` is the integral
`∫ ψ η • φ e_η dη` of test functions over the compact support of `ψ`, and `T` passes under that
integral (`Distribution.complexPairing_eq_integral_of_continuous_iteratedFDeriv`).

Consequently the Fourier description of local Sobolev regularity used for the `H^s` wave front
set agrees with Mathlib's Bessel-potential spaces: `φ T ∈ H^s`, in the sense of
`TemperedDistribution.MemSobolev`, exactly when `η ↦ ⟨η⟩ ^ s T (φ e_η)` is square integrable
(`Distribution.memSobolev_cutoffTempered_iff`). So `T` is `H^s` near `x` exactly when `φ T ∈ H^s`
for a cutoff `φ` with `φ x ≠ 0`, and then for every cutoff supported in a neighbourhood of `x`;
and every `φ T` lies in some `H^s`. This transfers estimates on the Bessel-potential spaces `H^s`,
such as the mapping properties of pseudodifferential operators, to distributions on open sets.

## Main results

* `Distribution.fourier_cutoffTempered_apply`: the Fourier transform of `φ T` is the localized
  Fourier transform of `T`.
* `Distribution.memSobolev_cutoffTempered_iff`: `φ T ∈ H^s` exactly when the weighted localized
  Fourier transform is square integrable.
* `Distribution.isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered`,
  `Distribution.IsLocallySobolevAt.exists_nhds_forall_memSobolev_cutoffTempered`: being `H^s` near
  a point in terms of Mathlib's Bessel-potential spaces.
* `Distribution.exists_memSobolev_cutoffTempered`: every `φ T` has a finite Sobolev order.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 7.1.14 (the
  Fourier transform of a compactly supported distribution is the function `η ↦ T (e_η)`).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory TemperedDistribution
open scoped Distributions Topology SchwartzMap ContDiff FourierTransform RealInnerProductSpace

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivatives in the point of the modulated cutoffs `x ↦ ψ η * (φ x * e_η x)` are jointly
continuous in the frequency `η` and the point. -/
private theorem continuous_iteratedFDeriv_mul_fourierAtom (φ : 𝓓(Ω, ℂ)) (ψ : 𝓢(E, ℂ)) (k : ℕ) :
    Continuous fun p : E × E ↦
      iteratedFDeriv ℝ k (fun x ↦ ψ p.1 * (φ x * TauCeti.fourierAtom p.1 x)) p.2 := by
  have hG : ContDiff ℝ ∞ fun p : E × E ↦ ψ p.2 * (φ p.1 * TauCeti.fourierAtom p.2 p.1) :=
    ((ψ.smooth ⊤).comp contDiff_snd).mul ((φ.contDiff.comp contDiff_fst).mul
      (TauCeti.contDiff_uncurry_fourierAtom.comp (contDiff_snd.prodMk contDiff_fst)))
  have hc := (hG.contDiffOn (s := univ)).continuousOn_iteratedFDeriv_partial isOpen_univ
    (k := k) (mod_cast le_top)
  exact (continuousOn_univ.1 hc).comp continuous_swap

/-- **The Fourier transform of `φ T` is the localized Fourier transform of `T`.** For every
compactly supported Schwartz function `ψ`, `𝓕 (φ T) ψ = ∫ ψ η • T (φ e_η) dη`. -/
theorem fourier_cutoffTempered_apply (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) {ψ : 𝓢(E, ℂ)}
    (hψ : HasCompactSupport ψ) :
    𝓕 (T.cutoffTempered φ) ψ = ∫ η, ψ η • T.localFourier φ η := by
  rw [TemperedDistribution.fourier_apply]
  -- The parameter space is the compact support of `ψ`.
  let Y := tsupport (ψ : E → ℂ)
  have hY : MeasurableSet Y := (isClosed_tsupport _).measurableSet
  have : CompactSpace Y := isCompact_iff_compactSpace.1 hψ
  have : IsFiniteMeasure (volume.comap ((↑) : Y → E)) := ⟨by
    rw [comap_subtype_coe_apply hY, image_univ, Subtype.range_coe]
    exact hψ.measure_lt_top⟩
  -- The modulated cutoffs `ψ η • φ e_η`, and `φ 𝓕ψ` as their integral.
  let f : Y → 𝓓(Ω, ℂ) := fun η ↦
    ψ η • bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom (η : E)) φ
  have hf (η : Y) (x : E) : f η x = ψ η * (φ x * TauCeti.fourierAtom (η : E) x) := by
    simp [f, bilinLeftCLM_apply]
  let χ : 𝓓(Ω, ℂ) := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ((𝓕 ψ).smooth ⊤) φ
  -- The integrands vanish off the support of `ψ`, so integrals over `Y` are integrals over `E`.
  have hYE (g : E → ℂ) (hg : ∀ η, ψ η = 0 → g η = 0) :
      ∫ η : Y, g η ∂(volume.comap ((↑) : Y → E)) = ∫ η, g η := by
    rw [integral_subtype_comap hY]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun η hη ↦
      hg η (image_eq_zero_of_notMem_tsupport hη)
  have hχ (x : E) : χ x = ∫ η : Y, f η x ∂(volume.comap ((↑) : Y → E)) := by
    simp only [hf]
    rw [hYE (fun η ↦ ψ η * (φ x * TauCeti.fourierAtom η x)) fun η hη ↦ by simp [hη]]
    simp only [χ, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
    rw [SchwartzMap.fourier_coe, Real.fourier_eq, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun η ↦ ?_)
    simp only [TauCeti.fourierAtom_eq_fourierChar, Circle.smul_def, smul_eq_mul, real_inner_comm]
    ring
  -- The derivatives of the `f η` in the point are jointly continuous.
  have hjets (k : ℕ) : Continuous fun p : Y × E ↦ iteratedFDeriv ℝ k (f p.1) p.2 := by
    have heq (p : Y × E) : iteratedFDeriv ℝ k (f p.1) p.2 = iteratedFDeriv ℝ k
        (fun x ↦ ψ (p.1 : E) * (φ x * TauCeti.fourierAtom (p.1 : E) x)) p.2 :=
      congrArg (iteratedFDeriv ℝ k · p.2) (funext (hf p.1))
    simp only [heq]
    exact (continuous_iteratedFDeriv_mul_fourierAtom φ ψ k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hfK (η : Y) : tsupport (f η) ⊆ tsupport φ := by
    rw [show ⇑(f η) = fun x ↦ ψ η * (φ x * TauCeti.fourierAtom (η : E) x) from funext (hf η)]
    exact tsupport_mul_subset_right.trans tsupport_mul_subset_left
  rw [cutoffTempered_def, complexPairing_eq_integral_of_continuous_iteratedFDeriv T
    (K := ⟨_, φ.hasCompactSupport⟩) φ.tsupport_subset hfK hjets hχ]
  rw [← hYE _ fun η hη ↦ by simp [hη]]
  refine integral_congr_ae (ae_of_all _ fun η ↦ ?_)
  simp only [f, map_smul, smul_eq_mul, localFourier_def]

/-! ### Bessel-potential spaces -/

section Sobolev

variable {s : ℝ} {T : 𝓓'(Ω, ℂ)} {φ : 𝓓(Ω, ℂ)} {x : E}

/-- On compactly supported Schwartz functions, the Bessel weight times `𝓕 (φ T)` is the weighted
localized Fourier transform `η ↦ ⟨η⟩ ^ s T (φ e_η)`. -/
private theorem smulLeftCLM_fourier_cutoffTempered_apply (s : ℝ) (T : 𝓓'(Ω, ℂ))
    (φ : 𝓓(Ω, ℂ)) {ψ : 𝓢(E, ℂ)} (hψ : HasCompactSupport ψ) :
    TemperedDistribution.smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
      (𝓕 (T.cutoffTempered φ)) ψ =
      ∫ η, ψ η • ((1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) := by
  have hw : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hcoe : ⇑(SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) ψ) =
      fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ψ x :=
    funext (SchwartzMap.smulLeftCLM_apply_apply hw ψ)
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    fourier_cutoffTempered_apply T φ (by
      rw [hcoe]
      exact hψ.smul_left (f := fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))), hcoe]
  refine integral_congr_ae (ae_of_all _ fun η ↦ ?_)
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- **`φ T ∈ H^s` in Fourier terms.** The tempered distribution `φ T` lies in Mathlib's
Bessel-potential space `H^s` exactly when the weighted localized Fourier transform
`η ↦ ⟨η⟩ ^ s T (φ e_η)` is square integrable. -/
theorem memSobolev_cutoffTempered_iff :
    MemSobolev s 2 (T.cutoffTempered φ) ↔
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 volume := by
  set G : E → ℂ := fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η
  have hGc : Continuous G :=
    ((continuous_const.add (continuous_norm.pow 2)).rpow_const fun η ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖η‖ ^ 2).ne').smul (T.continuous_localFourier φ)
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  constructor
  · rintro ⟨f', hf'⟩
    -- `G` and `f'` have the same integrals against real test functions.
    refine (Lp.memLp f').ae_eq (ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp f').locallyIntegrable one_le_two) hGc.locallyIntegrable fun g hg hgc ↦ ?_)
    have hgc' : HasCompactSupport fun x ↦ (g x : ℂ) := hgc.comp_left ofReal_zero
    let ψ : 𝓢(E, ℂ) := hgc'.toSchwartzMap (ofRealCLM.contDiff.comp hg)
    -- Mathlib has no evaluation lemma for `HasCompactSupport.toSchwartzMap`; by definition it
    -- evaluates to the underlying function.
    have hψ (x : E) : ψ x = g x := (rfl)
    have h := smulLeftCLM_fourier_cutoffTempered_apply s T φ (ψ := ψ) hgc'
    rw [hf', Lp.toTemperedDistribution_apply] at h
    simpa [hψ, G, Complex.real_smul] using h
  · intro hG
    refine ⟨hG.toLp G, TemperedDistribution.ext_real fun ψ hψ ↦ ?_⟩
    rw [smulLeftCLM_fourier_cutoffTempered_apply s T φ (hψ.comp_left ofReal_zero),
      Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (hG.coeFn_toLp.mono fun η hη ↦ by simp only [hη, G])

/-- **Local Sobolev regularity on Bessel-potential spaces.** A distribution is `H^s` near `x`
exactly when `φ T ∈ H^s` for some test function `φ` with `φ x ≠ 0`. -/
theorem isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered :
    T.IsLocallySobolevAt s x ↔ ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ MemSobolev s 2 (T.cutoffTempered φ) := by
  simp only [isLocallySobolevAt_iff, memSobolev_cutoffTempered_iff]

/-- If `T` is `H^s` near `x`, then `φ T ∈ H^s` for every test function `φ` supported in some
neighbourhood of `x`. -/
theorem IsLocallySobolevAt.exists_nhds_forall_memSobolev_cutoffTempered
    (h : T.IsLocallySobolevAt s x) :
    ∃ U ∈ 𝓝 x, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → MemSobolev s 2 (T.cutoffTempered φ) := by
  obtain ⟨U, hU, hL⟩ := h.exists_nhds
  exact ⟨U, hU, fun φ hφ ↦ memSobolev_cutoffTempered_iff.2 (hL φ hφ)⟩

/-- **Finite Sobolev order.** Every cut-off distribution `φ T` lies in the Bessel-potential space
`H^s` for some real order `s`. -/
theorem exists_memSobolev_cutoffTempered (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ s : ℝ, MemSobolev s 2 (T.cutoffTempered φ) :=
  (T.exists_memLp_one_add_norm_sq_rpow_smul_localFourier φ).imp fun _ h ↦
    memSobolev_cutoffTempered_iff.2 h

end Sobolev

end Distribution
