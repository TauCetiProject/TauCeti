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
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.MeasureTheory.Measure.Comap

/-!
# Local Sobolev regularity on Bessel-potential spaces

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`, and `φ` a complex test function on `Ω`. The localized Fourier transform
`η ↦ T (φ e_η)` of `Distribution.localFourier`, with `e_η x = 𝐞 (-⟪x, η⟫)`, is the Fourier
transform of the tempered distribution `φ T` of `Distribution.cutoffTempered`:

`𝓕 (φ T) ψ = ∫ ψ η • T (φ e_η) dη`

for every Schwartz function `ψ` (`Distribution.fourier_cutoffTempered_apply`). For compactly
supported `ψ`, `φ 𝓕ψ` is the integral `∫ ψ η • φ e_η dη` of test functions over the compact support
of `ψ`, and `T` passes under that integral
(`Distribution.complexPairing_eq_integral_of_continuous_iteratedFDeriv`). Both sides are tempered
distributions in `ψ`, since the localized Fourier transform grows at most polynomially, and the
compactly supported Schwartz functions are dense. Pairing with an inverse Fourier transform, this
reads `∫ 𝓕⁻ f η T (φ e_η) dη = T (φ f)` for every Schwartz function `f`
(`Distribution.integral_fourierInv_mul_localFourier`).

Consequently the Fourier description of local Sobolev regularity used for the `H^s` wave front
set agrees with Mathlib's Bessel-potential spaces: `φ T ∈ H^s`, in the sense of
`TemperedDistribution.MemSobolev`, exactly when `η ↦ ⟨η⟩ ^ s T (φ e_η)` is square integrable
(`Distribution.memSobolev_cutoffTempered_iff`). So `T` is `H^s` near `x` exactly when `φ T ∈ H^s`
for a cutoff `φ` with `φ x ≠ 0`, and then for every cutoff supported in a neighbourhood of `x`;
and every `φ T` lies in some `H^s`. This transfers estimates on the Bessel-potential spaces `H^s`,
such as the mapping properties of pseudodifferential operators, to distributions on open sets.

Local regularity also gives global regularity of cut-off distributions: if `T` is `H^s` near every
point of the support of `φ`, then `φ T ∈ H^s`
(`Distribution.memSobolev_cutoffTempered_of_forall_isLocallySobolevAt`). Indeed a partition of
unity splits `φ` into finitely many test functions, each supported in a neighbourhood on which every
cutoff gives an `H^s` product. So the distributions with empty `H^s` singular support are exactly
those of `H^s_loc(Ω)`, all of whose cut-offs lie in `H^s`.

A tempered distribution `u` is a distribution on `Ω` by restriction
(`TemperedDistribution.toDistribution`), and then `φ u` is its product with the test function `φ`.
So for tempered distributions, being `H^s` near a point is a statement about the products `φ u`;
an element of `H^s` is `H^s` near every point; and a tempered distribution with compact support
lies in `H^s` exactly when it is `H^s` near every point of its support
(`TemperedDistribution.memSobolev_iff_sobolevSingularSupport_toDistribution_eq_empty`). This is
how regularity of a tempered distribution near each point, as a pseudodifferential operator or
elliptic regularity argument provides it, assembles into membership of a Bessel-potential space.

## Main results

* `Distribution.fourier_cutoffTempered_apply`: the Fourier transform of `φ T` is the localized
  Fourier transform of `T`.
* `Distribution.integral_fourierInv_mul_localFourier`: pairing the localized Fourier transform
  with `𝓕⁻ f` recovers `T (φ f)`.
* `Distribution.smulLeftCLM_fourier_cutoffTempered_eq`,
  `Distribution.memSobolev_cutoffTempered_iff`: `φ T ∈ H^s` exactly when the weighted localized
  Fourier transform is square integrable, and it then represents the weighted Fourier transform of
  `φ T`.
* `Distribution.isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered`,
  `Distribution.IsLocallySobolevAt.exists_nhds_forall_memSobolev_cutoffTempered`: being `H^s` near
  a point in terms of Mathlib's Bessel-potential spaces.
* `Distribution.exists_memSobolev_cutoffTempered`: every `φ T` has a finite Sobolev order.
* `Distribution.memSobolev_cutoffTempered_of_forall_isLocallySobolevAt`: if `T` is `H^s` near every
  point of the support of `φ`, then `φ T ∈ H^s`.
* `Distribution.sobolevSingularSupport_eq_empty_iff_forall_memSobolev_cutoffTempered`: the
  distributions with empty `H^s` singular support are those with `φ T ∈ H^s` for every `φ`.
* `TemperedDistribution.isLocallySobolevAt_toDistribution_iff`,
  `TemperedDistribution.MemSobolev.sobolevSingularSupport_toDistribution_eq_empty`,
  `TemperedDistribution.MemSobolev.sobolevWaveFrontSet_toDistribution_eq_empty`: local Sobolev
  regularity of tempered distributions, and of elements of `H^s`.
* `TemperedDistribution.memSobolev_of_isCompact_dsupport_of_forall_isLocallySobolevAt`,
  `TemperedDistribution.memSobolev_iff_sobolevSingularSupport_toDistribution_eq_empty`: a tempered
  distribution with compact support lies in `H^s` exactly when it is `H^s` near every point.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 7.1.14 (the
  Fourier transform of a compactly supported distribution is the function `η ↦ T (e_η)`).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2 (localization by
  partitions of unity) and §7.1 (tempered distributions as distributions).
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

/-- The Fourier transform of `φ T` on a compactly supported Schwartz function `ψ`:
`𝓕 (φ T) ψ = ∫ ψ η • T (φ e_η) dη`. -/
private theorem fourier_cutoffTempered_apply_of_hasCompactSupport (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ))
    {ψ : 𝓢(E, ℂ)} (hψ : HasCompactSupport ψ) :
    𝓕 (T.cutoffTempered φ) ψ = ∫ η, ψ η • T.localFourier φ η := by
  rw [TemperedDistribution.fourier_apply]
  -- The parameter space is the compact support of `ψ`.
  let Y := tsupport (ψ : E → ℂ)
  have hY : MeasurableSet Y := (isClosed_tsupport _).measurableSet
  have : CompactSpace Y := isCompact_iff_compactSpace.1 hψ
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
      ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
  have hfK (η : Y) : tsupport (f η) ⊆ tsupport φ := by
    rw [show ⇑(f η) = fun x ↦ ψ η * (φ x * TauCeti.fourierAtom (η : E) x) from funext (hf η)]
    exact tsupport_mul_subset_right.trans tsupport_mul_subset_left
  rw [cutoffTempered_def, complexPairing_eq_integral_of_continuous_iteratedFDeriv T
    (K := ⟨_, φ.hasCompactSupport⟩) φ.tsupport_subset hfK hjets hχ]
  rw [← hYE _ fun η hη ↦ by simp [hη]]
  refine integral_congr_ae (ae_of_all _ fun η ↦ ?_)
  simp only [f, map_smul, smul_eq_mul, localFourier_def]

/-- **The Fourier transform of `φ T` is the localized Fourier transform of `T`.** For every
Schwartz function `ψ`, `𝓕 (φ T) ψ = ∫ ψ η • T (φ e_η) dη`. -/
theorem fourier_cutoffTempered_apply (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (ψ : 𝓢(E, ℂ)) :
    𝓕 (T.cutoffTempered φ) ψ = ∫ η, ψ η • T.localFourier φ η := by
  -- The right-hand side is the tempered distribution `w M`, for `M = ⟨η⟩ ^ s T (φ e_η)` square
  -- integrable and the weight `w = ⟨η⟩ ^ (-s)` of temperate growth.
  obtain ⟨s, hs⟩ := T.exists_memLp_one_add_norm_sq_rpow_smul_localFourier φ
  set w : E → ℂ := fun η ↦ (((1 + ‖η‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  have hwM (η : E) :
      w η • (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η = T.localFourier φ η := by
    have hpos : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
    have hne : ((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hpos _).ne'
    simp only [w, neg_div, Real.rpow_neg hpos.le, smul_eq_mul, Complex.real_smul, ofReal_inv,
      ← mul_assoc]
    rw [inv_mul_cancel₀ (by exact_mod_cast hne), one_mul]
  have key (ψ : 𝓢(E, ℂ)) :
      TemperedDistribution.smulLeftCLM ℂ w (hs.toLp _ : 𝓢'(E, ℂ)) ψ =
        ∫ η, ψ η • T.localFourier φ η := by
    rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae (hs.coeFn_toLp.mono fun η hη ↦ ?_)
    dsimp only at hη ⊢
    rw [hη, SchwartzMap.smulLeftCLM_apply_apply hw]
    conv_rhs => rw [← hwM η]
    simp only [smul_eq_mul, Complex.real_smul]
    ring
  have h : 𝓕 (T.cutoffTempered φ) =
      TemperedDistribution.smulLeftCLM ℂ w (hs.toLp _ : 𝓢'(E, ℂ)) :=
    TemperedDistribution.ext_real fun ψ hψ ↦ by
      rw [key, fourier_cutoffTempered_apply_of_hasCompactSupport T φ (hψ.comp_left ofReal_zero)]
  rw [h, key]

/-- **Fourier inversion for `φ T`.** Pairing the localized Fourier transform of `T` with the inverse
Fourier transform of a Schwartz function `f` gives `φ T` evaluated at `f`:
`∫ 𝓕⁻ f η T (φ e_η) dη = T (φ f)`. -/
theorem integral_fourierInv_mul_localFourier (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (f : 𝓢(E, ℂ)) :
    ∫ η, 𝓕⁻ f η * T.localFourier φ η = T.cutoffTempered φ f := by
  rw [← FourierTransform.fourier_fourierInv_eq (F := 𝓢(E, ℂ)) f,
    ← TemperedDistribution.fourier_apply, fourier_cutoffTempered_apply,
    FourierTransform.fourier_fourierInv_eq]
  simp only [smul_eq_mul]

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
    fourier_cutoffTempered_apply_of_hasCompactSupport T φ (by
      rw [hcoe]
      exact hψ.smul_left (f := fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))), hcoe]
  refine integral_congr_ae (ae_of_all _ fun η ↦ ?_)
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- **The weighted Fourier transform of `φ T`.** If the weighted localized Fourier transform
`η ↦ ⟨η⟩ ^ s T (φ e_η)` is square integrable, then it represents `⟨η⟩ ^ s 𝓕 (φ T)`. -/
theorem smulLeftCLM_fourier_cutoffTempered_eq
    (hG : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 volume) :
    TemperedDistribution.smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
      (𝓕 (T.cutoffTempered φ)) = hG.toLp _ :=
  TemperedDistribution.ext_real fun ψ hψ ↦ by
    rw [smulLeftCLM_fourier_cutoffTempered_apply s T φ (hψ.comp_left ofReal_zero),
      Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (hG.coeFn_toLp.mono fun η hη ↦ by simp only [hη])

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
  · exact fun hG ↦ ⟨hG.toLp G, smulLeftCLM_fourier_cutoffTempered_eq hG⟩

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

/-- **From local to global regularity.** If `T` is `H^s` near every point of the support of a test
function `φ`, then `φ T ∈ H^s`. -/
theorem memSobolev_cutoffTempered_of_forall_isLocallySobolevAt
    (h : ∀ x ∈ tsupport φ, T.IsLocallySobolevAt s x) : MemSobolev s 2 (T.cutoffTempered φ) := by
  -- Each point of `tsupport φ` has a neighbourhood on which every cutoff gives an `H^s` product.
  choose U hU hUs using fun x : tsupport φ ↦
    (h x x.property).exists_nhds_forall_memSobolev_cutoffTempered
  -- Split `φ` into finitely many test functions supported in these neighbourhoods.
  obtain ⟨t, ψ, hψU, hψφ, -⟩ := φ.exists_sum_subordinate (fun x ↦ interior (U x))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU ⟨x, hx⟩)⟩
  rw [← hψφ, cutoffTempered_sum_cutoff]
  exact MemSobolev.sum fun i _ ↦ hUs i _ ((hψU i).trans interior_subset)

/-- **Local `H^s` regularity on all of `Ω`.** A distribution has empty `H^s` singular support,
that is, it is `H^s` near every point of `Ω`, exactly when `φ T ∈ H^s` for every test function
`φ`: these are the distributions of `H^s_loc(Ω)`. -/
theorem sobolevSingularSupport_eq_empty_iff_forall_memSobolev_cutoffTempered :
    T.sobolevSingularSupport s = ∅ ↔ ∀ φ : 𝓓(Ω, ℂ), MemSobolev s 2 (T.cutoffTempered φ) := by
  simp only [eq_empty_iff_forall_notMem, mem_sobolevSingularSupport_iff, not_and, not_not]
  refine ⟨fun h φ ↦ memSobolev_cutoffTempered_of_forall_isLocallySobolevAt fun x hx ↦
    h x (φ.tsupport_subset hx), fun h x hx ↦ ?_⟩
  obtain ⟨φ, -, hφx⟩ :=
    exists_tsupport_subset_apply_eq (n := ⊤) (Ω.isOpen.mem_nhds hx) subset_rfl (1 : ℂ)
  exact isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2 ⟨φ, by simp [hφx], h φ⟩

end Sobolev

end Distribution

/-! ### Tempered distributions -/

namespace TemperedDistribution

open Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s : ℝ} {u : 𝓢'(E, ℂ)} {x : E}

/-- A tempered distribution is `H^s` near `x`, as a distribution on `Ω`, exactly when `φ u ∈ H^s`
for some test function `φ` on `Ω` with `φ x ≠ 0`. -/
theorem isLocallySobolevAt_toDistribution_iff :
    (toDistribution Ω u).IsLocallySobolevAt s x ↔
      ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ MemSobolev s 2 (smulLeftCLM ℂ (φ : E → ℂ) u) := by
  simp only [isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered,
    cutoffTempered_toDistribution]

/-- A tempered distribution in `H^s` is `H^s` near every point, as a distribution on `Ω`. -/
theorem MemSobolev.isLocallySobolevAt_toDistribution (hu : MemSobolev s 2 u) (hx : x ∈ Ω) :
    (toDistribution Ω u).IsLocallySobolevAt s x := by
  obtain ⟨φ, -, hφx⟩ :=
    exists_tsupport_subset_apply_eq (n := ⊤) (Ω.isOpen.mem_nhds hx) subset_rfl (1 : ℂ)
  refine isLocallySobolevAt_toDistribution_iff.2 ⟨φ, by simp [hφx], ?_⟩
  simpa using hu.smulLeftCLM (toSchwartzMapCLM ℝ φ)

/-- A tempered distribution in `H^s` has empty `H^s` singular support as a distribution on `Ω`. -/
theorem MemSobolev.sobolevSingularSupport_toDistribution_eq_empty (hu : MemSobolev s 2 u) :
    (toDistribution Ω u).sobolevSingularSupport s = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx ↦
    (mem_sobolevSingularSupport_iff.1 hx).2 (hu.isLocallySobolevAt_toDistribution
      (mem_sobolevSingularSupport_iff.1 hx).1)

/-- A tempered distribution in `H^s` has empty `H^s` wave front set as a distribution on `Ω`. -/
theorem MemSobolev.sobolevWaveFrontSet_toDistribution_eq_empty (hu : MemSobolev s 2 u) :
    (toDistribution Ω u).sobolevWaveFrontSet s = ∅ :=
  sobolevSingularSupport_eq_empty_iff_sobolevWaveFrontSet_eq_empty.1
    hu.sobolevSingularSupport_toDistribution_eq_empty

/-- **From local to global regularity for tempered distributions.** A tempered distribution with
compact support which is `H^s` near every point of its support lies in `H^s`. -/
theorem memSobolev_of_isCompact_dsupport_of_forall_isLocallySobolevAt (hu : IsCompact (dsupport u))
    (h : ∀ x ∈ dsupport u, (toDistribution ⊤ u).IsLocallySobolevAt s x) : MemSobolev s 2 u := by
  set T := toDistribution (⊤ : Opens E) u
  -- `u` is the cut-off distribution `χ T` for a cutoff `χ` equal to `1` near its support.
  obtain ⟨χ, hχ, -⟩ := exists_eventually_eq_one (n := ⊤) (Ω := ⊤) hu (subset_univ _)
  set χ' : 𝓓((⊤ : Opens E), ℂ) := postcompCLM ofRealCLM χ
  have hχ' : (χ' : E → ℂ) =ᶠ[𝓝ˢ (dsupport T)] 1 :=
    (hχ.filter_mono (nhdsSet_mono (dsupport_toDistribution_subset u))).mono fun y hy ↦ by
      simp [χ', postcompCLM_apply, hy]
  have hu' : u = T.cutoffTempered χ' := eq_cutoffTempered_of_forall T χ' fun ψ ψ' hψ hψ' ↦ by
    -- `ψ` is a test function, and `ψ' = χ' ψ` agrees with it near the support of `T`.
    let ψt : 𝓓((⊤ : Opens E), ℂ) := postcompCLM ofRealCLM (ψ.toTestFunction hψ (subset_univ _))
    have hψt : toSchwartzMapCLM ℝ ψt = ψ.postcompCLM ofRealCLM := by simp [ψt]
    rw [← hψt, ← complexPairing_toDistribution]
    exact complexPairing_eq_of_eventuallyEq T (hχ'.mono fun y hy ↦ by simp [ψt, hψ' y, hy])
  rw [hu']
  refine memSobolev_cutoffTempered_of_forall_isLocallySobolevAt fun y _ ↦ ?_
  by_cases hy : y ∈ dsupport u
  · exact h y hy
  · exact (notMem_sobolevSingularSupport_iff (mem_univ y)).1 fun hy' ↦
      hy (dsupport_toDistribution_subset u (sobolevSingularSupport_subset_dsupport s T hy'))

/-- A tempered distribution with compact support lies in `H^s` exactly when it is `H^s` near every
point. -/
theorem memSobolev_iff_sobolevSingularSupport_toDistribution_eq_empty
    (hu : IsCompact (dsupport u)) :
    MemSobolev s 2 u ↔ (toDistribution ⊤ u).sobolevSingularSupport s = ∅ :=
  ⟨MemSobolev.sobolevSingularSupport_toDistribution_eq_empty, fun h ↦
    memSobolev_of_isCompact_dsupport_of_forall_isLocallySobolevAt hu fun x _ ↦
      (notMem_sobolevSingularSupport_iff (mem_univ x)).1 (h ▸ notMem_empty x)⟩

end TemperedDistribution
