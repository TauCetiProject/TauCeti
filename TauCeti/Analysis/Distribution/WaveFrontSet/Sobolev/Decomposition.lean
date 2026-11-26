/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TestFunction.FourierAtom
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.WaveFrontSet.Tempered
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Sobolev.BesselPotential.PrescribedFourier
import TauCeti.MeasureTheory.Integral.ConicDecay

/-!
# Microlocal Sobolev regularity modulo microlocal smoothness

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. This file shows that `T` is microlocally `H^s` at `(x, ξ)`
(`Distribution.IsMicrolocallySobolevAt`) exactly when it is the sum of an element of the
Bessel-potential space `H^s` and of a distribution that is microlocally smooth at `(x, ξ)`:

`T` is microlocally `H^s` at `(x, ξ)` ↔ `T - u` is microlocally smooth at `(x, ξ)` for some
`u ∈ H^s`

(`Distribution.isMicrolocallySobolevAt_iff_exists_memSobolev`), where `u` is read as a distribution
on `Ω` by restriction (`TemperedDistribution.toDistribution`). This reduces statements about the
`H^s` wave front set to statements about `H^s` itself and about the wave front set. For instance,
local `H^s` regularity is invariant under smooth changes of variables, and so is microlocal
smoothness; together they give the invariance of microlocal `H^s` regularity
(`Distribution.IsMicrolocallySobolevAt.compCLMOfOpenPartialHomeomorph`).

## The construction

Let `T` be microlocally `H^s` at `(x, ξ)`. There are a cutoff `ψ` equal to `1` near `x` and an open
cone `Γ` around `ξ` such that `⟨η⟩ ^ s F` is square integrable on `Γ`, where
`F η = T (ψ e_η)` is the localized Fourier transform of `T`, the Fourier transform of `ψ T`
(`Distribution.fourier_cutoffTempered_apply`). Let `u` be the tempered distribution whose Fourier
transform is the function `F` on `Γ` and `0` off `Γ`
(`TemperedDistribution.exists_memSobolev_fourier_apply_eq_integral`); it lies in `H^s`. Near `x`,
`T - u` agrees with `ψ T - u`, whose Fourier transform is `F` off `Γ` and `0` on `Γ`. For a cutoff
`φ` supported where `ψ = 1`, its localized Fourier transform is the convolution

`(T - u) (φ e_η) = ∫ 𝓕 φ (η - ζ) F ζ dζ`, over `ζ ∉ Γ`.

On a smaller cone `Γ'` around `ξ`, the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in
`Γ` (`IsOpen.exists_cone_closedBall_subset`), where the integrand vanishes, so the rapid decay of
`𝓕 φ` beats the polynomial growth of `F` and the convolution decays rapidly on `Γ'`
(`TauCeti.exists_one_add_norm_pow_mul_norm_integral_le`).

## Main results

* `Distribution.IsMicrolocallySobolevAt.exists_memSobolev_isMicrolocallySmoothAt_sub`: a
  distribution microlocally `H^s` at `(x, ξ)` is an element of `H^s` plus a distribution
  microlocally smooth at `(x, ξ)`.
* `Distribution.isMicrolocallySobolevAt_iff_exists_memSobolev`: the characterization of microlocal
  `H^s` regularity as `H^s` modulo microlocal smoothness.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory TemperedDistribution
open scoped Distributions Topology SchwartzMap ContDiff FourierTransform RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Distribution

variable {Ω : Opens E}

/-- A Schwartz function times the localized Fourier transform of `T`, restricted to a measurable
set, is integrable: the localized Fourier transform grows at most polynomially. -/
private theorem integrable_mul_indicator_localFourier (T : 𝓓'(Ω, ℂ)) (ψ : 𝓓(Ω, ℂ))
    (g : 𝓢(E, ℂ)) {Γ : Set E} (hΓ : MeasurableSet Γ) :
    Integrable fun ζ ↦ g ζ * Γ.indicator (T.localFourier ψ) ζ := by
  obtain ⟨C, k, hC⟩ := exists_norm_localFourier_le T ψ
  refine ((g.integrable_one_add_norm_sq_rpow_mul_norm (μ := volume) (k : ℝ)).const_mul
    (C * 2 ^ k)).mono' (g.continuous.aestronglyMeasurable.mul
      ((T.continuous_localFourier ψ).aestronglyMeasurable.indicator hΓ))
    (.of_forall fun ζ ↦ ?_)
  -- `1 + ‖ζ‖ ≤ 2 (1 + ‖ζ‖ ^ 2)`, so the growth of `F` is absorbed by the weight.
  have hζ : (1 + ‖ζ‖) ^ k ≤ 2 ^ k * (1 + ‖ζ‖ ^ 2) ^ (k : ℝ) := by
    rw [Real.rpow_natCast, ← mul_pow]
    gcongr
    nlinarith [sq_nonneg (‖ζ‖ - 1 / 4), norm_nonneg ζ]
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  have hind : ‖Γ.indicator (T.localFourier ψ) ζ‖ ≤ C * (1 + ‖ζ‖) ^ k :=
    (norm_indicator_le_norm_self _ ζ).trans (hC ζ)
  calc ‖g ζ * Γ.indicator (T.localFourier ψ) ζ‖ ≤ ‖g ζ‖ * (C * (1 + ‖ζ‖) ^ k) := by
        rw [norm_mul]; gcongr
    _ ≤ ‖g ζ‖ * (C * (2 ^ k * (1 + ‖ζ‖ ^ 2) ^ (k : ℝ))) := by gcongr
    _ = C * 2 ^ k * ((1 + ‖ζ‖ ^ 2) ^ (k : ℝ) * ‖g ζ‖) := by ring

/-- **The localized Fourier transform of `T - u` as a convolution.** Let `ψ = 1` on a neighbourhood
of the support of the cutoff `φ`, and let the tempered distribution `u` have Fourier transform
the localized Fourier transform `F = T (ψ e_·)` of `T` on a measurable set `Γ` and `0` off it.
Then `(T - u) (φ e_η)` is the convolution `∫ 𝓕 φ (η - ζ) F ζ dζ` over `ζ ∉ Γ`. -/
private theorem localFourier_sub_toDistribution_eq_integral (T : 𝓓'(Ω, ℂ)) {ψ φ : 𝓓(Ω, ℂ)}
    (hψφ : ∀ y ∈ tsupport φ, ψ y = 1) {Γ : Set E} (hΓ : MeasurableSet Γ) {u : 𝓢'(E, ℂ)}
    (hu : ∀ g : 𝓢(E, ℂ), 𝓕 u g = ∫ ζ, g ζ • Γ.indicator (T.localFourier ψ) ζ) (η : E) :
    (T - toDistribution Ω u).localFourier φ η =
      ∫ ζ, 𝓕 (φ : E → ℂ) (η - ζ) * Γᶜ.indicator (T.localFourier ψ) ζ := by
  set f : 𝓢(E, ℂ) := φ.fourierAtomMulSchwartzMap η
  -- `T (φ e_η) = (ψ T) (φ e_η)`, since `ψ = 1` on the support of `φ`.
  have hT : T.localFourier φ η = ∫ ζ, 𝓕⁻ f ζ * T.localFourier ψ ζ := by
    rw [integral_fourierInv_mul_localFourier, localFourier_def,
      cutoffTempered_apply T ψ (χ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
        (TauCeti.contDiff_fourierAtom η) φ)]
    intro y
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', f,
      fourierAtomMulSchwartzMap_apply]
    by_cases hy : y ∈ tsupport φ
    · rw [hψφ y hy, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  -- `u (φ e_η) = 𝓕 u (𝓕⁻ (φ e_η))`.
  have hu' : (toDistribution Ω u).localFourier φ η =
      ∫ ζ, 𝓕⁻ f ζ * Γ.indicator (T.localFourier ψ) ζ := by
    have huf : u f = 𝓕 u (𝓕⁻ f) := by
      rw [TemperedDistribution.fourier_apply, FourierTransform.fourier_fourierInv_eq]
    rw [localFourier_toDistribution, huf, hu]
    simp only [smul_eq_mul]
  rw [localFourier_sub, hT, hu', ← integral_sub (by
      simpa using integrable_mul_indicator_localFourier T ψ (𝓕⁻ f) MeasurableSet.univ)
      (integrable_mul_indicator_localFourier T ψ (𝓕⁻ f) hΓ)]
  refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
  -- `𝓕⁻ (φ e_η) ζ = 𝓕 (φ e_η) (-ζ) = 𝓕 φ (η - ζ)`.
  have hf : 𝓕⁻ f ζ = 𝓕 (φ : E → ℂ) (η - ζ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourier_coe,
      fourier_fourierAtomMulSchwartzMap, SchwartzMap.fourier_coe, neg_add_eq_sub,
      coe_toSchwartzMapCLM]
  by_cases hζ : ζ ∈ Γ <;> simp [hζ, hf]

/-- **Microlocal `H^s` regularity splits off an element of `H^s`.** If `T` is microlocally `H^s` at
`(x, ξ)`, then `T - u` is microlocally smooth at `(x, ξ)` for some element `u` of the
Bessel-potential space `H^s`, read as a distribution on `Ω`. -/
theorem IsMicrolocallySobolevAt.exists_memSobolev_isMicrolocallySmoothAt_sub {s : ℝ}
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (h : T.IsMicrolocallySobolevAt s x ξ) :
    ∃ u : 𝓢'(E, ℂ), MemSobolev s 2 u ∧ (T - toDistribution Ω u).IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := h.mem
  obtain ⟨W, hW, Γ, hΓo, hξΓ, hΓc, hL⟩ := h.exists_nhds_cone
  -- A cutoff `ψ` equal to `1` on a neighbourhood `V` of `x` and supported in `W`.
  obtain ⟨ψ, V, hVo, hxV, hψV, hψW⟩ := exists_eqOn_one_tsupport_subset (n := ⊤) (𝕜 := ℂ) hW hx
  set F := T.localFourier ψ
  -- `u ∈ H^s` has Fourier transform `F` on `Γ` and `0` off `Γ`.
  have hG : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • Γ.indicator F η) 2 volume := by
    have he : (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • Γ.indicator F η) =
        Γ.indicator fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η := by
      ext η
      by_cases hη : η ∈ Γ <;> simp [hη]
    rw [he, memLp_indicator_iff_restrict hΓo.measurableSet.nullMeasurableSet]
    exact hL ψ hψW
  obtain ⟨u, hu, hFu⟩ := exists_memSobolev_fourier_apply_eq_integral hG
  refine ⟨u, hu, ?_⟩
  -- On a smaller cone `Γ'`, the frequencies off `Γ` are far from those of `Γ'`.
  obtain ⟨Γ', hΓ'o, hξΓ', hΓ'c, c, hc, hball⟩ := hΓo.exists_cone_closedBall_subset hΓc hξΓ
  -- A cutoff `φ` at `x` supported in `V`, where `ψ = 1`.
  obtain ⟨φ, hφV, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hVo.mem_nhds hxV) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  have hψφ : ∀ y ∈ tsupport φ, ψ y = 1 := fun y hy ↦ by
    simpa using hψV (hφV hy).1
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ', hΓ'o, hξΓ', hΓ'c, fun N ↦ ?_⟩
  -- The convolution of `𝓕 φ`, rapidly decreasing, with `F` off `Γ`, which vanishes on `Γ`.
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T ψ
  obtain ⟨C, hC⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_integral_le (μ := volume) (M := 0)
    (K := fun θ _ ↦ 𝓕 (φ : E → ℂ) θ • ContinuousLinearMap.id ℂ ℂ)
    (fun j ↦ (TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport
      j).imp fun A hA θ _ ↦ by simpa [norm_smul] using hA θ)
    (F := Γᶜ.indicator F) (fun ζ ↦ (norm_indicator_le_norm_self _ ζ).trans (hF ζ)) hc hball
    (N := N) ⟨0, fun η hη ↦ by simp [indicator_of_notMem (notMem_compl_iff.2 hη)]⟩
  exact ⟨C, fun η hη ↦ by
    rw [localFourier_sub_toDistribution_eq_integral T hψφ hΓo.measurableSet hFu]
    simpa using hC η hη⟩

/-- **Microlocal `H^s` regularity is `H^s` modulo microlocal smoothness.** A distribution `T` on
`Ω` is microlocally `H^s` at `(x, ξ)` exactly when `T - u` is microlocally smooth at `(x, ξ)` for
some element `u` of the Bessel-potential space `H^s`, read as a distribution on `Ω`. -/
theorem isMicrolocallySobolevAt_iff_exists_memSobolev {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E} :
    T.IsMicrolocallySobolevAt s x ξ ↔
      ∃ u : 𝓢'(E, ℂ), MemSobolev s 2 u ∧ (T - toDistribution Ω u).IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun h ↦ h.exists_memSobolev_isMicrolocallySmoothAt_sub, fun ⟨u, hu, hT⟩ ↦ ?_⟩
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 hT
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  simpa using ((hu.isLocallySobolevAt_toDistribution hx).isMicrolocallySobolevAt ξ).add
    (hT.isMicrolocallySobolevAt s)

end Distribution
