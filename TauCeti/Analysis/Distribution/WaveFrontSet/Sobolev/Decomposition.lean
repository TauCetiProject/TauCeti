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

On a smaller cone `Γ'` around `ξ`, every `ζ ∉ Γ` is at distance at least `c (‖η‖ + ‖ζ‖)` from
`η ∈ Γ'` (`IsOpen.exists_cone_mul_add_le_norm_sub`), so the rapid decay of `𝓕 φ` beats the
polynomial growth of `F` (`TauCeti.exists_one_add_norm_pow_mul_one_add_norm_pow_mul_norm_mul_le`),
and the convolution decays rapidly on `Γ'`.

## Main results

* `TemperedDistribution.exists_memSobolev_fourier_apply_eq_integral`: a function `F` with
  `⟨η⟩ ^ s F` square integrable is the Fourier transform of an element of `H^s`.
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

namespace TemperedDistribution

/-- **An element of `H^s` with a prescribed Fourier transform.** If `F` is a function with
`⟨η⟩ ^ s F = (1 + ‖η‖ ^ 2) ^ (s / 2) F` square integrable, then some element `u` of the
Bessel-potential space `H^s` has Fourier transform the function `F`: `𝓕 u g = ∫ g η • F η` for
every Schwartz function `g`. -/
theorem exists_memSobolev_fourier_apply_eq_integral {s : ℝ} {F : E → ℂ}
    (hF : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 volume) :
    ∃ u : 𝓢'(E, ℂ), MemSobolev s 2 u ∧ ∀ g : 𝓢(E, ℂ), 𝓕 u g = ∫ η, g η • F η := by
  -- `u` is the inverse Fourier transform of `⟨η⟩ ^ (-s)` times the `L²` function `⟨η⟩ ^ s F`.
  set w : E → ℂ := fun η ↦ (((1 + ‖η‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  have hb : (fun η : E ↦ (((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hwb (η : E) : w η * (((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) = 1 := by
    have hpos : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
    rw [← ofReal_mul, ← Real.rpow_add hpos, neg_div, neg_add_cancel, Real.rpow_zero, ofReal_one]
  set v : 𝓢'(E, ℂ) := smulLeftCLM ℂ w (hF.toLp _ : 𝓢'(E, ℂ))
  have hv : 𝓕 (𝓕⁻ v) = v := FourierTransform.fourier_fourierInv_eq v
  refine ⟨𝓕⁻ v, memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨hF.toLp _, ?_⟩, fun g ↦ ?_⟩
  · rw [hv, smulLeftCLM_smulLeftCLM_apply hw hb]
    have h1 : (w * fun η : E ↦ (((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) = fun _ ↦ 1 := funext hwb
    rw [h1, smulLeftCLM_const, one_smul]
  · rw [hv, smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae (hF.coeFn_toLp.mono fun η hη ↦ ?_)
    dsimp only at hη ⊢
    rw [hη, SchwartzMap.smulLeftCLM_apply_apply hw]
    simp only [smul_eq_mul, Complex.real_smul]
    linear_combination (g η * F η) * hwb η

end TemperedDistribution

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
  rw [sub_eq_add_neg, localFourier_add, ← neg_one_smul ℂ (toDistribution Ω u), localFourier_smul,
    hT, hu', neg_one_mul, ← sub_eq_add_neg, ← integral_sub (by
      simpa using integrable_mul_indicator_localFourier T ψ (𝓕⁻ f) MeasurableSet.univ)
      (integrable_mul_indicator_localFourier T ψ (𝓕⁻ f) hΓ)]
  refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
  -- `𝓕⁻ (φ e_η) ζ = 𝓕 (φ e_η) (-ζ) = 𝓕 φ (η - ζ)`.
  have hf : 𝓕⁻ f ζ = 𝓕 (φ : E → ℂ) (η - ζ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourier_coe,
      fourier_fourierAtomMulSchwartzMap, SchwartzMap.fourier_coe, neg_add_eq_sub,
      coe_toSchwartzMapCLM]
  by_cases hζ : ζ ∈ Γ <;> simp [hζ, hf]

/-- **Rapid decay of a convolution with a function vanishing on a cone.** Let `F` grow at most
polynomially and vanish on a set `Γ`, and let every `ζ ∉ Γ` be at distance at least
`c (‖η‖ + ‖ζ‖)` from every `η ∈ Γ'`. Then the convolution `∫ 𝓕 φ (η - ζ) F ζ dζ` of `F` with the
Fourier transform of a test function `φ` decays rapidly on `Γ'`. -/
private theorem exists_one_add_norm_pow_mul_norm_integral_le (φ : 𝓓(Ω, ℂ)) {F : E → ℂ}
    (hF : ∃ (C : ℝ) (k : ℕ), ∀ ζ, ‖F ζ‖ ≤ C * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E}
    (hFΓ : ∀ ζ ∈ Γ, F ζ = 0) {c : ℝ} (hc : 0 < c)
    (hsep : ∀ η ∈ Γ', ∀ ζ ∉ Γ, c * (‖η‖ + ‖ζ‖) ≤ ‖ζ - η‖) (N : ℕ) :
    ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N * ‖∫ ζ, 𝓕 (φ : E → ℂ) (η - ζ) * F ζ‖ ≤ C := by
  set d := Module.finrank ℝ E
  set M := N + (d + 1)
  obtain ⟨C, hC⟩ := TauCeti.exists_one_add_norm_pow_mul_one_add_norm_pow_mul_norm_mul_le
    (ContinuousLinearMap.id ℝ E) hc (Γ := Γ) (Γ' := Γ') (fun η hη ζ hζ ↦ hsep η hη ζ hζ)
    (g := 𝓕 (φ : E → ℂ)) (F := F)
    (TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport) hF
    (fun _ ↦ ⟨0, fun ζ hζ ↦ by simp [hFΓ ζ hζ]⟩) M
  have hint : Integrable (fun ζ : E ↦ C * (1 + ‖ζ‖) ^ (-((d : ℝ) + 1))) :=
    (integrable_one_add_norm (by linarith)).const_mul C
  refine ⟨∫ ζ : E, C * (1 + ‖ζ‖) ^ (-((d : ℝ) + 1)), fun η hη ↦ ?_⟩
  rw [← Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖η‖) ^ N), ← norm_smul,
    ← integral_smul]
  refine norm_integral_le_of_norm_le hint (.of_forall fun ζ ↦ ?_)
  -- With `a = 1 + ‖η‖` and `b = 1 + ‖ζ‖`: `a ^ M (b ^ M X) ≤ C` gives `a ^ N X ≤ C b ^ (-(d + 1))`.
  have ha : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
  have hb : 1 ≤ 1 + ‖ζ‖ := le_add_of_nonneg_right (norm_nonneg ζ)
  have hpow : (1 + ‖ζ‖) ^ (-((d : ℝ) + 1)) = ((1 + ‖ζ‖) ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast, Nat.cast_succ]
  have hCη := hC η hη ζ
  simp only [ContinuousLinearMap.coe_id', id_eq] at hCη
  rw [norm_smul, Real.norm_of_nonneg (by positivity), hpow, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc (1 + ‖η‖) ^ N * ‖𝓕 (φ : E → ℂ) (η - ζ) * F ζ‖ * (1 + ‖ζ‖) ^ (d + 1)
      ≤ (1 + ‖η‖) ^ M * ‖𝓕 (φ : E → ℂ) (η - ζ) * F ζ‖ * (1 + ‖ζ‖) ^ M := by
        gcongr <;> omega
    _ = (1 + ‖η‖) ^ M * ((1 + ‖ζ‖) ^ M * ‖𝓕 (φ : E → ℂ) (η - ζ) * F ζ‖) := by ring
    _ ≤ C := hCη

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
  obtain ⟨Γ', hΓ'o, hξΓ', hΓ'c, c, hc, hsep⟩ :=
    hΓo.exists_cone_mul_add_le_norm_sub hΓc hξΓ (ContinuousLinearEquiv.refl ℝ E)
  -- A cutoff `φ` at `x` supported in `V`, where `ψ = 1`.
  obtain ⟨φ, hφV, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hVo.mem_nhds hxV) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  have hψφ : ∀ y ∈ tsupport φ, ψ y = 1 := fun y hy ↦ by
    simpa using hψV (hφV hy).1
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ', hΓ'o, by simpa using hξΓ', hΓ'c,
    fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_integral_le φ (F := Γᶜ.indicator F)
    ((exists_norm_localFourier_le T ψ).imp fun C ⟨k, hk⟩ ↦
      ⟨k, fun ζ ↦ (norm_indicator_le_norm_self _ ζ).trans (hk ζ)⟩)
    (fun ζ hζ ↦ indicator_of_notMem (notMem_compl_iff.2 hζ) _) hc
    (fun η hη ζ hζ ↦ by simpa using hsep η hη ζ (Or.inl hζ)) N
  exact ⟨C, fun η hη ↦ by
    rw [localFourier_sub_toDistribution_eq_integral T hψφ hΓo.measurableSet hFu]
    exact hC η hη⟩

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
