/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Topology.Algebra.Group.Pointwise

/-!
# The spectrum of a product

The Fourier transform turns products into convolutions, so the frequencies of a product `f g` are
sums of a frequency of `f` and a frequency of `g`. This file proves the support statement for
tempered distributions on a finite-dimensional real inner product space `E`: write
"`𝓕 u` vanishes outside `K`" for `Distribution.IsVanishingOn (𝓕 u) Kᶜ`.

* If `𝓕 u` vanishes outside a set `s` and `g` is a Schwartz function with `𝓕 g` vanishing
  outside a compact set `K`, then `𝓕 (g • u)` vanishes outside `s + K`
  (`TemperedDistribution.isVanishingOn_fourier_smulLeftCLM`).
* If `u ∈ Lᵖ` and `v ∈ L^q` have Fourier transforms vanishing outside compact sets `K₁` and `K₂`,
  and `1/r = 1/p + 1/q` with `r ≥ 1`, then the Fourier transform of the product `u • v ∈ Lʳ`
  vanishes outside `K₁ + K₂` (`MeasureTheory.Lp.isVanishingOn_fourier_smul`). For balls the radii
  and the centres add (`MeasureTheory.Lp.isVanishingOn_fourier_smul_closedBall`).

This is the spectral localization behind Bony's paraproduct decomposition: the dyadic blocks of a
bounded function, or of an element of a Besov space, are `L^∞` functions with spectra in balls and
annuli, and the products
`S_{j-1} f · Δⱼ g` and `Δⱼ f · Δₖ g` that make up the paraproducts and the resonant term then have
spectra in annuli and balls of comparable size.

## The argument

For the first statement, `𝓕 (g • u) ψ = u (g • 𝓕 ψ) = 𝓕 u (T_g ψ)`, where `T_g ψ = 𝓕⁻ (g • 𝓕 ψ)`
is convolution of `ψ` with `𝓕⁻ g = 𝓕 g (-·)` (`SchwartzMap.fourierMultiplierCLM_eq_convolution`).
Hence `T_g ψ` is carried by the closed set `tsupport ψ - K`, which misses `s` when `tsupport ψ`
misses `s + K`.

For the second, neither factor is a Schwartz function, so one factor is first written as a
superposition of Schwartz functions. Fix a test function `φ` with `tsupport φ` disjoint from
`K₁ + K₂`. The open set `U = (tsupport φ - K₂)ᶜ` contains `K₁`, so there is a smooth compactly
supported `χ` equal to one near `K₁` with `tsupport χ ⊆ U`. Then `u = ψ ⋆ u` with `ψ = 𝓕⁻ χ`
(`TemperedDistribution.ae_eq_fourierInv_convolution_of_isVanishingOn`), and Fubini's theorem
gives

`∫ 𝓕 φ • (u • v) = ∫ u y • ∫ (ψ (x - y) * 𝓕 φ x) • v x dx dy = ∫ u y • 𝓕 (ψ (· - y) • v) φ dy`.

The Fourier transform of `ψ (· - y)` is a phase times `χ`, so by the first statement
`𝓕 (ψ (· - y) • v)` vanishes outside `K₂ + tsupport χ`, which misses `tsupport φ` by the choice of
`U`. The double integral converges absolutely: for fixed `x` the inner integral in `y` is bounded
by `‖ψ‖_{p'} ‖u‖_p` by Hölder's inequality, and `𝓕 φ • v` is integrable.

## Main declarations

* `TemperedDistribution.isVanishingOn_fourier_smulLeftCLM`: multiplying by a Schwartz function
  whose spectrum lies in `K` adds `K` to the spectrum.
* `MeasureTheory.Lp.isVanishingOn_fourier_smul`: the spectrum of a product of two `Lᵖ` functions
  with compact spectra lies in the sum of their spectra.
* `MeasureTheory.Lp.isVanishingOn_fourier_smul_closedBall`: the same for spectra in balls.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2
  (the spectral support of products of dyadic blocks in Bony's decomposition).
-/

public section

open SchwartzMap MeasureTheory Distribution Function Set Metric Filter
open scoped ENNReal FourierTransform SchwartzMap Pointwise Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

omit [CompleteSpace F] in
/-- **Multiplication by a band-limited Schwartz function shifts the spectrum.** If the Fourier
transform of a tempered distribution `u` vanishes outside `s`, and `g` is a Schwartz function whose
Fourier transform vanishes outside a compact set `K`, then the Fourier transform of `g • u`
vanishes outside `s + K`. -/
theorem isVanishingOn_fourier_smulLeftCLM {u : 𝓢'(E, F)} {s K : Set E}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) sᶜ) {g : 𝓢(E, ℂ)} (hK : IsCompact K)
    (hgK : support ⇑(𝓕 g : 𝓢(E, ℂ)) ⊆ K) :
    IsVanishingOn (𝓕 (smulLeftCLM F (g : E → ℂ) u) : 𝓢'(E, F)) (s + K)ᶜ := by
  intro ψ hψ
  -- `𝓕 (g • u) ψ = u (g • 𝓕 ψ) = 𝓕 u (T_g ψ)`, where `T_g ψ = 𝓕⁻ (g • 𝓕 ψ)`.
  have h : 𝓕 (smulLeftCLM F (g : E → ℂ) u) ψ =
      𝓕 u (SchwartzMap.fourierMultiplierCLM ℂ (g : E → ℂ) ψ) := by
    rw [fourier_apply, smulLeftCLM_apply_apply, fourier_apply,
      SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  rw [h]
  refine hu _ ?_
  -- `T_g ψ` is the convolution of `ψ` with `𝓕⁻ g = 𝓕 g (-·)`, so it is carried by `tsupport ψ - K`.
  have hsupp : support (SchwartzMap.fourierMultiplierCLM ℂ (g : E → ℂ) ψ) ⊆ tsupport ψ - K := by
    have hconv : ⇑(SchwartzMap.fourierMultiplierCLM ℂ (g : E → ℂ) ψ) =
        ⇑(𝓕⁻ g : 𝓢(E, ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] ⇑ψ := funext fun x ↦ by
      rw [SchwartzMap.fourierMultiplierCLM_eq_convolution, SchwartzMap.convolution_apply]
    rw [hconv, sub_eq_add_neg]
    refine (support_convolution_subset_swap ..).trans (add_subset_add (subset_tsupport _) ?_)
    intro ξ hξ
    rw [mem_support, fourierInv_apply_eq_fourier_neg] at hξ
    exact Set.mem_neg.2 (hgK hξ)
  refine (closure_minimal hsupp ((isClosed_tsupport ψ).sub_right_of_isCompact hK)).trans ?_
  rintro _ ⟨y, hy, t, ht, rfl⟩ hs
  exact hψ hy ⟨y - t, hs, t, ht, sub_add_cancel y t⟩

end TemperedDistribution

namespace MeasureTheory.Lp

omit [CompleteSpace F] in
/-- The integrand `(x, y) ↦ (ψ (x - y) • u y) • (θ x • v x)` of the pairing of `u • v` with `θ`,
after `u` is written as the convolution `ψ ⋆ u`, is integrable on `E × E`: for fixed `x` the
integral in `y` is at most `‖ψ‖_{p'} ‖u‖_p` by Hölder's inequality, and `θ • v` is integrable. -/
private theorem integrable_smul_smul {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]
    (ψ θ : 𝓢(E, ℂ)) (u : Lp ℂ p (volume : Measure E)) (v : Lp F q (volume : Measure E)) :
    Integrable (uncurry fun x y ↦ (ψ (x - y) • u y) • (θ x • v x))
      ((volume : Measure E).prod volume) := by
  have hθv : Integrable (fun x ↦ θ x • v x) := by
    have : (1 - q⁻¹)⁻¹.HolderConjugate q :=
      (ENNReal.HolderConjugate.inv_one_sub_inv' hq.out).symm
    exact memLp_one_iff_integrable.1 ((θ.memLp (1 - q⁻¹)⁻¹ (μ := volume)).smul (Lp.memLp v))
  have hmeas : AEStronglyMeasurable (uncurry fun x y ↦ (ψ (x - y) • u y) • (θ x • v x))
      ((volume : Measure E).prod volume) :=
    ((ψ.continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable u).comp_snd).smul
      ((θ.continuous.comp continuous_fst).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable v).comp_fst)
  refine ⟨hmeas, ?_⟩
  have : (1 - p⁻¹)⁻¹.HolderTriple p 1 := (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  set C := eLpNorm ψ (1 - p⁻¹)⁻¹ volume * eLpNorm u p volume
  have hC : C < ∞ := ENNReal.mul_lt_top (ψ.eLpNorm_lt_top _ volume) (Lp.eLpNorm_lt_top u)
  have hinner : ∀ x, ∫⁻ y, ‖(ψ (x - y) • u y) • (θ x • v x)‖ₑ ≤ C * ‖θ x • v x‖ₑ := fun x ↦ by
    simp_rw [eNorm_smul _ (θ x • v x)]
    rw [lintegral_mul_const' _ _ eNorm_ne_top]
    gcongr
    have hψx : AEStronglyMeasurable (fun y ↦ ψ (x - y)) volume :=
      (ψ.continuous.comp (continuous_sub_left x)).aestronglyMeasurable
    calc ∫⁻ y, ‖ψ (x - y) • u y‖ₑ = eLpNorm ((fun y ↦ ψ (x - y)) • ⇑u) 1 volume := by
          simp only [eLpNorm_one_eq_lintegral_eNorm (hψx.smul (Lp.aestronglyMeasurable u)),
            Pi.smul_apply']
      _ ≤ eLpNorm (fun y ↦ ψ (x - y)) (1 - p⁻¹)⁻¹ volume * eLpNorm u p volume :=
          eLpNorm_smul_le_mul_eLpNorm hψx (Lp.aestronglyMeasurable u)
      _ = C := by
          have h := eLpNorm_comp_measurePreserving (p := (1 - p⁻¹)⁻¹)
            ψ.continuous.aestronglyMeasurable (volume.measurePreserving_sub_left x)
          rw [Function.comp_def] at h
          rw [h]
  rw [HasFiniteIntegral, lintegral_prod _ hmeas.eNorm]
  calc ∫⁻ x, ∫⁻ y, ‖uncurry (fun x y ↦ (ψ (x - y) • u y) • (θ x • v x)) (x, y)‖ₑ
      ≤ ∫⁻ x, C * ‖θ x • v x‖ₑ := lintegral_mono hinner
    _ = C * ∫⁻ x, ‖θ x • v x‖ₑ := lintegral_const_mul' _ _ hC.ne
    _ < ∞ := ENNReal.mul_lt_top hC hθv.2

/-- **The spectrum of a product.** Let `u ∈ Lᵖ` and `v ∈ L^q` have Fourier transforms vanishing
outside compact sets `K₁` and `K₂`, and let `1/r = 1/p + 1/q` with `r ≥ 1`. Then the Fourier
transform of the product `u • v ∈ Lʳ` vanishes outside `K₁ + K₂`. -/
theorem isVanishingOn_fourier_smul {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [Fact (1 ≤ r)] [p.HolderTriple q r] {u : Lp ℂ p (volume : Measure E)}
    {v : Lp F q (volume : Measure E)} {K₁ K₂ : Set E} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hu : IsVanishingOn (𝓕 (u : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ)) K₁ᶜ)
    (hv : IsVanishingOn (𝓕 (v : 𝓢'(E, F)) : 𝓢'(E, F)) K₂ᶜ) :
    IsVanishingOn (𝓕 ((u • v : Lp F r (volume : Measure E)) : 𝓢'(E, F)) : 𝓢'(E, F))
      (K₁ + K₂)ᶜ := by
  intro φ hφ
  -- The open set `U = (tsupport φ - K₂)ᶜ` contains `K₁`, and `U + K₂` misses `tsupport φ`.
  have hU : IsOpen (tsupport φ - K₂)ᶜ :=
    ((isClosed_tsupport φ).sub_right_of_isCompact hK₂).isOpen_compl
  have hK₁U : K₁ ⊆ (tsupport φ - K₂)ᶜ := by
    rintro x hx ⟨y, hy, k, hk, rfl⟩
    exact hφ hy ⟨y - k, hx, k, hk, sub_add_cancel y k⟩
  -- A smooth cutoff `χ`, equal to one near `K₁`, with compact support in `U`.
  obtain ⟨χ₀, hχ₀, -, hχ₀1, hχ₀c, hχ₀U⟩ := hK₁.exists_contDiff_cutoff hU hK₁U
  let χ : 𝓢(E, ℂ) := HasCompactSupport.toSchwartzMap (f := fun ξ ↦ (χ₀ ξ : ℂ))
    (hχ₀c.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hχ₀)
  have hχ : ∀ ξ, χ ξ = χ₀ ξ := fun ξ ↦ HasCompactSupport.toSchwartzMap_toFun _ _ ξ
  have hχsupp : support (χ : E → ℂ) = support χ₀ := by
    ext ξ
    simp [hχ]
  have hχ1 : tsupport (⇑χ - 1) ⊆ K₁ᶜ := by
    have hsub : support (⇑χ - 1) ⊆ (interior (χ₀ ⁻¹' {1}))ᶜ := fun ξ hξ hint ↦ by
      have hξ1 : χ₀ ξ = 1 := interior_subset hint
      exact hξ (by simp [hχ, hξ1])
    exact (closure_minimal hsub isOpen_interior.isClosed_compl).trans
      (compl_subset_compl.2 hχ₀1)
  -- `u` is reproduced by convolution with `ψ = 𝓕⁻ χ`.
  set ψ : 𝓢(E, ℂ) := 𝓕⁻ χ
  have hconv : u =ᵐ[volume] fun x ↦ ∫ y, ψ (x - y) • u y := by
    filter_upwards [TemperedDistribution.ae_eq_fourierInv_convolution_of_isVanishingOn hu hχ1]
      with x hx
    rw [hx, convolution_eq_swap, ← SchwartzMap.fourierInv_coe]
    simp only [ContinuousLinearMap.lsmul_apply, ψ]
  -- For each `y`, the integral in `x` is `𝓕 (ψ (· - y) • v) φ`, which vanishes because the
  -- Fourier transform of `ψ (· - y)` is carried by `tsupport χ`.
  have hχK : IsCompact (tsupport (χ : E → ℂ)) := by
    rw [tsupport, hχsupp]
    exact hχ₀c
  have hφK : tsupport φ ⊆ (K₂ + tsupport (χ : E → ℂ))ᶜ := by
    rintro b hb ⟨k, hk, c, hc, rfl⟩
    exact hχ₀U (by rwa [tsupport, ← hχsupp]) ⟨k + c, hb, k, hk, add_sub_cancel_left k c⟩
  have hzero : ∀ y, ∫ x, (ψ (x - y) • u y) • (𝓕 φ x • v x) = 0 := fun y ↦ by
    set ψy : 𝓢(E, ℂ) := ψ.compSubConstCLM ℂ y
    have hψy : support ⇑(𝓕 ψy : 𝓢(E, ℂ)) ⊆ tsupport (χ : E → ℂ) := by
      rw [support_fourier_compSubConstCLM, FourierTransform.fourier_fourierInv_eq]
      exact subset_tsupport _
    have h := TemperedDistribution.isVanishingOn_fourier_smulLeftCLM hv hχK hψy φ hφK
    rw [TemperedDistribution.fourier_apply, TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply] at h
    calc ∫ x, (ψ (x - y) • u y) • (𝓕 φ x • v x)
        = u y • ∫ x, SchwartzMap.smulLeftCLM ℂ (ψy : E → ℂ) (𝓕 φ) x • v x := by
          rw [← integral_smul]
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp only [SchwartzMap.smulLeftCLM_apply_apply ψy.hasTemperateGrowth,
            compSubConstCLM_apply, ψy, smul_eq_mul, smul_smul]
          ring_nf
      _ = 0 := by rw [h, smul_zero]
  -- Insert `u = ψ ⋆ u` into the pairing and exchange the order of integration.
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  calc ∫ x, 𝓕 φ x • (u • v : Lp F r (volume : Measure E)) x
      = ∫ x, ∫ y, (ψ (x - y) • u y) • (𝓕 φ x • v x) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_lpSMul (r := r) u v, hconv] with x hx hxc
        rw [hx, Pi.smul_apply', hxc, integral_smul_const, smul_comm]
    _ = ∫ y, ∫ x, (ψ (x - y) • u y) • (𝓕 φ x • v x) :=
        integral_integral_swap (integrable_smul_smul ψ (𝓕 φ) u v)
    _ = 0 := by simp only [hzero, integral_zero]

/-- **The spectrum of a product of band-limited functions.** If `u ∈ Lᵖ` and `v ∈ L^q` have Fourier
transforms vanishing outside the closed balls of radii `R₁, R₂ ≥ 0` about `a` and `b`, and
`1/r = 1/p + 1/q` with `r ≥ 1`, then the Fourier transform of `u • v ∈ Lʳ` vanishes outside the
closed ball of radius `R₁ + R₂` about `a + b`. -/
theorem isVanishingOn_fourier_smul_closedBall {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [Fact (1 ≤ r)] [p.HolderTriple q r] {u : Lp ℂ p (volume : Measure E)}
    {v : Lp F q (volume : Measure E)} {a b : E} {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hu : IsVanishingOn (𝓕 (u : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ)) (closedBall a R₁)ᶜ)
    (hv : IsVanishingOn (𝓕 (v : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall b R₂)ᶜ) :
    IsVanishingOn (𝓕 ((u • v : Lp F r (volume : Measure E)) : 𝓢'(E, F)) : 𝓢'(E, F))
      (closedBall (a + b) (R₁ + R₂))ᶜ := by
  have h := isVanishingOn_fourier_smul (r := r) (isCompact_closedBall a R₁)
    (isCompact_closedBall b R₂) hu hv
  rwa [closedBall_add_closedBall hR₁ hR₂] at h

end MeasureTheory.Lp
