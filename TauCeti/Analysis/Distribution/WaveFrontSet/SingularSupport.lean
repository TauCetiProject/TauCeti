/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# The singular support and the projection of the wave front set

The *singular support* `Distribution.singSupport T` of a complex distribution `T` on an open set
`Ω` of a finite-dimensional real inner product space `E` is the set of points of `Ω` near which `T`
is not a smooth function. The wave front set refines it by recording, over each such point, the
directions in which `T` fails to be smooth. This file proves that nothing is lost in this
refinement: the singular support is exactly the projection of the wave front set to `Ω`
(Hörmander I, Proposition 8.1.3).

One inclusion is `Distribution.isMicrolocallySmoothAt_of_apply_eq_integral`: there is no wave front
set over an open set on which `T` is smooth. For the other, suppose `T` is microlocally smooth at
`(x, ξ)` for every `ξ ≠ 0`. By compactness of the unit sphere, finitely many open cones on which
suitable localized Fourier transforms decay rapidly cover `E \ {0}`, and the localization of decay
(`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`) provides one cutoff `φ`, equal to one near
`x`, whose localized Fourier transform `η ↦ T (φ e_η)` decays rapidly in every direction. Then `φ T`
is a smooth compactly supported function: expanding test functions in Fourier series on a compact
set around the support of `φ` (`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`) writes `φ T`
as a trigonometric series whose coefficients `T (φ e_(-m))` decay rapidly, hence a smooth function
(`TauCeti.contDiff_tsum_mul_cexp_inner`).

## Main declarations

* `Distribution.singSupport T`: the singular support of `T`.
* `Distribution.exists_complexPairing_eq_integral_of_forall_decay`: if the localized Fourier
  transform of `T` with cutoff `φ` decays rapidly in every direction, then `φ T` is a test
  function `g`, that is, `T (φ ψ) = ∫ ψ g` for every complex test function `ψ`.
* `Distribution.exists_apply_eq_integral_of_forall_isMicrolocallySmoothAt`: a distribution
  microlocally smooth at `x` in every nonzero direction is a smooth function near `x`.
* `Distribution.fst_image_waveFrontSet`: the projection of the wave front set to `Ω` is the
  singular support.
* `Distribution.waveFrontSet_eq_empty_iff`: the wave front set is empty exactly when the singular
  support is.
* `Distribution.singSupport_add_subset`, `Distribution.singSupport_smul`: the singular support of
  a sum lies in the union of the singular supports, and nonzero multiples keep it.
* `Distribution.singSupport_delta`: the point mass at `x₀` has singular support `{x₀}`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Proposition 8.1.3 and Lemma 8.1.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff Real

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-! ### The singular support -/

/-- The **singular support** of a complex distribution `T` on `Ω`: the points `x ∈ Ω` with no open
neighbourhood `U` on which `T` is a smooth function, that is, on which `T φ = ∫ φ • f` for a
function `f` smooth on `U` and every real test function `φ` supported in `U`. -/
def singSupport (T : 𝓓'(Ω, ℂ)) : Set E :=
  {x | x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y}

@[simp]
theorem mem_singSupport_iff {T : 𝓓'(Ω, ℂ)} {x : E} :
    x ∈ T.singSupport ↔ x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- The singular support lies in `Ω`. -/
theorem singSupport_subset (T : 𝓓'(Ω, ℂ)) : T.singSupport ⊆ Ω :=
  fun _ hx ↦ hx.1

/-- The singular support is closed in `Ω`. -/
theorem isOpen_diff_singSupport (T : 𝓓'(Ω, ℂ)) : IsOpen ((Ω : Set E) \ T.singSupport) := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨hxΩ, hx⟩ ↦ ?_
  obtain ⟨U, hU, hxU, f, hf, hT⟩ : ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y := by
    by_contra h
    exact hx ⟨hxΩ, h⟩
  -- Every point of `U ∩ Ω` has the same neighbourhood `U` and the same smooth function `f`.
  filter_upwards [inter_mem (Ω.isOpen.mem_nhds hxΩ) (hU.mem_nhds hxU)] with y hy
  exact ⟨hy.1, fun h ↦ h.2 ⟨U, hU, hy.2, f, hf, hT⟩⟩

/-- A function smooth on `Ω` has empty singular support. -/
theorem singSupport_ofFun_eq_empty {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f MeasureTheory.volume ⊤).singSupport = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx.2 ⟨Ω, Ω.isOpen, hx.1, f, hf, fun _ _ ↦
    ofFun_apply (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)⟩

/-! ### Smoothness from rapid decay in every direction -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The character `y ↦ 𝐞 (-⟪y, w⟫)` of Mathlib's Fourier transform, written as an exponential. -/
private theorem fourierChar_neg_inner (y w : E) :
    (𝐞 (-⟪y, w⟫) : ℂ) = cexp (2 * π * I * ⟪y, -w⟫) := by
  rw [Real.fourierChar_apply, inner_neg_right]
  congr 1
  push_cast
  ring

/-- Pairing `T` with `φ` times the Fourier expansion of a function `h` supported in a compact set
`K ⊆ Ω` that meets none of its nonzero lattice translates. If the cutoff `χ` equals one on the
supports of `h` and of `φ`, then `T (φ h) = ∑ m, (covolume L)⁻¹ 𝓕 h (m) T (φ e_(-m))`. -/
private theorem hasSum_complexPairing_of_eq_mul (T : 𝓓'(Ω, ℂ)) {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hK : ∀ x ∈ K, ∀ ℓ : L, x + ℓ ∈ K → ℓ = 0) {φ ψ : 𝓓(Ω, ℂ)} {h χ : 𝓓_{K}(E, ℂ)}
    (hχh : EqOn χ 1 (support h)) (hφχ : ∀ x, φ x = φ x * χ x) (hψ : ∀ x, ψ x = φ x * h x) :
    HasSum (fun m : ZLattice.dual L ↦
        (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (h : E → ℂ) m * T.localFourier φ (-m))
      (T.complexPairing ψ) := by
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L
    (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff ∘L
      ofSupportedInCLM ℂ hKΩ)
  have hΛ (f : 𝓓_{K}(E, ℂ)) : Λ f = T.complexPairing
      (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff
        (ofSupportedIn hKΩ f)) := by
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
  have h1 : Λ h = T.complexPairing ψ := by
    rw [hΛ]
    congr 1
    ext x
    simp [TestFunction.bilinLeftCLM_apply, hψ, mul_comm]
  have h2 (m : ZLattice.dual L) (a : ℂ) :
      Λ (a • χ.modulate m) = a * T.localFourier φ (-m) := by
    rw [map_smul, smul_eq_mul, hΛ, localFourier_eq_complexPairing_mul_modulate T hKΩ hφχ, neg_neg]
  have hmap := (ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L h χ hK hχh).map Λ
    Λ.continuous
  rw [h1] at hmap
  convert hmap using 1
  ext m
  exact (h2 m _).symm

/-- Summing Fourier transforms of an integrable function against summable coefficients:
`∑ b i 𝓕 h (w i) = ∫ h y (∑ b i 𝐞 (-⟪y, w i⟫)) dy`. -/
private theorem tsum_mul_fourier_eq_integral {ι : Type*} [Countable ι] {h : E → ℂ}
    (hh : MeasureTheory.Integrable h) {b : ι → ℂ} (hb : Summable fun i ↦ ‖b i‖) (w : ι → E) :
    ∑' i, b i * 𝓕 h (w i) = ∫ y, h y * ∑' i, b i * 𝐞 (-⟪y, w i⟫) := by
  have hint (i : ι) : MeasureTheory.Integrable fun y ↦ b i * (𝐞 (-⟪y, w i⟫) • h y) :=
    ((Real.fourierIntegral_convergent_iff (w i)).2 hh).const_mul (b i)
  have hnorm (i : ι) : ∫ y, ‖b i * (𝐞 (-⟪y, w i⟫) • h y)‖ = ‖b i‖ * ∫ y, ‖h y‖ := by
    simp only [norm_mul, Circle.norm_smul, MeasureTheory.integral_const_mul]
  calc ∑' i, b i * 𝓕 h (w i) = ∑' i, ∫ y, b i * (𝐞 (-⟪y, w i⟫) • h y) := by
        simp_rw [Real.fourier_eq, MeasureTheory.integral_const_mul]
    _ = ∫ y, ∑' i, b i * (𝐞 (-⟪y, w i⟫) • h y) :=
        MeasureTheory.integral_tsum_of_summable_integral_norm hint
          (by simpa only [hnorm] using hb.mul_right (∫ y, ‖h y‖))
    _ = ∫ y, h y * ∑' i, b i * 𝐞 (-⟪y, w i⟫) := by
        congr 1
        ext y
        rw [← tsum_mul_left]
        congr 1
        ext i
        rw [Circle.smul_def, smul_eq_mul]
        ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- If the localized Fourier transform `η ↦ T (φ e_η)` decays rapidly in every direction, then its
values `c T (φ e_(-m))` along a discrete subgroup are summable against every power of
`1 + ‖m‖`. -/
private theorem summable_one_add_norm_pow_mul_norm_mul_localFourier {T : 𝓓'(Ω, ℂ)}
    {φ : 𝓓(Ω, ℂ)} (h : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (c : ℂ) (k : ℕ) :
    Summable fun m : Λ ↦ (1 + ‖(m : E)‖) ^ k * ‖c * T.localFourier φ (-m)‖ := by
  obtain ⟨C, hC⟩ := h (k + Module.finrank ℤ Λ + 1)
  refine ZLattice.summable_one_add_norm_pow_mul_norm_of_le Λ (C := ‖c‖ * C) fun m ↦ ?_
  have hm := hC (-m)
  rw [norm_neg] at hm
  calc (1 + ‖(m : E)‖) ^ (k + Module.finrank ℤ Λ + 1) * ‖c * T.localFourier φ (-m)‖
      = ‖c‖ * ((1 + ‖(m : E)‖) ^ (k + Module.finrank ℤ Λ + 1) * ‖T.localFourier φ (-m)‖) := by
        rw [norm_mul]
        ring
    _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left hm (norm_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A trigonometric series `y ↦ ∑' m, b m 𝐞 (-⟪y, m⟫)` over a subgroup `Λ`, whose coefficients
are summable against every power of `1 + ‖m‖`, is smooth. -/
private theorem contDiff_tsum_mul_fourierChar {Λ : Submodule ℤ E} {b : Λ → ℂ}
    (hb : ∀ k : ℕ, Summable fun m : Λ ↦ (1 + ‖(m : E)‖) ^ k * ‖b m‖) :
    ContDiff ℝ ∞ fun y ↦ ∑' m : Λ, b m * 𝐞 (-⟪y, (m : E)⟫) := by
  simp_rw [fourierChar_neg_inner]
  refine TauCeti.contDiff_tsum_mul_cexp_inner fun k ↦ (hb k).of_nonneg_of_le
    (fun m ↦ by positivity) fun m ↦ ?_
  rw [norm_neg]
  gcongr
  linarith

/-- **A cut-off distribution with rapidly decreasing Fourier transform is smooth.** If the localized
Fourier transform `η ↦ T (φ e_η)` of `T` with cutoff `φ` decays rapidly in every direction, then
`φ T` is a test function: there is `g ∈ 𝓓(Ω, ℂ)` with `T (φ ψ) = ∫ ψ g` for every complex test
function `ψ`. -/
theorem exists_complexPairing_eq_integral_of_forall_decay {T : 𝓓'(Ω, ℂ)} {φ : 𝓓(Ω, ℂ)}
    (h : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C) :
    ∃ g : 𝓓(Ω, ℂ), ∀ ψ ψ' : 𝓓(Ω, ℂ), (∀ y, ψ' y = φ y * ψ y) →
      T.complexPairing ψ' = ∫ y, ψ y * g y := by
  -- Nested compact sets `tsupport φ ⊆ K₁ ⊆ K₂ ⊆ Ω`, a cutoff `χ₁` equal to one near
  -- `tsupport φ` and supported in `K₁`, and a cutoff `χ₂` equal to one near `K₁`.
  obtain ⟨K₁, hK₁, hφK₁, hK₁Ω⟩ :=
    exists_compact_between φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  obtain ⟨K₂, hK₂, hK₁K₂, hK₂Ω⟩ := exists_compact_between hK₁ Ω.isOpen hK₁Ω
  obtain ⟨χ₁, hχ₁, -, hχ₁1, hχ₁c, hχ₁s⟩ :=
    φ.hasCompactSupport.exists_contDiff_cutoff isOpen_interior hφK₁
  obtain ⟨χ₂, hχ₂, -, hχ₂1, -, hχ₂s⟩ := hK₁.exists_contDiff_cutoff isOpen_interior hK₁K₂
  let K : Compacts E := ⟨K₂, hK₂⟩
  have hKΩ : (K : Set E) ⊆ Ω := hK₂Ω
  have hχ₁φ {x : E} (hx : φ x ≠ 0) : χ₁ x = 1 := interior_subset (hχ₁1 (subset_tsupport _ hx))
  have hχ₂K₁ {x : E} (hx : x ∈ K₁) : χ₂ x = 1 := interior_subset (hχ₂1 hx)
  have hχ₁K₁ : tsupport χ₁ ⊆ K₁ := hχ₁s.trans interior_subset
  have hχK : support (fun x ↦ (χ₂ x : ℂ)) ⊆ K₂ := fun x hx ↦
    interior_subset (hχ₂s (subset_tsupport _ (by simpa using hx)))
  let χ : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset (ofRealCLM.contDiff.comp hχ₂) hχK
  -- A lattice none of whose nonzero translates of `K₂` meet `K₂`, and the rapidly decreasing
  -- coefficients `b m = (covolume L)⁻¹ T (φ e_(-m))` of `φ T` on the dual lattice.
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
  set b : ZLattice.dual L → ℂ := fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * T.localFourier φ (-m)
    with hb_def
  have hb := summable_one_add_norm_pow_mul_norm_mul_localFourier h (ZLattice.dual L)
    (ZLattice.covolume L : ℂ)⁻¹
  -- The trigonometric series `S` with these coefficients is smooth, and `φ T = χ₁ S`.
  let S : E → ℂ := fun y ↦ ∑' m : ZLattice.dual L, b m * 𝐞 (-⟪y, (m : E)⟫)
  have hS : ContDiff ℝ ∞ S := contDiff_tsum_mul_fourierChar hb
  let g : 𝓓(Ω, ℂ) := ⟨fun y ↦ (χ₁ y : ℂ) * S y, (ofRealCLM.contDiff.comp hχ₁).mul hS,
    (hχ₁c.comp_left ofReal_zero).mul_right,
    tsupport_mul_subset_left.trans ((tsupport_comp_subset ofReal_zero _).trans
      (hχ₁K₁.trans hK₁Ω))⟩
  have hg (y : E) : g y = χ₁ y * ∑' m : ZLattice.dual L, b m * 𝐞 (-⟪y, (m : E)⟫) := rfl
  refine ⟨g, fun ψ ψ' hψ' ↦ ?_⟩
  have hsupp : support (fun x ↦ (χ₁ x : ℂ) * ψ x) ⊆ K₂ := fun x hx ↦
    interior_subset (hK₁K₂ (hχ₁K₁ (subset_tsupport _ (by simpa using left_ne_zero_of_mul hx))))
  let f : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset ((ofRealCLM.contDiff.comp hχ₁).mul ψ.contDiff) hsupp
  have hf (x : E) : f x = χ₁ x * ψ x := by
    simp [f, ContDiffMapSupportedIn.coe_of_support_subset]
  -- `χ = 1` on the supports of `f` and `φ`, which lie in `K₁`, and `φ f = φ ψ = ψ'`.
  have hχx {x : E} (hx : x ∈ K₁) : χ x = 1 := by
    rw [show χ x = χ₂ x from ContDiffMapSupportedIn.coe_of_support_subset _ _ x, hχ₂K₁ hx,
      ofReal_one]
  have hχf : EqOn χ 1 (support f) := fun x hx ↦ by
    have hx' : χ₁ x ≠ 0 := by
      rw [mem_support, hf] at hx
      exact_mod_cast left_ne_zero_of_mul hx
    exact hχx (hχ₁K₁ (subset_tsupport _ hx'))
  have hφχ (x : E) : φ x = φ x * χ x := by
    by_cases hx : φ x = 0
    · simp [hx]
    · rw [hχx (interior_subset (hφK₁ (subset_tsupport _ hx))), mul_one]
  have hψf (x : E) : ψ' x = φ x * f x := by
    by_cases hx : φ x = 0
    · simp [hψ', hx]
    · simp [hψ', hf, hχ₁φ hx]
  have hsum := hasSum_complexPairing_of_eq_mul T hKΩ L
    (fun x hx ℓ h ↦ Subtype.ext (hL x hx ℓ ℓ.2 h)) hχf hφχ hψf
  rw [← hsum.tsum_eq]
  have hterm (m : ZLattice.dual L) : (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : E → ℂ) m *
      T.localFourier φ (-m) = b m * 𝓕 (f : E → ℂ) m := by
    rw [hb_def]
    ring
  simp_rw [hterm]
  rw [tsum_mul_fourier_eq_integral (ι := ZLattice.dual L)
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    (by simpa only [pow_zero, one_mul] using hb 0) fun m ↦ (m : E)]
  congr 1
  ext y
  rw [hf, hg]
  ring

/-- **Smoothness from microlocal smoothness in every direction.** If `T` is microlocally smooth at
`(x, ξ)` for every `ξ ≠ 0`, then `T` coincides near `x` with a smooth function: there are an open
neighbourhood `U` of `x` and a smooth `f` with `T φ = ∫ φ • f` for every real test function `φ`
supported in `U`. -/
theorem exists_apply_eq_integral_of_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) (h : ∀ ξ, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ, ContDiff ℝ ∞ f ∧
      ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y := by
  -- Finitely many of the cones given by the localization of decay cover the unit sphere.
  choose! U hU Γ hΓ hξΓ hcone hdecay using fun ξ (hξ : ξ ∈ sphere (0 : E) 1) ↦
    (h ξ (ne_zero_of_mem_sphere one_ne_zero ⟨ξ, hξ⟩)).exists_nhds_cone
  obtain ⟨t, hts, hcover⟩ := (isCompact_sphere (0 : E) 1).elim_nhds_subcover Γ
    fun ξ hξ ↦ (hΓ ξ hξ).mem_nhds (hξΓ ξ hξ)
  have hV : (⋂ ξ ∈ t, U ξ) ∩ Ω ∈ 𝓝 x :=
    inter_mem ((biInter_finset_mem t).2 fun ξ hξ ↦ hU ξ (hts ξ hξ)) (Ω.isOpen.mem_nhds hx)
  -- A cutoff `φ` equal to one near `x` and supported in all the neighbourhoods `U ξ`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχs⟩ := (isCompact_singleton (x := x)).exists_contDiff_cutoff
    isOpen_interior (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hV))
  have hχV : tsupport χ ⊆ (⋂ ξ ∈ t, U ξ) ∩ Ω := hχs.trans interior_subset
  let φ : 𝓓(Ω, ℂ) := ⟨fun y ↦ (χ y : ℂ), ofRealCLM.contDiff.comp hχ,
    hχc.comp_left ofReal_zero,
    (tsupport_comp_subset ofReal_zero _).trans (hχV.trans inter_subset_right)⟩
  have hφU (ξ : E) (hξ : ξ ∈ t) : tsupport φ ⊆ U ξ :=
    (tsupport_comp_subset ofReal_zero _).trans
      (hχV.trans (inter_subset_left.trans (biInter_subset_of_mem hξ)))
  -- The localized Fourier transform of `T` with cutoff `φ` decays rapidly in every direction.
  have hdec (N : ℕ) : ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C := by
    choose! C hC using fun ξ (hξ : ξ ∈ t) ↦ hdecay ξ (hts ξ hξ) φ (hφU ξ hξ) N
    refine ⟨‖T.localFourier φ 0‖ + ∑ ξ ∈ t, |C ξ|, fun η ↦ ?_⟩
    have hsum : 0 ≤ ∑ ξ ∈ t, |C ξ| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    rcases eq_or_ne η 0 with rfl | hη
    · simpa using hsum
    -- The direction `η / ‖η‖` lies in one of the cones, and hence so does `η`.
    obtain ⟨ξ, hξ, hηξ⟩ := mem_iUnion₂.1 (hcover (show ‖η‖⁻¹ • η ∈ sphere (0 : E) 1 by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hη)]))
    have hηΓ : η ∈ Γ ξ := by
      simpa [smul_smul, hη] using
        hcone ξ (hts ξ hξ) ‖η‖ (norm_pos_iff.2 hη) (‖η‖⁻¹ • η) hηξ
    calc (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ |C ξ| := (hC ξ hξ η hηΓ).trans (le_abs_self _)
      _ ≤ ∑ ξ ∈ t, |C ξ| := Finset.single_le_sum (f := fun ξ ↦ |C ξ|) (fun _ _ ↦ abs_nonneg _) hξ
      _ ≤ _ := le_add_of_nonneg_left (norm_nonneg _)
  -- Hence `φ T` is a smooth function `g`, and `T` coincides with `g` where `φ = 1`.
  obtain ⟨g, hg⟩ := exists_complexPairing_eq_integral_of_forall_decay hdec
  refine ⟨interior (χ ⁻¹' {1}), isOpen_interior, hχ1 rfl, g, g.contDiff, fun ρ hρ ↦ ?_⟩
  set ρ' := postcompCLM (𝕜 := ℝ) ofRealCLM ρ
  have hρ' (y : E) : ρ' y = φ y * ρ' y := by
    by_cases hy : ρ y = 0
    · simp [ρ', hy]
    · have hφy : φ y = 1 := by
        change (χ y : ℂ) = 1
        rw [interior_subset (hρ (subset_tsupport _ hy)), ofReal_one]
      rw [hφy, one_mul]
  rw [← complexPairing_postcompCLM_ofRealCLM, hg ρ' ρ' hρ']
  simp [ρ', Complex.real_smul]

/-! ### The projection of the wave front set -/

/-- **The projection of the wave front set is the singular support** (Hörmander I,
Proposition 8.1.3): a point of `Ω` lies under the wave front set of `T` exactly when `T` is not a
smooth function near it. -/
theorem fst_image_waveFrontSet (T : 𝓓'(Ω, ℂ)) : Prod.fst '' T.waveFrontSet = T.singSupport := by
  ext x
  refine ⟨?_, fun ⟨hxΩ, hx⟩ ↦ ?_⟩
  · rintro ⟨⟨x, ξ⟩, hp, rfl⟩
    obtain ⟨hxΩ, -, hT⟩ := mem_waveFrontSet_iff.1 hp
    exact ⟨hxΩ, fun ⟨U, hU, hxU, f, hf, hTf⟩ ↦
      hT (isMicrolocallySmoothAt_of_apply_eq_integral hU hf hTf hxU hxΩ ξ)⟩
  · by_contra hW
    refine hx ?_
    obtain ⟨U, hU, hxU, f, hf, hT⟩ := exists_apply_eq_integral_of_forall_isMicrolocallySmoothAt hxΩ
      fun ξ hξ ↦ by_contra fun hT ↦ hW ⟨(x, ξ), mem_waveFrontSet_iff.2 ⟨hxΩ, hξ, hT⟩, rfl⟩
    exact ⟨U, hU, hxU, f, hf.contDiffOn, hT⟩

/-- A point of `Ω` lies in the singular support of `T` exactly when `T` fails to be microlocally
smooth there in some nonzero direction. -/
theorem mem_singSupport_iff_exists_mem_waveFrontSet {T : 𝓓'(Ω, ℂ)} {x : E} :
    x ∈ T.singSupport ↔ ∃ ξ, (x, ξ) ∈ T.waveFrontSet := by
  simp [← fst_image_waveFrontSet]

/-- The wave front set is empty exactly when the singular support is. -/
theorem waveFrontSet_eq_empty_iff {T : 𝓓'(Ω, ℂ)} :
    T.waveFrontSet = ∅ ↔ T.singSupport = ∅ := by
  rw [← fst_image_waveFrontSet, image_eq_empty]

/-- The singular support lies in the support. -/
theorem singSupport_subset_dsupport (T : 𝓓'(Ω, ℂ)) : T.singSupport ⊆ dsupport T := by
  rw [← fst_image_waveFrontSet]
  exact (image_mono (waveFrontSet_subset_dsupport T)).trans (fst_image_prod_subset _ _)

/-- The singular support of a sum lies in the union of the singular supports. -/
theorem singSupport_add_subset (S T : 𝓓'(Ω, ℂ)) :
    (S + T).singSupport ⊆ S.singSupport ∪ T.singSupport := by
  simp only [← fst_image_waveFrontSet, ← image_union]
  exact image_mono (waveFrontSet_add_subset S T)

/-- A nonzero scalar multiple of `T` has the same singular support as `T`. -/
@[simp]
theorem singSupport_smul {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, ℂ)) :
    (c • T).singSupport = T.singSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet, waveFrontSet_smul hc]

/-- The negative of `T` has the same singular support as `T`. -/
@[simp]
theorem singSupport_neg (T : 𝓓'(Ω, ℂ)) : (-T).singSupport = T.singSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet, waveFrontSet_neg]

/-- The point mass at `x₀ ∈ Ω` has singular support `{x₀}`, when `E` is nontrivial. -/
theorem singSupport_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).singSupport = {x₀} := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  rw [← fst_image_waveFrontSet, waveFrontSet_delta hx₀, fst_image_prod _ ⟨v, hv⟩]

end Distribution
