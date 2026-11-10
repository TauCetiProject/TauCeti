/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SingularSupport
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# The wave front set lies over the singular support

The wave front set of a complex distribution `T` on an open set `Ω` refines its singular support:
the points `x` over which `T` has some wave front covector `(x, ξ)` are exactly the points at which
`T` is not a smooth function (Hörmander I, Proposition 8.1.3),

`Prod.fst '' waveFrontSet T = singularSupport T`.

Where `T` is smooth, its localized Fourier transforms decay rapidly in every direction, so there is
no wave front set over the smooth part (`Distribution.IsSmoothAt.isMicrolocallySmoothAt`).
Conversely, suppose `T` is microlocally smooth at `(x, ξ)` for every `ξ ≠ 0`. Each such `ξ` has a
neighbourhood `U_ξ` of `x` and an open cone `Γ_ξ` such that every cutoff supported in `U_ξ` has
localized Fourier transform rapidly decreasing on `Γ_ξ`. Finitely many of these cones cover the
unit sphere, so a single cutoff `ψ`, equal to one near `x` and supported in the intersection of the
corresponding `U_ξ`, has localized Fourier transform rapidly decreasing in all directions. Then
`T` is smooth near `x` (`Distribution.isSmoothAt_of_forall_decay`): on the support of `ψ`,
expand a test function in the Fourier series of a lattice `L` whose nonzero translates move the
support of `ψ` off itself (`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`). Pairing with
`T` and resumming, `T φ = ∫ φ g` for every test function `φ` supported where `ψ = 1`, where

`g y = (covolume L)⁻¹ ∑ m : L^∨, T (ψ e_(-m)) exp (-2πi ⟪y, m⟫)`

is a lattice Fourier series with rapidly decreasing coefficients, hence a smooth function.

## Main results

* `Distribution.exists_hasSum_apply_localFourier`: on the set where a cutoff `ψ` equals one, `T`
  is the sum of a lattice Fourier series whose coefficients are values of the localized Fourier
  transform with cutoff `ψ`.
* `Distribution.isSmoothAt_of_forall_decay`: a distribution is smooth near every point where a
  cutoff whose localized Fourier transform decays rapidly is equal to one.
* `Distribution.isSmoothAt_iff_forall_isMicrolocallySmoothAt`: a distribution is smooth at
  `x ∈ Ω` if and only if it is microlocally smooth at `(x, ξ)` for every `ξ ≠ 0`.
* `Distribution.fst_image_waveFrontSet`: the projection of the wave front set is the singular
  support.
* `Distribution.waveFrontSet_eq_empty_iff`: the wave front set is empty exactly when the singular
  support is.
* `Distribution.singularSupport_delta`: on a nontrivial space `E`, the singular support of the
  point mass at `x₀ ∈ Ω` is `{x₀}`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Proposition 8.1.3.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff Real

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- **The Fourier series of a distribution where a cutoff equals one.** For every cutoff `ψ`
there is a full lattice `L` such that, for every real test function `φ` supported in the set where
`ψ = 1`,

`T φ = ∑ m : L^∨, (covolume L)⁻¹ 𝓕 φ (m) T (ψ e_(-m))`,

where `T (ψ e_(-m))` is the localized Fourier transform of `T` with cutoff `ψ` at `-m`. -/
theorem exists_hasSum_apply_localFourier (T : 𝓓'(Ω, ℂ)) (ψ : 𝓓(Ω, ℂ)) :
    ∃ (L : Submodule ℤ E) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L),
      ∀ φ : 𝓓(Ω, ℝ), (∀ y, φ y ≠ 0 → ψ y = 1) →
        HasSum (fun m : ZLattice.dual L ↦
          (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (fun y ↦ (φ y : ℂ)) m * T.localFourier ψ (-m)) (T φ) := by
  -- The cutoff `ψ`, read as a smooth function supported in `K = tsupport ψ`, and a lattice `L`
  -- none of whose nonzero translates of `K` meet `K`.
  let K : Compacts E := ⟨tsupport ψ, ψ.hasCompactSupport⟩
  have hKΩ : (K : Set E) ⊆ Ω := ψ.tsupport_subset
  let χ : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport _)
  have hχψ (y : E) : χ y = ψ y := ContDiffMapSupportedIn.coe_of_support_subset _ _ y
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded K.isCompact.isBounded
  refine ⟨L, inferInstance, inferInstance, fun φ hφψ ↦ ?_⟩
  -- The test function `φ`, read as a complex smooth function supported in `K`, has a Fourier
  -- expansion in the modulations of `χ`.
  have hφK : support (fun y ↦ (φ y : ℂ)) ⊆ K := fun y hy ↦
    subset_tsupport _ (by simp [hφψ y (by simpa using hy)])
  let f : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset (ofRealCLM.contDiff.comp φ.contDiff) hφK
  have hfφ (y : E) : f y = φ y := ContDiffMapSupportedIn.coe_of_support_subset _ _ y
  have hχ : EqOn χ 1 (support f) := fun y hy ↦ by
    simpa [hχψ] using hφψ y (by simpa [hfφ] using hy)
  have hexp := ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L f χ
    (fun y hy ℓ h ↦ Subtype.ext (hL y hy ℓ ℓ.2 h)) hχ
  -- Pair the expansion with `T`: the modulations of `χ` pair to the localized Fourier transform.
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L ofSupportedInCLM ℂ hKΩ
  have h1 : Λ f = T φ := by
    have hf : ofSupportedIn hKΩ f = postcompCLM (𝕜 := ℝ) ofRealCLM φ := by
      ext y
      simp [hfφ]
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM, hf,
      complexPairing_postcompCLM_ofRealCLM]
  have h2 (m : ZLattice.dual L) (a : ℂ) :
      Λ (a • χ.modulate m) = a * T.localFourier ψ (-m) := by
    simp only [Λ, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM,
      localFourier_eq_complexPairing_modulate T hKΩ (f := χ) hχψ, neg_neg]
  have hfφ' : (f : E → ℂ) = fun y ↦ (φ y : ℂ) := funext hfφ
  simpa only [h1, h2, hfφ', comp_def] using hexp.map Λ Λ.continuous

/-- **Rapid decay gives smoothness.** If a cutoff `ψ` equal to one near `x` has localized Fourier
transform `η ↦ T (ψ e_η)` decaying faster than every power of `‖η‖`, then `T` is smooth at `x`. -/
theorem isSmoothAt_of_forall_decay {T : 𝓓'(Ω, ℂ)} {ψ : 𝓓(Ω, ℂ)} {x : E}
    (hψ : ∀ᶠ y in 𝓝 x, ψ y = 1)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C) :
    T.IsSmoothAt x := by
  obtain ⟨L, _, _, hT⟩ := exists_hasSum_apply_localFourier T ψ
  -- Near `x`, `T` is the trigonometric series `g y = ∑ m, c m exp (-2πi ⟪y, m⟫)`, whose
  -- coefficients `c m` decay rapidly by hypothesis, so that `g` is smooth.
  let c : ZLattice.dual L → ℂ := fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * T.localFourier ψ (-m)
  have hc (k : ℕ) : Summable fun m : ZLattice.dual L ↦ (1 + ‖-(m : E)‖) ^ k * ‖c m‖ := by
    have h := ZLattice.summable_one_add_norm_pow_mul_norm_of_decay (ZLattice.dual L)
      (f := fun η ↦ T.localFourier ψ (-η)) (fun N ↦ ?_) k
    · refine (h.mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖).congr fun m ↦ ?_
      simp only [c, norm_neg, norm_mul]
      ring
    · obtain ⟨C, hC⟩ := hdecay N
      exact ⟨C, fun η ↦ by simpa using hC (-η)⟩
  let e : ZLattice.dual L → E → ℂ := fun m y ↦ c m * cexp (2 * π * I * ⟪y, -(m : E)⟫)
  have he (m : ZLattice.dual L) : Continuous (e m) := by fun_prop
  have hnorm_exp (m : ZLattice.dual L) (y : E) : ‖cexp (2 * π * I * ⟪y, -(m : E)⟫)‖ = 1 := by
    rw [norm_exp]
    simp
  refine isSmoothAt_iff.2 ⟨interior {y | ψ y = 1}, isOpen_interior,
    mem_interior_iff_mem_nhds.2 hψ, _, (TauCeti.contDiff_tsum_mul_cexp hc).contDiffOn,
    fun φ hφ ↦ ?_⟩
  have hφψ (y : E) (hy : φ y ≠ 0) : ψ y = 1 := interior_subset (hφ (subset_tsupport _ hy))
  -- Each term of the Fourier series of `T φ` is the integral of `φ` against a term of `g`; the
  -- rapid decay of the coefficients lets the sum and the integral be exchanged.
  have hterm (m : ZLattice.dual L) :
      (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (fun y ↦ (φ y : ℂ)) m * T.localFourier ψ (-m) =
        ∫ y, φ y • e m y := by
    rw [Real.fourier_eq', mul_right_comm, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [e, c, smul_eq_mul, real_smul, inner_neg_right]
    push_cast
    ring_nf
  have hint (m : ZLattice.dual L) : Integrable fun y ↦ φ y • e m y :=
    (φ.continuous.smul (he m)).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_right
  have hnorm (m : ZLattice.dual L) : ∫ y, ‖φ y • e m y‖ = (∫ y, ‖φ y‖) * ‖c m‖ := by
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [e, norm_smul, norm_mul, hnorm_exp, mul_one]
  have hsum : Summable fun m : ZLattice.dual L ↦ ∫ y, ‖φ y • e m y‖ := by
    simp_rw [hnorm]
    exact ((hc 0).mul_left (∫ y, ‖φ y‖)).congr fun m ↦ by simp
  calc T φ = ∑' m, ∫ y, φ y • e m y := by
        rw [← (hT φ hφψ).tsum_eq]
        exact tsum_congr hterm
    _ = ∫ y, ∑' m, φ y • e m y := integral_tsum_of_summable_integral_norm hint hsum
    _ = ∫ y, φ y • ∑' m, e m y := integral_congr_ae (Eventually.of_forall fun y ↦
      tsum_const_smul'' (φ y))

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `T` is microlocally smooth at `(x, ξ)` for every `ξ ≠ 0`, then some cutoff equal to one near
`x` has localized Fourier transform decaying faster than every power of `‖η‖` in all
directions. -/
theorem exists_forall_decay_of_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) (h : ∀ ξ, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ) :
    ∃ ψ : 𝓓(Ω, ℂ), (∀ᶠ y in 𝓝 x, ψ y = 1) ∧
      ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  -- Each unit covector has a neighbourhood of `x` and a cone on which all cutoffs decay rapidly.
  have key (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :=
    (h ξ (ne_zero_of_mem_unit_sphere ⟨ξ, hξ⟩)).exists_nhds_cone
  choose! U hU Γ hΓ hξΓ hcone hdecay using key
  -- Finitely many of the cones cover the unit sphere.
  obtain ⟨t, htS, ht, hcover⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover_image
    (b := sphere (0 : E) 1) (c := Γ) hΓ fun ξ hξ ↦ mem_biUnion hξ (hξΓ ξ hξ)
  have hU₀ : (⋂ ξ ∈ t, U ξ) ∩ Ω ∈ 𝓝 x :=
    inter_mem ((biInter_mem ht).2 fun ξ hξ ↦ hU ξ (htS hξ)) (Ω.isOpen.mem_nhds hx)
  -- A cutoff `ψ` equal to one near `x` and supported in the intersection of the neighbourhoods.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχs⟩ := (isCompact_singleton (x := x)).exists_contDiff_cutoff
    isOpen_interior (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU₀))
  have hsupp : tsupport (fun y ↦ χ y • (1 : ℂ)) ⊆ (⋂ ξ ∈ t, U ξ) ∩ Ω :=
    (tsupport_smul_subset_left _ _).trans (hχs.trans interior_subset)
  let ψ : 𝓓(Ω, ℂ) := ⟨fun y ↦ χ y • (1 : ℂ), hχ.smul contDiff_const, hχc.smul_right,
    hsupp.trans inter_subset_right⟩
  have hψU (ξ : E) (hξ : ξ ∈ t) : tsupport ψ ⊆ U ξ :=
    hsupp.trans (inter_subset_left.trans (biInter_subset_of_mem hξ))
  refine ⟨ψ, ?_, fun N ↦ ?_⟩
  · filter_upwards [mem_interior_iff_mem_nhds.1 (hχ1 rfl)] with y hy
    simp [ψ, show χ y = 1 from hy]
  · choose! C hC using fun ξ (hξ : ξ ∈ t) ↦ hdecay ξ (htS hξ) ψ (hψU ξ hξ) N
    refine ⟨‖T.localFourier ψ 0‖ + ∑ ξ ∈ ht.toFinset, |C ξ|, fun η ↦ ?_⟩
    have hsum_nonneg : 0 ≤ ∑ ξ ∈ ht.toFinset, |C ξ| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    rcases eq_or_ne η 0 with rfl | hη
    · simpa using hsum_nonneg
    -- A nonzero `η` lies, by conicity, in the cone of a covector of `t`.
    have hη' : ‖η‖⁻¹ • η ∈ sphere (0 : E) 1 := by
      simp [norm_smul, norm_ne_zero_iff.2 hη]
    obtain ⟨ξ, hξ, hηξ⟩ := mem_iUnion₂.1 (hcover hη')
    have hηΓ : η ∈ Γ ξ := by
      simpa [smul_smul, norm_ne_zero_iff.2 hη] using
        hcone ξ (htS hξ) ‖η‖ (norm_pos_iff.2 hη) _ hηξ
    calc (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ |C ξ| := (hC ξ hξ η hηΓ).trans (le_abs_self _)
      _ ≤ ∑ ξ ∈ ht.toFinset, |C ξ| :=
        Finset.single_le_sum (f := fun ξ ↦ |C ξ|) (fun _ _ ↦ abs_nonneg _) (ht.mem_toFinset.2 hξ)
      _ ≤ _ := le_add_of_nonneg_left (norm_nonneg _)

/-- A complex distribution is smooth at `x ∈ Ω` if and only if it is microlocally smooth at
`(x, ξ)` for every nonzero covector `ξ`. -/
theorem isSmoothAt_iff_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω) :
    T.IsSmoothAt x ↔ ∀ ξ, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun hs ξ _ ↦ hs.isMicrolocallySmoothAt hx ξ, fun h ↦ ?_⟩
  obtain ⟨ψ, hψ, hdecay⟩ := exists_forall_decay_of_forall_isMicrolocallySmoothAt hx h
  exact isSmoothAt_of_forall_decay hψ hdecay

/-- **The wave front set lies over the singular support** (Hörmander I, Proposition 8.1.3): the
projection of the wave front set of a complex distribution to the base is its singular
support. -/
theorem fst_image_waveFrontSet (T : 𝓓'(Ω, ℂ)) : Prod.fst '' T.waveFrontSet = T.singularSupport := by
  ext x
  simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right, mem_waveFrontSet_iff,
    mem_singularSupport_iff]
  constructor
  · rintro ⟨ξ, hx, hξ, hT⟩
    exact ⟨hx, fun hs ↦ hT (hs.isMicrolocallySmoothAt hx ξ)⟩
  · rintro ⟨hx, hs⟩
    by_contra! hT
    exact hs ((isSmoothAt_iff_forall_isMicrolocallySmoothAt hx).2 fun ξ hξ ↦ hT ξ hx hξ)

/-- The wave front set of a complex distribution is empty exactly when its singular support is. -/
theorem waveFrontSet_eq_empty_iff {T : 𝓓'(Ω, ℂ)} :
    T.waveFrontSet = ∅ ↔ T.singularSupport = ∅ := by
  rw [← fst_image_waveFrontSet, image_eq_empty]

/-- On a nontrivial space `E`, the singular support of the point mass at `x₀ ∈ Ω` is `{x₀}`. -/
theorem singularSupport_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).singularSupport = {x₀} := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  rw [← fst_image_waveFrontSet, waveFrontSet_delta hx₀, fst_image_prod _ ⟨ξ, hξ⟩]

end Distribution
