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
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The wave front set projects onto the singular support

The wave front set of a complex distribution `T` on an open set `Ω` refines its singular support:
a point `x ∈ Ω` lies in the singular support exactly when `T` fails to be microlocally smooth at
`(x, ξ)` for some direction `ξ ≠ 0`. Equivalently, the projection of the wave front set to `Ω` is
the singular support (`Distribution.fst_image_waveFrontSet`).

One inclusion holds because a distribution that is a smooth function near `x` has rapidly
decreasing localized Fourier transforms at `x`. For the other, suppose `T` is microlocally smooth
at `(x, ξ)` for every `ξ ≠ 0`. Each such direction has an open cone of rapid decay that works for
all cutoffs supported near `x`, and finitely many of these cones cover the unit sphere. So a single
cutoff `φ` equal to one near `x` has localized Fourier transform `η ↦ T (φ e_η)` rapidly decreasing
in every direction (`Distribution.exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt`).
Then `φ T` is a smooth function (`Distribution.exists_contDiff_complexPairing_eq_integral`): on a
compact set around the support of `φ`, a test function `ψ` is the sum of its Fourier series along
a lattice, and pairing it with `φ T` gives the Fourier series
`∑ m, (covolume L)⁻¹ T (φ e_{-m}) exp (-2πi ⟪y, m⟫)`, with rapidly decreasing coefficients,
integrated against `ψ`. This is Fourier inversion for the compactly supported distribution `φ T`,
in the discrete form that only needs the convergence of Fourier series in the space of test
functions.

## Main results

* `Distribution.exists_contDiff_complexPairing_eq_integral`: if the localized Fourier transform of
  `T` with cutoff `φ` decays rapidly in every direction, then `φ T` is a smooth function.
* `Distribution.exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt`: if `T` is microlocally
  smooth at `(x, ξ)` for every `ξ ≠ 0`, then every cutoff supported near `x` has rapidly decreasing
  localized Fourier transform.
* `Distribution.notMem_singularSupport_iff_forall_isMicrolocallySmoothAt`: a point `x ∈ Ω` lies
  outside the singular support exactly when `T` is microlocally smooth at `(x, ξ)` for every
  `ξ ≠ 0`.
* `Distribution.fst_image_waveFrontSet`: the projection of the wave front set to `Ω` is the
  singular support; in particular the wave front set is empty exactly when the singular support is
  (`Distribution.waveFrontSet_eq_empty_iff`).
* `Distribution.singularSupport_delta`: in positive dimension, the singular support of the point
  mass at `x₀ ∈ Ω` is `{x₀}`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Proposition 8.1.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- **A distribution with rapidly decreasing localized Fourier transform is smooth.** If the
localized Fourier transform `η ↦ T (φ e_η)` of `T` with cutoff `φ` decays faster than every power
of `‖η‖` in every direction, then the compactly supported distribution `φ T` is a smooth function
`G`: `T (φ ψ) = ∫ ψ G` for every complex test function `ψ`. -/
theorem exists_contDiff_complexPairing_eq_integral (T : 𝓓'(Ω, ℂ)) {φ : 𝓓(Ω, ℂ)}
    (h : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C) :
    ∃ G : E → ℂ, ContDiff ℝ ∞ G ∧
      ∀ ψ ψ' : 𝓓(Ω, ℂ), (∀ y, ψ' y = φ y * ψ y) → T.complexPairing ψ' = ∫ y, ψ y * G y := by
  -- A cutoff `χ₁` equal to one near the support of `φ`, a compact set `K ⊆ Ω` around its support,
  -- and a cutoff `χ` supported in `K` and equal to one on the support of `χ₁`.
  obtain ⟨χ₁, hχ₁, -, hχ₁1, hχ₁c, hχ₁Ω⟩ :=
    φ.hasCompactSupport.exists_contDiff_cutoff Ω.isOpen φ.tsupport_subset
  obtain ⟨K₂, hK₂, hK₁K₂, hK₂Ω⟩ := exists_compact_between hχ₁c Ω.isOpen hχ₁Ω
  let K₁ : Compacts E := ⟨tsupport χ₁, hχ₁c⟩
  let K : Compacts E := ⟨K₂, hK₂⟩
  have hKΩ : (K : Set E) ⊆ Ω := hK₂Ω
  obtain ⟨χ, hχ⟩ := ContDiffMapSupportedIn.exists_eqOn_one_of_subset_interior (K := K₁) (K' := K)
    hK₁K₂
  have hχ₁φ {y : E} (hy : φ y ≠ 0) : χ₁ y = 1 := interior_subset (hχ₁1 (subset_tsupport _ hy))
  have hχφ {y : E} (hy : φ y ≠ 0) : χ y = 1 :=
    hχ (subset_tsupport χ₁ (by simp [hχ₁φ hy] : χ₁ y ≠ 0))
  -- A lattice none of whose nonzero translates of `K` meet `K`, and the Fourier coefficients
  -- `c m = (covolume L)⁻¹ T (φ e_{-m})` of `φ T` along its dual lattice.
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
  set c : ZLattice.dual L → ℂ := fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * T.localFourier φ (-m)
  have hc (k : ℕ) : Summable fun m : ZLattice.dual L ↦ (1 + ‖-(m : E)‖) ^ k * ‖c m‖ := by
    simp only [norm_neg]
    refine ZLattice.summable_one_add_norm_pow_mul_norm_of_bounded _ (fun N ↦ ?_) k
    obtain ⟨C, hC⟩ := h N
    refine ⟨‖(ZLattice.covolume L : ℂ)⁻¹‖ * C, fun m ↦ ?_⟩
    have := hC (-m)
    rw [norm_neg] at this
    simp only [c, norm_mul]
    nlinarith [norm_nonneg ((ZLattice.covolume L : ℂ)⁻¹)]
  refine ⟨fun y ↦ χ₁ y * ∑' m, c m * 𝐞 ⟪y, -(m : E)⟫,
    (ofRealCLM.contDiff.comp hχ₁).mul (TauCeti.contDiff_tsum_mul_fourierChar hc),
    fun ψ ψ' hψ' ↦ ?_⟩
  -- The test function `f = χ₁ ψ`, supported in `K`, and its Fourier expansion.
  have hfs : ContDiff ℝ ∞ fun y ↦ (χ₁ y : ℂ) * ψ y := (ofRealCLM.contDiff.comp hχ₁).mul ψ.contDiff
  have hfK : support (fun y ↦ (χ₁ y : ℂ) * ψ y) ⊆ K := fun y hy ↦
    interior_subset (hK₁K₂ (subset_tsupport _ (by simpa using left_ne_zero_of_mul hy)))
  let f : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hfs hfK
  have hfapply (y : E) : f y = χ₁ y * ψ y := by
    simp [f, ContDiffMapSupportedIn.coe_of_support_subset]
  have hχf : EqOn χ 1 (support f) := fun y hy ↦ hχ (subset_tsupport χ₁ (by
    rw [mem_support, hfapply] at hy
    simpa using left_ne_zero_of_mul hy))
  have hexp := ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L f χ
    (fun y hy ℓ h ↦ Subtype.ext (hL y hy ℓ ℓ.2 h)) hχf
  -- Pair the expansion with `φ T`.
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L
    (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff ∘L
      ofSupportedInCLM ℂ hKΩ)
  have hΛf : Λ f = T.complexPairing ψ' := by
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    congr 1
    ext y
    by_cases hy : φ y = 0
    · simp [TestFunction.bilinLeftCLM_apply, hψ', hy]
    · simp [TestFunction.bilinLeftCLM_apply, hψ', hfapply, hχ₁φ hy, mul_comm]
  have hΛχ (m : ZLattice.dual L) (a : ℂ) :
      Λ (a • χ.modulate m) = a * T.localFourier φ (-m) := by
    rw [map_smul, smul_eq_mul, localFourier_eq_complexPairing_mul_modulate T hKΩ (φ := φ)
      (f := χ) (fun y ↦ ?_), neg_neg]
    · simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    · by_cases hy : φ y = 0
      · simp [hy]
      · simp [hχφ hy]
  have hsum := hexp.map Λ Λ.continuous
  simp only [comp_def, hΛχ, hΛf] at hsum
  rw [← hsum.tsum_eq]
  -- Exchange the sum with the integral: the coefficients are summable and `f` is integrable.
  have hpair := TauCeti.integral_mul_tsum_mul_fourierChar (c := c)
    (v := fun m : ZLattice.dual L ↦ -(m : E))
    ((hc 0).congr fun m ↦ by simp)
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  simp only [neg_neg] at hpair
  calc ∑' m : ZLattice.dual L,
        (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : E → ℂ) m * T.localFourier φ (-m)
      = ∫ y, f y * ∑' m, c m * 𝐞 ⟪y, -(m : E)⟫ := by
        rw [hpair]
        exact tsum_congr fun m ↦ by ring
    _ = ∫ y, ψ y * (χ₁ y * ∑' m, c m * 𝐞 ⟪y, -(m : E)⟫) := by
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        simp only [hfapply]
        ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Rapid decay in every direction.** If `T` is microlocally smooth at `(x, ξ)` for every
`ξ ≠ 0`, then there is a neighbourhood `U` of `x` such that every cutoff supported in `U` has
localized Fourier transform decaying faster than every power of `‖η‖` in all directions. -/
theorem exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : ∀ ξ ≠ 0, T.IsMicrolocallySmoothAt x ξ) :
    ∃ U ∈ 𝓝 x, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  -- Cones of rapid decay around the unit vectors, valid for all cutoffs supported near `x`.
  have hcone : ∀ ξ ∈ sphere (0 : E) 1, ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧ ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
        ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := fun ξ hξ ↦
    (h ξ (norm_ne_zero_iff.1 (by simp [mem_sphere_zero_iff_norm.1 hξ]))).exists_nhds_cone
  choose! U hU Γ hΓo hξΓ hΓc hdecay using hcone
  -- Finitely many of the cones cover the unit sphere.
  obtain ⟨t, ht, hcover⟩ := (isCompact_sphere (0 : E) 1).elim_nhds_subcover Γ
    fun ξ hξ ↦ (hΓo ξ hξ).mem_nhds (hξΓ ξ hξ)
  refine ⟨⋂ ξ ∈ t, U ξ, (biInter_finset_mem t).2 fun ξ hξ ↦ hU ξ (ht ξ hξ),
    fun ψ hψ N ↦ ?_⟩
  choose! C hC using fun ξ hξ ↦
    hdecay ξ (ht ξ hξ) ψ (hψ.trans (biInter_subset_of_mem hξ)) N
  refine ⟨‖T.localFourier ψ 0‖ + ∑ ξ ∈ t, |C ξ|, fun η ↦ ?_⟩
  rcases eq_or_ne η 0 with rfl | hη
  · simpa using Finset.sum_nonneg fun ξ _ ↦ abs_nonneg (C ξ)
  · -- The direction of `η` lies in one of the cones, and so does `η`.
    have hu : ‖η‖⁻¹ • η ∈ sphere (0 : E) 1 := by simp [norm_smul, hη]
    obtain ⟨ξ, hξt, hηξ⟩ := mem_iUnion₂.1 (hcover hu)
    have hηΓ : η ∈ Γ ξ := by
      simpa [smul_smul, hη] using hΓc ξ (ht ξ hξt) ‖η‖ (norm_pos_iff.2 hη) _ hηξ
    calc (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ |C ξ| := (hC ξ hξt η hηΓ).trans (le_abs_self _)
      _ ≤ ∑ ξ ∈ t, |C ξ| := Finset.single_le_sum (fun ξ _ ↦ abs_nonneg (C ξ)) hξt
      _ ≤ ‖T.localFourier ψ 0‖ + ∑ ξ ∈ t, |C ξ| := le_add_of_nonneg_left (norm_nonneg _)

/-- **Microlocal smoothness detects the singular support.** A point `x ∈ Ω` lies outside the
singular support of `T` exactly when `T` is microlocally smooth at `(x, ξ)` for every
direction `ξ ≠ 0`. -/
theorem notMem_singularSupport_iff_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) : x ∉ T.singularSupport ↔ ∀ ξ ≠ 0, T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun h ξ _ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨U, hU, hxU, -, f, hf, hT⟩ := exists_apply_eq_integral_of_notMem_singularSupport hx h
    exact isMicrolocallySmoothAt_of_apply_eq_integral hU hf hT hxU hx ξ
  obtain ⟨V, hV, hdecay⟩ := exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt h
  -- A real cutoff `χ` equal to one near `x` and supported in `V`, and its localization `φ T`.
  obtain ⟨χ, -, hχ1, hχV⟩ := exists_cutoff_tsupport_subset (n := ⊤) (Ω := Ω)
    (isCompact_singleton (x := x)) (isOpen_interior.inter Ω.isOpen)
    (singleton_subset_iff.2 ⟨mem_interior_iff_mem_nhds.2 hV, hx⟩) inter_subset_right
  have hφV : tsupport (postcompCLM (𝕜 := ℝ) ofRealCLM χ) ⊆ V := by
    rw [postcompCLM_apply]
    exact (tsupport_comp_subset (map_zero _) χ).trans
      (hχV.trans (inter_subset_left.trans interior_subset))
  obtain ⟨G, hG, hTG⟩ := exists_contDiff_complexPairing_eq_integral T (hdecay _ hφV)
  -- On the open set where `χ = 1`, `T` is the smooth function `G`.
  refine notMem_singularSupport_of_apply_eq_integral isOpen_interior hG.contDiffOn
    (U := interior {y | χ y = 1}) (fun ψ hψ ↦ ?_)
    (mem_interior_iff_mem_nhds.2 (by rwa [nhdsSet_singleton] at hχ1))
  have hψχ (y : E) : (ψ y : ℂ) = χ y * ψ y := by
    by_cases hy : ψ y = 0
    · simp [hy]
    · simp [show χ y = 1 from interior_subset (hψ (subset_tsupport _ hy))]
  rw [← complexPairing_postcompCLM_ofRealCLM,
    hTG (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) _ fun y ↦ by simpa [postcompCLM_apply] using hψχ y]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ by simp [postcompCLM_apply, real_smul])

/-- **The wave front set projects onto the singular support** (Hörmander I, Proposition 8.1.3):
the points of `Ω` over which `T` has a wave front direction are exactly those of its singular
support. -/
theorem fst_image_waveFrontSet (T : 𝓓'(Ω, ℂ)) : Prod.fst '' T.waveFrontSet = T.singularSupport := by
  ext x
  constructor
  · rintro ⟨⟨y, ξ⟩, hyξ, rfl⟩
    obtain ⟨hy, hξ, hT⟩ := mem_waveFrontSet_iff.1 hyξ
    exact by_contra fun h ↦
      hT ((notMem_singularSupport_iff_forall_isMicrolocallySmoothAt hy).1 h ξ hξ)
  · intro hx
    have hxΩ := singularSupport_subset T hx
    have h : ¬ ∀ ξ ≠ 0, T.IsMicrolocallySmoothAt x ξ := fun h ↦
      (notMem_singularSupport_iff_forall_isMicrolocallySmoothAt hxΩ).2 h hx
    obtain ⟨ξ, hξ, hT⟩ := by simpa only [not_forall, exists_prop] using h
    exact ⟨(x, ξ), mem_waveFrontSet_iff.2 ⟨hxΩ, hξ, hT⟩, rfl⟩

/-- The wave front set is empty exactly when the singular support is. -/
theorem waveFrontSet_eq_empty_iff {T : 𝓓'(Ω, ℂ)} :
    T.waveFrontSet = ∅ ↔ T.singularSupport = ∅ := by
  rw [← fst_image_waveFrontSet, image_eq_empty]

/-- In positive dimension, the point mass at `x₀ ∈ Ω` has singular support `{x₀}`. -/
theorem singularSupport_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).singularSupport = {x₀} := by
  rw [← fst_image_waveFrontSet, waveFrontSet_delta hx₀,
    fst_image_prod _ ((exists_ne (0 : E)).imp fun _ h ↦ h)]

end Distribution
