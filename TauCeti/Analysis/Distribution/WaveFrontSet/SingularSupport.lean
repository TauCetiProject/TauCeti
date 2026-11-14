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
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The projection of the wave front set onto the singular support

The *singular support* `Distribution.singularSupport T` of a distribution `T` on an open set `Ω`,
defined in `TauCeti.Analysis.Distribution.SingularSupport`, consists of the points of `Ω` near
which `T` is not a smooth function. The wave front set refines the singular support by recording
the directions of the singularities. This file proves that it forgets nothing more: the projection
of the wave front set of a complex distribution onto the base is exactly its singular support
(`Distribution.fst_image_waveFrontSet`, Hörmander I, Proposition 8.1.3). Over a point at which
`T` is smooth there is no wave front set, by
`Distribution.isMicrolocallySmoothAt_of_apply_eq_integral`. The converse has two steps.

* **Compactness of the sphere of directions.** If `T` is microlocally smooth at `(x, ξ)` for every
  `ξ ≠ 0`, then finitely many of the open cones provided by
  `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone` cover the unit sphere. So there is one
  neighbourhood `U` of `x` such that the localized Fourier transform of `T` decays rapidly in
  *every* direction for every cutoff supported in `U`
  (`Distribution.exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt`).
* **Fourier inversion.** If the localized Fourier transform `F = localFourier T χ` decays rapidly
  on all of `E`, then `T` is a smooth function wherever `χ = 1`
  (`Distribution.exists_contDiff_apply_eq_integral_of_forall_decay`). Choose a full lattice `L`
  none of whose nonzero translates of `tsupport χ` meet it. A real test function `φ` supported
  where `χ = 1` is the sum, in the topology of smooth functions supported in `tsupport χ`, of its
  Fourier series `∑ m : L^∨, (covolume L)⁻¹ 𝓕 φ (m) χ e_m` in the modulated cutoffs `χ e_m`
  (`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`). Pairing with `T` gives
  `T φ = ∑ m, (covolume L)⁻¹ 𝓕 φ (m) F (-m)`. Writing out `𝓕 φ (m)` as an integral and exchanging
  sum and integral, this is `∫ φ • f` for the lattice Fourier series
  `f y = ∑ m, (covolume L)⁻¹ F (-m) exp (-2πi ⟪y, m⟫)`, which is smooth because its coefficients
  decay rapidly. Working with a series rather than with the Fourier integral avoids integrating
  test-function-valued maps against `T`.

## Main declarations

* `Distribution.exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt` and
  `Distribution.exists_contDiff_apply_eq_integral_of_forall_decay`: the two steps above.
* `Distribution.notMem_singularSupport_iff_forall_isMicrolocallySmoothAt`: `T` is smooth near a
  point of `Ω` exactly when it is microlocally smooth there in every nonzero direction.
* `Distribution.fst_image_waveFrontSet`: the projection of the wave front set is the singular
  support.
* `Distribution.singularSupport_eq_empty_iff_waveFrontSet_eq_empty`: a complex distribution has
  empty singular support exactly when it has empty wave front set.
* `Distribution.singularSupport_delta`: the singular support of the point mass at `x₀` is `{x₀}`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.2 (singular support) and Proposition 8.1.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-! ### Rapid decay in every direction -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Compactness of the sphere of directions.** If `T` is microlocally smooth at `(x, ξ)` for
every `ξ ≠ 0`, then there is a neighbourhood `U` of `x` such that for every cutoff `ψ` supported in
`U` the localized Fourier transform of `T` decays rapidly on all of `E`. -/
theorem exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : ∀ ξ, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ) :
    ∃ U ∈ 𝓝 x, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  classical
  -- For each unit direction, a neighbourhood of `x` and an open cone with uniform decay.
  choose U hU Γ hΓ hξΓ hcone hdecay using fun ξ : sphere (0 : E) 1 ↦
    (h ξ (ne_zero_of_mem_unit_sphere ξ)).exists_nhds_cone
  -- Finitely many of the cones cover the nonzero vectors.
  obtain ⟨t, ht⟩ := TauCeti.exists_finset_compl_singleton_subset_biUnion hΓ hξΓ hcone
  refine ⟨⋂ ξ ∈ t, U ξ, (biInter_finset_mem t).2 fun ξ _ ↦ hU ξ, fun ψ hψ N ↦ ?_⟩
  have hdecay' : ∀ ξ ∈ t, ∃ C, ∀ η ∈ Γ ξ, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C :=
    fun ξ hξ ↦ hdecay ξ ψ (hψ.trans (biInter_subset_of_mem hξ)) N
  choose! C hC using hdecay'
  have hsum : 0 ≤ ∑ ξ ∈ t, |C ξ| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨‖T.localFourier ψ 0‖ + ∑ ξ ∈ t, |C ξ|, fun η ↦ ?_⟩
  rcases eq_or_ne η 0 with rfl | hη
  · simpa using hsum
  obtain ⟨ξ, hξt, hηΓ⟩ := mem_iUnion₂.1 (ht hη)
  calc (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C ξ := hC ξ hξt η hηΓ
    _ ≤ |C ξ| := le_abs_self _
    _ ≤ ∑ ξ ∈ t, |C ξ| := Finset.single_le_sum (f := fun ξ ↦ |C ξ|) (fun _ _ ↦ abs_nonneg _) hξt
    _ ≤ _ := le_add_of_nonneg_left (norm_nonneg _)

/-! ### Fourier inversion for a rapidly decreasing localized Fourier transform -/

/-- **The pairing with a test function as a lattice Fourier series.** Let `L` be a full lattice
none of whose nonzero vectors translates `tsupport χ` into a set meeting it. If `χ = 1` on the
support of a real test function `φ`, then
`T φ = ∑ m : L^∨, (covolume L)⁻¹ 𝓕 φ (m) T (χ e_(-m))`: expand `φ` in its Fourier series along
`L` in the modulated cutoffs `χ e_(-m)` and pair with `T`. -/
private theorem hasSum_fourier_mul_localFourier (T : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℂ))
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ x ∈ tsupport χ, ∀ ℓ ∈ L, x + ℓ ∈ tsupport χ → ℓ = 0) {φ : 𝓓(Ω, ℝ)}
    (hφ : EqOn (χ : E → ℂ) 1 (support φ)) :
    HasSum (fun m : ZLattice.dual L ↦ (ZLattice.covolume L : ℂ)⁻¹ *
      𝓕 (fun y ↦ (φ y : ℂ)) m * T.localFourier χ (-m)) (T φ) := by
  -- The cutoff and the test function as smooth functions supported in `K = tsupport χ`.
  let K : Compacts E := ⟨tsupport χ, χ.hasCompactSupport⟩
  have hKΩ : (K : Set E) ⊆ Ω := χ.tsupport_subset
  let χK : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset χ.contDiff (subset_tsupport _)
  have hχK (y : E) : χK y = χ y := by simp [χK, ContDiffMapSupportedIn.coe_of_support_subset]
  have hφK : support (fun y ↦ (φ y : ℂ)) ⊆ K := fun y hy ↦ by
    have hy' : y ∈ support φ := by simpa using hy
    exact subset_tsupport _ (by simp [hφ hy'])
  have hφc : ContDiff ℝ ∞ fun y ↦ (φ y : ℂ) := ofRealCLM.contDiff.comp φ.contDiff
  let φK : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hφc hφK
  have hφK' : (φK : E → ℂ) = fun y ↦ (φ y : ℂ) := by
    ext y
    simp [φK, ContDiffMapSupportedIn.coe_of_support_subset]
  have hexp := ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L φK χK
    (fun y hy ℓ h ↦ Subtype.ext (hL y hy ℓ ℓ.2 h)) fun y hy ↦ by
      rw [hχK]
      exact hφ (by simpa [hφK'] using hy)
  -- Pair the expansion with `T`.
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L ofSupportedInCLM ℂ hKΩ
  have hΛφ : Λ φK = T φ := by
    have h : ofSupportedIn hKΩ φK = postcompCLM (𝕜 := ℝ) ofRealCLM φ := by
      ext y
      simp [hφK']
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM, h,
      complexPairing_postcompCLM_ofRealCLM]
  have hΛχ (m : ZLattice.dual L) (b : ℂ) :
      Λ (b • χK.modulate m) = b * T.localFourier χ (-m) := by
    rw [map_smul, smul_eq_mul]
    congr 1
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    rw [localFourier_eq_complexPairing_modulate T hKΩ (f := χK) hχK, neg_neg]
  have h := hexp.map Λ Λ.continuous
  simp only [comp_def, hΛχ, hΛφ, hφK'] at h
  exact h

/-- **Fourier inversion for a rapidly decreasing localized Fourier transform.** If the localized
Fourier transform of `T` with cutoff `χ` decays rapidly on all of `E`, there is a smooth function
`f` such that `T φ = ∫ φ • f` for every real test function `φ` on whose support `χ = 1`. -/
theorem exists_contDiff_apply_eq_integral_of_forall_decay {T : 𝓓'(Ω, ℂ)} {χ : 𝓓(Ω, ℂ)}
    (hdecay : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier χ η‖ ≤ C) :
    ∃ f : E → ℂ, ContDiff ℝ ∞ f ∧
      ∀ φ : 𝓓(Ω, ℝ), EqOn (χ : E → ℂ) 1 (support φ) → T φ = ∫ y, φ y • f y := by
  -- A lattice none of whose nonzero vectors translates `tsupport χ` into a set meeting it.
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  set G : E → ℂ := T.localFourier χ
  set c : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  -- `f` is the lattice Fourier series with the rapidly decreasing coefficients `c G (-m)`.
  have hb : ∀ k : ℕ, Summable fun m : ZLattice.dual L ↦ (1 + ‖(m : E)‖) ^ k * ‖c * G (-m)‖ :=
    ZLattice.summable_one_add_norm_pow_mul_norm_of_decay (ZLattice.dual L)
      (f := fun η ↦ c * G (-η)) fun N ↦ by
      obtain ⟨C, hC⟩ := hdecay N
      refine ⟨‖c‖ * C, fun η ↦ ?_⟩
      rw [norm_mul, mul_left_comm]
      gcongr
      simpa using hC (-η)
  have hb₀ : Summable fun m : ZLattice.dual L ↦ ‖c * G (-m)‖ := by simpa using hb 0
  let a : ZLattice.dual L → E → ℂ := fun m y ↦ (c * G (-m)) • TauCeti.fourierAtom (m : E) y
  have hnorm (m : ZLattice.dual L) (y : E) : ‖a m y‖ = ‖c * G (-m)‖ := by
    simp only [a, norm_smul, TauCeti.norm_fourierAtom, mul_one]
  refine ⟨fun y ↦ ∑' m, a m y, TauCeti.contDiff_tsum_smul_fourierAtom hb, fun φ hφ ↦ ?_⟩
  rw [← (hasSum_fourier_mul_localFourier T χ L hL hφ).tsum_eq]
  -- Exchange the sum over the lattice with the integral.
  have hint (m : ZLattice.dual L) : Integrable (fun y ↦ φ y • a m y) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ φ.hasCompactSupport.smul_right
    have ha : Continuous (a m) := by
      simp only [a]
      exact (TauCeti.continuous_fourierAtom (m : E)).const_smul (c * G (-m))
    exact φ.continuous.smul ha
  have hnorm' (m : ZLattice.dual L) : ∫ y, ‖φ y • a m y‖ = ‖c * G (-m)‖ * ∫ y, ‖φ y‖ := by
    have h (y : E) : ‖φ y • a m y‖ = ‖φ y‖ * ‖c * G (-m)‖ := by rw [norm_smul, hnorm]
    simp_rw [h]
    rw [integral_mul_const, mul_comm]
  have hsum : Summable fun m : ZLattice.dual L ↦ ∫ y, ‖φ y • a m y‖ := by
    simp_rw [hnorm']
    exact hb₀.mul_right _
  have hpt (y : E) : φ y • ∑' m, a m y = ∑' m, φ y • a m y :=
    (hb₀.of_norm_bounded fun m ↦ (hnorm m y).le).tsum_const_smul _ |>.symm
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun m ↦ ?_
  -- Each term is `c G (-m)` times the Fourier coefficient `𝓕 φ (m)`.
  have h (y : E) : φ y • a m y = (c * G (-m)) * (𝐞 (-⟪y, (m : E)⟫) • (φ y : ℂ)) := by
    simp only [a, TauCeti.fourierAtom_eq_fourierChar, Circle.smul_def, real_smul, smul_eq_mul]
    ring
  simp_rw [h]
  rw [integral_const_mul, Real.fourier_eq]
  ring

/-! ### The projection of the wave front set -/

/-- A complex distribution is a smooth function near a point `x ∈ Ω` exactly when it is
microlocally smooth at `x` in every nonzero direction. -/
theorem notMem_singularSupport_iff_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) :
    x ∉ T.singularSupport ↔ ∀ ξ, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun h ξ _ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨U, hU, hxU, f, hf, hT⟩ := (notMem_singularSupport_iff hx).1 h
    exact isMicrolocallySmoothAt_of_apply_eq_integral hU hf hT hxU hx ξ
  obtain ⟨U, hU, hdecay⟩ := exists_nhds_forall_decay_of_forall_isMicrolocallySmoothAt h
  -- A cutoff equal to one near `x` and supported in `U ∩ Ω`.
  obtain ⟨χ, -, hχ1, hχs⟩ := exists_cutoff_tsupport_subset (n := ⊤) (isCompact_singleton (x := x))
    (isOpen_interior.inter Ω.isOpen) (singleton_subset_iff.2 ⟨mem_interior_iff_mem_nhds.2 hU, hx⟩)
    inter_subset_right
  rw [nhdsSet_singleton] at hχ1
  obtain ⟨V, hV1, hV, hxV⟩ := _root_.eventually_nhds_iff.1 hχ1
  let χc : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
  have hχc (y : E) : χc y = χ y := by simp [χc]
  have hχcs : tsupport χc ⊆ U := by
    refine (tsupport_comp_subset (g := ofRealCLM) (by simp) χ).trans ?_
    exact hχs.trans (inter_subset_left.trans interior_subset)
  obtain ⟨f, hf, hT⟩ := exists_contDiff_apply_eq_integral_of_forall_decay (hdecay χc hχcs)
  refine (notMem_singularSupport_iff hx).2 ⟨V, hV, hxV, f, hf.contDiffOn, fun φ hφ ↦ hT φ ?_⟩
  intro y hy
  simp [hχc, hV1 y (hφ (subset_tsupport _ hy))]

/-- **The projection of the wave front set is the singular support** (Hörmander I,
Proposition 8.1.3). -/
theorem fst_image_waveFrontSet (T : 𝓓'(Ω, ℂ)) :
    Prod.fst '' T.waveFrontSet = T.singularSupport := by
  ext x
  constructor
  · rintro ⟨⟨x, ξ⟩, hp, rfl⟩
    obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
    exact by_contra fun h ↦ hT ((notMem_singularSupport_iff_forall_isMicrolocallySmoothAt hx).1 h
      ξ hξ)
  · intro h
    have hx := T.singularSupport_subset h
    obtain ⟨ξ, hξ, hT⟩ := not_forall₂.1 fun hne ↦
      (notMem_singularSupport_iff_forall_isMicrolocallySmoothAt hx).2 hne h
    exact ⟨(x, ξ), mem_waveFrontSet_iff.2 ⟨hx, hξ, hT⟩, rfl⟩

/-- A complex distribution has empty singular support exactly when it has empty wave front
set. -/
theorem singularSupport_eq_empty_iff_waveFrontSet_eq_empty {T : 𝓓'(Ω, ℂ)} :
    T.singularSupport = ∅ ↔ T.waveFrontSet = ∅ := by
  rw [← fst_image_waveFrontSet, image_eq_empty]

/-- The singular support of the complex point mass at `x₀ ∈ Ω` is `{x₀}`, for `E` nontrivial. -/
theorem singularSupport_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).singularSupport = {x₀} := by
  rw [← fst_image_waveFrontSet, waveFrontSet_delta hx₀]
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  exact fst_image_prod _ ⟨ξ, hξ⟩

end Distribution
