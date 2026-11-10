/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SingularSupport
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The singular support and the projection of the wave front set

Let `Ω` be an open subset of a finite-dimensional real inner product space `E`. The singular
support `Distribution.singSupport T` of a complex distribution `T` on `Ω` is the set of points
of `Ω` having no open neighbourhood on which `T` is a smooth function. This file proves that it is
the projection of the wave front set (Hörmander I, Proposition 8.1.3):

`Prod.fst '' waveFrontSet T = singSupport T`.

One inclusion is `Distribution.isMicrolocallySmoothAt_of_apply_eq_integral`: over an open set on
which `T` is smooth there is no wave front set. For the other, suppose `T` is microlocally smooth
at `(x, ξ)` for every `ξ ≠ 0`. By compactness of the unit sphere, finitely many of the cones
provided by `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone` cover `E \ {0}`, so a single
cutoff `ψ` equal to one near `x` has localized Fourier transform `η ↦ T (ψ e_η)` rapidly decreasing
on all of `E`. Such a cut-off distribution `ψ T` is a smooth function
(`Distribution.exists_contDiff_complexPairing_eq_integral_of_forall_decay`). The proof expands a
test function in a Fourier series on a compact set around the support of `ψ`
(`TestFunction.exists_hasSum_fourier_smul_modulate`). Pairing with `ψ T` turns its coefficients
into the values of the localized Fourier transform along a lattice. The rapid decay of these values
makes the resulting trigonometric series a smooth function.

## Main results

* `Distribution.exists_contDiff_complexPairing_eq_integral_of_forall_decay`: if the localized
  Fourier transform of `T` with cutoff `ψ` decays rapidly, then `ψ T` is a smooth function.
* `Distribution.exists_forall_decay_of_forall_isMicrolocallySmoothAt`: microlocal smoothness at
  `(x, ξ)` for every `ξ ≠ 0` gives a single cutoff near `x` with rapid decay in every direction.
* `Distribution.notMem_singSupport_iff_forall_isMicrolocallySmoothAt`: a point of `Ω` lies outside
  the singular support exactly when `T` is microlocally smooth there in every nonzero direction.
* `Distribution.image_fst_waveFrontSet`: the projection of the wave front set is the singular
  support.
* `Distribution.singSupport_subset_dsupport`: the singular support lies in the support.
* `Distribution.singSupport_zero`, `Distribution.singSupport_neg`, `Distribution.singSupport_smul`,
  `Distribution.singSupport_add_subset`, `Distribution.singSupport_sub_subset`: the singular
  support under the linear operations.
* `Distribution.singSupport_ofFun_eq_empty`, `Distribution.singSupport_delta`: a smooth function
  has empty singular support, and the point mass at `x₀` has singular support `{x₀}`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Proposition 8.1.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-! ### Distributions with rapidly decreasing localized Fourier transform -/

/-- **A cut-off distribution with rapidly decreasing Fourier transform is smooth.** If the
localized Fourier transform `η ↦ T (ψ e_η)` of `T` with cutoff `ψ` decays faster than every power
of `‖η‖`, then the compactly supported distribution `ψ T` is a smooth function `f`: for all test
functions `φ` and `θ = ψ φ`, `T θ = ∫ φ f`. -/
theorem exists_contDiff_complexPairing_eq_integral_of_forall_decay (T : 𝓓'(Ω, ℂ))
    {ψ : 𝓓(Ω, ℂ)} (h : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C) :
    ∃ f : E → ℂ, ContDiff ℝ ∞ f ∧ ∀ φ θ : 𝓓(Ω, ℂ), (∀ x, θ x = ψ x * φ x) →
      T.complexPairing θ = ∫ x, φ x * f x := by
  -- A cutoff `χ₁` equal to one where `ψ ≠ 0`, and a lattice `L` along which smooth multiples of
  -- `χ₁` expand in the modulations of a cutoff `χ` with `ψ = ψ χ`.
  obtain ⟨K, hKΩ, L, _, _, χ₁, χ, hχ₁, hχ₁ψ, hψχ, hexp⟩ := ψ.exists_hasSum_fourier_smul_modulate
  generalize hF : T.localFourier ψ = F at h
  -- The values of the localized Fourier transform along the dual lattice decay rapidly.
  have hsum (k : ℕ) :
      Summable fun m : ZLattice.dual L ↦ (1 + ‖(m : E)‖) ^ k * ‖F (-(m : E))‖ := by
    set r := Module.finrank ℤ (ZLattice.dual L) + 1
    obtain ⟨C, hC⟩ := h (k + r)
    refine ((ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L)
      (r := r) (Nat.lt_succ_self _)).mul_left C).of_nonneg_of_le (fun m ↦ by positivity)
      fun m ↦ ?_
    have hpos : 0 < (1 + ‖(m : E)‖) ^ r := by positivity
    rw [le_mul_inv_iff₀ hpos, mul_right_comm, ← pow_add]
    simpa [norm_neg] using hC (-(m : E))
  -- The candidate function: `χ₁` times the trigonometric series with coefficients `c m`.
  set c : ZLattice.dual L → ℂ := fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * F (-(m : E)) with hc
  have hcs (k : ℕ) : Summable fun m ↦ ‖c m‖ * ‖(m : E)‖ ^ k := by
    refine ((hsum k).mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖).of_nonneg_of_le
      (fun m ↦ by positivity) fun m ↦ ?_
    rw [hc, norm_mul, mul_assoc, mul_comm ‖F _‖]
    gcongr
    linarith [norm_nonneg (m : E)]
  have hg := TauCeti.contDiff_tsum_mul_fourierAtom (fun m : ZLattice.dual L ↦ (m : E))
    c hcs
  refine ⟨fun x ↦ (χ₁ x : ℂ) * ∑' m, c m * TauCeti.fourierAtom (m : E) x,
    (ofRealCLM.contDiff.comp hχ₁).mul hg, fun φ θ hθ ↦ ?_⟩
  -- Expand `u = χ₁ φ` in the modulations of `χ`.
  obtain ⟨u, hu, hexp⟩ := hexp φ φ.contDiff.contDiffOn
  -- Pair the expansion with `T` after multiplying by `ψ`: the modulated cutoffs give the values
  -- of the localized Fourier transform along the dual lattice.
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L
    (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ψ.contDiff ∘L
      ofSupportedInCLM ℂ hKΩ)
  have h1 : Λ u = T.complexPairing θ := by
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    congr 1
    ext x
    by_cases hx : ψ x = 0
    · simp [TestFunction.bilinLeftCLM_apply, hθ, hx]
    · simp [TestFunction.bilinLeftCLM_apply, hθ, hu, hχ₁ψ x hx, mul_comm]
  have h2 (m : ZLattice.dual L) (a : ℂ) : Λ (a • χ.modulate m) = a * F (-(m : E)) := by
    rw [map_smul, smul_eq_mul, ← hF, localFourier_eq_complexPairing_mul_modulate T hKΩ hψχ,
      neg_neg]
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
  -- The integral against the trigonometric series, computed term by term.
  have hint : ∫ x, φ x * ((χ₁ x : ℂ) * ∑' m, c m * TauCeti.fourierAtom (m : E) x) =
      ∑' m, c m * 𝓕 (u : E → ℂ) m := by
    rw [← TauCeti.integral_mul_tsum_mul_fourierAtom _ ((hcs 0).congr fun m ↦ by simp)
      u.continuous u.hasCompactSupport]
    congr 1
    ext x
    rw [hu]
    ring
  rw [hint, ← h1, ← (hexp.map Λ Λ.continuous).tsum_eq]
  refine tsum_congr fun m ↦ ?_
  rw [Function.comp_apply, h2, hc]
  ring

/-! ### Microlocal smoothness and the singular support -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Microlocal smoothness in every direction gives one cutoff with rapid decay.** If `T` is
microlocally smooth at `(x, ξ)` for every `ξ ≠ 0`, then some test function `ψ`, equal to one near
`x`, has localized Fourier transform `η ↦ T (ψ e_η)` rapidly decreasing on all of `E`. -/
theorem exists_forall_decay_of_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) (h : ∀ ξ : E, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ) :
    ∃ ψ : 𝓓(Ω, ℂ), (∀ᶠ y in 𝓝 x, ψ y = 1) ∧
      ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  -- Finitely many of the cones of uniform decay cover the unit sphere.
  choose U hU Γ hΓ hξΓ hcone hdecay using fun ξ : sphere (0 : E) 1 ↦
    (h ξ (ne_zero_of_mem_unit_sphere ξ)).exists_nhds_cone
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover (fun ξ ↦ Γ ξ) hΓ
    fun ξ hξ ↦ mem_iUnion.2 ⟨⟨ξ, hξ⟩, hξΓ _⟩
  -- A cutoff `ψ` equal to one near `x` and supported in every neighbourhood `U ξ`, `ξ ∈ t`.
  have hV : (⋂ ξ ∈ t, U ξ) ∩ Ω ∈ 𝓝 x :=
    inter_mem ((t.iInter_mem_sets).2 fun ξ _ ↦ hU ξ) (Ω.isOpen.mem_nhds hx)
  obtain ⟨χ, hχ, -, hχ1, hχc, hχs⟩ := (isCompact_singleton (x := x)).exists_contDiff_cutoff
    isOpen_interior (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hV))
  have hχV : tsupport (fun y ↦ (χ y : ℂ)) ⊆ (⋂ ξ ∈ t, U ξ) ∩ Ω :=
    (tsupport_comp_subset ofReal_zero χ).trans (hχs.trans interior_subset)
  let ψ : 𝓓(Ω, ℂ) := TestFunction.mk (fun y ↦ (χ y : ℂ)) (ofRealCLM.contDiff.comp hχ)
    (hχc.comp_left ofReal_zero) (hχV.trans inter_subset_right)
  have hψ : ⇑ψ = fun y ↦ (χ y : ℂ) := TestFunction.coe_mk
  refine ⟨ψ, ?_, fun N ↦ ?_⟩
  · filter_upwards [mem_interior_iff_mem_nhds.1 (hχ1 rfl)] with y hy
    simp [hψ, show χ y = 1 from hy]
  -- On each cone `Γ ξ`, `ξ ∈ t`, the decay comes from `exists_nhds_cone`; the cones cover
  -- `E \ {0}`, and the single point `0` is harmless.
  have hψU (ξ : sphere (0 : E) 1) (hξ : ξ ∈ t) : tsupport ψ ⊆ U ξ := by
    rw [hψ]
    exact hχV.trans (inter_subset_left.trans (biInter_subset_of_mem hξ))
  choose! C hC using fun ξ (hξ : ξ ∈ t) ↦ hdecay ξ ψ (hψU ξ hξ) N
  refine ⟨‖T.localFourier ψ 0‖ + ∑ ξ ∈ t, |C ξ|, fun η ↦ ?_⟩
  have hsum : 0 ≤ ∑ ξ ∈ t, |C ξ| := t.sum_nonneg fun _ _ ↦ abs_nonneg _
  rcases eq_or_ne η 0 with rfl | hη
  · simpa using hsum
  have hη' : ‖η‖⁻¹ • η ∈ sphere (0 : E) 1 := by
    simp [norm_smul, norm_ne_zero_iff.2 hη]
  obtain ⟨ξ, hξt, hξ⟩ := mem_iUnion₂.1 (ht hη')
  have hηΓ : η ∈ Γ ξ := by
    simpa [smul_smul, norm_ne_zero_iff.2 hη] using hcone ξ ‖η‖ (norm_pos_iff.2 hη) _ hξ
  calc (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C ξ := hC ξ hξt η hηΓ
    _ ≤ |C ξ| := le_abs_self _
    _ ≤ ∑ ξ ∈ t, |C ξ| :=
      Finset.single_le_sum (f := fun ξ ↦ |C ξ|) (fun _ _ ↦ abs_nonneg _) hξt
    _ ≤ _ := le_add_of_nonneg_left (norm_nonneg _)

/-- **Microlocal smoothness in every direction is smoothness.** A point `x ∈ Ω` lies outside the
singular support of `T` exactly when `T` is microlocally smooth at `(x, ξ)` for every `ξ ≠ 0`. -/
theorem notMem_singSupport_iff_forall_isMicrolocallySmoothAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) :
    x ∉ T.singSupport ↔ ∀ ξ : E, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun h ξ _ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨U, hU, hxU, f, hf, hT⟩ := (notMem_singSupport_iff hx).1 h
    exact isMicrolocallySmoothAt_of_apply_eq_integral hU hf hT hxU hx ξ
  -- A cutoff `ψ` with rapid decay makes `ψ T` a smooth function, and `T` agrees with it where
  -- `ψ = 1`.
  obtain ⟨ψ, hψ1, hdec⟩ := exists_forall_decay_of_forall_isMicrolocallySmoothAt hx h
  obtain ⟨f, hf, hTf⟩ := exists_contDiff_complexPairing_eq_integral_of_forall_decay T hdec
  refine notMem_singSupport_of_apply_eq_integral (isOpen_interior (s := {y | ψ y = 1}))
    hf.contDiffOn (fun φ hφ ↦ ?_) (mem_interior_iff_mem_nhds.2 hψ1)
  have hψφ (y : E) : postcompCLM (𝕜 := ℝ) ofRealCLM φ y =
      ψ y * postcompCLM (𝕜 := ℝ) ofRealCLM φ y := by
    by_cases hy : φ y = 0
    · simp [hy]
    · rw [show ψ y = 1 from interior_subset (hφ (subset_tsupport _ hy)), one_mul]
  rw [← complexPairing_postcompCLM_ofRealCLM T φ, hTf _ _ hψφ]
  simp [Complex.real_smul]

/-- **The projection of the wave front set is the singular support** (Hörmander I,
Proposition 8.1.3). -/
theorem image_fst_waveFrontSet (T : 𝓓'(Ω, ℂ)) : Prod.fst '' T.waveFrontSet = T.singSupport := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨⟨x, ξ⟩, hp, rfl⟩
    obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
    exact mem_singSupport_iff.2 ⟨hx, fun h ↦ hT
      ((notMem_singSupport_iff_forall_isMicrolocallySmoothAt hx).1
        (fun h' ↦ (mem_singSupport_iff.1 h').2 h) ξ hξ)⟩
  · have hxΩ := singSupport_subset T hx
    obtain ⟨ξ, hξ, hT⟩ := not_forall₂.1 fun h ↦
      (notMem_singSupport_iff_forall_isMicrolocallySmoothAt hxΩ).2 h hx
    exact ⟨(x, ξ), mem_waveFrontSet_iff.2 ⟨hxΩ, hξ, hT⟩, rfl⟩

/-- The wave front set is empty exactly when the singular support is. -/
theorem waveFrontSet_eq_empty_iff {T : 𝓓'(Ω, ℂ)} :
    T.waveFrontSet = ∅ ↔ T.singSupport = ∅ := by
  rw [← image_fst_waveFrontSet, image_eq_empty]

/-- The singular support lies in the support. -/
theorem singSupport_subset_dsupport (T : 𝓓'(Ω, ℂ)) : T.singSupport ⊆ dsupport T := by
  rw [← image_fst_waveFrontSet]
  rintro _ ⟨p, hp, rfl⟩
  exact (waveFrontSet_subset_dsupport T hp).1

/-- The zero distribution has empty singular support. -/
@[simp]
theorem singSupport_zero : (0 : 𝓓'(Ω, ℂ)).singSupport = ∅ := by
  rw [← waveFrontSet_eq_empty_iff, waveFrontSet_zero]

/-- The negative of `T` has the same singular support as `T`. -/
@[simp]
theorem singSupport_neg (T : 𝓓'(Ω, ℂ)) : (-T).singSupport = T.singSupport := by
  rw [← image_fst_waveFrontSet, waveFrontSet_neg, image_fst_waveFrontSet]

/-- A nonzero scalar multiple of `T` has the same singular support as `T`. -/
@[simp]
theorem singSupport_smul {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, ℂ)) :
    (c • T).singSupport = T.singSupport := by
  rw [← image_fst_waveFrontSet, waveFrontSet_smul hc, image_fst_waveFrontSet]

/-- The singular support of a sum lies in the union of the singular supports. -/
theorem singSupport_add_subset (S T : 𝓓'(Ω, ℂ)) :
    (S + T).singSupport ⊆ S.singSupport ∪ T.singSupport := by
  simp only [← image_fst_waveFrontSet, ← image_union]
  exact image_mono (waveFrontSet_add_subset S T)

/-- The singular support of a difference lies in the union of the singular supports. -/
theorem singSupport_sub_subset (S T : 𝓓'(Ω, ℂ)) :
    (S - T).singSupport ⊆ S.singSupport ∪ T.singSupport := by
  simpa [sub_eq_add_neg] using singSupport_add_subset S (-T)

/-- A function smooth on `Ω` has empty singular support. -/
theorem singSupport_ofFun_eq_empty {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f MeasureTheory.volume ⊤).singSupport = ∅ := by
  rw [← waveFrontSet_eq_empty_iff, waveFrontSet_ofFun_eq_empty hf]

/-- In positive dimension, the point mass at `x₀ ∈ Ω` has singular support `{x₀}`. -/
theorem singSupport_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).singSupport = {x₀} := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  rw [← image_fst_waveFrontSet, waveFrontSet_delta hx₀, fst_image_prod _ ⟨ξ, hξ⟩]

end Distribution
