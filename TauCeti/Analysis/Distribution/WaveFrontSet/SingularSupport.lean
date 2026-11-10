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
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The singular support and the projection of the wave front set

Let `Ω` be an open subset of a finite-dimensional real inner product space `E`. The **singular
support** `Distribution.singSupport T` of a complex distribution `T` on `Ω` is the set of points
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
(`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`). Pairing with `ψ T` turns its coefficients
into the values of the localized Fourier transform along a lattice. The rapid decay of these values
makes the resulting trigonometric series a smooth function.

## Main declarations

* `Distribution.singSupport T`: the singular support of a complex distribution.

## Main results

* `Distribution.exists_contDiff_complexPairing_eq_integral_of_forall_decay`: if the localized
  Fourier transform of `T` with cutoff `ψ` decays rapidly, then `ψ T` is a smooth function.
* `Distribution.exists_forall_decay_of_forall_isMicrolocallySmoothAt`: microlocal smoothness at
  `(x, ξ)` for every `ξ ≠ 0` gives a single cutoff near `x` with rapid decay in every direction.
* `Distribution.notMem_singSupport_iff_forall_isMicrolocallySmoothAt`: a point of `Ω` lies outside
  the singular support exactly when `T` is microlocally smooth there in every nonzero direction.
* `Distribution.image_fst_waveFrontSet`: the projection of the wave front set is the singular
  support.
* `Distribution.isOpen_diff_singSupport`, `Distribution.singSupport_subset_dsupport`,
  `Distribution.singSupport_add_subset`: the singular support is closed in `Ω`, lies in the
  support, and the singular support of a sum lies in the union of the singular supports.
* `Distribution.singSupport_ofFun_eq_empty`, `Distribution.singSupport_delta`: a smooth function
  has empty singular support, and the point mass at `x₀` has singular support `{x₀}`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Definition 2.2.3 and Proposition 8.1.3.
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
  -- Nested compact sets `tsupport ψ ⊆ K₁ ⊆ K₂ ⊆ Ω` and cutoffs `χ₁, χ₂` adapted to them.
  obtain ⟨K₁, hK₁, hψK₁, hK₁Ω⟩ :=
    exists_compact_between ψ.hasCompactSupport Ω.isOpen ψ.tsupport_subset
  obtain ⟨K₂, hK₂, hK₁K₂, hK₂Ω⟩ := exists_compact_between hK₁ Ω.isOpen hK₁Ω
  obtain ⟨χ₁, hχ₁, -, hχ₁1, -, hχ₁s⟩ :=
    ψ.hasCompactSupport.exists_contDiff_cutoff isOpen_interior hψK₁
  obtain ⟨χ₂, hχ₂, -, hχ₂1, -, hχ₂s⟩ := hK₁.exists_contDiff_cutoff isOpen_interior hK₁K₂
  let K : Compacts E := ⟨K₂, hK₂⟩
  have hKΩ : (K : Set E) ⊆ Ω := hK₂Ω
  have hχ₁ψ {x : E} (hx : ψ x ≠ 0) : χ₁ x = 1 := interior_subset (hχ₁1 (subset_tsupport _ hx))
  have hχ₂K₁ {x : E} (hx : x ∈ K₁) : χ₂ x = 1 := interior_subset (hχ₂1 hx)
  have hχ₁K₁ : tsupport χ₁ ⊆ K₁ := hχ₁s.trans interior_subset
  -- A lattice none of whose nonzero translates of `K₂` meet `K₂`.
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
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
  -- Expand `u = χ₁ φ`, a smooth function supported in `K₂`, in the modulations of `χ = χ₂`.
  have hu : ContDiff ℝ ∞ fun x ↦ (χ₁ x : ℂ) * φ x := (ofRealCLM.contDiff.comp hχ₁).mul φ.contDiff
  have huK : support (fun x ↦ (χ₁ x : ℂ) * φ x) ⊆ K₂ := fun x hx ↦
    interior_subset (hK₁K₂ (hχ₁K₁ (subset_tsupport _ (by simpa using left_ne_zero_of_mul hx))))
  have hχ₂c : ContDiff ℝ ∞ fun x ↦ (χ₂ x : ℂ) := ofRealCLM.contDiff.comp hχ₂
  have hχK : support (fun x ↦ (χ₂ x : ℂ)) ⊆ K₂ := fun x hx ↦
    interior_subset (hχ₂s (subset_tsupport _ (by simpa using hx)))
  let u : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hu huK
  let χ : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hχ₂c hχK
  have hχ : EqOn χ 1 (support u) := fun x hx ↦ by
    have hx' : χ₁ x ≠ 0 := by
      simpa [u, ContDiffMapSupportedIn.coe_of_support_subset] using left_ne_zero_of_mul hx
    simp [χ, ContDiffMapSupportedIn.coe_of_support_subset, hχ₂K₁ (hχ₁K₁ (subset_tsupport _ hx'))]
  have hexp := ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L u χ
    (fun x hx ℓ h ↦ Subtype.ext (hL x hx ℓ ℓ.2 h)) hχ
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
    · simp [TestFunction.bilinLeftCLM_apply, hθ, u, ContDiffMapSupportedIn.coe_of_support_subset,
        hχ₁ψ hx, mul_comm]
  have hψχ (x : E) : ψ x = ψ x * χ x := by
    by_cases hx : ψ x = 0
    · simp [hx]
    · simp [χ, ContDiffMapSupportedIn.coe_of_support_subset,
        hχ₂K₁ (interior_subset (hψK₁ (subset_tsupport _ hx)))]
  have h2 (m : ZLattice.dual L) (a : ℂ) : Λ (a • χ.modulate m) = a * F (-(m : E)) := by
    rw [map_smul, smul_eq_mul, ← hF, localFourier_eq_complexPairing_mul_modulate T hKΩ hψχ,
      neg_neg]
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
  -- The integral against the trigonometric series, computed term by term.
  have hint : ∫ x, φ x * ((χ₁ x : ℂ) * ∑' m, c m * TauCeti.fourierAtom (m : E) x) =
      ∑' m, c m * 𝓕 (u : E → ℂ) m := by
    have hG (m : ZLattice.dual L) : MeasureTheory.Integrable
        fun x ↦ u x * (c m * TauCeti.fourierAtom (m : E) x) :=
      (u.continuous.mul (continuous_const.mul (TauCeti.continuous_fourierAtom _)))
        |>.integrable_of_hasCompactSupport u.hasCompactSupport.mul_right
    have hnorm (m : ZLattice.dual L) :
        ∫ x, ‖u x * (c m * TauCeti.fourierAtom (m : E) x)‖ = ‖c m‖ * ∫ x, ‖u x‖ := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      ext x
      rw [norm_mul, norm_mul, TauCeti.norm_fourierAtom, mul_one, mul_comm]
    have hfun : (fun x ↦ φ x * ((χ₁ x : ℂ) * ∑' m, c m * TauCeti.fourierAtom (m : E) x)) =
        fun x ↦ ∑' m, u x * (c m * TauCeti.fourierAtom (m : E) x) := funext fun x ↦ by
      rw [tsum_mul_left]
      simp [u, ContDiffMapSupportedIn.coe_of_support_subset]
      ring
    rw [hfun, ← MeasureTheory.integral_tsum_of_summable_integral_norm hG
        (by simpa only [hnorm] using ((hcs 0).congr fun m ↦ by simp).mul_right _)]
    refine tsum_congr fun m ↦ ?_
    rw [Real.fourier_eq, ← MeasureTheory.integral_const_mul]
    congr 1
    ext x
    rw [TauCeti.fourierAtom_eq_fourierChar, Circle.smul_def, smul_eq_mul]
    ring
  rw [hint, ← h1, ← (hexp.map Λ Λ.continuous).tsum_eq]
  refine tsum_congr fun m ↦ ?_
  rw [Function.comp_apply, h2, hc]
  ring

/-! ### The singular support -/

/-- The **singular support** of a complex distribution `T` on `Ω`: the points `x ∈ Ω` having no
open neighbourhood `U` on which `T` is a smooth function, in the sense that `T φ = ∫ φ • f` for
every real test function `φ` supported in `U`, with `f` smooth on `U`. -/
def singSupport (T : 𝓓'(Ω, ℂ)) : Set E :=
  {x | x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y}

theorem mem_singSupport_iff {T : 𝓓'(Ω, ℂ)} {x : E} :
    x ∈ T.singSupport ↔ x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → ℂ,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- The singular support lies in `Ω`. -/
theorem singSupport_subset (T : 𝓓'(Ω, ℂ)) : T.singSupport ⊆ Ω := fun _ hx ↦ hx.1

/-- A point of an open set on which `T` is a smooth function lies outside the singular support. -/
theorem notMem_singSupport_of_apply_eq_integral {T : 𝓓'(Ω, ℂ)} {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (hT : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y) {x : E} (hx : x ∈ U) :
    x ∉ T.singSupport :=
  fun h ↦ h.2 ⟨U, hU, hx, f, hf, hT⟩

/-- The singular support is closed in `Ω`. -/
theorem isOpen_diff_singSupport (T : 𝓓'(Ω, ℂ)) : IsOpen ((Ω : Set E) \ T.singSupport) := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨hxΩ, hx⟩ ↦ ?_
  obtain ⟨U, hU, hxU, f, hf, hT⟩ := not_not.1 fun h ↦ hx ⟨hxΩ, h⟩
  filter_upwards [Ω.isOpen.mem_nhds hxΩ, hU.mem_nhds hxU] with y hyΩ hyU
  exact ⟨hyΩ, notMem_singSupport_of_apply_eq_integral hU hf hT hyU⟩

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
  · obtain ⟨U, hU, hxU, f, hf, hT⟩ := not_not.1 fun h' ↦ h ⟨hx, h'⟩
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
    exact ⟨hx, fun h ↦ hT ((notMem_singSupport_iff_forall_isMicrolocallySmoothAt hx).1
      (fun h' ↦ h'.2 h) ξ hξ)⟩
  · obtain ⟨ξ, hξ, hT⟩ := not_forall₂.1 fun h ↦
      (notMem_singSupport_iff_forall_isMicrolocallySmoothAt hx.1).2 h hx
    exact ⟨(x, ξ), mem_waveFrontSet_iff.2 ⟨hx.1, hξ, hT⟩, rfl⟩

/-- The wave front set is empty exactly when the singular support is. -/
theorem waveFrontSet_eq_empty_iff {T : 𝓓'(Ω, ℂ)} :
    T.waveFrontSet = ∅ ↔ T.singSupport = ∅ := by
  rw [← image_fst_waveFrontSet, image_eq_empty]

/-- The singular support lies in the support. -/
theorem singSupport_subset_dsupport (T : 𝓓'(Ω, ℂ)) : T.singSupport ⊆ dsupport T := by
  rw [← image_fst_waveFrontSet]
  rintro _ ⟨p, hp, rfl⟩
  exact (waveFrontSet_subset_dsupport T hp).1

/-- The singular support of a sum lies in the union of the singular supports. -/
theorem singSupport_add_subset (S T : 𝓓'(Ω, ℂ)) :
    (S + T).singSupport ⊆ S.singSupport ∪ T.singSupport := by
  simp only [← image_fst_waveFrontSet, ← image_union]
  exact image_mono (waveFrontSet_add_subset S T)

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
