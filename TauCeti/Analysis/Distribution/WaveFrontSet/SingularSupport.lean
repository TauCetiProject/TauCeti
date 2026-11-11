/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.Algebra.Module.ZLattice.Dual
public import TauCeti.Analysis.Distribution.SingularSupport
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The wave front set lies over the singular support

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner
product space `E`. The projection of its wave front set to the base is exactly its singular
support (Hörmander I, Proposition 8.1.3):

`Prod.fst '' WF(T) = singsupp T`.

So the wave front set refines the singular support: over a point `x` it records the directions
in which `T` fails to be smooth at `x`, and it is nonempty exactly over the points near which `T`
is not a smooth function.

Over a point near which `T` is smooth there is no wave front set, by
`Distribution.isMicrolocallySmoothAt_of_apply_eq_integral`. The converse is the content of this
file. If `T` is microlocally smooth at `(x, ξ)` for every `ξ ≠ 0`, then the open cones of rapid
decay supplied by `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone` cover the unit sphere,
and finitely many of them suffice. So for every cutoff `φ` supported near `x`, the localized
Fourier transform `η ↦ T (φ e_η)` decays rapidly in *all* directions
(`Distribution.exists_nhds_forall_decay`). Fourier inversion then shows that `φ T` is a smooth
function (`Distribution.exists_contDiff_complexPairing_eq_integral`), and so is `T` wherever
`φ = 1`.

## Main results

* `Distribution.exists_hasSum_complexPairing`: the pairing of `φ T` with a test function `ψ` as
  a Fourier series in the localized Fourier transform of `T`.
* `Distribution.exists_contDiff_complexPairing_eq_integral`: if the localized Fourier transform
  of `T` with cutoff `φ` decays rapidly on all of `E`, then `φ T` is a smooth function.
* `Distribution.exists_nhds_forall_decay`: if `T` is microlocally smooth at `x` in every nonzero
  direction, then every cutoff supported in a fixed neighbourhood of `x` has rapidly decreasing
  localized Fourier transform.
* `Distribution.fst_image_waveFrontSet`: the projection of the wave front set is the singular
  support.
* `Distribution.singularSupport_eq_empty_iff`: a distribution has empty singular support exactly
  when it has empty wave front set.
* `Distribution.singularSupport_delta`: in positive dimension the point mass at `x₀` has singular
  support `{x₀}`.

## Implementation notes

Fourier inversion for `φ T` is done with a Fourier *series* rather than the Fourier integral, so
that the distribution is only ever applied to test functions. On a compact set `K` around the
support of `φ` that meets none of its nonzero translates by a lattice `L`, the product `χ ψ` of a
test function `ψ` with a cutoff `χ` equal to one near the support of `φ` is the sum of its Fourier
series along the dual lattice `L^∨`, in the topology of test functions supported in `K`
(`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`). Pairing with `φ T` turns the modes into
values `(φ T)^(-m)` of the localized Fourier transform, so

`T (φ ψ) = (covolume L)⁻¹ ∑ m : L^∨, 𝓕 (χ ψ) (m) (φ T)^(-m) = ∫ ψ χ g`,

with `g y = (covolume L)⁻¹ ∑ m, (φ T)^(-m) exp (-2πi ⟪y, m⟫)`. Since `(φ T)^` decays rapidly,
the series for `g` converges with all its derivatives, so `g` is smooth.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Proposition 8.1.3.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- **Fourier series of a localized distribution.** For a cutoff `φ` there are a full lattice `L`
and a smooth function `χ`, equal to one where `φ ≠ 0`, such that for every complex test function
`ψ` the localized distribution `φ T` is paired with `ψ` by the Fourier series

`T (ψ φ) = (covolume L)⁻¹ ∑ m : L^∨, (φ T)^(-m) 𝓕 (χ ψ) (m)`.

Here `(φ T)^(η) = T (φ e_η)` is the localized Fourier transform. The lattice is chosen so that a
compact neighbourhood of the support of `φ` meets none of its nonzero translates, and `χ ψ` is
expanded in its Fourier series on that neighbourhood. -/
theorem exists_hasSum_complexPairing (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (L : Submodule ℤ E) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L) (χ : E → ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ x, φ x ≠ 0 → χ x = 1) ∧ ∀ ψ : 𝓓(Ω, ℂ),
        HasSum (fun m : ZLattice.dual L ↦ (ZLattice.covolume L : ℂ)⁻¹ * T.localFourier φ (-m) *
          𝓕 (fun y ↦ (χ y : ℂ) * ψ y) m)
          (T.complexPairing (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff ψ)) := by
  -- Nested compact sets `tsupport φ ⊆ K₁ ⊆ K₂ ⊆ Ω` and cutoffs `χ₁, χ₂` adapted to them.
  obtain ⟨K₁, hK₁, hφK₁, hK₁Ω⟩ :=
    exists_compact_between φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  obtain ⟨K₂, hK₂, hK₁K₂, hK₂Ω⟩ := exists_compact_between hK₁ Ω.isOpen hK₁Ω
  obtain ⟨χ₁, hχ₁, -, hχ₁1, -, hχ₁s⟩ :=
    φ.hasCompactSupport.exists_contDiff_cutoff isOpen_interior hφK₁
  obtain ⟨χ₂, hχ₂, -, hχ₂1, -, hχ₂s⟩ := hK₁.exists_contDiff_cutoff isOpen_interior hK₁K₂
  let K : Compacts E := ⟨K₂, hK₂⟩
  have hKΩ : (K : Set E) ⊆ Ω := hK₂Ω
  have hχ₁φ {x : E} (hx : φ x ≠ 0) : χ₁ x = 1 := interior_subset (hχ₁1 (subset_tsupport _ hx))
  have hχ₂K₁ {x : E} (hx : x ∈ K₁) : χ₂ x = 1 := interior_subset (hχ₂1 hx)
  have hχ₁K₁ : tsupport χ₁ ⊆ K₁ := hχ₁s.trans interior_subset
  have hχ₁c : ContDiff ℝ ∞ fun x ↦ (χ₁ x : ℂ) := ofRealCLM.contDiff.comp hχ₁
  have hχK : support (fun x ↦ (χ₂ x : ℂ)) ⊆ K₂ := fun x hx ↦
    interior_subset (hχ₂s (subset_tsupport _ (by simpa using hx)))
  let χ : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset (ofRealCLM.contDiff.comp hχ₂) hχK
  have hχv (x : E) : χ x = χ₂ x :=
    ContDiffMapSupportedIn.coe_of_support_subset (K := K) (ofRealCLM.contDiff.comp hχ₂) hχK x
  -- A lattice none of whose nonzero translates of `K` meet `K`.
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
  refine ⟨L, inferInstance, inferInstance, χ₁, hχ₁, fun x hx ↦ hχ₁φ hx, fun ψ ↦ ?_⟩
  -- The test function `χ₁ ψ`, supported in `K`, which agrees with `ψ` near the support of `φ`.
  have hfK : support (fun x ↦ (χ₁ x : ℂ) * ψ x) ⊆ K₂ := fun x hx ↦
    interior_subset (hK₁K₂ (hχ₁K₁ (subset_tsupport _ (by simpa using left_ne_zero_of_mul hx))))
  let f : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset (hχ₁c.mul ψ.contDiff) hfK
  have hf : (f : E → ℂ) = fun x ↦ (χ₁ x : ℂ) * ψ x :=
    funext (ContDiffMapSupportedIn.coe_of_support_subset (K := K) (hχ₁c.mul ψ.contDiff) hfK)
  have hχ : EqOn χ 1 (support f) := fun x hx ↦ by
    rw [mem_support, hf] at hx
    have hx' : χ₁ x ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hx
    simp [hχv, hχ₂K₁ (hχ₁K₁ (subset_tsupport _ hx'))]
  -- Pair the Fourier expansion of `f` with `φ T`; its modes give the localized Fourier transform.
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L
    (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff ∘L ofSupportedInCLM ℂ hKΩ)
  have hΛ (k : 𝓓_{K}(E, ℂ)) : Λ k = T.complexPairing
      (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff (ofSupportedIn hKΩ k)) := by
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
  have h1 : Λ f = T.complexPairing (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff ψ) := by
    rw [hΛ]
    congr 1
    ext x
    by_cases hx : φ x = 0
    · simp [bilinLeftCLM_apply, hx]
    · simp [bilinLeftCLM_apply, hf, hχ₁φ hx]
  have h2 (m : ZLattice.dual L) : Λ (χ.modulate m) = T.localFourier φ (-m) := by
    rw [hΛ, localFourier_eq_complexPairing_mul_modulate T hKΩ (φ := φ) (ψ := φ) (f := χ)
      (fun x ↦ ?_) (-m), neg_neg]
    by_cases hx : φ x = 0
    · simp [hx]
    · simp [hχv, hχ₂K₁ (hφK₁.trans interior_subset (subset_tsupport _ hx))]
  have hmap := (ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L f χ
    (fun x hx ℓ h ↦ Subtype.ext (hL x hx ℓ ℓ.2 h)) hχ).map Λ Λ.continuous
  rw [h1] at hmap
  convert hmap using 1
  ext m
  simp only [comp_apply, map_smul, smul_eq_mul, h2, hf]
  ring

/-- **Fourier inversion for a localized distribution.** If the localized Fourier transform
`η ↦ T (φ e_η)` of `T` with cutoff `φ` decays rapidly on all of `E`, then the compactly
supported distribution `φ T` is a smooth function `f`: `T (ψ φ) = ∫ ψ f` for every complex test
function `ψ`. -/
theorem exists_contDiff_complexPairing_eq_integral (T : 𝓓'(Ω, ℂ)) {φ : 𝓓(Ω, ℂ)}
    (h : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C) :
    ∃ f : E → ℂ, ContDiff ℝ ∞ f ∧ ∀ ψ : 𝓓(Ω, ℂ),
      T.complexPairing (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff ψ) =
        ∫ y, ψ y * f y := by
  obtain ⟨L, _, _, χ, hχ, -, hsum⟩ := exists_hasSum_complexPairing T φ
  have hχc : ContDiff ℝ ∞ fun x ↦ (χ x : ℂ) := ofRealCLM.contDiff.comp hχ
  -- The coefficients `c m = (covolume L)⁻¹ (φ T)^(-m)` decay rapidly along the dual lattice.
  set c : ZLattice.dual L → ℂ := fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * T.localFourier φ (-m)
  have hdecay (k : ℕ) : Summable fun m : ZLattice.dual L ↦ (1 + ‖(m : E)‖) ^ k * ‖c m‖ := by
    have hF := ZLattice.summable_one_add_norm_pow_mul_norm_of_decay (ZLattice.dual L)
      (g := fun η ↦ T.localFourier φ (-η)) (fun N ↦ (h N).imp fun C hC η ↦ by
        simpa using hC (-η)) k
    refine (hF.mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖).congr fun m ↦ ?_
    simp only [c, norm_mul]
    ring
  -- `φ T` is `χ g` for the smooth function `g y = ∑ m, c m exp (-2πi ⟪y, m⟫)`.
  set u : ZLattice.dual L → E → ℂ := fun m y ↦ c m * TauCeti.fourierAtom (m : E) y
  refine ⟨fun y ↦ (χ y : ℂ) * ∑' m, u m y,
    hχc.mul (TauCeti.contDiff_tsum_mul_fourierAtom hdecay), fun ψ ↦ (hsum ψ).unique ?_⟩
  -- Integrate the series for `g` against `χ ψ` term by term.
  set f : E → ℂ := fun y ↦ (χ y : ℂ) * ψ y
  have hfi : MeasureTheory.Integrable f :=
    (hχc.continuous.mul ψ.continuous).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_left
  have hint (m : ZLattice.dual L) : MeasureTheory.Integrable fun y ↦ f y * u m y :=
    hfi.mul_bdd (continuous_const.mul (TauCeti.continuous_fourierAtom _)).aestronglyMeasurable
      (.of_forall fun y ↦ by
        simp only [u, norm_mul, TauCeti.norm_fourierAtom, mul_one, le_refl] :
          ∀ᵐ y, ‖u m y‖ ≤ ‖c m‖)
  have hnorm (m : ZLattice.dual L) : ∫ y, ‖f y * u m y‖ = ‖c m‖ * ∫ y, ‖f y‖ := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext y
    simp only [u, norm_mul, TauCeti.norm_fourierAtom]
    ring
  have hI := MeasureTheory.hasSum_integral_of_summable_integral_norm hint
    (((hdecay 0).mul_right (∫ y, ‖f y‖)).congr fun m ↦ by rw [hnorm, pow_zero, one_mul])
  convert hI using 1
  · ext m
    rw [Real.fourier_eq, ← MeasureTheory.integral_const_mul]
    congr 1
    ext y
    simp only [u, c, TauCeti.fourierAtom_eq_fourierChar, Circle.smul_def, smul_eq_mul]
    ring
  · congr 1
    ext y
    simp only [u, f, tsum_mul_left]
    ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Decay in every direction.** If `T` is microlocally smooth at `x` in every nonzero direction,
then there is a neighbourhood `U` of `x` such that for every test function `ψ` supported in `U`
the localized Fourier transform of `T` with cutoff `ψ` decays rapidly on all of `E`. -/
theorem exists_nhds_forall_decay {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : ∀ ξ : E, ξ ≠ 0 → T.IsMicrolocallySmoothAt x ξ) :
    ∃ U ∈ 𝓝 x, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  -- Cones of rapid decay around the points of the unit sphere, and finitely many covering it.
  choose U hU Γ hΓ hξΓ hcone hdecay using fun ξ : sphere (0 : E) 1 ↦
    (h ξ (ne_zero_of_mem_unit_sphere ξ)).exists_nhds_cone
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover Γ hΓ
    fun ξ hξ ↦ mem_iUnion.2 ⟨⟨ξ, hξ⟩, hξΓ _⟩
  refine ⟨⋂ i ∈ t, U i, (biInter_finset_mem t).2 fun i _ ↦ hU i, fun ψ hψ N ↦ ?_⟩
  choose C hC using fun i : t ↦ hdecay i ψ (hψ.trans (biInter_subset_of_mem i.2)) N
  refine ⟨‖T.localFourier ψ 0‖ + ∑ i, |C i|, fun η ↦ ?_⟩
  have hnonneg : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  rcases eq_or_ne η 0 with rfl | hη
  · simpa using hnonneg
  -- The direction of `η` lies in one of the covering cones, and so does `η`.
  have hη' : 0 < ‖η‖ := norm_pos_iff.2 hη
  obtain ⟨i, hi, hηi⟩ := mem_iUnion₂.1 (ht (show ‖η‖⁻¹ • η ∈ sphere (0 : E) 1 by
    simp [norm_smul, hη'.ne']))
  have hmem : η ∈ Γ i := by
    simpa [smul_smul, hη'.ne'] using hcone i ‖η‖ hη' _ hηi
  calc (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ |C ⟨i, hi⟩| := (hC ⟨i, hi⟩ η hmem).trans
        (le_abs_self _)
    _ ≤ ∑ j, |C j| := Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ _)
    _ ≤ ‖T.localFourier ψ 0‖ + ∑ j, |C j| := le_add_of_nonneg_left (norm_nonneg _)

/-- **The wave front set lies over the singular support** (Hörmander I, Proposition 8.1.3): its
projection to the base is exactly the singular support. -/
theorem fst_image_waveFrontSet (T : 𝓓'(Ω, ℂ)) : Prod.fst '' T.waveFrontSet = T.singularSupport := by
  ext x
  refine ⟨fun ⟨⟨y, ξ⟩, hyξ, hyx⟩ ↦ ?_, fun hx ↦ ?_⟩
  · -- Over a point near which `T` is smooth, `T` is microlocally smooth in every direction.
    subst hyx
    obtain ⟨hy, -, hT⟩ := mem_waveFrontSet_iff.1 hyξ
    refine mem_singularSupport_iff.2 ⟨hy, fun ⟨U, hU, hyU, f, hf, hTf⟩ ↦ hT ?_⟩
    exact isMicrolocallySmoothAt_of_apply_eq_integral hU hf hTf hyU hy ξ
  · obtain ⟨hxΩ, hx⟩ := mem_singularSupport_iff.1 hx
    by_contra hWF
    have hsmooth (ξ : E) (hξ : ξ ≠ 0) : T.IsMicrolocallySmoothAt x ξ :=
      by_contra fun hT ↦ hWF ⟨(x, ξ), mem_waveFrontSet_iff.2 ⟨hxΩ, hξ, hT⟩, rfl⟩
    obtain ⟨U, hU, hdecay⟩ := exists_nhds_forall_decay hsmooth
    -- A real cutoff `θ`, supported in `U ∩ Ω` and equal to one near `x`.
    obtain ⟨θ, hθ, -, hθ1, hθc, hθs⟩ := (isCompact_singleton (x := x)).exists_contDiff_cutoff
      isOpen_interior (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 (inter_mem hU
        (Ω.isOpen.mem_nhds hxΩ))))
    have hθU : tsupport θ ⊆ U ∩ Ω := hθs.trans interior_subset
    have hθc' : ContDiff ℝ ∞ fun y ↦ (θ y : ℂ) := ofRealCLM.contDiff.comp hθ
    have hθt : tsupport (fun y ↦ (θ y : ℂ)) = tsupport θ := tsupport_comp_eq ofReal_eq_zero θ
    let φ : 𝓓(Ω, ℂ) := ⟨fun y ↦ (θ y : ℂ), hθc', by simpa [HasCompactSupport, hθt] using hθc,
      by simpa [hθt] using hθU.trans inter_subset_right⟩
    -- `φ T` is a smooth function `f`, and so is `T` where `θ = 1`.
    obtain ⟨f, hf, hTf⟩ := exists_contDiff_complexPairing_eq_integral T (φ := φ)
      (hdecay φ (by simpa [φ, hθt] using hθU.trans inter_subset_left))
    refine hx ⟨interior (θ ⁻¹' {1}), isOpen_interior, hθ1 rfl, f, hf.contDiffOn,
      fun ψ hψ ↦ ?_⟩
    have hψφ : bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff
        (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) = postcompCLM (𝕜 := ℝ) ofRealCLM ψ := by
      ext y
      by_cases hy : y ∈ tsupport ψ
      · have hθy : θ y = 1 := interior_subset (hψ hy)
        simp [bilinLeftCLM_apply, φ, hθy]
      · simp [bilinLeftCLM_apply, image_eq_zero_of_notMem_tsupport hy]
    rw [← complexPairing_postcompCLM_ofRealCLM, ← hψφ, hTf]
    simp [Complex.real_smul]

/-- A distribution has empty singular support exactly when it has empty wave front set. -/
theorem singularSupport_eq_empty_iff {T : 𝓓'(Ω, ℂ)} :
    T.singularSupport = ∅ ↔ T.waveFrontSet = ∅ := by
  rw [← fst_image_waveFrontSet, image_eq_empty]

/-- In positive dimension, the point mass at `x₀ ∈ Ω` has singular support `{x₀}`. -/
theorem singularSupport_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).singularSupport = {x₀} := by
  rw [← fst_image_waveFrontSet, waveFrontSet_delta hx₀,
    fst_image_prod _ (nonempty_compl_of_nontrivial 0)]

end Distribution
