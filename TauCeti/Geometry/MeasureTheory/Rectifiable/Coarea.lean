/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Subspace
public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Calculus.ApproximatesLinearOn
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Countable rectifiability of fibres in the coarea setting

Let `E` and `F` be finite-dimensional real normed spaces of dimensions `n` and `m`. This file proves
the fibre-rectifiability statements accompanying the coarea formula:

* **Near a surjective linear map.** If `f` is approximated on `s` up to `δ` by a continuous linear
  map `L` with a continuous linear right inverse `M` satisfying `δ ‖M‖ < 1`, then every fibre
  `s ∩ f ⁻¹' {y}` is countably `(n - m)`-rectifiable: the straightening map from
  `TauCeti.Analysis.Calculus.ApproximatesLinearOn` exhibits `s ∩ f ⁻¹' {y}` as a Lipschitz image of
  a slice of the linear fibre `L ⁻¹' {y}`.
* **On the regular locus.** If `f` has a surjective derivative within `s` at every point of `s`,
  then every fibre `s ∩ f ⁻¹' {y}` is countably `(n - m)`-rectifiable, without any measurability or
  Lipschitz assumption on `s`.
* **Almost everywhere for Lipschitz and locally Lipschitz maps.** If `f : E → F` is locally
  Lipschitz on an arbitrary subset `s ⊆ E` (in particular, if `f` is `LipschitzOnWith`,
  `LipschitzWith`, or `LocallyLipschitz`), then for `μ`-almost every `y : F` the fibre
  `s ∩ f ⁻¹' {y}` is countably `(n - m)`-rectifiable, for every additive Haar measure `μ` on `F`.
  Neither openness nor measurability of `s`, nor an inner product on `E` or `F`, is required.

## The argument

To use the inner-product coarea theory of `TauCeti.MeasureTheory.Function.Coarea.Lipschitz`,
continuous linear equivalences first transport `E` and `F` to Euclidean spaces (preserving
countable rectifiability and additive-Haar-null sets). There,
`LipschitzOnWith.extend_finite_dimension` (Lipschitz extension into a finite-dimensional real normed
space, which enlarges the Lipschitz constant by a dimension-dependent factor) extends a map that is
Lipschitz on `s` to a globally Lipschitz map `g`. Splitting each fibre `g ⁻¹' {y}` into its regular
part—countably `(n - m)`-rectifiable for every `y`—and its complement—`μHE[n - m]`-null for almost
every `y` by
`LipschitzWith.ae_euclideanHausdorffMeasure_compl_setOf_regular_inter_preimage_eq_zero`—makes almost
every fibre of `g`, hence of `f` on `s`, countably `(n - m)`-rectifiable. Second countability then
extends the result to locally Lipschitz maps on arbitrary sets.

## Main statements

* `ApproximatesLinearOn.countablyRectifiable_inter_preimage`: every fibre of a map sufficiently
  well approximated by a linear map with a right inverse is countably `(dim E - dim F)`-rectifiable.
* `TauCeti.countablyRectifiable_inter_preimage_of_hasFDerivWithinAt`,
  `TauCeti.countablyRectifiable_inter_preimage_of_surjective_fderiv`: every fibre over a set with
  surjective derivative is countably `(dim E - dim F)`-rectifiable.
* `LipschitzOnWith.ae_countablyRectifiable_inter_preimage`: almost every fibre of a map Lipschitz on
  an arbitrary set is countably `(dim E - dim F)`-rectifiable.
* `LipschitzWith.ae_countablyRectifiable_preimage`,
  `LipschitzWith.ae_countablyRectifiable_inter_preimage`: almost every fibre of a Lipschitz map is
  countably `(dim E - dim F)`-rectifiable.
* `LocallyLipschitzOn.ae_countablyRectifiable_inter_preimage`,
  `LocallyLipschitz.ae_countablyRectifiable_preimage`: almost every fibre of a locally Lipschitz map
  is countably `(dim E - dim F)`-rectifiable.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 (rectifiability of level sets of Lipschitz maps).
* H. Federer, *Geometric Measure Theory*, Theorem 3.2.11 and Theorem 3.2.15.
-/

public section

open Filter Function MeasureTheory Measure Metric Module Set
open scoped NNReal Topology

/-! ### Deterministic rectifiability of regular fibres -/

namespace ApproximatesLinearOn

/-- If `f` is approximated on `s` up to `δ` by a continuous linear map `L` with a continuous linear
right inverse `M` satisfying `δ ‖M‖ < 1`, then every fibre `s ∩ f ⁻¹' {y}` is countably
`(dim E - dim F)`-rectifiable. -/
theorem countablyRectifiable_inter_preimage {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {L : E →L[ℝ] F} {M : F →L[ℝ] E}
    {s : Set E} {δ : ℝ≥0} (hf : ApproximatesLinearOn f L s δ) (hM : RightInverse M L)
    (hδ : δ * ‖M‖₊ < 1) (y : F) :
    TauCeti.CountablyRectifiable (finrank ℝ E - finrank ℝ F) (s ∩ f ⁻¹' {y}) := by
  obtain ⟨t, g, hg, hfib⟩ := hf.exists_lipschitzOnWith_eq_image_inter_preimage hM hδ
  rw [hfib y]
  exact ((L.toLinearMap.countablyRectifiable_preimage_singleton_of_surjective hM.surjective y).mono
    inter_subset_right).image (hg.mono inter_subset_left)

end ApproximatesLinearOn

namespace TauCeti

section Regular

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {f : E → F} {s : Set E}

/-- If `f` has a surjective derivative within `s` at every point of `s`, then every fibre
`s ∩ f ⁻¹' {y}` is countably `(dim E - dim F)`-rectifiable. Neither measurability of `s` nor a
Lipschitz hypothesis is needed. -/
theorem countablyRectifiable_inter_preimage_of_hasFDerivWithinAt {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hsurj : ∀ x ∈ s, Surjective (f' x)) (y : F) :
    CountablyRectifiable (finrank ℝ E - finrank ℝ F) (s ∩ f ⁻¹' {y}) := by
  have hA (A : E →L[ℝ] F) : ∃ (M : F →L[ℝ] E) (δ : ℝ≥0), 0 < δ ∧
      (Surjective A → RightInverse M A ∧ δ * ‖M‖₊ < 1) := by
    by_cases h : Surjective A
    · have hR : A.HasRightInverse := .of_surjective_of_finiteDimensional h
      have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * ‖hR.rightInverse‖₊ < 1 :=
        (continuous_id.mul continuous_const).continuousAt.tendsto.eventually_lt_const (by simp)
      obtain ⟨δ, hδM, hδ⟩ := (hsmall.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Ioi (0 : ℝ≥0))) |>.exists
      exact ⟨hR.rightInverse, δ, hδ, fun _ ↦ ⟨hR.rightInverse_rightInverse, hδM⟩⟩
    · exact ⟨0, 1, one_pos, fun h' ↦ (h h').elim⟩
  choose M δ hδpos hδ using hA
  obtain ⟨t, A, -, -, hcover, happrox, hAt⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hd δ fun A ↦ (hδpos A).ne'
  have hpiece (n : ℕ) :
      CountablyRectifiable (finrank ℝ E - finrank ℝ F) ((s ∩ t n) ∩ f ⁻¹' {y}) := by
    rcases (s ∩ t n).eq_empty_or_nonempty with hemp | ⟨x₀, hx₀⟩
    · simp [hemp]
    obtain ⟨x₁, hx₁, hAx₁⟩ := hAt ⟨x₀, hx₀.1⟩ n
    obtain ⟨hM, hδM⟩ := hδ (A n) (hAx₁ ▸ hsurj x₁ hx₁)
    exact (happrox n).countablyRectifiable_inter_preimage hM hδM y
  refine (CountablyRectifiable.iUnion hpiece).mono fun x ⟨hxs, hxy⟩ ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcover hxs)
  exact mem_iUnion.2 ⟨n, ⟨hxs, hn⟩, hxy⟩

/-- If `f` is differentiable at every point of `s` with surjective derivative, then every fibre
`s ∩ f ⁻¹' {y}` is countably `(dim E - dim F)`-rectifiable. -/
theorem countablyRectifiable_inter_preimage_of_surjective_fderiv
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) (y : F) :
    CountablyRectifiable (finrank ℝ E - finrank ℝ F) (s ∩ f ⁻¹' {y}) :=
  countablyRectifiable_inter_preimage_of_hasFDerivWithinAt
    (fun x hx ↦ (hd x hx).hasFDerivAt.hasFDerivWithinAt) hsurj y

end Regular

end TauCeti

/-! ### Almost-everywhere rectifiability of fibres of Lipschitz and locally Lipschitz maps -/

section InnerProduct

open TauCeti

/-- On finite-dimensional real inner product spaces, almost every fibre of a globally Lipschitz map
is countably `(dim E - dim F)`-rectifiable: the regular part is countably rectifiable on every
fibre, while its complement has `μHE[dim E - dim F]`-null fibre for almost every `y`. -/
private theorem ae_countablyRectifiable_preimage_of_innerProductSpace {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ y : F, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (f ⁻¹' {y}) := by
  let G := {x : E | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hreg (y : F) : CountablyRectifiable (finrank ℝ E - finrank ℝ F) (G ∩ f ⁻¹' {y}) :=
    countablyRectifiable_inter_preimage_of_surjective_fderiv
      (fun _ (hx : _ ∈ G) ↦ hx.1) (fun _ (hx : _ ∈ G) ↦ hx.2) y
  filter_upwards [hf.ae_euclideanHausdorffMeasure_compl_setOf_regular_inter_preimage_eq_zero]
    with y hy
  have hfib : f ⁻¹' {y} = (G ∩ f ⁻¹' {y}) ∪ (Gᶜ ∩ f ⁻¹' {y}) := by
    rw [← union_inter_distrib_right, union_compl_self, univ_inter]
  rw [hfib]
  exact (hreg y).union (.of_null hy)

end InnerProduct

namespace LipschitzOnWith

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- **Almost every fibre of a map Lipschitz on a set is countably rectifiable.** Let `E` and `F` be
finite-dimensional real normed spaces, `μ` an additive Haar measure on `F`, and `f : E → F`
Lipschitz on an arbitrary subset `s ⊆ E`. Then for `μ`-almost every `y : F`, the fibre
`s ∩ f ⁻¹' {y}` is countably `(dim E - dim F)`-rectifiable. No measurability of `s` is needed. -/
theorem ae_countablyRectifiable_inter_preimage {f : E → F} {s : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) :
    ∀ᵐ y ∂μ, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (s ∩ f ⁻¹' {y}) := by
  let E₀ := EuclideanSpace ℝ (Fin (finrank ℝ E))
  let F₀ := EuclideanSpace ℝ (Fin (finrank ℝ F))
  let eE : E ≃L[ℝ] E₀ :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  let eF : F ≃L[ℝ] F₀ :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  -- Transport `f` on `s` to `f₀` on `eE '' s ⊆ E₀` (to use the inner-product coarea theory), and
  -- extend `f₀` to a globally Lipschitz map `g₀ : E₀ → F₀`.
  let f₀ : E₀ → F₀ := eF ∘ f ∘ eE.symm
  have hf₀ : LipschitzOnWith (‖eF.toContinuousLinearMap‖₊ * (K * ‖eE.symm.toContinuousLinearMap‖₊))
      f₀ (eE '' s) := by
    refine eF.toContinuousLinearMap.lipschitzWith.comp_lipschitzOnWith ?_
    refine hf.comp eE.symm.toContinuousLinearMap.lipschitzWith.lipschitzOnWith ?_
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  obtain ⟨g₀, hg₀, hg₀_eq⟩ := hf₀.extend_finite_dimension
  have hae₀ : ∀ᵐ z : F₀, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (g₀ ⁻¹' {z}) := by
    simpa only [E₀, F₀, finrank_euclideanSpace_fin] using
      ae_countablyRectifiable_preimage_of_innerProductSpace hg₀
  -- Pull the almost-everywhere statement back along the linear isomorphism `eF`.
  have : (μ.map eF).IsAddHaarMeasure := eF.isAddHaarMeasure_map μ
  have hqmp : QuasiMeasurePreserving eF μ volume :=
    ⟨eF.continuous.measurable, absolutelyContinuous_isAddHaarMeasure (μ.map eF) volume⟩
  filter_upwards [hqmp.ae hae₀] with y hy
  -- Push `(eE '' s) ∩ g₀ ⁻¹' {eF y}` forward along the Lipschitz inverse `eE.symm`.
  have hsub : eE.symm '' (eE '' s ∩ g₀ ⁻¹' {eF y}) = s ∩ f ⁻¹' {y} := by
    ext x
    simp only [mem_image, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨u, ⟨⟨x', hx', rfl⟩, hgu⟩, rfl⟩
      have hfg : g₀ (eE x') = eF (f x') := by
        rw [← hg₀_eq ⟨x', hx', rfl⟩]
        simp [f₀]
      exact ⟨by simpa using hx', by simpa using eF.injective (hfg.symm.trans hgu)⟩
    · rintro ⟨hxs, rfl⟩
      refine ⟨eE x, ⟨⟨x, hxs, rfl⟩, ?_⟩, eE.symm_apply_apply x⟩
      rw [← hg₀_eq ⟨x, hxs, rfl⟩]
      simp [f₀]
  rw [← hsub]
  exact (hy.mono inter_subset_right).image
    eE.symm.toContinuousLinearMap.lipschitzWith.lipschitzOnWith

end LipschitzOnWith

namespace LipschitzWith

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- For a Lipschitz map between finite-dimensional real normed spaces and any subset `s ⊆ E`,
almost every fibre `s ∩ f ⁻¹' {y}` is countably `(dim E - dim F)`-rectifiable. -/
theorem ae_countablyRectifiable_inter_preimage {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    (s : Set E) :
    ∀ᵐ y ∂μ, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (s ∩ f ⁻¹' {y}) :=
  hf.lipschitzOnWith.ae_countablyRectifiable_inter_preimage μ

/-- **Almost every fibre of a Lipschitz map is countably `(dim E - dim F)`-rectifiable.** -/
theorem ae_countablyRectifiable_preimage {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ y ∂μ, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (f ⁻¹' {y}) := by
  simpa only [univ_inter] using hf.ae_countablyRectifiable_inter_preimage μ univ

end LipschitzWith

namespace LocallyLipschitzOn

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- **Almost every fibre of a map locally Lipschitz on a set is countably rectifiable.** Neither
openness nor measurability of `s` is required. -/
theorem ae_countablyRectifiable_inter_preimage {f : E → F} {s : Set E}
    (hf : LocallyLipschitzOn s f) :
    ∀ᵐ y ∂μ, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (s ∩ f ⁻¹' {y}) := by
  obtain ⟨U, K, -, hcov, hK⟩ := hf.exists_open_cover_lipschitzOnWith
  filter_upwards [ae_all_iff.2 fun n ↦ (hK n).ae_countablyRectifiable_inter_preimage μ] with y hy
  refine (CountablyRectifiable.iUnion hy).mono fun z ⟨hzs, hzy⟩ ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hzs)
  exact mem_iUnion.2 ⟨n, ⟨hzs, hn⟩, hzy⟩

end LocallyLipschitzOn

namespace LocallyLipschitz

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- For a locally Lipschitz map between finite-dimensional real normed spaces and any subset
`s ⊆ E`, almost every fibre `s ∩ f ⁻¹' {y}` is countably `(dim E - dim F)`-rectifiable. -/
theorem ae_countablyRectifiable_inter_preimage {f : E → F} (hf : LocallyLipschitz f) (s : Set E) :
    ∀ᵐ y ∂μ, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (s ∩ f ⁻¹' {y}) :=
  hf.locallyLipschitzOn.ae_countablyRectifiable_inter_preimage μ

/-- **Almost every fibre of a locally Lipschitz map is countably `(dim E - dim F)`-rectifiable.** -/
theorem ae_countablyRectifiable_preimage {f : E → F} (hf : LocallyLipschitz f) :
    ∀ᵐ y ∂μ, CountablyRectifiable (finrank ℝ E - finrank ℝ F) (f ⁻¹' {y}) := by
  simpa only [univ_inter] using hf.ae_countablyRectifiable_inter_preimage μ univ

end LocallyLipschitz

end
