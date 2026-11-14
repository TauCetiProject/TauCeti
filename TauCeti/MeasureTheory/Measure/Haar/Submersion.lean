/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.MeasureTheory.Measure.Haar.Differentiable

/-!
# Null preimages under submersions of finite-dimensional spaces

Let `E₀` and `E` be finite-dimensional real normed spaces with additive Haar measures `μ₀` and
`μ`. A map `θ : E₀ → E` that is a `C¹` submersion on a set `A`, in the chart normal form
`Manifold.IsSubmersionAt`, pulls `μ`-null sets back to sets whose intersection with `A` is
`μ₀`-null. The same holds on an open set `U` on which `θ` is `C¹` with surjective derivative,
since such a map has the normal form by the inverse function theorem. Neither injectivity nor
properness of `θ` is required, and the dimensions of `E₀` and `E` may differ.

In the normal form, `θ` reads as the linear surjection `u ↦ (L u).1` between charts which are
`C¹` diffeomorphisms of open sets. Chart images of null sets are null
(`DifferentiableOn.addHaar_image_eq_zero`), and the pushforward of a Haar measure under a linear
surjection is a multiple of a Haar measure (`LinearMap.exists_map_addHaar_eq_smul_addHaar`), so
it has the same null sets. Countably many normal-form charts cover `A`.

Consequently, almost-everywhere statements on an open set `Ω ⊆ E` pull back along `θ` to its
open domain `U` when `θ` maps `U` into `Ω`: the pushforward of `μ₀.restrict U` is absolutely
continuous with respect to `μ.restrict Ω`, and composition with `θ` preserves almost-everywhere
strong measurability. This is how local integrability classes pull back along submersions.

## Main results

* `TauCeti.addHaar_preimage_inter_eq_zero_of_isSubmersionAt`: a submersion in normal form at
  every point of `A` has `μ₀ (θ ⁻¹' s ∩ A) = 0` whenever `μ s = 0`.
* `ContDiffOn.addHaar_preimage_inter_eq_zero`: the same on an open set where `θ` is `C¹` with
  surjective derivative.
* `ContDiffOn.absolutelyContinuous_map_restrict`: the pushforward of `μ₀.restrict U` under such a
  map into `Ω` is absolutely continuous with respect to `μ.restrict Ω`.
* `MeasureTheory.AEStronglyMeasurable.comp_contDiffOn_of_surjective_fderiv`: precomposition with
  such a map preserves almost-everywhere strong measurability.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem for submersions) and Chapter 6 (sets of measure zero).
-/

public section

open MeasureTheory Measure Set Function Manifold
open scoped Manifold Topology ContDiff

variable {E₀ E : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [MeasurableSpace E₀] [BorelSpace E₀]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ₀ : Measure E₀} [μ₀.IsAddHaarMeasure] {μ : Measure E} [μ.IsAddHaarMeasure]
  {θ : E₀ → E} {n : WithTop ℕ∞} {s : Set E}

namespace TauCeti

/-- On the domain chart of a submersion in normal form, the preimage of a null set is null. -/
private theorem addHaar_preimage_inter_domChart_source_eq_zero {x : E₀}
    (h : IsSubmersionAt 𝓘(ℝ, E₀) 𝓘(ℝ, E) n θ x) (hn : 1 ≤ n) (hs : μ s = 0) :
    μ₀ (θ ⁻¹' s ∩ h.domChart.source) = 0 := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  set φ := h.domChart
  set ψ := h.codChart
  set P : E₀ →ₗ[ℝ] E := (LinearMap.fst ℝ E h.complement).comp h.equiv.toLinearMap
  have hP : Surjective P := fun y ↦ ⟨h.equiv.symm (y, 0), by simp [P]⟩
  have : FiniteDimensional ℝ E := Module.Finite.of_surjective P hP
  -- The charts of the normal form are `C¹` diffeomorphisms between open sets.
  have hφ : DifferentiableOn ℝ φ.symm φ.target :=
    (contMDiffOn_iff_contDiffOn.1 (contMDiffOn_symm_of_mem_maximalAtlas
      h.domChart_mem_maximalAtlas)).differentiableOn hn₀
  have hψ : DifferentiableOn ℝ ψ ψ.source :=
    (contMDiffOn_iff_contDiffOn.1 (contMDiffOn_of_mem_maximalAtlas
      h.codChart_mem_maximalAtlas)).differentiableOn hn₀
  -- The chart image of `s` is null, hence so is its preimage under the linear surjection `P`.
  obtain ⟨T, hTs, hT, hT0⟩ := exists_measurable_superset_of_null
    ((hψ.mono inter_subset_right).addHaar_image_eq_zero μ μ le_rfl
      (measure_mono_null inter_subset_left hs))
  have hPT : μ₀ (P ⁻¹' T) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem] at hT0 ⊢
    exact (ae_comp_linearMap_mem_iff P μ₀ μ hP hT.compl).2 hT0
  -- In the charts, the preimage of `s` lies in the `φ⁻¹`-image of `P ⁻¹' T`.
  refine measure_mono_null ?_ ((hφ.mono inter_subset_left).addHaar_image_eq_zero μ₀ μ₀ le_rfl
    (measure_mono_null inter_subset_right hPT))
  rintro z ⟨hzs, hzφ⟩
  refine ⟨φ z, ⟨φ.map_source hzφ, hTs ⟨θ z, ⟨hzs, h.source_subset_preimage_source hzφ⟩, ?_⟩⟩,
    φ.left_inv hzφ⟩
  have := h.writtenInCharts (show φ z ∈ (φ.extend 𝓘(ℝ, E₀)).target by
    simpa [OpenPartialHomeomorph.extend_target] using φ.map_source hzφ)
  simp only [comp_apply, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq] at this
  rw [φ.left_inv hzφ] at this
  simpa [P] using this

/-- **Submersions pull back null sets.** If `θ : E₀ → E` is a `C¹` submersion in normal form at
every point of `A`, then the preimage of a `μ`-null set meets `A` in a `μ₀`-null set. -/
theorem addHaar_preimage_inter_eq_zero_of_isSubmersionAt {A : Set E₀}
    (hθ : ∀ x ∈ A, IsSubmersionAt 𝓘(ℝ, E₀) 𝓘(ℝ, E) n θ x) (hn : 1 ≤ n) (hs : μ s = 0) :
    μ₀ (θ ⁻¹' s ∩ A) = 0 := by
  classical
  obtain ⟨t, htA, htc, hAt⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := A) (f := fun x ↦ if hx : x ∈ A then (hθ x hx).domChart.source else univ)
    fun x hx ↦ by
      simp only [hx, ↓reduceDIte]
      exact mem_nhdsWithin_of_mem_nhds
        ((hθ x hx).domChart.open_source.mem_nhds (hθ x hx).mem_domChart_source)
  refine measure_mono_null (inter_subset_inter_right _ hAt) ?_
  rw [inter_iUnion₂]
  refine (measure_biUnion_null_iff htc).2 fun x hx ↦ ?_
  simpa [htA hx] using addHaar_preimage_inter_domChart_source_eq_zero (hθ x (htA hx)) hn hs

end TauCeti

namespace ContDiffOn

variable {U : Set E₀}

/-- **`C¹` maps with surjective derivative pull back null sets.** If `θ` is `C¹` on an open set
`U` and its derivative is surjective at every point of `U`, then the preimage of a `μ`-null set
meets `U` in a `μ₀`-null set. -/
theorem addHaar_preimage_inter_eq_zero (hθ : ContDiffOn ℝ 1 θ U) (hU : IsOpen U)
    (hsurj : ∀ x ∈ U, Surjective (fderiv ℝ θ x)) (hs : μ s = 0) :
    μ₀ (θ ⁻¹' s ∩ U) = 0 := by
  refine TauCeti.addHaar_preimage_inter_eq_zero_of_isSubmersionAt (n := 1) (fun x hx ↦ ?_)
    le_rfl hs
  have : FiniteDimensional ℝ E :=
    Module.Finite.of_surjective (fderiv ℝ θ x : E₀ →ₗ[ℝ] E) (hsurj x hx)
  refine (ContMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv
    (contMDiffOn_iff_contDiffOn.2 hθ) hU hx le_rfl ?_).isSubmersionAt
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (NormedSpace.fromTangentSpace (θ x)).symm.surjective.comp
    ((hsurj x hx).comp (NormedSpace.fromTangentSpace x).surjective)

variable {Ω : Set E}

/-- If `θ` is `C¹` with surjective derivative on an open set `U` and maps `U` into `Ω`, then the
pushforward of `μ₀.restrict U` under `θ` is absolutely continuous with respect to
`μ.restrict Ω`. -/
theorem absolutelyContinuous_map_restrict (hθ : ContDiffOn ℝ 1 θ U) (hU : IsOpen U)
    (hsurj : ∀ x ∈ U, Surjective (fderiv ℝ θ x)) (hmaps : MapsTo θ U Ω) :
    (μ₀.restrict U).map θ ≪ μ.restrict Ω := by
  refine AbsolutelyContinuous.mk fun t ht ht0 ↦ ?_
  rw [restrict_apply ht] at ht0
  rw [map_apply_of_aemeasurable (hθ.continuousOn.aemeasurable hU.measurableSet) ht,
    restrict_apply' hU.measurableSet]
  have hnull : μ₀ (θ ⁻¹' (t ∩ Ω) ∩ U) = 0 := hθ.addHaar_preimage_inter_eq_zero hU hsurj ht0
  have hsub : θ ⁻¹' t ∩ U ⊆ θ ⁻¹' (t ∩ Ω) ∩ U := fun x hx ↦ ⟨⟨hx.1, hmaps hx.2⟩, hx.2⟩
  exact measure_mono_null hsub hnull

end ContDiffOn

namespace MeasureTheory.AEStronglyMeasurable

variable {F : Type*} [TopologicalSpace F] {u : E → F} {U : Set E₀} {Ω : Set E}

/-- Precomposition with a map that is `C¹` with surjective derivative on an open set `U` and maps
`U` into `Ω` carries functions almost everywhere strongly measurable on `Ω` to functions almost
everywhere strongly measurable on `U`. -/
theorem comp_contDiffOn_of_surjective_fderiv (hu : AEStronglyMeasurable u (μ.restrict Ω))
    (hθ : ContDiffOn ℝ 1 θ U) (hU : IsOpen U) (hsurj : ∀ x ∈ U, Surjective (fderiv ℝ θ x))
    (hmaps : MapsTo θ U Ω) :
    AEStronglyMeasurable (u ∘ θ) (μ₀.restrict U) :=
  (hu.mono_ac (hθ.absolutelyContinuous_map_restrict hU hsurj hmaps)).comp_aemeasurable
    (hθ.continuousOn.aemeasurable hU.measurableSet)

end MeasureTheory.AEStronglyMeasurable
