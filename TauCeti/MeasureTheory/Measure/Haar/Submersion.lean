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
`μ₀`-null. The same holds on a set at each point of which `θ` is `C¹` with surjective derivative,
since such a map has the normal form there by the inverse function theorem
(`ContDiffAt.isSubmersionAt_of_surjective_fderiv`). Neither injectivity nor properness of `θ` is
required, and the dimensions of `E₀` and `E` may differ.

In the normal form, `θ` reads as the linear surjection
`Manifold.IsSubmersionAtOfComplement.projection` between charts which are `C¹` diffeomorphisms
of open sets. Chart images of null sets are null (`DifferentiableOn.addHaar_image_eq_zero`), and
the pushforward of a Haar measure under a linear surjection is a multiple of a Haar measure
(`LinearMap.exists_map_addHaar_eq_smul_addHaar`), so it has the same null sets.
Countably many normal-form charts cover `A`.

Consequently, when `θ` maps `A` into `Ω`, it is quasi-measure-preserving from `μ₀.restrict A` to
`μ.restrict Ω`, so almost-everywhere statements on `Ω` pull back along `θ` to `A`, and composition
with `θ` preserves almost-everywhere strong measurability. This is how local integrability classes
pull back along submersions.

## Main results

* `TauCeti.addHaar_preimage_inter_eq_zero_of_isSubmersionAt`: a submersion in normal form at
  every point of `A` has `μ₀ (θ ⁻¹' s ∩ A) = 0` whenever `μ s = 0`.
* `TauCeti.quasiMeasurePreserving_restrict_of_isSubmersionAt`: such a map from a set `A` into `Ω`
  is quasi-measure-preserving from `μ₀.restrict A` to `μ.restrict Ω`.
* `TauCeti.addHaar_preimage_inter_eq_zero_of_surjective_fderiv`,
  `TauCeti.quasiMeasurePreserving_restrict_of_surjective_fderiv`: the same for a map that is `C¹`
  with surjective derivative at every point of `A`.
* `ContDiffOn.addHaar_preimage_inter_eq_zero_of_surjective_fderiv`,
  `ContDiffOn.quasiMeasurePreserving_restrict_of_surjective_fderiv`: the same on an open set where
  `θ` is `C¹` with surjective derivative.
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
  {θ : E₀ → E} {n : WithTop ℕ∞} {s : Set E} {A : Set E₀} {Ω : Set E}

namespace TauCeti

/-- On the domain chart of a submersion in normal form, the preimage of a null set is null. -/
private theorem addHaar_preimage_inter_domChart_source_eq_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {x : E₀}
    (h : IsSubmersionAtOfComplement F 𝓘(ℝ, E₀) 𝓘(ℝ, E) n θ x) (hn : 1 ≤ n) (hs : μ s = 0) :
    μ₀ (θ ⁻¹' s ∩ h.domChart.source) = 0 := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  set φ := h.domChart
  set ψ := h.codChart
  set P : E₀ →ₗ[ℝ] E := h.projection.toLinearMap
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
  simpa [OpenPartialHomeomorph.extend_coe, φ, ψ, P] using h.codChart_extend_apply hzφ

variable (μ₀) in
/-- **Submersions pull back null sets.** If `θ : E₀ → E` is a `C¹` submersion in normal form at
every point of `A`, then the preimage of a `μ`-null set meets `A` in a `μ₀`-null set. -/
theorem addHaar_preimage_inter_eq_zero_of_isSubmersionAt
    (hθ : ∀ x ∈ A, IsSubmersionAt 𝓘(ℝ, E₀) 𝓘(ℝ, E) n θ x) (hn : 1 ≤ n) (hs : μ s = 0) :
    μ₀ (θ ⁻¹' s ∩ A) = 0 := by
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  let h := (hθ x hx.2).isSubmersionAtOfComplement_complement
  refine ⟨θ ⁻¹' s ∩ h.domChart.source, ?_,
    addHaar_preimage_inter_domChart_source_eq_zero (μ₀ := μ₀) h hn hs⟩
  exact Filter.mem_of_superset
    (inter_mem_nhdsWithin _ (h.domChart.open_source.mem_nhds h.mem_domChart_source))
    (fun y hy ↦ ⟨hy.1.1, hy.2⟩)

variable (μ₀ μ) in
/-- If `θ` is a `C¹` submersion in normal form at every point of a set `A` and maps
`A` into `Ω`, then `θ` is quasi-measure-preserving from `μ₀.restrict A` to `μ.restrict Ω`. -/
theorem quasiMeasurePreserving_restrict_of_isSubmersionAt
    (hθ : ∀ x ∈ A, IsSubmersionAt 𝓘(ℝ, E₀) 𝓘(ℝ, E) n θ x) (hn : 1 ≤ n)
    (hmaps : MapsTo θ A Ω) :
    QuasiMeasurePreserving θ (μ₀.restrict A) (μ.restrict Ω) := by
  -- The open submersion locus is a measurable neighbourhood of `A` on which `θ` is continuous.
  let U := {x | IsSubmersionAt 𝓘(ℝ, E₀) 𝓘(ℝ, E) n θ x}
  have hU : IsOpen U := isOpen_isSubmersionAt
  have hθU : ContinuousOn θ U := fun x hx ↦
    hx.contMDiffAt.continuousAt.continuousWithinAt
  have hθm : AEMeasurable θ (μ₀.restrict A) :=
    AEMeasurable.mono_set (t := U) hθ (hθU.aemeasurable hU.measurableSet)
  refine ⟨hθm, AbsolutelyContinuous.mk fun t ht ht0 ↦ ?_⟩
  rw [restrict_apply ht] at ht0
  rw [map_apply_of_aemeasurable hθm ht, restrict_apply₀ (hθm.nullMeasurable ht)]
  have hsub : θ ⁻¹' t ∩ A ⊆ θ ⁻¹' (t ∩ Ω) ∩ A := fun x hx ↦ ⟨⟨hx.1, hmaps hx.2⟩, hx.2⟩
  exact measure_mono_null hsub (addHaar_preimage_inter_eq_zero_of_isSubmersionAt μ₀ hθ hn ht0)

variable (μ₀) in
/-- **`C¹` maps with surjective derivative pull back null sets.** If `θ` is `C¹` at every point of
`A` with surjective derivative there, then the preimage of a `μ`-null set meets `A` in a
`μ₀`-null set. -/
theorem addHaar_preimage_inter_eq_zero_of_surjective_fderiv (hθ : ∀ x ∈ A, ContDiffAt ℝ 1 θ x)
    (hsurj : ∀ x ∈ A, Surjective (fderiv ℝ θ x)) (hs : μ s = 0) :
    μ₀ (θ ⁻¹' s ∩ A) = 0 :=
  addHaar_preimage_inter_eq_zero_of_isSubmersionAt μ₀
    (fun x hx ↦ (hθ x hx).isSubmersionAt_of_surjective_fderiv (hsurj x hx)) le_rfl hs

variable (μ₀ μ) in
/-- If `θ` is `C¹` with surjective derivative at every point of a set `A` and maps
`A` into `Ω`, then `θ` is quasi-measure-preserving from `μ₀.restrict A` to `μ.restrict Ω`. -/
theorem quasiMeasurePreserving_restrict_of_surjective_fderiv (hθ : ∀ x ∈ A, ContDiffAt ℝ 1 θ x)
    (hsurj : ∀ x ∈ A, Surjective (fderiv ℝ θ x))
    (hmaps : MapsTo θ A Ω) : QuasiMeasurePreserving θ (μ₀.restrict A) (μ.restrict Ω) :=
  quasiMeasurePreserving_restrict_of_isSubmersionAt μ₀ μ
    (fun x hx ↦ (hθ x hx).isSubmersionAt_of_surjective_fderiv (hsurj x hx)) le_rfl hmaps

end TauCeti

namespace ContDiffOn

variable {U : Set E₀}

variable (μ₀) in
/-- **`C¹` maps with surjective derivative pull back null sets.** If `θ` is `C¹` on an open set
`U` and its derivative is surjective at every point of `U`, then the preimage of a `μ`-null set
meets `U` in a `μ₀`-null set. -/
theorem addHaar_preimage_inter_eq_zero_of_surjective_fderiv (hθ : ContDiffOn ℝ 1 θ U)
    (hU : IsOpen U) (hsurj : ∀ x ∈ U, Surjective (fderiv ℝ θ x)) (hs : μ s = 0) :
    μ₀ (θ ⁻¹' s ∩ U) = 0 :=
  TauCeti.addHaar_preimage_inter_eq_zero_of_surjective_fderiv μ₀
    (fun _ hx ↦ hθ.contDiffAt (hU.mem_nhds hx)) hsurj hs

variable (μ₀ μ) in
/-- If `θ` is `C¹` with surjective derivative on an open set `U` and maps `U` into `Ω`, then `θ` is
quasi-measure-preserving from `μ₀.restrict U` to `μ.restrict Ω`. -/
theorem quasiMeasurePreserving_restrict_of_surjective_fderiv (hθ : ContDiffOn ℝ 1 θ U)
    (hU : IsOpen U) (hsurj : ∀ x ∈ U, Surjective (fderiv ℝ θ x)) (hmaps : MapsTo θ U Ω) :
    QuasiMeasurePreserving θ (μ₀.restrict U) (μ.restrict Ω) :=
  TauCeti.quasiMeasurePreserving_restrict_of_surjective_fderiv μ₀ μ
    (fun _ hx ↦ hθ.contDiffAt (hU.mem_nhds hx)) hsurj hmaps

end ContDiffOn

namespace MeasureTheory.AEStronglyMeasurable

variable {F : Type*} [TopologicalSpace F] {u : E → F} {U : Set E₀}

variable (μ₀) in
/-- Precomposition with a map that is `C¹` with surjective derivative on an open set `U` and maps
`U` into `Ω` carries functions almost everywhere strongly measurable on `Ω` to functions almost
everywhere strongly measurable on `U`. -/
theorem comp_contDiffOn_of_surjective_fderiv (hu : AEStronglyMeasurable u (μ.restrict Ω))
    (hθ : ContDiffOn ℝ 1 θ U) (hU : IsOpen U) (hsurj : ∀ x ∈ U, Surjective (fderiv ℝ θ x))
    (hmaps : MapsTo θ U Ω) :
    AEStronglyMeasurable (u ∘ θ) (μ₀.restrict U) :=
  hu.comp_quasiMeasurePreserving (hθ.quasiMeasurePreserving_restrict_of_surjective_fderiv μ₀ μ hU
    hsurj hmaps)

end MeasureTheory.AEStronglyMeasurable
