/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Distribution.TestFunction.Translation

/-!
# Isometric transport of distributional total variation, BV spaces, and perimeter

Distributional total variation is unchanged when a function and its open domain are pulled back
by a measure-preserving linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'`, such as a rotation or a
reflection of a Euclidean space with its Lebesgue measure. If only `e '' V ⊆ Ω`, the pulled-back
variation on `V` is bounded by the variation on `Ω`. Perimeter is transported in the same way,
both for preimages and for images of sets.

Transporting test vector fields along the linear part of an affine isometry equivalence
`f : E ≃ᵃⁱ[ℝ] E'` followed by translation by `f 0` extends these results to arbitrary
measure-preserving affine isometry equivalences, without requiring `μ` or `ν` to be translation
invariant; in particular they apply to rigid motions of Euclidean spaces.

Combining invariance of total variation with `L¹` change of variables transports the unbundled
membership predicate `TauCeti.MemBV` and induces linear isometric equivalences
`TauCeti.BV.compLinearIsometryEquiv` and `TauCeti.BV.compAffineIsometryEquiv` between the Banach
spaces `TauCeti.BV` on isometric open sets.

The variation identity transports each admissible test vector field `φ` to `y ↦ e (φ (e.symm y))`.
This preserves the pointwise norm, and its divergence is the transported divergence of `φ`, so the
defining pairings agree after the change of variables `y = e x`. For the variation and perimeter
identities, no integrability, measurability, boundedness, or finiteness assumption on the function
or the set is needed; in particular the results apply to sets of infinite volume or infinite
perimeter.

## Main declarations

* `LinearIsometryEquiv.totalVariationOn_comp_le`: pulling back into a smaller domain does not
  increase total variation.
* `LinearIsometryEquiv.totalVariationOn_comp` and `LinearIsometryEquiv.totalVariationOn_comap`:
  invariance under exact transport.
* `LinearIsometryEquiv.memBV_comp`, `LinearIsometryEquiv.memBV_comp_iff`, and
  `LinearIsometryEquiv.memBV_comap_iff`: preservation and invariance of `TauCeti.MemBV` under
  linear isometry equivalences.
* `LinearIsometryEquiv.perimeter_preimage_le`, `LinearIsometryEquiv.perimeter_preimage`,
  `LinearIsometryEquiv.perimeter_comap` and `LinearIsometryEquiv.perimeter_image`: the
  corresponding statements for perimeter.
* `AffineIsometryEquiv.totalVariationOn_comp_le`, `AffineIsometryEquiv.totalVariationOn_comp`,
  `AffineIsometryEquiv.totalVariationOn_comap`, `AffineIsometryEquiv.memBV_comp`,
  `AffineIsometryEquiv.memBV_comp_iff`, `AffineIsometryEquiv.memBV_comap_iff`,
  `AffineIsometryEquiv.perimeter_preimage_le`, `AffineIsometryEquiv.perimeter_preimage`,
  `AffineIsometryEquiv.perimeter_comap`, and `AffineIsometryEquiv.perimeter_image`: transport and
  invariance under affine isometry equivalences.
* `TauCeti.BV.compLinearIsometryEquiv` and `TauCeti.BV.compAffineIsometryEquiv`: isometric
  equivalences of `TauCeti.BV` spaces along measure-preserving linear and affine isometry
  equivalences.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
-/

public section

noncomputable section

open MeasureTheory Set TestFunction TopologicalSpace TauCeti
open scoped Distributions

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'} {u : E' → ℝ} {s : Set E'}

namespace TauCeti

omit [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E] [BorelSpace E'] in
/-- The perimeter of a preimage is the total variation of the pulled-back indicator. -/
private theorem perimeter_preimage_eq_totalVariationOn (f : E → E') :
    perimeter μ V (f ⁻¹' s) = totalVariationOn μ V (s.indicator 1 ∘ f) := by
  rw [perimeter_def]
  exact congrArg (totalVariationOn μ V)
    (funext fun _ => Set.indicator_comp_right (g := fun _ => (1 : ℝ)) f)

end TauCeti

namespace LinearIsometryEquiv

/-- Pulling a function back along a measure-preserving linear isometry equivalence `e` does not
increase its total variation when `e` maps `V` into `Ω`. -/
theorem totalVariationOn_comp_le (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hVO : MapsTo e V Ω) :
    totalVariationOn μ V (u ∘ e) ≤ totalVariationOn ν Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let e' : E ≃L[ℝ] E' := e.toContinuousLinearEquiv
  have hVO' : MapsTo e' V Ω := hVO
  -- The transported field `y ↦ e (φ (e.symm y))`, a test vector field on `Ω`.
  let ψ : 𝓓(Ω, E') := postcompCLM (e' : E →L[ℝ] E') (e'.transportTestFunction hVO' φ)
  have hdiv (y : E') : divergenceCLM ψ y = divergenceCLM φ (e.symm y) := by
    simp only [ψ, ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction,
      ContinuousLinearEquiv.transportTestFunction_apply, e', coe_symm_toContinuousLinearEquiv]
  have hpair : (∫ x, divergenceCLM φ x * (u ∘ e) x ∂μ) = ∫ y, divergenceCLM ψ y * u y ∂ν := by
    rw [← he.integral_comp e.toMeasurableEquiv.measurableEmbedding]
    simp [hdiv]
  rw [hpair]
  refine ofReal_integral_le_totalVariationOn ψ fun y => ?_
  simp only [ψ, postcompCLM_apply, Function.comp_apply,
    ContinuousLinearEquiv.transportTestFunction_apply]
  simpa [e'] using hφ (e.symm y)

/-- **Isometry invariance of total variation.** If a measure-preserving linear isometry
equivalence `e` identifies `V` with `Ω`, then pulling a function back along `e` does not change
its total variation. -/
theorem totalVariationOn_comp (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    totalVariationOn μ V (u ∘ e) = totalVariationOn ν Ω u := by
  refine le_antisymm (totalVariationOn_comp_le e he hVO) ?_
  simpa [Function.comp_def] using totalVariationOn_comp_le (u := u ∘ e)
    e.symm (by simpa using MeasurePreserving.symm e.toMeasurableEquiv he) hOV

/-- Total variation is invariant under a measure-preserving linear isometry equivalence, with the
pulled-back domain written canonically as the preimage open set. -/
theorem totalVariationOn_comap (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) :
    totalVariationOn μ (Opens.comap (e : C(E, E')) Ω) (u ∘ e) = totalVariationOn ν Ω u :=
  totalVariationOn_comp e he (fun _ hx => Opens.mem_comap.mp hx)
    fun y hy => Opens.mem_comap.mpr (by simpa using hy)

/-- Pulling a set back along a measure-preserving linear isometry equivalence `e` does not increase
its perimeter when `e` maps `V` into `Ω`. -/
theorem perimeter_preimage_le (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hVO : MapsTo e V Ω) :
    perimeter μ V (e ⁻¹' s) ≤ perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_le e he hVO

/-- **Isometry invariance of perimeter.** If a measure-preserving linear isometry equivalence `e`
identifies `V` with `Ω`, then the perimeter in `V` of the preimage of `s` equals the perimeter of
`s` in `Ω`. -/
theorem perimeter_preimage (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    perimeter μ V (e ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp e he hVO hOV

/-- Perimeter is invariant when a set and its ambient open set are both pulled back along the same
measure-preserving linear isometry equivalence. -/
theorem perimeter_comap (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) :
    perimeter μ (Opens.comap (e : C(E, E')) Ω) (e ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap e he

/-- The image of a set under a measure-preserving linear isometry equivalence `e` identifying `V`
with `Ω` has, in `Ω`, the perimeter of the original set in `V`. -/
theorem perimeter_image {s : Set E} (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    perimeter ν Ω (e '' s) = perimeter μ V s := by
  rw [e.image_eq_preimage_symm]
  exact perimeter_preimage e.symm
    (by simpa using MeasurePreserving.symm e.toMeasurableEquiv he) hOV (by simpa using hVO)

omit [BorelSpace E] [BorelSpace E'] in
/-- Pulling a BV function back along a measure-preserving linear isometry equivalence `e` mapping
`V` into `Ω` gives a BV function on `V`. -/
theorem memBV_comp [OpensMeasurableSpace E'] (e : E ≃ₗᵢ[ℝ] E') (he : MeasurePreserving e μ ν)
    (hVO : MapsTo e V Ω) (hu : MemBV ν Ω u) : MemBV μ V (u ∘ e) := by
  have hres : MeasurePreserving e (μ.restrict (e ⁻¹' Ω)) (ν.restrict Ω) :=
    he.restrict_preimage Ω.isOpen.measurableSet
  refine memBV_iff.mpr
    ⟨IntegrableOn.mono_set
        ((hres.integrable_comp hu.integrableOn.aestronglyMeasurable).mpr hu.integrableOn) hVO,
      (totalVariationOn_le_iff.mpr fun φ hφ => ?_).trans_lt hu.totalVariationOn_lt_top⟩
  let e' : E ≃L[ℝ] E' := e.toContinuousLinearEquiv
  have hVO' : MapsTo e' V Ω := hVO
  let ψ : 𝓓(Ω, E') := postcompCLM (e' : E →L[ℝ] E') (e'.transportTestFunction hVO' φ)
  have hg : AEStronglyMeasurable (fun y => divergenceCLM ψ y * u y) ν := by
    have hon : AEStronglyMeasurable (fun y => divergenceCLM ψ y * u y) (ν.restrict Ω) :=
      (divergenceCLM ψ).continuous.aestronglyMeasurable.mul hu.integrableOn.aestronglyMeasurable
    refine ((aestronglyMeasurable_indicator_iff Ω.isOpen.measurableSet).mpr hon).congr
      (.of_forall fun y => ?_)
    by_cases hy : y ∈ (Ω : Set E')
    · simp [hy]
    · simp [hy, image_eq_zero_of_notMem_tsupport fun hmem =>
        hy ((divergenceCLM ψ).tsupport_subset hmem)]
  have hdiv (y : E') : divergenceCLM ψ y = divergenceCLM φ (e.symm y) := by
    simp only [ψ, ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction,
      ContinuousLinearEquiv.transportTestFunction_apply, e', coe_symm_toContinuousLinearEquiv]
  have hpair : (∫ x, divergenceCLM φ x * (u ∘ e) x ∂μ) = ∫ y, divergenceCLM ψ y * u y ∂ν := by
    rw [← he.map_eq, integral_map he.measurable.aemeasurable (he.map_eq.symm ▸ hg)]
    exact integral_congr_ae (.of_forall fun x => by simp [hdiv])
  rw [hpair]
  exact ofReal_integral_le_totalVariationOn ψ fun y => by
    simp only [ψ, postcompCLM_apply, Function.comp_apply,
      ContinuousLinearEquiv.transportTestFunction_apply]
    simpa [e'] using hφ (e.symm y)

/-- **Isometry invariance of BV membership.** If a measure-preserving linear isometry equivalence
`e` identifies `V` with `Ω`, then `u ∘ e` belongs to `MemBV μ V` if and only if `u` belongs to
`MemBV ν Ω`. -/
theorem memBV_comp_iff (e : E ≃ₗᵢ[ℝ] E') (he : MeasurePreserving e μ ν)
    (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    MemBV μ V (u ∘ e) ↔ MemBV ν Ω u := by
  refine ⟨fun hu => ?_, e.memBV_comp he hVO⟩
  simpa [Function.comp_def] using e.symm.memBV_comp
    (by simpa using MeasurePreserving.symm e.toMeasurableEquiv he) hOV hu

/-- BV membership is invariant under pulling a function and its open domain back along a
measure-preserving linear isometry equivalence. -/
theorem memBV_comap_iff (e : E ≃ₗᵢ[ℝ] E') (he : MeasurePreserving e μ ν) :
    MemBV μ (Opens.comap (e : C(E, E')) Ω) (u ∘ e) ↔ MemBV ν Ω u :=
  e.memBV_comp_iff he (fun _ hx => Opens.mem_comap.mp hx)
    fun _ hy => Opens.mem_comap.mpr (by simpa using hy)

end LinearIsometryEquiv

namespace AffineIsometryEquiv

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] in
private theorem mapsTo_linearIsometryEquiv_preimage_add (f : E ≃ᵃⁱ[ℝ] E') (hVO : MapsTo f V Ω) :
    MapsTo f.linearIsometryEquiv.toContinuousLinearEquiv V
      (⟨(· + f 0) ⁻¹' Ω, Ω.isOpen.preimage (continuous_add_const _)⟩ : Opens E') := fun x hx => by
  have hfx : f x = f.linearIsometryEquiv x + f 0 := by simpa using f.map_vadd 0 x
  change f.linearIsometryEquiv x + f 0 ∈ Ω
  rw [← hfx]
  exact hVO hx

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] in
/-- Transport a test vector field on `V` to `Ω` along an affine isometry equivalence `f` mapping
`V` into `Ω`. -/
private def transportTestVectorField (f : E ≃ᵃⁱ[ℝ] E') (hVO : MapsTo f V Ω) (φ : 𝓓(V, E)) :
    𝓓(Ω, E') :=
  translateTestFunction
    (V := ⟨(· + f 0) ⁻¹' Ω, Ω.isOpen.preimage (continuous_add_const _)⟩)
    (mapsTo_preimage (· + f 0) Ω)
    (postcompCLM (f.linearIsometryEquiv.toContinuousLinearEquiv : E →L[ℝ] E')
      (f.linearIsometryEquiv.toContinuousLinearEquiv.transportTestFunction
        (mapsTo_linearIsometryEquiv_preimage_add f hVO) φ))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] in
private theorem norm_transportTestVectorField_le (f : E ≃ᵃⁱ[ℝ] E') (hVO : MapsTo f V Ω)
    {φ : 𝓓(V, E)} (hφ : ∀ x, ‖φ x‖ ≤ 1) (z : E') :
    ‖transportTestVectorField f hVO φ z‖ ≤ 1 := by
  rw [transportTestVectorField, translateTestFunction_apply, postcompCLM_apply,
    Function.comp_apply, ContinuousLinearEquiv.transportTestFunction_apply]
  simpa using hφ _

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
private theorem divergenceCLM_transportTestVectorField_apply (f : E ≃ᵃⁱ[ℝ] E')
    (hVO : MapsTo f V Ω) (φ : 𝓓(V, E)) (x : E) :
    divergenceCLM (transportTestVectorField f hVO φ) (f x) = divergenceCLM φ x := by
  have hfx : f x - f 0 = f.linearIsometryEquiv x := by
    have h := f.map_vadd 0 x
    simp only [vadd_eq_add, add_zero] at h
    rw [h, add_sub_cancel_right]
  rw [transportTestVectorField, divergenceCLM_translateTestFunction, translateTestFunction_apply,
    hfx, ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction,
    ContinuousLinearEquiv.transportTestFunction_apply,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply]

/-- Pulling a function back along a measure-preserving affine isometry equivalence `f` does not
increase its total variation when `f` maps `V` into `Ω`. -/
theorem totalVariationOn_comp_le (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) :
    totalVariationOn μ V (u ∘ f) ≤ totalVariationOn ν Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let ψ : 𝓓(Ω, E') := transportTestVectorField f hVO φ
  have hpair : (∫ x, divergenceCLM φ x * (u ∘ f) x ∂μ) = ∫ z, divergenceCLM ψ z * u z ∂ν := by
    rw [← hf.integral_comp f.toHomeomorph.measurableEmbedding]
    simp only [ψ, Function.comp_apply, divergenceCLM_transportTestVectorField_apply]
  rw [hpair]
  exact ofReal_integral_le_totalVariationOn ψ (norm_transportTestVectorField_le f hVO hφ)

/-- **Invariance of total variation under affine isometries.** If a measure-preserving affine
isometry equivalence `f` maps `V` into `Ω` and `f.symm` maps `Ω` back into `V`, pulling `u` back
along `f` preserves its total variation. -/
theorem totalVariationOn_comp (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    totalVariationOn μ V (u ∘ f) = totalVariationOn ν Ω u := by
  refine le_antisymm (f.totalVariationOn_comp_le hf hVO) ?_
  have hsymm : MeasurePreserving f.symm ν μ :=
    MeasurePreserving.symm f.toHomeomorph.toMeasurableEquiv hf
  simpa [Function.comp_def] using
    f.symm.totalVariationOn_comp_le (u := u ∘ f) hsymm hOV

/-- **Invariance of total variation under affine isometries.** Pulling a function and its open
domain back along a measure-preserving affine isometry equivalence does not change its total
variation. -/
theorem totalVariationOn_comap (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) :
    totalVariationOn μ (Opens.comap ⟨f, f.continuous⟩ Ω) (u ∘ f) = totalVariationOn ν Ω u :=
  f.totalVariationOn_comp hf (fun _ hx => Opens.mem_comap.mp hx)
    fun _ hy => Opens.mem_comap.mpr (by simpa using hy)

/-- Pulling a set back along a measure-preserving affine isometry equivalence `f` does not increase
its perimeter when `f` maps `V` into `Ω`. -/
theorem perimeter_preimage_le (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) :
    perimeter μ V (f ⁻¹' s) ≤ perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact f.totalVariationOn_comp_le hf hVO

/-- **Invariance of perimeter under affine isometries.** If a measure-preserving affine isometry
equivalence `f` identifies `V` with `Ω`, then the perimeter in `V` of `f ⁻¹' s` equals the
perimeter of `s` in `Ω`. -/
theorem perimeter_preimage (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    perimeter μ V (f ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact f.totalVariationOn_comp hf hVO hOV

/-- **Invariance of perimeter under affine isometries.** Pulling a set and its open domain back
along a measure-preserving affine isometry equivalence does not change its perimeter. -/
theorem perimeter_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) :
    perimeter μ (Opens.comap ⟨f, f.continuous⟩ Ω) (f ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap f hf

/-- The image of a set under a measure-preserving affine isometry equivalence `f` identifying `V`
with `Ω` has, in `Ω`, the perimeter of the original set in `V`. -/
theorem perimeter_image {s : Set E} (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    perimeter ν Ω (f '' s) = perimeter μ V s := by
  have himg : f '' s = f.symm ⁻¹' s := f.toEquiv.image_eq_preimage_symm s
  rw [himg]
  exact f.symm.perimeter_preimage
    (MeasurePreserving.symm f.toHomeomorph.toMeasurableEquiv hf) hOV (by simpa using hVO)

omit [BorelSpace E] [BorelSpace E'] in
/-- Pulling a BV function back along a measure-preserving affine isometry equivalence `f` mapping
`V` into `Ω` gives a BV function on `V`. -/
theorem memBV_comp [OpensMeasurableSpace E'] (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hu : MemBV ν Ω u) : MemBV μ V (u ∘ f) := by
  have hres : MeasurePreserving f (μ.restrict (f ⁻¹' Ω)) (ν.restrict Ω) :=
    hf.restrict_preimage Ω.isOpen.measurableSet
  refine memBV_iff.mpr
    ⟨IntegrableOn.mono_set
        ((hres.integrable_comp hu.integrableOn.aestronglyMeasurable).mpr hu.integrableOn) hVO,
      (totalVariationOn_le_iff.mpr fun φ hφ => ?_).trans_lt hu.totalVariationOn_lt_top⟩
  let ψ : 𝓓(Ω, E') := transportTestVectorField f hVO φ
  have hg : AEStronglyMeasurable (fun z => divergenceCLM ψ z * u z) ν := by
    have hon : AEStronglyMeasurable (fun z => divergenceCLM ψ z * u z) (ν.restrict Ω) :=
      (divergenceCLM ψ).continuous.aestronglyMeasurable.mul hu.integrableOn.aestronglyMeasurable
    refine ((aestronglyMeasurable_indicator_iff Ω.isOpen.measurableSet).mpr hon).congr
      (.of_forall fun z => ?_)
    by_cases hz : z ∈ (Ω : Set E')
    · simp [hz]
    · simp [hz, image_eq_zero_of_notMem_tsupport fun hmem =>
        hz ((divergenceCLM ψ).tsupport_subset hmem)]
  have hpair : (∫ x, divergenceCLM φ x * (u ∘ f) x ∂μ) = ∫ z, divergenceCLM ψ z * u z ∂ν := by
    rw [← hf.map_eq, integral_map hf.measurable.aemeasurable (hf.map_eq.symm ▸ hg)]
    exact integral_congr_ae (.of_forall fun x => by
      simp only [ψ, Function.comp_apply, divergenceCLM_transportTestVectorField_apply])
  rw [hpair]
  exact ofReal_integral_le_totalVariationOn ψ (norm_transportTestVectorField_le f hVO hφ)

/-- **Invariance of BV membership under affine isometries.** If a measure-preserving affine
isometry equivalence `f` identifies `V` with `Ω`, then `u ∘ f` belongs to `MemBV μ V` if and only
if `u` belongs to `MemBV ν Ω`. -/
theorem memBV_comp_iff (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    MemBV μ V (u ∘ f) ↔ MemBV ν Ω u := by
  refine ⟨fun hu => ?_, f.memBV_comp hf hVO⟩
  simpa [Function.comp_def] using f.symm.memBV_comp
    (MeasurePreserving.symm f.toHomeomorph.toMeasurableEquiv hf) hOV hu

/-- Pulling a function and its open domain back along a measure-preserving affine isometry
equivalence preserves and reflects `MemBV`. -/
theorem memBV_comap_iff (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) :
    MemBV μ (Opens.comap ⟨f, f.continuous⟩ Ω) (u ∘ f) ↔ MemBV ν Ω u :=
  f.memBV_comp_iff hf (fun _ hx => Opens.mem_comap.mp hx)
    fun _ hy => Opens.mem_comap.mpr (by simpa using hy)

end AffineIsometryEquiv

namespace TauCeti.BV

section Aux

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
/-- If `f : α → β` is measurable from a Borel space `α` to an `OpensMeasurableSpace` `β` and has a
continuous right inverse `g`, then `β` is also a `BorelSpace`. -/
private theorem borelSpace_of_measurable_of_continuous_rightInv
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    {f : α → β} {g : β → α} (hf : Measurable f) (hg : Continuous g) (hfg : ∀ y, f (g y) = y) :
    BorelSpace β := by
  refine ⟨le_antisymm (fun s hs => ?_) OpensMeasurableSpace.borel_le⟩
  have hpre : g ⁻¹' (f ⁻¹' s) = s := Set.ext fun y => by simp [hfg y]
  rw [← hpre]
  exact hg.borel_measurable (BorelSpace.measurable_eq (α := α) ▸ hf hs)

omit [BorelSpace E] [BorelSpace E'] in
/-- Pull a BV class back along a map preserving the restricted measure and total variation. -/
private def compAux [OpensMeasurableSpace E] [OpensMeasurableSpace E'] {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) : BV μ V :=
  ofFunction (u ∘ f) <| memBV_iff.mpr
    ⟨(hf.integrable_comp u.integrableOn.aestronglyMeasurable).mpr u.integrableOn,
      (htv u).trans_lt u.totalVariationOn_lt_top⟩

omit [BorelSpace E] [BorelSpace E'] in
private theorem coeFn_compAux [OpensMeasurableSpace E] [OpensMeasurableSpace E'] {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    (compAux hf htv u : E → ℝ) =ᵐ[μ.restrict V] u ∘ f :=
  coeFn_ofFunction (u ∘ f) _

omit [BorelSpace E] [BorelSpace E'] in
private theorem toL1_compAux [OpensMeasurableSpace E] [OpensMeasurableSpace E'] {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    (compAux hf htv u).toL1 = Lp.compMeasurePreserving f hf u.toL1 :=
  Lp.ext <| (coeFn_compAux hf htv u).trans (Lp.coeFn_compMeasurePreserving u.toL1 hf).symm

omit [BorelSpace E] [BorelSpace E'] in
private theorem norm_compAux [OpensMeasurableSpace E] [OpensMeasurableSpace E'] {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    ‖compAux hf htv u‖ = ‖u‖ := by
  rw [norm_def, norm_def, totalVariationOn_congr_ae (coeFn_compAux hf htv u), htv u,
    toL1_compAux hf htv u, Lp.norm_compMeasurePreserving u.toL1 hf]

omit [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E] [BorelSpace E'] in
private theorem totalVariationOn_comp_symm {f : E → E'} {g : E' → E}
    (hgf : ∀ x, g (f x) = x) {tv' : (E' → ℝ) → ENNReal}
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = tv' w) (w : E → ℝ) :
    tv' (w ∘ g) = totalVariationOn μ V w := by
  rw [← htv (w ∘ g)]
  exact congrArg (totalVariationOn μ V) (funext fun x => congrArg w (hgf x))

omit [BorelSpace E] [BorelSpace E'] in
/-- Assemble a linear isometric equivalence `BV ν Ω ≃ₗᵢ[ℝ] BV μ V` from an inverse pair of maps
that preserve the restricted measures and total variation. -/
private def compEquivAux [OpensMeasurableSpace E] [OpensMeasurableSpace E']
    {f : E → E'} {g : E' → E}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (hg : MeasurePreserving g (ν.restrict Ω) (μ.restrict V))
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w) :
    BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  LinearIsometryEquiv.ofBounds
    { toFun := compAux hf htv
      invFun := compAux hg (totalVariationOn_comp_symm hgf htv)
      left_inv u := ext <| by
        filter_upwards [coeFn_compAux hg (totalVariationOn_comp_symm hgf htv) (compAux hf htv u),
          hg.quasiMeasurePreserving.ae_eq_comp (coeFn_compAux hf htv u)] with y h₁ h₂
        exact h₁.trans (h₂.trans (congrArg u (hfg y)))
      right_inv v := ext <| by
        filter_upwards [coeFn_compAux hf htv (compAux hg (totalVariationOn_comp_symm hgf htv) v),
          hf.quasiMeasurePreserving.ae_eq_comp
            (coeFn_compAux hg (totalVariationOn_comp_symm hgf htv) v)] with x h₁ h₂
        exact h₁.trans (h₂.trans (congrArg v (hgf x)))
      map_add' u v := toL1_injective <| by
        rw [toL1_compAux, toL1_add, toL1_add, toL1_compAux, toL1_compAux]
        exact map_add (Lp.compMeasurePreserving f hf) u.toL1 v.toL1
      map_smul' c u := toL1_injective <| by
        rw [RingHom.id_apply, toL1_compAux, toL1_smul, toL1_smul, toL1_compAux]
        exact map_smul (Lp.compMeasurePreservingₗ ℝ f hf) c u.toL1 }
    (fun u => (norm_compAux hf htv u).le)
    (fun v => (norm_compAux hg (totalVariationOn_comp_symm hgf htv) v).le)

omit [BorelSpace E] [BorelSpace E'] in
private theorem toL1_compEquivAux [OpensMeasurableSpace E] [OpensMeasurableSpace E']
    {f : E → E'} {g : E' → E}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (hg : MeasurePreserving g (ν.restrict Ω) (μ.restrict V))
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    (compEquivAux hf hg hfg hgf htv u).toL1 = Lp.compMeasurePreserving f hf u.toL1 :=
  toL1_compAux hf htv u

omit [BorelSpace E] [BorelSpace E'] in
private theorem coeFn_compEquivAux [OpensMeasurableSpace E] [OpensMeasurableSpace E']
    {f : E → E'} {g : E' → E}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (hg : MeasurePreserving g (ν.restrict Ω) (μ.restrict V))
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    (compEquivAux hf hg hfg hgf htv u : E → ℝ) =ᵐ[μ.restrict V] u ∘ f :=
  coeFn_compAux hf htv u

omit [BorelSpace E] [BorelSpace E'] in
private theorem coeFn_compEquivAux_symm [OpensMeasurableSpace E] [OpensMeasurableSpace E']
    {f : E → E'} {g : E' → E}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (hg : MeasurePreserving g (ν.restrict Ω) (μ.restrict V))
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (v : BV μ V) :
    ((compEquivAux hf hg hfg hgf htv).symm v : E' → ℝ) =ᵐ[ν.restrict Ω] v ∘ g :=
  coeFn_compAux hg (totalVariationOn_comp_symm hgf htv) v

end Aux

section LinearIsometryEquiv

variable [OpensMeasurableSpace E'] {e : E ≃ₗᵢ[ℝ] E'}

omit [BorelSpace E'] in
/-- **Isometric transport of `BV` along a linear isometry equivalence.** Precomposition with a
measure-preserving linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` is a linear isometric equivalence
`BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = e ⁻¹' Ω`. -/
def compLinearIsometryEquiv (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) :
    BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  have : BorelSpace E' :=
    borelSpace_of_measurable_of_continuous_rightInv he.measurable e.symm.continuous
      e.apply_symm_apply
  have hOV : (Ω : Set E') = e.symm ⁻¹' V := by
    rw [hVO, ← Set.preimage_comp]
    ext y
    simp
  compEquivAux (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet)
    (hOV ▸ (MeasurePreserving.symm e.toMeasurableEquiv he).restrict_preimage V.isOpen.measurableSet)
    e.apply_symm_apply e.symm_apply_apply fun w =>
      e.totalVariationOn_comp he (mapsTo_iff_subset_preimage.mpr hVO.subset)
        (mapsTo_iff_subset_preimage.mpr hOV.subset)

omit [BorelSpace E'] in
/-- The `L¹` class of a BV class pulled back along `e` is `Lp.compMeasurePreserving` of its `L¹`
class. -/
theorem toL1_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    (compLinearIsometryEquiv he hVO u).toL1 =
      Lp.compMeasurePreserving e (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet) u.toL1 := by
  rw [compLinearIsometryEquiv]
  exact toL1_compEquivAux _ _ _ _ _ u

omit [BorelSpace E'] in
/-- Pulling a BV class back along `e` precomposes its representative with `e` almost everywhere on
`V`. -/
theorem coeFn_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    (compLinearIsometryEquiv he hVO u : E → ℝ) =ᵐ[μ.restrict V] u ∘ e := by
  rw [compLinearIsometryEquiv]
  exact coeFn_compEquivAux _ _ _ _ _ u

omit [BorelSpace E'] in
/-- The inverse of `compLinearIsometryEquiv` precomposes representatives with `e.symm` almost
everywhere on `Ω`. -/
theorem coeFn_compLinearIsometryEquiv_symm (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (v : BV μ V) :
    ((compLinearIsometryEquiv he hVO).symm v : E' → ℝ) =ᵐ[ν.restrict Ω] v ∘ e.symm := by
  rw [compLinearIsometryEquiv]
  exact coeFn_compEquivAux_symm _ _ _ _ _ v

omit [BorelSpace E'] in
/-- Pulling a BV class back along `e` preserves its total variation. -/
@[simp]
theorem totalVariationOn_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    totalVariationOn μ V (compLinearIsometryEquiv he hVO u) = totalVariationOn ν Ω u := by
  have : BorelSpace E' :=
    borelSpace_of_measurable_of_continuous_rightInv he.measurable e.symm.continuous
      e.apply_symm_apply
  have hOV : MapsTo e.symm Ω V := fun y hy => by
    rw [hVO, mem_preimage, e.apply_symm_apply]
    exact hy
  exact (totalVariationOn_congr_ae (coeFn_compLinearIsometryEquiv he hVO u)).trans
    (e.totalVariationOn_comp he (mapsTo_iff_subset_preimage.mpr hVO.subset) hOV)

omit [BorelSpace E'] in
/-- Forming a BV class from a representative commutes with `compLinearIsometryEquiv`. -/
@[simp]
theorem compLinearIsometryEquiv_ofFunction (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : E' → ℝ) (hu : MemBV ν Ω u) :
    compLinearIsometryEquiv he hVO (ofFunction u hu) =
      ofFunction (u ∘ e) (e.memBV_comp he (mapsTo_iff_subset_preimage.mpr hVO.subset) hu) := by
  have hres : MeasurePreserving e (μ.restrict V) (ν.restrict Ω) :=
    hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet
  refine ext ((coeFn_compLinearIsometryEquiv he hVO _).trans ?_)
  exact (hres.quasiMeasurePreserving.ae_eq_comp (coeFn_ofFunction u hu)).trans
    (coeFn_ofFunction (u ∘ e) _).symm

end LinearIsometryEquiv

section AffineIsometryEquiv

variable [OpensMeasurableSpace E'] {f : E ≃ᵃⁱ[ℝ] E'}

omit [BorelSpace E'] in
/-- **Isometric transport of `BV` along an affine isometry equivalence.** Precomposition with a
measure-preserving affine isometry equivalence `f : E ≃ᵃⁱ[ℝ] E'` is a linear isometric equivalence
`BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = f ⁻¹' Ω`. -/
def compAffineIsometryEquiv (hf : MeasurePreserving f μ ν) (hVO : (V : Set E) = f ⁻¹' Ω) :
    BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  have : BorelSpace E' :=
    borelSpace_of_measurable_of_continuous_rightInv hf.measurable f.symm.continuous
      f.apply_symm_apply
  have hOV : (Ω : Set E') = f.symm ⁻¹' V := by
    rw [hVO, ← Set.preimage_comp]
    ext y
    simp
  compEquivAux (hVO ▸ hf.restrict_preimage Ω.isOpen.measurableSet)
    (hOV ▸ (MeasurePreserving.symm f.toHomeomorph.toMeasurableEquiv hf).restrict_preimage
      V.isOpen.measurableSet)
    f.apply_symm_apply f.symm_apply_apply fun w =>
      f.totalVariationOn_comp hf (mapsTo_iff_subset_preimage.mpr hVO.subset)
        (mapsTo_iff_subset_preimage.mpr hOV.subset)

omit [BorelSpace E'] in
/-- The `L¹` class of a BV class pulled back along `f` is `Lp.compMeasurePreserving` of its `L¹`
class. -/
theorem toL1_compAffineIsometryEquiv (hf : MeasurePreserving f μ ν)
    (hVO : (V : Set E) = f ⁻¹' Ω) (u : BV ν Ω) :
    (compAffineIsometryEquiv hf hVO u).toL1 =
      Lp.compMeasurePreserving f (hVO ▸ hf.restrict_preimage Ω.isOpen.measurableSet) u.toL1 := by
  rw [compAffineIsometryEquiv]
  exact toL1_compEquivAux _ _ _ _ _ u

omit [BorelSpace E'] in
/-- Pulling a BV class back along `f` precomposes its representative with `f` almost everywhere on
`V`. -/
theorem coeFn_compAffineIsometryEquiv (hf : MeasurePreserving f μ ν)
    (hVO : (V : Set E) = f ⁻¹' Ω) (u : BV ν Ω) :
    (compAffineIsometryEquiv hf hVO u : E → ℝ) =ᵐ[μ.restrict V] u ∘ f := by
  rw [compAffineIsometryEquiv]
  exact coeFn_compEquivAux _ _ _ _ _ u

omit [BorelSpace E'] in
/-- The inverse of `compAffineIsometryEquiv` precomposes representatives with `f.symm` almost
everywhere on `Ω`. -/
theorem coeFn_compAffineIsometryEquiv_symm (hf : MeasurePreserving f μ ν)
    (hVO : (V : Set E) = f ⁻¹' Ω) (v : BV μ V) :
    ((compAffineIsometryEquiv hf hVO).symm v : E' → ℝ) =ᵐ[ν.restrict Ω] v ∘ f.symm := by
  rw [compAffineIsometryEquiv]
  exact coeFn_compEquivAux_symm _ _ _ _ _ v

omit [BorelSpace E'] in
/-- Pulling a BV class back along `f` preserves its total variation. -/
@[simp]
theorem totalVariationOn_compAffineIsometryEquiv (hf : MeasurePreserving f μ ν)
    (hVO : (V : Set E) = f ⁻¹' Ω) (u : BV ν Ω) :
    totalVariationOn μ V (compAffineIsometryEquiv hf hVO u) = totalVariationOn ν Ω u := by
  have : BorelSpace E' :=
    borelSpace_of_measurable_of_continuous_rightInv hf.measurable f.symm.continuous
      f.apply_symm_apply
  have hOV : MapsTo f.symm Ω V := fun y hy => by
    rw [hVO, mem_preimage, f.apply_symm_apply]
    exact hy
  exact (totalVariationOn_congr_ae (coeFn_compAffineIsometryEquiv hf hVO u)).trans
    (f.totalVariationOn_comp hf (mapsTo_iff_subset_preimage.mpr hVO.subset) hOV)

omit [BorelSpace E'] in
/-- Forming a BV class from a representative commutes with `compAffineIsometryEquiv`. -/
@[simp]
theorem compAffineIsometryEquiv_ofFunction (hf : MeasurePreserving f μ ν)
    (hVO : (V : Set E) = f ⁻¹' Ω) (u : E' → ℝ) (hu : MemBV ν Ω u) :
    compAffineIsometryEquiv hf hVO (ofFunction u hu) =
      ofFunction (u ∘ f) (f.memBV_comp hf (mapsTo_iff_subset_preimage.mpr hVO.subset) hu) := by
  have hres : MeasurePreserving f (μ.restrict V) (ν.restrict Ω) :=
    hVO ▸ hf.restrict_preimage Ω.isOpen.measurableSet
  refine ext ((coeFn_compAffineIsometryEquiv hf hVO _).trans ?_)
  exact (hres.quasiMeasurePreserving.ae_eq_comp (coeFn_ofFunction u hu)).trans
    (coeFn_ofFunction (u ∘ f) _).symm

end AffineIsometryEquiv

end TauCeti.BV
