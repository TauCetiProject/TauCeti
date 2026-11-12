/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Translation
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Isometric transport of distributional total variation and perimeter

Distributional total variation is unchanged when a function and its open domain are pulled back
by a measure-preserving linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'`, such as a rotation or a
reflection of a Euclidean space with its Lebesgue measure. If only `e '' V ⊆ Ω`, the pulled-back
variation on `V` is bounded by the variation on `Ω`. Perimeter is transported in the same way,
both for preimages and for images of sets.

Combined with the translation invariance in `TauCeti.Analysis.BoundedVariation.Translation`, this
gives invariance under measure-preserving affine isometry equivalences into a space whose measure
is translation invariant, in particular under rigid motions of a Euclidean space.

The proof transports each admissible test vector field `φ` to `y ↦ e (φ (e.symm y))`. This
preserves the pointwise norm, and its divergence is the transported divergence of `φ`, so the
defining pairings agree after the change of variables `y = e x`. No integrability,
measurability, boundedness, or finiteness assumption on the function or the set is needed; in
particular the results apply to sets of infinite volume or infinite perimeter.

## Main declarations

* `LinearIsometryEquiv.totalVariationOn_comp_le`: pulling back into a smaller domain does not
  increase total variation.
* `LinearIsometryEquiv.totalVariationOn_comp` and `LinearIsometryEquiv.totalVariationOn_comap`:
  invariance under exact transport.
* `LinearIsometryEquiv.perimeter_preimage_le`, `LinearIsometryEquiv.perimeter_preimage`,
  `LinearIsometryEquiv.perimeter_comap` and `LinearIsometryEquiv.perimeter_image`: the
  corresponding statements for perimeter.
* `AffineIsometryEquiv.totalVariationOn_comap` and `AffineIsometryEquiv.perimeter_comap`:
  invariance under affine isometry equivalences.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
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

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable [ν.IsAddRightInvariant]

/-- **Invariance of total variation under affine isometries.** Pulling a function and its open
domain back along a measure-preserving affine isometry equivalence into a space with a
translation-invariant measure does not change its total variation. -/
theorem totalVariationOn_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) :
    totalVariationOn μ (Opens.comap ⟨f, f.continuous⟩ Ω) (u ∘ f) = totalVariationOn ν Ω u := by
  let L := f.linearIsometryEquiv
  have hfx (x : E) : f x = L x + f 0 := by simpa using f.map_vadd 0 x
  -- The linear part is `f` followed by translation by `-f 0`, so it is measure preserving.
  have hL : MeasurePreserving L μ ν := by
    have h := (measurePreserving_sub_right ν (f 0)).comp hf
    convert h using 1
    funext x
    simp [hfx x]
  have hdom : Opens.comap ⟨f, f.continuous⟩ Ω =
      Opens.comap (L : C(E, E')) (Opens.comap (ContinuousMap.addRight (f 0)) Ω) := by
    ext x
    simp [hfx x]
  have hfun : u ∘ f = (fun y => u (y + f 0)) ∘ L := by
    funext x
    simp [hfx x]
  rw [hdom, hfun, L.totalVariationOn_comap hL,
    totalVariationOn_comap_add_right]

/-- **Invariance of perimeter under affine isometries.** Pulling a set and its open domain back
along a measure-preserving affine isometry equivalence into a space with a translation-invariant
measure does not change its perimeter. -/
theorem perimeter_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) :
    perimeter μ (Opens.comap ⟨f, f.continuous⟩ Ω) (f ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap f hf

end AffineIsometryEquiv
