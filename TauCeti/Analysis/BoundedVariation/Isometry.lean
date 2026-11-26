/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Dynamics.Ergodic.MeasurePreserving
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Isometric transport of distributional total variation, BV spaces, and perimeter

Distributional total variation is unchanged when a function and its open domain are pulled back
by a measure-preserving affine isometry equivalence `f : E ≃ᵃⁱ[ℝ] E'` with measurable inverse,
such as a rigid motion of a Euclidean space with its Borel or completed Lebesgue measure, without
assuming that the target measure is translation invariant or that the measurable spaces are Borel.
If only `f '' V ⊆ Ω`, the pulled-back variation on `V` is bounded by the variation on `Ω`.
Perimeter is transported in the same way, both for preimages and for images of sets. Specializing
via `LinearIsometryEquiv.toAffineIsometryEquiv` gives the corresponding results for linear isometry
equivalences `e : E ≃ₗᵢ[ℝ] E'`.

Combining invariance of total variation with `L¹` change of variables shows that BV membership is
invariant under such an `f` and induces the linear isometric equivalence
`AffineIsometryEquiv.compBV : BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = f ⁻¹' Ω`, with no boundedness
or regularity assumption on the open sets. Consequently compactness of `BV.toL1CLM` is transported
along measure-preserving affine isometry equivalences with measurable inverse; linear isometry
equivalences are covered via `LinearIsometryEquiv.toAffineIsometryEquiv`.

The proof transports each admissible test vector field `φ` on `V` to `y ↦ L (φ (f.symm y))` on `Ω`,
where `L` is the linear part of `f`. This preserves the pointwise norm, and its divergence is the
transported divergence of `φ`, so the defining pairings agree after the change of variables
`y = f x`. No integrability, measurability, boundedness, or finiteness assumption on the function
or the set is needed; in particular the results apply to sets of infinite volume or infinite
perimeter.

## Main declarations

* `AffineIsometryEquiv.totalVariationOn_comp_le`: pulling back into a smaller domain along an
  affine isometry equivalence does not increase total variation.
* `AffineIsometryEquiv.totalVariationOn_comp` and `AffineIsometryEquiv.totalVariationOn_comap`:
  invariance of total variation under exact affine-isometric transport.
* `AffineIsometryEquiv.perimeter_preimage_le`, `AffineIsometryEquiv.perimeter_preimage`,
  `AffineIsometryEquiv.perimeter_comap` and `AffineIsometryEquiv.perimeter_image`: the
  corresponding statements for perimeter.
* `LinearIsometryEquiv.totalVariationOn_comp_le`, `LinearIsometryEquiv.totalVariationOn_comp`,
  `LinearIsometryEquiv.totalVariationOn_comap`, `LinearIsometryEquiv.perimeter_preimage_le`,
  `LinearIsometryEquiv.perimeter_preimage`, `LinearIsometryEquiv.perimeter_comap` and
  `LinearIsometryEquiv.perimeter_image`: specializations to linear isometry equivalences.
* `AffineIsometryEquiv.memBV_comp_iff`: invariance of BV membership under affine isometries.
* `AffineIsometryEquiv.compBV`: isometric equivalence of `TauCeti.BV` spaces along a
  measure-preserving affine isometry equivalence with measurable inverse, with its inverse
  `AffineIsometryEquiv.compBV_symm` and its action on representatives, `L¹` classes and total
  variation.
* `AffineIsometryEquiv.isCompactOperator_toL1CLM` and
  `AffineIsometryEquiv.isCompactOperator_toL1CLM_iff`: invariance of compactness of
  `BV.toL1CLM` under affine isometry equivalences.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
-/

public section

noncomputable section

open MeasureTheory Set TestFunction TopologicalSpace TauCeti
open scoped Distributions

namespace TauCeti

/-- The perimeter of a preimage is the total variation of the pulled-back indicator. -/
private theorem perimeter_preimage_eq_totalVariationOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] {E' : Type*} {μ : Measure E} {V : Opens E} {s : Set E'}
    (f : E → E') :
    perimeter μ V (f ⁻¹' s) = totalVariationOn μ V (s.indicator 1 ∘ f) := by
  rw [perimeter_def]
  exact congrArg (totalVariationOn μ V)
    (funext fun _ => Set.indicator_comp_right (g := fun _ => (1 : ℝ)) f)

/-- If precomposition with `f` preserves total variation and `g` is a left inverse of `f`, then
precomposition with `g` preserves total variation in the opposite direction. -/
private theorem totalVariationOn_comp_symm
    {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E] [MeasurableSpace E']
    {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'}
    {f : E → E'} {g : E' → E} (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w) (w : E → ℝ) :
    totalVariationOn ν Ω (w ∘ g) = totalVariationOn μ V w := by
  rw [← htv (w ∘ g)]
  exact congrArg (totalVariationOn μ V) (funext fun x => congrArg w (hgf x))

end TauCeti

section VariationAndPerimeter

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [MeasurableSpace E']
  {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'} {u : E' → ℝ} {s : Set E'}

namespace AffineIsometryEquiv

/-- Pulling a function back along a measure-preserving affine isometry equivalence `f` with
measurable inverse does not increase its total variation when `f` maps `V` into `Ω`. -/
theorem totalVariationOn_comp_le (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm) (hVO : MapsTo f V Ω) :
    totalVariationOn μ V (u ∘ f) ≤ totalVariationOn ν Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let L : E ≃L[ℝ] E' := f.linearIsometryEquiv.toContinuousLinearEquiv
  have hfx (x : E) : f x = L x + f 0 := by simpa [L] using f.map_vadd 0 x
  have hfsymm (y : E') : f.symm y = L.symm (y - f 0) :=
    f.injective <| by rw [f.apply_symm_apply, hfx, L.apply_symm_apply, sub_add_cancel]
  let W : Opens E' := Opens.comap (ContinuousMap.addRight (f 0)) Ω
  have hVW : MapsTo L V W := fun x hx => by
    simpa [W, ← hfx x] using hVO hx
  have hWΩ : MapsTo (· + f 0) W Ω := fun _ hy => Opens.mem_comap.mp hy
  -- Transport `φ` along the linear part `L` to `W`, then translate by `f 0` to `Ω`.
  let ψ₁ : 𝓓(W, E') := postcompCLM (L : E →L[ℝ] E') (L.transportTestFunction hVW φ)
  let ψ : 𝓓(Ω, E') := translateTestFunction hWΩ ψ₁
  have hdiv (y : E') : divergenceCLM ψ y = divergenceCLM φ (f.symm y) := by
    simp only [ψ, ψ₁, divergenceCLM_translateTestFunction, translateTestFunction_apply,
      ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction,
      ContinuousLinearEquiv.transportTestFunction_apply, hfsymm]
  have hpair : (∫ x, divergenceCLM φ x * (u ∘ f) x ∂μ) = ∫ y, divergenceCLM ψ y * u y ∂ν := by
    rw [← hf.integral_comp (⟨f.toEquiv, hf.measurable, hinv⟩ : E ≃ᵐ E').measurableEmbedding]
    simp [hdiv]
  rw [hpair]
  refine ofReal_integral_le_totalVariationOn ψ fun y => ?_
  simp only [ψ, ψ₁, translateTestFunction_apply, postcompCLM_apply, Function.comp_apply,
    ContinuousLinearEquiv.transportTestFunction_apply, ← hfsymm]
  simpa [L] using hφ (f.symm y)

/-- **Invariance of total variation under affine isometries.** If a measure-preserving affine
isometry equivalence `f` with measurable inverse identifies `V` with `Ω`, then pulling a function
back along `f` does not change its total variation. -/
theorem totalVariationOn_comp (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    totalVariationOn μ V (u ∘ f) = totalVariationOn ν Ω u := by
  refine le_antisymm (totalVariationOn_comp_le f hf hinv hVO) ?_
  simpa [Function.comp_def] using totalVariationOn_comp_le (u := u ∘ f) f.symm
    (MeasurePreserving.symm ⟨f.toEquiv, hf.measurable, hinv⟩ hf) hf.measurable hOV

/-- Total variation is invariant under a measure-preserving affine isometry equivalence with
measurable inverse, with the pulled-back domain written canonically as the preimage open set. -/
theorem totalVariationOn_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm) :
    totalVariationOn μ (Opens.comap ⟨f, f.continuous⟩ Ω) (u ∘ f) = totalVariationOn ν Ω u :=
  totalVariationOn_comp f hf hinv (fun _ hx => Opens.mem_comap.mp hx)
    fun y hy => Opens.mem_comap.mpr (by simpa using hy)

/-- Pulling a set back along a measure-preserving affine isometry equivalence `f` with measurable
inverse does not increase its perimeter when `f` maps `V` into `Ω`. -/
theorem perimeter_preimage_le (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm) (hVO : MapsTo f V Ω) :
    perimeter μ V (f ⁻¹' s) ≤ perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_le f hf hinv hVO

/-- **Invariance of perimeter under affine isometries.** If a measure-preserving affine isometry
equivalence `f` with measurable inverse identifies `V` with `Ω`, then the perimeter in `V` of the
preimage of `s` equals the perimeter of `s` in `Ω`. -/
theorem perimeter_preimage (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    perimeter μ V (f ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp f hf hinv hVO hOV

/-- Perimeter is invariant when a set and its ambient open set are both pulled back along the same
measure-preserving affine isometry equivalence with measurable inverse. -/
theorem perimeter_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm) :
    perimeter μ (Opens.comap ⟨f, f.continuous⟩ Ω) (f ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap f hf hinv

/-- The image of a set under a measure-preserving affine isometry equivalence `f` with measurable
inverse identifying `V` with `Ω` has, in `Ω`, the perimeter of the original set in `V`. -/
theorem perimeter_image {s : Set E} (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    perimeter ν Ω (f '' s) = perimeter μ V s := by
  rw [image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply]
  exact perimeter_preimage f.symm
    (MeasurePreserving.symm ⟨f.toEquiv, hf.measurable, hinv⟩ hf)
    hf.measurable hOV (by simpa using hVO)

end AffineIsometryEquiv

namespace LinearIsometryEquiv

/-- Pulling a function back along a measure-preserving linear isometry equivalence `e` with
measurable inverse does not increase its total variation when `e` maps `V` into `Ω`. -/
theorem totalVariationOn_comp_le (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hinv : Measurable e.symm) (hVO : MapsTo e V Ω) :
    totalVariationOn μ V (u ∘ e) ≤ totalVariationOn ν Ω u :=
  e.toAffineIsometryEquiv.totalVariationOn_comp_le he hinv hVO

/-- **Isometry invariance of total variation.** If a measure-preserving linear isometry
equivalence `e` with measurable inverse identifies `V` with `Ω`, then pulling a function back
along `e` does not change its total variation. -/
theorem totalVariationOn_comp (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hinv : Measurable e.symm)
    (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    totalVariationOn μ V (u ∘ e) = totalVariationOn ν Ω u :=
  e.toAffineIsometryEquiv.totalVariationOn_comp he hinv hVO hOV

/-- Total variation is invariant under a measure-preserving linear isometry equivalence with
measurable inverse, with the pulled-back domain written canonically as the preimage open set. -/
theorem totalVariationOn_comap (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hinv : Measurable e.symm) :
    totalVariationOn μ (Opens.comap (e : C(E, E')) Ω) (u ∘ e) = totalVariationOn ν Ω u :=
  e.toAffineIsometryEquiv.totalVariationOn_comap he hinv

/-- Pulling a set back along a measure-preserving linear isometry equivalence `e` with measurable
inverse does not increase its perimeter when `e` maps `V` into `Ω`. -/
theorem perimeter_preimage_le (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hinv : Measurable e.symm) (hVO : MapsTo e V Ω) :
    perimeter μ V (e ⁻¹' s) ≤ perimeter ν Ω s :=
  e.toAffineIsometryEquiv.perimeter_preimage_le he hinv hVO

/-- **Isometry invariance of perimeter.** If a measure-preserving linear isometry equivalence `e`
with measurable inverse identifies `V` with `Ω`, then the perimeter in `V` of the preimage of `s`
equals the perimeter of `s` in `Ω`. -/
theorem perimeter_preimage (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hinv : Measurable e.symm)
    (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    perimeter μ V (e ⁻¹' s) = perimeter ν Ω s :=
  e.toAffineIsometryEquiv.perimeter_preimage he hinv hVO hOV

/-- Perimeter is invariant when a set and its ambient open set are both pulled back along the same
measure-preserving linear isometry equivalence with measurable inverse. -/
theorem perimeter_comap (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hinv : Measurable e.symm) :
    perimeter μ (Opens.comap (e : C(E, E')) Ω) (e ⁻¹' s) = perimeter ν Ω s :=
  e.toAffineIsometryEquiv.perimeter_comap he hinv

/-- The image of a set under a measure-preserving linear isometry equivalence `e` with measurable
inverse identifying `V` with `Ω` has, in `Ω`, the perimeter of the original set in `V`. -/
theorem perimeter_image {s : Set E} (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hinv : Measurable e.symm)
    (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    perimeter ν Ω (e '' s) = perimeter μ V s :=
  e.toAffineIsometryEquiv.perimeter_image he hinv hVO hOV

end LinearIsometryEquiv

end VariationAndPerimeter

section BVSpace

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']
  {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'}

namespace TauCeti.BV

section Aux

/-- Pull a BV class back along a map preserving the restricted measure and total variation. -/
private def compAux {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) : BV μ V :=
  ofFunction (u ∘ f) <| memBV_iff.mpr
    ⟨(hf.integrable_comp u.integrableOn.aestronglyMeasurable).mpr u.integrableOn,
      (htv u).trans_lt u.totalVariationOn_lt_top⟩

private theorem coeFn_compAux {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    (compAux hf htv u : E → ℝ) =ᵐ[μ.restrict V] u ∘ f :=
  coeFn_ofFunction (u ∘ f) _

private theorem toL1_compAux {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    (compAux hf htv u).toL1 = Lp.compMeasurePreserving f hf u.toL1 :=
  Lp.ext <| (coeFn_compAux hf htv u).trans (Lp.coeFn_compMeasurePreserving u.toL1 hf).symm

private theorem totalVariationOn_compAux {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    totalVariationOn μ V (compAux hf htv u) = totalVariationOn ν Ω u :=
  (totalVariationOn_congr_ae (coeFn_compAux hf htv u)).trans (htv u)

private theorem norm_compAux {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    ‖compAux hf htv u‖ = ‖u‖ := by
  rw [norm_def, norm_def, totalVariationOn_compAux hf htv u,
    toL1_compAux hf htv u, Lp.norm_compMeasurePreserving u.toL1 hf]

/-- Assemble a linear isometric equivalence `BV ν Ω ≃ₗᵢ[ℝ] BV μ V` from an inverse pair of maps
that preserve the restricted measures and total variation. -/
private def compEquivAux {f : E → E'} {g : E' → E}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (hg : MeasurePreserving g (ν.restrict Ω) (μ.restrict V))
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w) :
    BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  { toFun := compAux hf htv
    invFun := compAux hg (totalVariationOn_comp_symm hgf htv)
    left_inv u := toL1_injective <| by
      rw [toL1_compAux, toL1_compAux]
      exact Lp.leftInverse_compMeasurePreserving hf hg (.of_forall hfg) u.toL1
    right_inv v := toL1_injective <| by
      rw [toL1_compAux, toL1_compAux]
      exact Lp.leftInverse_compMeasurePreserving hg hf (.of_forall hgf) v.toL1
    map_add' u v := toL1_injective <| by simp [toL1_compAux]
    map_smul' c u := toL1_injective <| by
      simpa only [RingHom.id_apply, toL1_compAux, toL1_smul, Lp.compMeasurePreservingₗᵢ_apply]
        using map_smul (Lp.compMeasurePreservingₗᵢ ℝ f hf) c u.toL1
    norm_map' := norm_compAux hf htv }

private theorem compEquivAux_apply {f : E → E'} {g : E' → E}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (hg : MeasurePreserving g (ν.restrict Ω) (μ.restrict V))
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    compEquivAux hf hg hfg hgf htv u = compAux hf htv u :=
  rfl

private theorem compEquivAux_symm_apply {f : E → E'} {g : E' → E}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (hg : MeasurePreserving g (ν.restrict Ω) (μ.restrict V))
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (v : BV μ V) :
    (compEquivAux hf hg hfg hgf htv).symm v =
      compAux hg (totalVariationOn_comp_symm hgf htv) v :=
  rfl

/-- Factoring `BV.toL1CLM` through a linear isometry equivalence `L : BV ν Ω ≃ₗᵢ[ℝ] BV μ V`
and a measure-preserving pullback `f` transports compactness of `BV.toL1CLM`. -/
private theorem isCompactOperator_toL1CLM_of_compEquiv
    {f : E → E'} (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (L : BV ν Ω ≃ₗᵢ[ℝ] BV μ V)
    (hcomm : ∀ x : BV ν Ω, (L x).toL1 = Lp.compMeasurePreserving f hf x.toL1)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) := by
  let S : (E' →₁[ν.restrict Ω] ℝ) →L[ℝ] (E →₁[μ.restrict V] ℝ) :=
    (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap
  have hfac : (BV.toL1CLM : BV μ V →L[ℝ] _) = S.comp ((BV.toL1CLM : BV ν Ω →L[ℝ] _).comp
      L.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext1 y
    simp [S, Lp.compMeasurePreservingₗᵢ_apply, ← hcomm (L.symm y)]
  rw [hfac]
  exact (hcpt.comp_clm _).clm_comp S

end Aux

end TauCeti.BV

namespace AffineIsometryEquiv

omit [OpensMeasurableSpace E] [OpensMeasurableSpace E'] in
/-- **BV membership is invariant under affine isometries.** If a measure-preserving affine
isometry equivalence `f` with measurable inverse satisfies `V = f ⁻¹' Ω`, then `u ∘ f` is BV on `V`
exactly when `u` is BV on `Ω`. -/
theorem memBV_comp_iff {u : E' → ℝ} (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω) :
    MemBV μ V (u ∘ f) ↔ MemBV ν Ω u := by
  have hOV : (Ω : Set E') = f.symm ⁻¹' V := hVO ▸ (f.toEquiv.symm_preimage_preimage Ω).symm
  rw [memBV_iff, memBV_iff, f.totalVariationOn_comp hf hinv
      (mapsTo_iff_subset_preimage.mpr hVO.subset) (mapsTo_iff_subset_preimage.mpr hOV.subset),
    hVO, hf.integrableOn_comp_preimage
      (⟨f.toEquiv, hf.measurable, hinv⟩ : E ≃ᵐ E').measurableEmbedding]

/-- **Isometric transport of `BV` along an affine isometry equivalence.** Precomposition with a
measure-preserving affine isometry equivalence `f : E ≃ᵃⁱ[ℝ] E'` with measurable inverse is a
linear isometric equivalence `BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = f ⁻¹' Ω`. Its inverse is the
transport along `f.symm` (`AffineIsometryEquiv.compBV_symm`). -/
def compBV (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm)
    (hVO : (V : Set E) = f ⁻¹' Ω) : BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  have hOV : (Ω : Set E') = f.symm ⁻¹' V := hVO ▸ (f.toEquiv.symm_preimage_preimage Ω).symm
  BV.compEquivAux (hf.restrict_of_preimage_eq Ω.isOpen.measurableSet hVO)
    (MeasurePreserving.restrict_of_preimage_eq (f := f.symm)
      (MeasurePreserving.symm ⟨f.toEquiv, hf.measurable, hinv⟩ hf) V.isOpen.measurableSet hOV)
    f.apply_symm_apply f.symm_apply_apply fun _ =>
      f.totalVariationOn_comp hf hinv (mapsTo_iff_subset_preimage.mpr hVO.subset)
        (mapsTo_iff_subset_preimage.mpr hOV.subset)

/-- The `L¹` class of a BV class pulled back along `f` is `Lp.compMeasurePreserving` of its `L¹`
class. -/
theorem toL1_compBV (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm)
    (hVO : (V : Set E) = f ⁻¹' Ω) (u : BV ν Ω) :
    (compBV f hf hinv hVO u).toL1 =
      Lp.compMeasurePreserving f (hf.restrict_of_preimage_eq Ω.isOpen.measurableSet hVO)
        u.toL1 := by
  rw [compBV, BV.compEquivAux_apply]
  exact BV.toL1_compAux _ _ u

/-- The `L¹` class of the inverse of `compBV f` is `Lp.compMeasurePreserving` along `f.symm`. -/
theorem toL1_compBV_symm (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω) (v : BV μ V) :
    ((compBV f hf hinv hVO).symm v).toL1 =
      Lp.compMeasurePreserving f.symm
        (hf.symm_restrict_of_preimage_eq ⟨f.toEquiv, hf.measurable, hinv⟩ hVO) v.toL1 := by
  rw [compBV, BV.compEquivAux_symm_apply]
  exact BV.toL1_compAux _ _ v

/-- The pulled-back class is represented by `u ∘ f` almost everywhere on `V`. -/
theorem coeFn_compBV (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm)
    (hVO : (V : Set E) = f ⁻¹' Ω) (u : BV ν Ω) :
    (compBV f hf hinv hVO u : E → ℝ) =ᵐ[μ.restrict V] u ∘ f := by
  rw [compBV, BV.compEquivAux_apply]
  exact BV.coeFn_compAux _ _ u

/-- The inverse of `compBV f` precomposes representatives with `f.symm` almost everywhere on
`Ω`. -/
theorem coeFn_compBV_symm (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω) (v : BV μ V) :
    ((compBV f hf hinv hVO).symm v : E' → ℝ) =ᵐ[ν.restrict Ω] v ∘ f.symm := by
  rw [compBV, BV.compEquivAux_symm_apply]
  exact BV.coeFn_compAux _ _ v

/-- Pulling a BV class back along `f` preserves its total variation. -/
@[simp]
theorem totalVariationOn_compBV (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω) (u : BV ν Ω) :
    totalVariationOn μ V (compBV f hf hinv hVO u) = totalVariationOn ν Ω u := by
  rw [compBV, BV.compEquivAux_apply]
  exact BV.totalVariationOn_compAux _ _ u

/-- Applying the inverse of `compBV f` preserves total variation. -/
@[simp]
theorem totalVariationOn_compBV_symm (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω) (v : BV μ V) :
    totalVariationOn ν Ω ((compBV f hf hinv hVO).symm v) = totalVariationOn μ V v := by
  rw [compBV, BV.compEquivAux_symm_apply]
  exact BV.totalVariationOn_compAux _ _ v

/-- The inverse of `compBV` along `f` is `compBV` along `f.symm`. -/
theorem compBV_symm (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) (hinv : Measurable f.symm)
    (hVO : (V : Set E) = f ⁻¹' Ω) :
    (compBV f hf hinv hVO).symm =
      compBV f.symm (MeasurePreserving.symm ⟨f.toEquiv, hf.measurable, hinv⟩ hf) hf.measurable
        (hVO ▸ (f.toEquiv.symm_preimage_preimage Ω).symm) := by
  ext1 v
  exact BV.ext <| (coeFn_compBV_symm f hf hinv hVO v).trans (coeFn_compBV _ _ _ _ v).symm

/-- Transport by `compBV f` commutes with forming a BV class. -/
@[simp]
theorem compBV_ofFunction (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω) (u : E' → ℝ) (hu : MemBV ν Ω u) :
    compBV f hf hinv hVO (BV.ofFunction u hu) =
      BV.ofFunction (u ∘ f) ((memBV_comp_iff f hf hinv hVO).mpr hu) :=
  BV.ext <| (coeFn_compBV f hf hinv hVO _).trans <|
    ((hf.restrict_of_preimage_eq Ω.isOpen.measurableSet hVO).quasiMeasurePreserving.ae_eq_comp
      (BV.coeFn_ofFunction u hu)).trans (BV.coeFn_ofFunction _ _).symm

/-- Pulling `BV` back along a measure-preserving affine isometry equivalence `f` with measurable
inverse and `V = f ⁻¹' Ω` transports compactness of `BV.toL1CLM` from `Ω` to `V`. -/
theorem isCompactOperator_toL1CLM (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) :=
  BV.isCompactOperator_toL1CLM_of_compEquiv
    (hf.restrict_of_preimage_eq Ω.isOpen.measurableSet hVO)
    (f.compBV hf hinv hVO) (f.toL1_compBV hf hinv hVO) hcpt

/-- **Invariance of compactness of `BV.toL1CLM` under affine isometry equivalences.** -/
theorem isCompactOperator_toL1CLM_iff (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hinv : Measurable f.symm) (hVO : (V : Set E) = f ⁻¹' Ω) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) ↔
      IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _) :=
  ⟨BV.isCompactOperator_toL1CLM_of_compEquiv
    (hf.symm_restrict_of_preimage_eq ⟨f.toEquiv, hf.measurable, hinv⟩ hVO)
    (f.compBV hf hinv hVO).symm
    (f.toL1_compBV_symm hf hinv hVO),
    f.isCompactOperator_toL1CLM hf hinv hVO⟩

end AffineIsometryEquiv

end BVSpace
