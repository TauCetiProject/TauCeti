/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.Space
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Isometric transport of distributional total variation, BV spaces, and perimeter

Distributional total variation is unchanged when a function and its open domain are pulled back
by a measure-preserving linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'`, such as a rotation or a
reflection of a Euclidean space with its Lebesgue measure. If only `e '' V ⊆ Ω`, the pulled-back
variation on `V` is bounded by the variation on `Ω`. Perimeter is transported in the same way,
both for preimages and for images of sets.

Combining linear transport and translation of test vector fields gives the same invariance for
every measure-preserving affine isometry equivalence `f : E ≃ᵃⁱ[ℝ] E'`, without assuming that the
target measure is translation invariant; in particular this covers rigid motions of a Euclidean
space.

Combining invariance of total variation with `L¹` change of variables induces the linear isometric
equivalence `TauCeti.BV.compLinearIsometryEquiv : BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = e ⁻¹' Ω`,
and consequently transports compactness of `BV.toL1CLM` along measure-preserving linear isometry
equivalences.

The proof transports each admissible test vector field `φ` on `V` to `y ↦ L (φ (f.symm y))` on `Ω`,
where `L` is the linear part of `f`. This preserves the pointwise norm, and its divergence is the
transported divergence of `φ`, so the defining pairings agree after the change of variables
`y = f x`. No integrability, measurability, boundedness, or finiteness assumption on the function
or the set is needed; in particular the results apply to sets of infinite volume or infinite
perimeter.

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
* `TauCeti.BV.compLinearIsometryEquiv`: isometric equivalence of `TauCeti.BV` spaces along a
  measure-preserving linear isometry equivalence.
* `TauCeti.BV.isCompactOperator_toL1CLM_of_linearIsometryEquiv` and
  `TauCeti.BV.isCompactOperator_toL1CLM_iff_of_linearIsometryEquiv`: invariance of compactness of
  `BV.toL1CLM` under linear isometry equivalences.

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

/-- Upgrade a measurable homeomorphism from a Borel space into an `OpensMeasurableSpace` to a
measurable equivalence. -/
private def measurableEquivOfMeasurable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasurableSpace α] [BorelSpace α] [MeasurableSpace β] [OpensMeasurableSpace β]
    (h : α ≃ₜ β) (hh : Measurable h) : α ≃ᵐ β :=
  ⟨h.toEquiv, hh, h.symm.continuous.measurable⟩

/-- A measurable homeomorphism from a Borel space into an `OpensMeasurableSpace` forces the target
to be a Borel space as well. -/
private theorem borelSpace_of_measurable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasurableSpace α] [BorelSpace α] [MeasurableSpace β] [OpensMeasurableSpace β]
    (h : α ≃ₜ β) (hh : Measurable h) : BorelSpace β :=
  (measurableEquivOfMeasurable h hh).symm.measurableEmbedding.borelSpace h.symm.isInducing

/-- The perimeter of a preimage is the total variation of the pulled-back indicator. -/
private theorem perimeter_preimage_eq_totalVariationOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] {E' : Type*} {μ : Measure E} {V : Opens E} {s : Set E'}
    (f : E → E') :
    perimeter μ V (f ⁻¹' s) = totalVariationOn μ V (s.indicator 1 ∘ f) := by
  rw [perimeter_def]
  exact congrArg (totalVariationOn μ V)
    (funext fun _ => Set.indicator_comp_right (g := fun _ => (1 : ℝ)) f)

/-- Pulling a function back along a measure-preserving affine isometry equivalence `f` does not
increase its total variation when `f` maps `V` into `Ω`. -/
private theorem totalVariationOn_comp_affine_le
    {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']
    {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'} {u : E' → ℝ}
    (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) (hVO : MapsTo f V Ω) :
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
    rw [← hf.integral_comp
      (measurableEquivOfMeasurable f.toHomeomorph hf.measurable).measurableEmbedding]
    simp [hdiv]
  rw [hpair]
  refine ofReal_integral_le_totalVariationOn ψ fun y => ?_
  simp only [ψ, ψ₁, translateTestFunction_apply, postcompCLM_apply, Function.comp_apply,
    ContinuousLinearEquiv.transportTestFunction_apply, ← hfsymm]
  simpa [L] using hφ (f.symm y)

end TauCeti

section VariationAndPerimeter

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']
  {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'} {u : E' → ℝ} {s : Set E'}

namespace LinearIsometryEquiv

/-- Pulling a function back along a measure-preserving linear isometry equivalence `e` does not
increase its total variation when `e` maps `V` into `Ω`. -/
theorem totalVariationOn_comp_le (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hVO : MapsTo e V Ω) :
    totalVariationOn μ V (u ∘ e) ≤ totalVariationOn ν Ω u :=
  totalVariationOn_comp_affine_le e.toAffineIsometryEquiv he hVO

/-- **Isometry invariance of total variation.** If a measure-preserving linear isometry
equivalence `e` identifies `V` with `Ω`, then pulling a function back along `e` does not change
its total variation. -/
theorem totalVariationOn_comp (e : E ≃ₗᵢ[ℝ] E')
    (he : MeasurePreserving e μ ν) (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    totalVariationOn μ V (u ∘ e) = totalVariationOn ν Ω u := by
  have : BorelSpace E' := borelSpace_of_measurable e.toHomeomorph he.measurable
  refine le_antisymm (totalVariationOn_comp_le e he hVO) ?_
  simpa [Function.comp_def] using totalVariationOn_comp_le (u := u ∘ e) e.symm
    (MeasurePreserving.symm (measurableEquivOfMeasurable e.toHomeomorph he.measurable) he) hOV

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
  have : BorelSpace E' := borelSpace_of_measurable e.toHomeomorph he.measurable
  rw [e.image_eq_preimage_symm]
  exact perimeter_preimage e.symm
    (MeasurePreserving.symm (measurableEquivOfMeasurable e.toHomeomorph he.measurable) he)
    hOV (by simpa using hVO)

end LinearIsometryEquiv

namespace AffineIsometryEquiv

/-- **Invariance of total variation under affine isometries.** Pulling a function and its open
domain back along a measure-preserving affine isometry equivalence does not change its total
variation. -/
theorem totalVariationOn_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) :
    totalVariationOn μ (Opens.comap ⟨f, f.continuous⟩ Ω) (u ∘ f) = totalVariationOn ν Ω u := by
  have : BorelSpace E' := borelSpace_of_measurable f.toHomeomorph hf.measurable
  refine le_antisymm
    (totalVariationOn_comp_affine_le f hf fun _ hx => Opens.mem_comap.mp hx) ?_
  simpa [Function.comp_def] using totalVariationOn_comp_affine_le (u := u ∘ f) f.symm
    (MeasurePreserving.symm (measurableEquivOfMeasurable f.toHomeomorph hf.measurable) hf)
    fun y hy => Opens.mem_comap.mpr (by simpa using hy)

/-- **Invariance of perimeter under affine isometries.** Pulling a set and its open domain back
along a measure-preserving affine isometry equivalence does not change its perimeter. -/
theorem perimeter_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) :
    perimeter μ (Opens.comap ⟨f, f.continuous⟩ Ω) (f ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap f hf

end AffineIsometryEquiv

end VariationAndPerimeter

namespace TauCeti.BV

section Aux

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']
  {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'}

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
  have htv' (w : E → ℝ) : totalVariationOn ν Ω (w ∘ g) = totalVariationOn μ V w := by
    rw [← htv (w ∘ g)]
    exact congrArg (totalVariationOn μ V) (funext fun x => congrArg w (hgf x))
  { toFun := compAux hf htv
    invFun := compAux hg htv'
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
    (compEquivAux hf hg hfg hgf htv).symm v = compAux hg (fun w => by
      rw [← htv (w ∘ g)]
      exact congrArg (totalVariationOn μ V) (funext fun x => congrArg w (hgf x))) v :=
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

section LinearIsometryEquiv

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']
  {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'} {e : E ≃ₗᵢ[ℝ] E'}

/-- **Isometric transport of `BV` along a linear isometry equivalence.** Precomposition with a
measure-preserving linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` is a linear isometric equivalence
`BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = e ⁻¹' Ω`. -/
def compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) : BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  have hOV : (Ω : Set E') = e.symm ⁻¹' V := by
    ext y
    simp [hVO]
  compEquivAux (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet)
    (hOV ▸ (MeasurePreserving.symm (measurableEquivOfMeasurable e.toHomeomorph he.measurable)
      he).restrict_preimage V.isOpen.measurableSet)
    e.apply_symm_apply e.symm_apply_apply fun w =>
      e.totalVariationOn_comp he (mapsTo_iff_subset_preimage.mpr hVO.subset)
        (mapsTo_iff_subset_preimage.mpr hOV.subset)

/-- The `L¹` class of a BV class pulled back along `e` is `Lp.compMeasurePreserving` of its `L¹`
class. -/
theorem toL1_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    (compLinearIsometryEquiv he hVO u).toL1 =
      Lp.compMeasurePreserving e (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet) u.toL1 := by
  rw [compLinearIsometryEquiv, compEquivAux_apply]
  exact toL1_compAux _ _ u

/-- The `L¹` class of the inverse of `compLinearIsometryEquiv` is `Lp.compMeasurePreserving` along
`e.symm`. -/
theorem toL1_compLinearIsometryEquiv_symm (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (v : BV μ V) :
    ((compLinearIsometryEquiv he hVO).symm v).toL1 =
      Lp.compMeasurePreserving e.symm
        (MeasurePreserving.symm ⟨e.toEquiv, he.measurable, e.symm.continuous.measurable⟩
          (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet)) v.toL1 := by
  rw [compLinearIsometryEquiv, compEquivAux_symm_apply]
  exact toL1_compAux _ _ v

/-- Pulling a BV class back along `e` precomposes its representative with `e` almost everywhere on
`V`. -/
theorem coeFn_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    (compLinearIsometryEquiv he hVO u : E → ℝ) =ᵐ[μ.restrict V] u ∘ e := by
  rw [compLinearIsometryEquiv, compEquivAux_apply]
  exact coeFn_compAux _ _ u

/-- The inverse of `compLinearIsometryEquiv` precomposes representatives with `e.symm` almost
everywhere on `Ω`. -/
theorem coeFn_compLinearIsometryEquiv_symm (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (v : BV μ V) :
    ((compLinearIsometryEquiv he hVO).symm v : E' → ℝ) =ᵐ[ν.restrict Ω] v ∘ e.symm := by
  rw [compLinearIsometryEquiv, compEquivAux_symm_apply]
  exact coeFn_compAux _ _ v

/-- Pulling a BV class back along `e` preserves its total variation. -/
@[simp]
theorem totalVariationOn_compLinearIsometryEquiv
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    totalVariationOn μ V (compLinearIsometryEquiv he hVO u) = totalVariationOn ν Ω u := by
  rw [compLinearIsometryEquiv, compEquivAux_apply]
  exact totalVariationOn_compAux _ _ u

/-- Applying the inverse of `compLinearIsometryEquiv` preserves total variation. -/
@[simp]
theorem totalVariationOn_compLinearIsometryEquiv_symm
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) (v : BV μ V) :
    totalVariationOn ν Ω ((compLinearIsometryEquiv he hVO).symm v) = totalVariationOn μ V v := by
  rw [compLinearIsometryEquiv, compEquivAux_symm_apply]
  exact totalVariationOn_compAux _ _ v

/-- The inverse of `compLinearIsometryEquiv` along `e` is `compLinearIsometryEquiv` along
`e.symm`. -/
theorem compLinearIsometryEquiv_symm (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) :
    (compLinearIsometryEquiv he hVO).symm =
      @compLinearIsometryEquiv E' E _ _ _ _ _ _ _
        ((⟨e.symm.toEquiv, e.symm.continuous.measurable, he.measurable⟩ :
          E' ≃ᵐ E).measurableEmbedding.borelSpace e.symm.toHomeomorph.isInducing)
        _ _ ν μ Ω V e.symm
        (MeasurePreserving.symm ⟨e.toEquiv, he.measurable, e.symm.continuous.measurable⟩ he)
        (show (Ω : Set E') = e.symm ⁻¹' V by ext y; simp [hVO]) := by
  have : BorelSpace E' := borelSpace_of_measurable e.toHomeomorph he.measurable
  ext1 v
  exact ext <| (coeFn_compLinearIsometryEquiv_symm he hVO v).trans
    (coeFn_compLinearIsometryEquiv _ _ v).symm

/-- Pulling `BV` back along a measure-preserving linear isometry equivalence `e` with `V = e ⁻¹' Ω`
transports compactness of `BV.toL1CLM` from `Ω` to `V`. -/
theorem isCompactOperator_toL1CLM_of_linearIsometryEquiv
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) :=
  isCompactOperator_toL1CLM_of_compEquiv
    (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet)
    (compLinearIsometryEquiv he hVO) (toL1_compLinearIsometryEquiv he hVO) hcpt

/-- **Invariance of compactness of `BV.toL1CLM` under linear isometry equivalences.** -/
theorem isCompactOperator_toL1CLM_iff_of_linearIsometryEquiv
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) ↔
      IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _) :=
  ⟨isCompactOperator_toL1CLM_of_compEquiv
    (MeasurePreserving.symm (measurableEquivOfMeasurable e.toHomeomorph he.measurable)
      (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet))
    (compLinearIsometryEquiv he hVO).symm (toL1_compLinearIsometryEquiv_symm he hVO),
    isCompactOperator_toL1CLM_of_linearIsometryEquiv he hVO⟩

end LinearIsometryEquiv

end TauCeti.BV
