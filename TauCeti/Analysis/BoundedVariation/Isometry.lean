/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Analysis.BoundedVariation.Translation
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Isometric transport of distributional total variation, BV spaces, and perimeter

Distributional total variation is unchanged when a function and its open domain are pulled back
by a measure-preserving linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'`, such as a rotation or a
reflection of a Euclidean space with its Lebesgue measure. If only `e '' V ⊆ Ω`, the pulled-back
variation on `V` is bounded by the variation on `Ω`. Perimeter is transported in the same way,
both for preimages and for images of sets.

Combined with the translation invariance in `TauCeti.Analysis.BoundedVariation.Translation`, this
gives invariance under measure-preserving affine isometry equivalences into a space whose measure
is translation invariant, in particular under rigid motions of a Euclidean space.

Combining invariance of total variation with `L¹` change of variables induces the linear isometric
equivalence `TauCeti.BV.compLinearIsometryEquiv : BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = e ⁻¹' Ω`,
and consequently transports compactness of `BV.toL1CLM` along measure-preserving linear isometry
equivalences.

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
* `AffineIsometryEquiv.totalVariationOn_comap`, `AffineIsometryEquiv.totalVariationOn_comp` and
  `AffineIsometryEquiv.perimeter_comap`: invariance under affine isometry equivalences.
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

/-- **Invariance of total variation under affine isometries**, for any open set `V` which a
measure-preserving affine isometry equivalence `f` identifies with `Ω`. -/
theorem totalVariationOn_comp (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    totalVariationOn μ V (u ∘ f) = totalVariationOn ν Ω u := by
  obtain rfl : V = Opens.comap ⟨f, f.continuous⟩ Ω :=
    Opens.ext <| Set.ext fun x => ⟨fun hx => hVO hx, fun hx => by simpa using hOV hx⟩
  exact totalVariationOn_comap f hf

/-- **Invariance of perimeter under affine isometries.** Pulling a set and its open domain back
along a measure-preserving affine isometry equivalence into a space with a translation-invariant
measure does not change its perimeter. -/
theorem perimeter_comap (f : E ≃ᵃⁱ[ℝ] E')
    (hf : MeasurePreserving f μ ν) :
    perimeter μ (Opens.comap ⟨f, f.continuous⟩ Ω) (f ⁻¹' s) = perimeter ν Ω s := by
  rw [perimeter_preimage_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap f hf

end AffineIsometryEquiv

namespace TauCeti.BV

section Aux

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
private theorem totalVariationOn_compAux [OpensMeasurableSpace E] [OpensMeasurableSpace E']
    {f : E → E'} (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    totalVariationOn μ V (compAux hf htv u) = totalVariationOn ν Ω u :=
  (totalVariationOn_congr_ae (coeFn_compAux hf htv u)).trans (htv u)

omit [BorelSpace E] [BorelSpace E'] in
private theorem norm_compAux [OpensMeasurableSpace E] [OpensMeasurableSpace E'] {f : E → E'}
    (hf : MeasurePreserving f (μ.restrict V) (ν.restrict Ω))
    (htv : ∀ w : E' → ℝ, totalVariationOn μ V (w ∘ f) = totalVariationOn ν Ω w)
    (u : BV ν Ω) :
    ‖compAux hf htv u‖ = ‖u‖ := by
  rw [norm_def, norm_def, totalVariationOn_compAux hf htv u,
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
      map_add' u v := toL1_injective <| by simp [toL1_compAux]
      map_smul' c u := toL1_injective <| by
        simpa only [RingHom.id_apply, toL1_compAux, toL1_smul, Lp.compMeasurePreservingₗᵢ_apply]
          using map_smul (Lp.compMeasurePreservingₗᵢ ℝ f hf) c u.toL1 }
    (fun u => (norm_compAux hf htv u).le)
    (fun v => (norm_compAux hg (totalVariationOn_comp_symm hgf htv) v).le)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
/-- Factoring `BV.toL1CLM` through a linear isometry equivalence `L : BV μ₁ Ω₁ ≃ₗᵢ[ℝ] BV μ₂ Ω₂`
and a measure-preserving pullback `f` transports compactness of `BV.toL1CLM`. -/
private theorem isCompactOperator_toL1CLM_of_compEquiv
    {α₁ α₂ : Type*} [NormedAddCommGroup α₁] [InnerProductSpace ℝ α₁] [FiniteDimensional ℝ α₁]
    [NormedAddCommGroup α₂] [InnerProductSpace ℝ α₂] [FiniteDimensional ℝ α₂]
    [MeasurableSpace α₁] [OpensMeasurableSpace α₁] [MeasurableSpace α₂] [OpensMeasurableSpace α₂]
    {μ₁ : Measure α₁} {μ₂ : Measure α₂} {Ω₁ : Opens α₁} {Ω₂ : Opens α₂}
    {f : α₂ → α₁} (hf : MeasurePreserving f (μ₂.restrict Ω₂) (μ₁.restrict Ω₁))
    (L : BV μ₁ Ω₁ ≃ₗᵢ[ℝ] BV μ₂ Ω₂)
    (hcomm : ∀ x : BV μ₁ Ω₁, (L x).toL1 = Lp.compMeasurePreserving f hf x.toL1)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ₁ Ω₁ →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ₂ Ω₂ →L[ℝ] _) := by
  let S : (α₁ →₁[μ₁.restrict Ω₁] ℝ) →L[ℝ] (α₂ →₁[μ₂.restrict Ω₂] ℝ) :=
    (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap
  have hfac : (BV.toL1CLM : BV μ₂ Ω₂ →L[ℝ] _) = S.comp ((BV.toL1CLM : BV μ₁ Ω₁ →L[ℝ] _).comp
      L.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext1 y
    simp [S, Lp.compMeasurePreservingₗᵢ_apply, ← hcomm (L.symm y)]
  rw [hfac]
  exact (hcpt.comp_clm _).clm_comp S

end Aux

section LinearIsometryEquiv

variable {e : E ≃ₗᵢ[ℝ] E'}

omit [BorelSpace E'] in
/-- **Isometric transport of `BV` along a linear isometry equivalence.** Precomposition with a
measure-preserving linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` is a linear isometric equivalence
`BV ν Ω ≃ₗᵢ[ℝ] BV μ V` whenever `V = e ⁻¹' Ω`. -/
def compLinearIsometryEquiv [OpensMeasurableSpace E'] (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) : BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  have : BorelSpace E' :=
    (⟨e.symm.toEquiv, e.symm.continuous.measurable, he.measurable⟩ :
      E' ≃ᵐ E).measurableEmbedding.borelSpace e.symm.toHomeomorph.isInducing
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
theorem toL1_compLinearIsometryEquiv [OpensMeasurableSpace E'] (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    (compLinearIsometryEquiv he hVO u).toL1 =
      Lp.compMeasurePreserving e (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet) u.toL1 := by
  simp only [compLinearIsometryEquiv, compEquivAux, LinearIsometryEquiv.ofBounds,
    LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact toL1_compAux _ _ u

omit [BorelSpace E'] in
/-- The `L¹` class of the inverse of `compLinearIsometryEquiv` is `Lp.compMeasurePreserving` along
`e.symm`. -/
theorem toL1_compLinearIsometryEquiv_symm [OpensMeasurableSpace E'] (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (v : BV μ V) :
    ((compLinearIsometryEquiv he hVO).symm v).toL1 =
      Lp.compMeasurePreserving e.symm
        (MeasurePreserving.symm ⟨e.toEquiv, he.measurable, e.symm.continuous.measurable⟩
          (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet)) v.toL1 := by
  simp only [compLinearIsometryEquiv, compEquivAux, LinearIsometryEquiv.ofBounds,
    LinearIsometryEquiv.symm, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_symm_mk]
  exact toL1_compAux _ _ v

omit [BorelSpace E'] in
/-- Pulling a BV class back along `e` precomposes its representative with `e` almost everywhere on
`V`. -/
theorem coeFn_compLinearIsometryEquiv [OpensMeasurableSpace E'] (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    (compLinearIsometryEquiv he hVO u : E → ℝ) =ᵐ[μ.restrict V] u ∘ e := by
  simp only [compLinearIsometryEquiv, compEquivAux, LinearIsometryEquiv.ofBounds,
    LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact coeFn_compAux _ _ u

omit [BorelSpace E'] in
/-- The inverse of `compLinearIsometryEquiv` precomposes representatives with `e.symm` almost
everywhere on `Ω`. -/
theorem coeFn_compLinearIsometryEquiv_symm [OpensMeasurableSpace E'] (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) (v : BV μ V) :
    ((compLinearIsometryEquiv he hVO).symm v : E' → ℝ) =ᵐ[ν.restrict Ω] v ∘ e.symm := by
  simp only [compLinearIsometryEquiv, compEquivAux, LinearIsometryEquiv.ofBounds,
    LinearIsometryEquiv.symm, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_symm_mk]
  exact coeFn_compAux _ _ v

omit [BorelSpace E'] in
/-- Pulling a BV class back along `e` preserves its total variation. -/
@[simp]
theorem totalVariationOn_compLinearIsometryEquiv [OpensMeasurableSpace E']
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) (u : BV ν Ω) :
    totalVariationOn μ V (compLinearIsometryEquiv he hVO u) = totalVariationOn ν Ω u := by
  simp only [compLinearIsometryEquiv, compEquivAux, LinearIsometryEquiv.ofBounds,
    LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact totalVariationOn_compAux _ _ u

omit [BorelSpace E'] in
/-- Applying the inverse of `compLinearIsometryEquiv` preserves total variation. -/
@[simp]
theorem totalVariationOn_compLinearIsometryEquiv_symm [OpensMeasurableSpace E']
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) (v : BV μ V) :
    totalVariationOn ν Ω ((compLinearIsometryEquiv he hVO).symm v) = totalVariationOn μ V v := by
  simp only [compLinearIsometryEquiv, compEquivAux, LinearIsometryEquiv.ofBounds,
    LinearIsometryEquiv.symm, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_symm_mk]
  exact totalVariationOn_compAux _ _ v

omit [BorelSpace E'] in
/-- The inverse of `compLinearIsometryEquiv` along `e` is `compLinearIsometryEquiv` along
`e.symm`. -/
theorem compLinearIsometryEquiv_symm [OpensMeasurableSpace E'] (he : MeasurePreserving e μ ν)
    (hVO : (V : Set E) = e ⁻¹' Ω) :
    (compLinearIsometryEquiv he hVO).symm =
      @compLinearIsometryEquiv E' E _ _ _ _ _ _ _
        ((⟨e.symm.toEquiv, e.symm.continuous.measurable, he.measurable⟩ :
          E' ≃ᵐ E).measurableEmbedding.borelSpace e.symm.toHomeomorph.isInducing)
        _ ν μ Ω V e.symm _
        (MeasurePreserving.symm ⟨e.toEquiv, he.measurable, e.symm.continuous.measurable⟩ he)
        (show (Ω : Set E') = e.symm ⁻¹' V by rw [hVO, ← Set.preimage_comp]; ext y; simp) := by
  have : BorelSpace E' :=
    (⟨e.symm.toEquiv, e.symm.continuous.measurable, he.measurable⟩ :
      E' ≃ᵐ E).measurableEmbedding.borelSpace e.symm.toHomeomorph.isInducing
  ext1 v
  exact ext <| (coeFn_compLinearIsometryEquiv_symm he hVO v).trans
    (coeFn_compLinearIsometryEquiv _ _ v).symm

omit [BorelSpace E'] in
/-- Pulling `BV` back along a measure-preserving linear isometry equivalence `e` with `V = e ⁻¹' Ω`
transports compactness of `BV.toL1CLM` from `Ω` to `V`. -/
theorem isCompactOperator_toL1CLM_of_linearIsometryEquiv [OpensMeasurableSpace E']
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) :=
  isCompactOperator_toL1CLM_of_compEquiv
    (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet)
    (compLinearIsometryEquiv he hVO) (toL1_compLinearIsometryEquiv he hVO) hcpt

omit [BorelSpace E'] in
/-- **Invariance of compactness of `BV.toL1CLM` under linear isometry equivalences.** -/
theorem isCompactOperator_toL1CLM_iff_of_linearIsometryEquiv [OpensMeasurableSpace E']
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) ↔
      IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _) :=
  ⟨isCompactOperator_toL1CLM_of_compEquiv
    (MeasurePreserving.symm ⟨e.toEquiv, he.measurable, e.symm.continuous.measurable⟩
      (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet))
    (compLinearIsometryEquiv he hVO).symm (toL1_compLinearIsometryEquiv_symm he hVO),
    isCompactOperator_toL1CLM_of_linearIsometryEquiv he hVO⟩

end LinearIsometryEquiv

end TauCeti.BV
