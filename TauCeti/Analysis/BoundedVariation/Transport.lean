/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Isometry
public import TauCeti.Analysis.BoundedVariation.Space

/-!
# Transport of BV functions by affine isometries

Global BV membership and the Banach space `BV(Ω)` of `TauCeti.Analysis.BoundedVariation.Space`
are transported along a measure-preserving affine isometry equivalence `f` identifying `V` with
`Ω`: `u ↦ u ∘ f` preserves BV membership (`AffineIsometryEquiv.memBV_comp_iff`) and induces a
linear isometry equivalence
`AffineIsometryEquiv.compBV f hf hVO hOV : BV ν Ω ≃ₗᵢ[ℝ] BV μ V`. Rigid motions of a Euclidean
space with its Lebesgue measure are the main instance. This extends
`TauCeti.BV.compLinearIsometryEquiv` from linear to affine isometries. Dilations of BV classes are
`TauCeti.BV.compSmul`.

The domains are arbitrary open sets, with no boundedness or regularity assumption. The operator
is characterized on representatives (`AffineIsometryEquiv.coeFn_compBV`) and on classes formed
from functions (`AffineIsometryEquiv.compBV_ofFunction`).

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TauCeti
open scoped ENNReal

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']

namespace TauCeti.BV

variable {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'}

/-- Pulling BV classes back along a map which is quasi-measure-preserving between the restricted
measures and which preserves BV membership. -/
private def compₗ (g : E → E') (hg : QuasiMeasurePreserving g (μ.restrict V) (ν.restrict Ω))
    (hmem : ∀ u : E' → ℝ, MemBV ν Ω u → MemBV μ V (u ∘ g)) : BV ν Ω →ₗ[ℝ] BV μ V where
  toFun u := ofFunction (u ∘ g) (hmem u u.memBV)
  map_add' u v := by
    apply ext
    filter_upwards [coeFn_ofFunction _ (hmem _ (u + v).memBV),
      coeFn_add (ofFunction _ (hmem u u.memBV)) (ofFunction _ (hmem v v.memBV)),
      coeFn_ofFunction _ (hmem u u.memBV), coeFn_ofFunction _ (hmem v v.memBV),
      hg.ae_eq_comp (coeFn_add u v)] with x h₁ h₂ h₃ h₄ h₅
    simp_all
  map_smul' c u := by
    apply ext
    filter_upwards [coeFn_ofFunction _ (hmem _ (c • u).memBV),
      coeFn_smul c (ofFunction _ (hmem u u.memBV)), coeFn_ofFunction _ (hmem u u.memBV),
      hg.ae_eq_comp (coeFn_smul c u)] with x h₁ h₂ h₃ h₄
    simp_all

private theorem compₗ_apply (g : E → E')
    (hg : QuasiMeasurePreserving g (μ.restrict V) (ν.restrict Ω))
    (hmem : ∀ u : E' → ℝ, MemBV ν Ω u → MemBV μ V (u ∘ g)) (u : BV ν Ω) :
    compₗ g hg hmem u = ofFunction (u ∘ g) (hmem u u.memBV) := (rfl)

private theorem compₗ_ofFunction (g : E → E')
    (hg : QuasiMeasurePreserving g (μ.restrict V) (ν.restrict Ω))
    (hmem : ∀ u : E' → ℝ, MemBV ν Ω u → MemBV μ V (u ∘ g)) (u : E' → ℝ) (hu : MemBV ν Ω u) :
    compₗ g hg hmem (ofFunction u hu) = ofFunction (u ∘ g) (hmem u hu) :=
  ext <| (coeFn_ofFunction _ _).trans <|
    (hg.ae_eq_comp (coeFn_ofFunction u hu)).trans (coeFn_ofFunction _ _).symm

/-- Pulling back along `g` and then along a right inverse `g'` of `g` is the identity. -/
private theorem compₗ_compₗ (g : E → E') (g' : E' → E) (hgg' : ∀ y, g (g' y) = y)
    (hg : QuasiMeasurePreserving g (μ.restrict V) (ν.restrict Ω))
    (hmem : ∀ u : E' → ℝ, MemBV ν Ω u → MemBV μ V (u ∘ g))
    (hg' : QuasiMeasurePreserving g' (ν.restrict Ω) (μ.restrict V))
    (hmem' : ∀ w : E → ℝ, MemBV μ V w → MemBV ν Ω (w ∘ g')) (u : BV ν Ω) :
    compₗ g' hg' hmem' (compₗ g hg hmem u) = u := by
  rw [compₗ_apply g, compₗ_ofFunction]
  conv_rhs => rw [← ofFunction_coeFn u]
  congr 1
  funext y
  simp [hgg']

end TauCeti.BV

/-! ### Affine isometries -/

namespace AffineIsometryEquiv

variable {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'} {u : E' → ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] in
private theorem coe_eq_preimage (f : E ≃ᵃⁱ[ℝ] E') (hVO : MapsTo f V Ω)
    (hOV : MapsTo f.symm Ω V) : (V : Set E) = f ⁻¹' Ω :=
  Set.ext fun x => ⟨fun hx => hVO hx, fun hx => by simpa using hOV hx⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
private theorem measurePreserving_symm (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) :
    MeasurePreserving f.symm ν μ := by
  simpa using MeasurePreserving.symm f.toHomeomorph.toMeasurableEquiv (by simpa using hf)

/-- **BV membership is invariant under affine isometries.** If a measure-preserving affine
isometry equivalence `f` identifies `V` with `Ω`, then `u ∘ f` is BV on `V` exactly when `u` is
BV on `Ω`. -/
theorem memBV_comp_iff (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    MemBV μ V (u ∘ f) ↔ MemBV ν Ω u := by
  rw [memBV_iff, memBV_iff, totalVariationOn_comp f hf f.symm.continuous.measurable hVO hOV,
    coe_eq_preimage f hVO hOV,
    hf.integrableOn_comp_preimage f.toHomeomorph.measurableEmbedding]

private theorem norm_ofFunction_comp (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) (u : BV ν Ω) (hu : MemBV μ V (u ∘ f)) :
    ‖BV.ofFunction _ hu‖ = ‖u‖ := by
  rw [BV.norm_def, BV.norm_def, BV.norm_toL1_ofFunction, BV.totalVariationOn_ofFunction,
    totalVariationOn_comp f hf f.symm.continuous.measurable hVO hOV, L1.norm_eq_integral_norm,
    coe_eq_preimage f hVO hOV]
  congr 1
  exact hf.setIntegral_preimage_emb f.toHomeomorph.measurableEmbedding (fun y => ‖u y‖) Ω

/-- Pulling BV classes back along a measure-preserving affine isometry equivalence `f`
identifying `V` with `Ω`, as a linear isometry equivalence for the BV norm. Its inverse pulls back
along `f.symm`. -/
def compBV (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) (hVO : MapsTo f V Ω)
    (hOV : MapsTo f.symm Ω V) : BV ν Ω ≃ₗᵢ[ℝ] BV μ V :=
  have hg := hf.quasiMeasurePreserving.restrict hVO
  have hg' := (measurePreserving_symm f hf).quasiMeasurePreserving.restrict hOV
  have hmem (u : E' → ℝ) (hu : MemBV ν Ω u) : MemBV μ V (u ∘ f) :=
    (memBV_comp_iff f hf hVO hOV).mpr hu
  have hmem' (w : E → ℝ) (hw : MemBV μ V w) : MemBV ν Ω (w ∘ f.symm) :=
    (memBV_comp_iff f hf hVO hOV).mp (by simpa [Function.comp_def] using hw)
  { BV.compₗ f hg hmem with
    invFun := BV.compₗ f.symm hg' hmem'
    left_inv := BV.compₗ_compₗ _ _ (fun y => f.apply_symm_apply y) hg hmem hg' hmem'
    right_inv := BV.compₗ_compₗ _ _ (fun x => f.symm_apply_apply x) hg' hmem' hg hmem
    norm_map' := fun u => norm_ofFunction_comp f hf hVO hOV u _ }

private theorem compBV_apply (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) (u : BV ν Ω) :
    compBV f hf hVO hOV u = BV.ofFunction (u ∘ f) ((memBV_comp_iff f hf hVO hOV).mpr u.memBV) :=
  (rfl)

private theorem compBV_symm_apply (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) (w : BV μ V) :
    (compBV f hf hVO hOV).symm w = BV.ofFunction (w ∘ f.symm)
      ((memBV_comp_iff f hf hVO hOV).mp (by simpa [Function.comp_def] using w.memBV)) :=
  (rfl)

/-- The pulled-back class is represented by `u ∘ f` almost everywhere on `V`. -/
theorem coeFn_compBV (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν) (hVO : MapsTo f V Ω)
    (hOV : MapsTo f.symm Ω V) (u : BV ν Ω) :
    (compBV f hf hVO hOV u : E → ℝ) =ᵐ[μ.restrict V] (u : E' → ℝ) ∘ f := by
  rw [compBV_apply]
  exact BV.coeFn_ofFunction _ _

/-- The inverse of `compBV f` pulls back along `f.symm`. -/
theorem coeFn_compBV_symm (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) (w : BV μ V) :
    ((compBV f hf hVO hOV).symm w : E' → ℝ) =ᵐ[ν.restrict Ω] (w : E → ℝ) ∘ f.symm := by
  rw [compBV_symm_apply]
  exact BV.coeFn_ofFunction _ _

/-- Transport by `compBV f` commutes with forming a BV class. -/
@[simp]
theorem compBV_ofFunction (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) (u : E' → ℝ) (hu : MemBV ν Ω u) :
    compBV f hf hVO hOV (BV.ofFunction u hu) =
      BV.ofFunction (u ∘ f) ((memBV_comp_iff f hf hVO hOV).mpr hu) :=
  BV.ext <| (coeFn_compBV f hf hVO hOV _).trans <|
    ((hf.quasiMeasurePreserving.restrict hVO).ae_eq_comp (BV.coeFn_ofFunction u hu)).trans
      (BV.coeFn_ofFunction _ _).symm

/-- Transport by `compBV f` preserves total variation. -/
@[simp]
theorem totalVariationOn_compBV (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) (u : BV ν Ω) :
    totalVariationOn μ V (compBV f hf hVO hOV u) = totalVariationOn ν Ω u := by
  rw [totalVariationOn_congr_ae (coeFn_compBV f hf hVO hOV u),
    totalVariationOn_comp f hf f.symm.continuous.measurable hVO hOV]

end AffineIsometryEquiv
