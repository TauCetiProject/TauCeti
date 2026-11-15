/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Dilation
public import TauCeti.Analysis.BoundedVariation.Isometry
public import TauCeti.Analysis.BoundedVariation.Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Transport of BV functions by affine isometries and dilations

Global BV membership and the Banach space `BV(Ω)` of `TauCeti.Analysis.BoundedVariation.Space`
are transported along the two kinds of change of variables under which variation behaves
predictably.

* A measure-preserving affine isometry equivalence `f` identifying `V` with `Ω`, into a space with
  a translation-invariant measure: `u ↦ u ∘ f` preserves BV membership
  (`AffineIsometryEquiv.memBV_comp_iff`) and induces a linear isometry equivalence
  `AffineIsometryEquiv.compBV f hf hVO hOV : BV ν Ω ≃ₗᵢ[ℝ] BV μ V`. Rigid motions of a
  Euclidean space with its Lebesgue measure are the main instance.
* A positive dilation `x ↦ r • x` identifying `V` with `Ω`, for an additive Haar measure on a
  space of dimension `n`: `u ↦ u (r • ·)` preserves BV membership (`TauCeti.memBV_comp_smul_iff`)
  and induces a continuous linear equivalence
  `TauCeti.BV.compSMul hr hVO hOV : BV μ Ω ≃L[ℝ] BV μ V`, whose inverse is the dilation by
  `r⁻¹`. It multiplies the `L¹` norm by `r⁻ⁿ` and the variation by `r¹⁻ⁿ`, so its operator norm
  is at most the larger of these two factors.

The domains are arbitrary open sets, with no boundedness or regularity assumption. Each operator
is characterized on representatives (`coeFn_compBV`, `BV.coeFn_compSMul`) and on classes formed
from functions (`compBV_ofFunction`, `BV.compSMul_ofFunction`).

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TauCeti
open scoped ENNReal Pointwise

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

variable [ν.IsAddRightInvariant]

/-- **BV membership is invariant under affine isometries.** If a measure-preserving affine
isometry equivalence `f` identifies `V` with `Ω`, then `u ∘ f` is BV on `V` exactly when `u` is
BV on `Ω`. -/
theorem memBV_comp_iff (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) :
    MemBV μ V (u ∘ f) ↔ MemBV ν Ω u := by
  rw [memBV_iff, memBV_iff, totalVariationOn_comp f hf hVO hOV, coe_eq_preimage f hVO hOV,
    hf.integrableOn_comp_preimage f.toHomeomorph.measurableEmbedding]

private theorem norm_ofFunction_comp (f : E ≃ᵃⁱ[ℝ] E') (hf : MeasurePreserving f μ ν)
    (hVO : MapsTo f V Ω) (hOV : MapsTo f.symm Ω V) (u : BV ν Ω) (hu : MemBV μ V (u ∘ f)) :
    ‖BV.ofFunction _ hu‖ = ‖u‖ := by
  rw [BV.norm_def, BV.norm_def, BV.norm_toL1_ofFunction, BV.totalVariationOn_ofFunction,
    totalVariationOn_comp f hf hVO hOV, L1.norm_eq_integral_norm, coe_eq_preimage f hVO hOV]
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
  rw [totalVariationOn_congr_ae (coeFn_compBV f hf hVO hOV u), totalVariationOn_comp f hf hVO hOV]

end AffineIsometryEquiv

/-! ### Positive dilations -/

namespace TauCeti

variable {μ : Measure E} {V Ω : Opens E} {r : ℝ} {u : E → ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem coe_eq_preimage_smul (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) : (V : Set E) = (r • ·) ⁻¹' Ω :=
  Set.ext fun x => ⟨fun hx => hVO hx, fun hx => by simpa [inv_smul_smul₀ hr.ne'] using hOV hx⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem smul_coe_eq (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) : r • (V : Set E) = Ω := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  exact ⟨fun hy => by simpa [smul_inv_smul₀ hr.ne'] using hVO hy, fun hy => hOV hy⟩

variable [μ.IsAddHaarMeasure]

/-- **BV membership is invariant under positive dilations.** For an additive Haar measure, if
`x ↦ r • x` with `r > 0` identifies `V` with `Ω`, then `u (r • ·)` is BV on `V` exactly when `u`
is BV on `Ω`. -/
theorem memBV_comp_smul_iff (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    MemBV μ V (fun x => u (r • x)) ↔ MemBV μ Ω u := by
  have hint : IntegrableOn (fun x => u (r • x)) V μ ↔ IntegrableOn u Ω μ := by
    rw [← integrable_indicator_iff V.isOpen.measurableSet,
      ← integrable_indicator_iff Ω.isOpen.measurableSet, coe_eq_preimage_smul hr hVO hOV]
    exact integrable_comp_smul_iff μ ((Ω : Set E).indicator u) hr.ne'
  have hpos : ENNReal.ofReal (r / r ^ Module.finrank ℝ E) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [memBV_iff, memBV_iff, totalVariationOn_comp_smul hr hVO hOV, hint]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ENNReal.mul_lt_top (by finiteness) h⟩
  rcases ENNReal.mul_lt_top_iff.mp h with ⟨-, h⟩ | h | h
  · exact h
  · exact absurd h hpos
  · simp [h]

namespace BV

/-- The BV norm of `u (r • ·)` on `V` is at most the larger of the `L¹` factor `r⁻ⁿ` and the
variation factor `r¹⁻ⁿ` times the BV norm of `u` on `Ω`. -/
private theorem norm_ofFunction_comp_smul_le (hr : 0 < r)
    (hVO : MapsTo (fun x : E => r • x) V Ω) (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V)
    (u : BV μ Ω) (hu : MemBV μ V (fun x => u (r • x))) :
    ‖ofFunction _ hu‖ ≤
      max (r ^ Module.finrank ℝ E)⁻¹ (r / r ^ Module.finrank ℝ E) * ‖u‖ := by
  have hL1 : ‖(ofFunction _ hu).toL1‖ = (r ^ Module.finrank ℝ E)⁻¹ * ‖u.toL1‖ := by
    rw [norm_toL1_ofFunction, L1.norm_eq_integral_norm,
      Measure.setIntegral_comp_smul_of_pos μ (fun y => ‖u y‖) V hr, smul_coe_eq hr hVO hOV,
      smul_eq_mul]
  rw [norm_def, hL1, totalVariationOn_ofFunction, totalVariationOn_comp_smul hr hVO hOV,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), norm_def, mul_add]
  gcongr
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Pulling BV classes back by the positive dilation `x ↦ r • x` identifying `V` with `Ω`, for an
additive Haar measure, as a continuous linear equivalence for the BV norm. Its inverse is the
dilation by `r⁻¹` (`TauCeti.BV.compSMul_symm`). -/
def compSMul (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) : BV μ Ω ≃L[ℝ] BV μ V :=
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  have hVO' : MapsTo (fun y : E => r⁻¹⁻¹ • y) V Ω := by simpa only [inv_inv] using hVO
  have hg := (Measure.quasiMeasurePreserving_smul μ hr.ne').restrict hVO
  have hg' := (Measure.quasiMeasurePreserving_smul μ hr'.ne').restrict hOV
  have hmem (u : E → ℝ) (hu : MemBV μ Ω u) : MemBV μ V (u ∘ fun x => r • x) :=
    (memBV_comp_smul_iff hr hVO hOV).mpr hu
  have hmem' (w : E → ℝ) (hw : MemBV μ V w) : MemBV μ Ω (w ∘ fun y => r⁻¹ • y) :=
    (memBV_comp_smul_iff hr' hOV hVO').mpr hw
  LinearEquiv.toContinuousLinearEquivOfBounds
    { compₗ _ hg hmem with
      invFun := compₗ _ hg' hmem'
      left_inv := compₗ_compₗ _ _ (fun y => smul_inv_smul₀ hr.ne' y) hg hmem hg' hmem'
      right_inv := compₗ_compₗ _ _ (fun x => inv_smul_smul₀ hr.ne' x) hg' hmem' hg hmem }
    _ _ (fun u => norm_ofFunction_comp_smul_le hr hVO hOV u _)
    (fun w => norm_ofFunction_comp_smul_le hr' hOV hVO' w _)

variable (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω)
  (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V)

private theorem compSMul_apply (u : BV μ Ω) :
    compSMul hr hVO hOV u =
      ofFunction (fun x => u (r • x)) ((memBV_comp_smul_iff hr hVO hOV).mpr u.memBV) :=
  (rfl)

/-- The dilated class is represented by `u (r • ·)` almost everywhere on `V`. -/
theorem coeFn_compSMul (u : BV μ Ω) :
    (compSMul hr hVO hOV u : E → ℝ) =ᵐ[μ.restrict V] fun x => u (r • x) := by
  rw [compSMul_apply]
  exact coeFn_ofFunction _ _

/-- The inverse of a positive dilation of BV classes is the dilation by the inverse ratio. -/
theorem compSMul_symm :
    (compSMul (μ := μ) hr hVO hOV).symm =
      compSMul (inv_pos.mpr hr) hOV (by simpa only [inv_inv] using hVO) :=
  ContinuousLinearEquiv.ext <| funext fun w => by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    have hVO' : MapsTo (fun y : E => r⁻¹⁻¹ • y) V Ω := by simpa only [inv_inv] using hVO
    refine ext ?_
    filter_upwards [coeFn_compSMul hr hVO hOV (compSMul (inv_pos.mpr hr) hOV hVO' w),
      ((Measure.quasiMeasurePreserving_smul μ hr.ne').restrict hVO).ae_eq_comp
        (coeFn_compSMul (inv_pos.mpr hr) hOV hVO' w)] with x h₁ h₂
    rw [h₁]
    simpa [inv_smul_smul₀ hr.ne'] using h₂.symm

/-- Dilation commutes with forming a BV class. -/
@[simp]
theorem compSMul_ofFunction (u : E → ℝ) (hu : MemBV μ Ω u) :
    compSMul hr hVO hOV (ofFunction u hu) =
      ofFunction (fun x => u (r • x)) ((memBV_comp_smul_iff hr hVO hOV).mpr hu) :=
  ext <| (coeFn_compSMul hr hVO hOV _).trans <|
    (((Measure.quasiMeasurePreserving_smul μ hr.ne').restrict hVO).ae_eq_comp
      (coeFn_ofFunction u hu)).trans (coeFn_ofFunction _ _).symm

/-- A positive dilation multiplies total variation by `r / r ^ n`, where `n` is the dimension. -/
@[simp]
theorem totalVariationOn_compSMul (u : BV μ Ω) :
    totalVariationOn μ V (compSMul hr hVO hOV u) =
      ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rw [totalVariationOn_congr_ae (coeFn_compSMul hr hVO hOV u)]
  exact totalVariationOn_comp_smul hr hVO hOV

/-- A positive dilation multiplies the `L¹` norm by `r⁻ⁿ`, where `n` is the dimension. -/
@[simp]
theorem norm_toL1_compSMul (u : BV μ Ω) :
    ‖(compSMul hr hVO hOV u).toL1‖ = (r ^ Module.finrank ℝ E)⁻¹ * ‖u.toL1‖ := by
  rw [compSMul_apply, norm_toL1_ofFunction, L1.norm_eq_integral_norm,
    Measure.setIntegral_comp_smul_of_pos μ (fun y => ‖u y‖) V hr, smul_coe_eq hr hVO hOV,
    smul_eq_mul]

/-- The BV norm of a dilated class is at most the larger of the `L¹` and variation scaling
factors times the original norm. -/
theorem norm_compSMul_le (u : BV μ Ω) :
    ‖compSMul hr hVO hOV u‖ ≤
      max (r ^ Module.finrank ℝ E)⁻¹ (r / r ^ Module.finrank ℝ E) * ‖u‖ := by
  rw [compSMul_apply]
  exact norm_ofFunction_comp_smul_le hr hVO hOV u _

end BV

end TauCeti
