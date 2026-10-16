/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Measure-preserving Lipschitz changes of variables in `W^{1,p}`

Let `Φ : E → E'` be a measure-preserving map between finite-dimensional real inner product spaces
carrying additive Haar measures, and let `U = Φ⁻¹(V)` for open sets `U ⊆ E`, `V ⊆ E'`. If `Φ` is
locally Lipschitz on `U` with `‖fderiv ℝ Φ x‖ ≤ M` there, precomposition with `Φ` is a bounded
linear operator

`TauCeti.W1p.compMeasurePreservingL : W^{1,p}(V) →L[ℝ] W^{1,p}(U)`,

of norm at most `max 1 M`. The value of `u ∘ Φ` is `u ∘ Φ` and its weak gradient is
`x ↦ (fderiv ℝ Φ x)† (∇u (Φ x))`, the weak chain rule
`TauCeti.HasWeakFDerivOn.comp_measurePreserving` read through the Riesz representation. For
`p < ∞` and `Φ` proper (for instance a homeomorphism) the operator maps `W^{1,p}_0(V)` into
`W^{1,p}_0(U)`: a test function on `V` composed with `Φ` is supported in the compact set
`Φ⁻¹(tsupport φ) ⊆ U`.

Such changes of variables are the local charts of the boundary theory: a shear of a product
flattens the region above the graph of a Lipschitz function onto a half-space, and transports the
half-space trace to that region. Since `fderiv ℝ Φ` vanishes where `Φ` is not differentiable, a
`K`-Lipschitz `Φ` satisfies the derivative bound with `M = K` (`norm_fderiv_le_of_lipschitz`).

## Main declarations

* `TauCeti.W1p.compMeasurePreservingL`: the composition operator.
* `TauCeti.W1p.value_compMeasurePreservingL_ae`, `TauCeti.W1p.gradient_compMeasurePreservingL_ae`:
  its value and weak gradient.
* `TauCeti.W1p.norm_compMeasurePreservingL_le`: the bound `‖u ∘ Φ‖ ≤ max 1 M ‖u‖`.
* `TauCeti.W1p.compMeasurePreservingL_mem_w1p0Submodule`: zero boundary values are preserved.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Opens E} {V : Opens E'} {Φ : E → E'} {M : ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
  [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [ν.IsAddHaarMeasure] in
/-- Precomposition with `Φ` is measure-preserving from `U = Φ⁻¹(V)` to `V`. -/
private theorem measurePreserving_restrict (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) :
    MeasurePreserving Φ (μ.restrict U) (ν.restrict V) :=
  hUV ▸ hΦ.restrict_preimage V.isOpen.measurableSet

omit [μ.IsAddHaarMeasure] in
/-- The transported gradient `x ↦ (fderiv ℝ Φ x)† (∇u (Φ x))` lies in `Lᵖ(U)`. -/
private theorem memLp_adjoint_gradient (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (u : W1p ν V p) :
    MemLp (fun x => ContinuousLinearMap.adjoint (fderiv ℝ Φ x) (W1p.gradient u (Φ x))) p
      (μ.restrict U) := by
  have hg := (Lp.memLp (W1p.gradient u)).comp_measurePreserving
    (measurePreserving_restrict hΦ hUV)
  refine hg.of_le_mul (c := M) ?_ ((ae_restrict_iff' U.isOpen.measurableSet).2 <|
    Filter.Eventually.of_forall fun x hx => ?_)
  · exact (ContinuousLinearMap.apply ℝ E).aestronglyMeasurable_comp₂ hg.aestronglyMeasurable
      (ContinuousLinearMap.adjoint.continuous.measurable.comp
        (measurable_fderiv ℝ Φ)).aestronglyMeasurable |>.congr
        (Filter.Eventually.of_forall fun x => rfl)
  · exact ((ContinuousLinearMap.adjoint (fderiv ℝ Φ x)).le_opNorm _).trans <| by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)

/-- The element `u ∘ Φ` of `W^{1,p}(U)`, before linearity and boundedness are proved. -/
private def compAux (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (u : W1p ν V p) :
    W1p μ U p :=
  W1p.mk (Lp.compMeasurePreserving Φ (measurePreserving_restrict hΦ hUV) (W1p.value u))
    ((memLp_adjoint_gradient hΦ hUV hM u).toLp _) <| by
      have hmaps : MapsTo Φ U V := fun x hx => by rwa [hUV] at hx
      refine (((W1p.hasWeakFDerivOn u).comp_measurePreserving hΦ hΦl
        hmaps).congr_ae (Lp.coeFn_compMeasurePreserving _ _).symm).congr_ae_deriv ?_
      filter_upwards [(memLp_adjoint_gradient hΦ hUV hM u).coeFn_toLp] with x hx
      ext v
      simp [hx, ContinuousLinearMap.adjoint_inner_left]

private theorem value_compAux_ae (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (u : W1p ν V p) :
    W1p.value (compAux hΦ hUV hΦl hM u) =ᵐ[μ.restrict U] fun x => W1p.value u (Φ x) := by
  rw [compAux, W1p.value_mk]
  exact Lp.coeFn_compMeasurePreserving _ _

private theorem gradient_compAux_ae (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (u : W1p ν V p) :
    W1p.gradient (compAux hΦ hUV hΦl hM u) =ᵐ[μ.restrict U]
      fun x => ContinuousLinearMap.adjoint (fderiv ℝ Φ x) (W1p.gradient u (Φ x)) := by
  rw [compAux, W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

/-- The pointwise bound behind `TauCeti.W1p.norm_compMeasurePreservingL_le`. -/
private theorem norm_compAux_le (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (u : W1p ν V p) :
    ‖compAux hΦ hUV hΦl hM u‖ ≤ max 1 M * ‖u‖ := by
  have hres := measurePreserving_restrict hΦ hUV
  rw [← Submodule.norm_coe, ← Submodule.norm_coe u,
    ← Lp.norm_compMeasurePreserving (u : Sobolev1JetLp ν V p) hres]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [W1p.norm_apply_sq_ae (compAux hΦ hUV hΦl hM u),
    value_compAux_ae hΦ hUV hΦl hM u, gradient_compAux_ae hΦ hUV hΦl hM u,
    hres.quasiMeasurePreserving.ae (W1p.norm_apply_sq_ae u),
    Lp.coeFn_compMeasurePreserving (u : Sobolev1JetLp ν V p) hres,
    ae_restrict_mem U.isOpen.measurableSet] with x h1 h2 h3 h4 h5 hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  have hadj : ‖ContinuousLinearMap.adjoint (fderiv ℝ Φ x) (W1p.gradient u (Φ x))‖ ≤
      M * ‖W1p.gradient u (Φ x)‖ :=
    ((ContinuousLinearMap.adjoint (fderiv ℝ Φ x)).le_opNorm _).trans <| by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)
  have h1M : 1 ≤ max 1 M := le_max_left _ _
  have hMM : M ≤ max 1 M := le_max_right _ _
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, h1, mul_pow, h5,
    Function.comp_apply, h4, h2, h3]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) hadj 2, sq_nonneg ‖W1p.value u (Φ x)‖,
    sq_nonneg ‖W1p.gradient u (Φ x)‖, mul_le_mul hMM hMM hM0 (by positivity),
    mul_le_mul h1M h1M zero_le_one (by positivity)]

/-- **Precomposition with a measure-preserving Lipschitz map on `W^{1,p}`.** If
`U = Φ⁻¹(V)` and `Φ` is locally Lipschitz on `U` with `‖fderiv ℝ Φ‖ ≤ M` there, then
`u ↦ u ∘ Φ` maps `W^{1,p}(V)` to `W^{1,p}(U)`, with weak gradient `x ↦ (fderiv ℝ Φ x)† (∇u (Φ x))`
(`TauCeti.W1p.value_compMeasurePreservingL_ae`, `TauCeti.W1p.gradient_compMeasurePreservingL_ae`).
-/
def W1p.compMeasurePreservingL (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) :
    W1p ν V p →L[ℝ] W1p μ U p :=
  LinearMap.mkContinuous
    { toFun := compAux hΦ hUV hΦl hM
      map_add' u v := W1p.ext_value <| by
        have h := map_add (W1p.valueL : W1p μ U p →L[ℝ] _) (compAux hΦ hUV hΦl hM u)
          (compAux hΦ hUV hΦl hM v)
        simp only [W1p.valueL_apply] at h
        rw [h]
        simp only [compAux, W1p.value_mk]
        simp only [← W1p.valueL_apply, map_add]
      map_smul' c u := W1p.ext_value <| by
        have h := map_smul (W1p.valueL : W1p μ U p →L[ℝ] _) c (compAux hΦ hUV hΦl hM u)
        simp only [W1p.valueL_apply] at h
        rw [RingHom.id_apply, h]
        simp only [compAux, W1p.value_mk]
        rw [← W1p.valueL_apply, map_smul, W1p.valueL_apply]
        -- `Lp.compMeasurePreservingₗ` bundles `Lp.compMeasurePreserving` as a linear map.
        exact (Lp.compMeasurePreservingₗ (E := ℝ) (p := p) ℝ Φ
          (measurePreserving_restrict hΦ hUV)).map_smul c _ }
    (max 1 M) (norm_compAux_le hΦ hUV hΦl hM)

/-- The value of `u ∘ Φ` is the composition of the value of `u` with `Φ`. -/
theorem W1p.value_compMeasurePreservingL_ae (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (u : W1p ν V p) :
    W1p.value (W1p.compMeasurePreservingL hΦ hUV hΦl hM u) =ᵐ[μ.restrict U]
      fun x => W1p.value u (Φ x) :=
  value_compAux_ae hΦ hUV hΦl hM u

/-- **The chain rule in `W^{1,p}`**: the weak gradient of `u ∘ Φ` at `x` is the adjoint of
`fderiv ℝ Φ x` applied to the weak gradient of `u` at `Φ x`. -/
theorem W1p.gradient_compMeasurePreservingL_ae (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (u : W1p ν V p) :
    W1p.gradient (W1p.compMeasurePreservingL hΦ hUV hΦl hM u) =ᵐ[μ.restrict U]
      fun x => ContinuousLinearMap.adjoint (fderiv ℝ Φ x) (W1p.gradient u (Φ x)) :=
  gradient_compAux_ae hΦ hUV hΦl hM u

/-- Precomposition with `Φ` multiplies the `W^{1,p}` norm by at most `max 1 M`. -/
theorem W1p.norm_compMeasurePreservingL_le (hΦ : MeasurePreserving Φ μ ν)
    (hUV : (U : Set E) = Φ ⁻¹' V) (hΦl : LocallyLipschitzOn U Φ)
    (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) :
    ‖(W1p.compMeasurePreservingL hΦ hUV hΦl hM : W1p ν V p →L[ℝ] W1p μ U p)‖ ≤ max 1 M :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans (le_max_left _ _)) _

/-- Precomposition with `Φ` undoes precomposition with a left inverse `Ψ` of `Φ` on `U`:
`(u ∘ Ψ) ∘ Φ = u`. -/
theorem W1p.compMeasurePreservingL_compMeasurePreservingL {Ψ : E' → E} {M' : ℝ}
    (hΦ : MeasurePreserving Φ μ ν) (hUV : (U : Set E) = Φ ⁻¹' V)
    (hΦl : LocallyLipschitzOn U Φ) (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M)
    (hΨ : MeasurePreserving Ψ ν μ) (hVU : (V : Set E') = Ψ ⁻¹' U)
    (hΨl : LocallyLipschitzOn V Ψ)
    (hM' : ∀ x ∈ (V : Set E'), ‖fderiv ℝ Ψ x‖ ≤ M') (hΨΦ : ∀ x ∈ (U : Set E), Ψ (Φ x) = x)
    (u : W1p μ U p) :
    W1p.compMeasurePreservingL hΦ hUV hΦl hM
      (W1p.compMeasurePreservingL hΨ hVU hΨl hM' u) = u := by
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [W1p.value_compMeasurePreservingL_ae (p := p) hΦ hUV hΦl hM _,
    (measurePreserving_restrict hΦ hUV).quasiMeasurePreserving.ae
      (W1p.value_compMeasurePreservingL_ae hΨ hVU hΨl hM' u),
    ae_restrict_mem U.isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2, hΨΦ x hx]

/-- **Zero boundary values are preserved.** For `p < ∞` and a proper map `Φ`, precomposition
with `Φ` maps `W^{1,p}_0(V)` into `W^{1,p}_0(U)`. -/
theorem W1p.compMeasurePreservingL_mem_w1p0Submodule (hp : p ≠ ∞) (hΦp : IsProperMap Φ)
    (hΦ : MeasurePreserving Φ μ ν) (hUV : (U : Set E) = Φ ⁻¹' V)
    (hΦl : LocallyLipschitzOn U Φ) (hM : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ M) {u : W1p ν V p}
    (hu : u ∈ w1p0Submodule ν V p) :
    W1p.compMeasurePreservingL hΦ hUV hΦl hM u ∈ w1p0Submodule μ U p := by
  refine w1p0Submodule_subset_of_isClosed (p := p)
    ((w1p0Submodule μ U p).isClosed.preimage
      (W1p.compMeasurePreservingL hΦ hUV hΦl hM).continuous)
    (fun φ => ?_) hu
  -- A test function `φ` on `V` composed with `Φ` vanishes off the compact `Φ⁻¹(tsupport φ) ⊆ U`.
  have hK : IsCompact (Φ ⁻¹' tsupport φ) := hΦp.isCompact_preimage φ.hasCompactSupport.isCompact
  have hKU : Φ ⁻¹' tsupport φ ⊆ U := hUV ▸ preimage_mono φ.tsupport_subset
  refine W1p.mem_w1p0Submodule_of_isCompact hp hK hKU ?_
  filter_upwards [W1p.value_compMeasurePreservingL_ae (p := p) hΦ hUV hΦl hM _,
    (measurePreserving_restrict hΦ hUV).quasiMeasurePreserving.ae
      (testFunctionLp_apply_ae (mu := ν) p φ)] with x h1 h2 hxK
  rw [h1, W1p.value_ofTestFunctionₗ, h2]
  exact image_eq_zero_of_notMem_tsupport hxK

end TauCeti
