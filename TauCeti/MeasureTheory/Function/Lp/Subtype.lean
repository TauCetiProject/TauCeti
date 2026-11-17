/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.LpOrder
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
public import TauCeti.MeasureTheory.Integral.Bochner.Subtype
public import TauCeti.MeasureTheory.Integral.ComapSubtype

/-!
# `Lᵖ` spaces of subtype pullback measures and extension by zero

For a measurable set `s : Set α`, the subtype inclusion `(↑) : s → α` is a measurable embedding
that pushes the pullback measure `μ.comap ((↑) : s → α)` forward to `μ.restrict s`
(`MeasureTheory.map_comap_subtype_coe`). The `eLpNorm` and `MemLp` dictionary between the subtype
measure `μ.comap (↑)`, the restricted measure `μ.restrict s`, and the ambient measure `μ` is in
`TauCeti.MeasureTheory.Integral.ComapSubtype`; this file adds the `Lᵖ`-space level:

* Precomposition with `(↑) : s → α` is a surjective linear isometry
  `MeasureTheory.Lp.comapSubtypeEquivₗᵢ : Lp E p (μ.restrict s) ≃ₗᵢ[𝕜] Lp E p (μ.comap (↑))`
  (requiring no nonemptiness assumption on `s`).
* Composing its inverse with `TauCeti.extendByZeroLpₗᵢ` gives the extension-by-zero linear isometry
  `MeasureTheory.Lp.extendByZeroComapₗᵢ : Lp E p (μ.comap (↑)) →ₗᵢ[𝕜] Lp E p μ`, paired with the
  norm-at-most-one restriction
  `MeasureTheory.Lp.restrictComapCLM : Lp E p μ →L[𝕜] Lp E p (μ.comap (↑))`.
  Restriction is a left inverse of extension by zero, and the range of extension by zero consists
  precisely of those `f : Lp E p μ` with `(f : α → E) =ᵐ[μ.restrict sᶜ] 0`.

## Main definitions

* `MeasureTheory.Lp.comapSubtypeEquivₗᵢ`: isometric isomorphism
  `Lp E p (μ.restrict s) ≃ₗᵢ[𝕜] Lp E p (μ.comap ((↑) : s → α))`.
* `MeasureTheory.Lp.extendByZeroComapₗᵢ`: extension by zero
  `Lp E p (μ.comap ((↑) : s → α)) →ₗᵢ[𝕜] Lp E p μ` as a linear isometry.
* `MeasureTheory.Lp.restrictComapCLM`: restriction
  `Lp E p μ →L[𝕜] Lp E p (μ.comap ((↑) : s → α))` as a continuous linear map.

## Main statements

* `MeasureTheory.Lp.restrictComapCLM_extendByZeroComapₗᵢ`,
  `MeasureTheory.Lp.extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.Lp.mem_range_extendByZeroComapₗᵢ_iff`: the retraction-section relationship and
  essential-support characterization of the range.
* `MeasureTheory.Lp.integral_extendByZeroComapₗᵢ`,
  `MeasureTheory.Lp.integral_restrictComapCLM_of_ae_restrict_compl_eq_zero`: extension by zero and
  supported restriction preserve Bochner integrals.
* `MeasureTheory.Lp.extendByZeroComapₗᵢ_le_iff`: extension by zero is an order embedding on real
  `Lᵖ`.
-/

public section

noncomputable section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

namespace Lp

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set α}

/-- Precomposition by `(↑) : s → α` is surjective from `Lp E p (μ.restrict s)` onto
`Lp E p (μ.comap ((↑) : s → α))`, even when `s` is empty. -/
private theorem surjective_compMeasurePreserving_subtype_coe (hs : MeasurableSet s) :
    Function.Surjective (compMeasurePreservingₗᵢ (E := E) (p := p) 𝕜 ((↑) : s → α)
      (measurePreserving_subtype_coe (μa := μ) hs)) := by
  intro f₀
  set F : α → E := Function.extend ((↑) : s → α) (⇑f₀) 0
  have hFcomp : F ∘ ((↑) : s → α) = ⇑f₀ :=
    funext fun x ↦ Subtype.coe_injective.extend_apply (⇑f₀) 0 x
  have hF : MemLp F p (μ.restrict s) :=
    (memLp_restrict_iff_comap_subtypeVal hs).2 (by
      change MemLp (F ∘ ((↑) : s → α)) p (μ.comap ((↑) : s → α))
      rw [hFcomp]
      exact Lp.memLp f₀)
  refine ⟨hF.toLp F, Lp.ext ?_⟩
  filter_upwards [coeFn_compMeasurePreserving (hF.toLp F)
    (measurePreserving_subtype_coe (μa := μ) hs),
    (ae_restrict_iff_subtype hs).1 hF.coeFn_toLp] with x hx1 hx2
  exact hx1.trans (hx2.trans (congrFun hFcomp x))

variable (μ) in
/-- **Isometric isomorphism `Lᵖ(μ.restrict s) ≃ₗᵢ[𝕜] Lᵖ(μ.comap (↑))`** for a measurable set `s`,
given by precomposing representatives with `(↑) : s → α`. -/
def comapSubtypeEquivₗᵢ (hs : MeasurableSet s) :
    Lp E p (μ.restrict s) ≃ₗᵢ[𝕜] Lp E p (μ.comap ((↑) : s → α)) :=
  LinearIsometryEquiv.ofSurjective
    (compMeasurePreservingₗᵢ 𝕜 ((↑) : s → α) (measurePreserving_subtype_coe (μa := μ) hs))
    (surjective_compMeasurePreserving_subtype_coe 𝕜 hs)

variable {𝕜}

/-- `comapSubtypeEquivₗᵢ` acts as `Lp.compMeasurePreserving` along `(↑) : s → α`. -/
@[simp]
theorem comapSubtypeEquivₗᵢ_apply (hs : MeasurableSet s) (f : Lp E p (μ.restrict s)) :
    comapSubtypeEquivₗᵢ 𝕜 μ hs f =
      compMeasurePreserving ((↑) : s → α) (measurePreserving_subtype_coe (μa := μ) hs) f := by
  rw [comapSubtypeEquivₗᵢ, LinearIsometryEquiv.coe_ofSurjective, compMeasurePreservingₗᵢ_apply]

/-- `comapSubtypeEquivₗᵢ` restricts representatives to `s` almost everywhere. -/
theorem coeFn_comapSubtypeEquivₗᵢ (hs : MeasurableSet s) (f : Lp E p (μ.restrict s)) :
    ⇑(comapSubtypeEquivₗᵢ 𝕜 μ hs f) =ᵐ[μ.comap ((↑) : s → α)] ⇑f ∘ ((↑) : s → α) := by
  rw [comapSubtypeEquivₗᵢ_apply]
  exact coeFn_compMeasurePreserving f (measurePreserving_subtype_coe (μa := μ) hs)

/-- The inverse of `comapSubtypeEquivₗᵢ` agrees with `f₀` along `(↑) : s → α` almost everywhere. -/
theorem coeFn_comapSubtypeEquivₗᵢ_symm_comp_subtype (hs : MeasurableSet s)
    (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    ⇑((comapSubtypeEquivₗᵢ 𝕜 μ hs).symm f₀) ∘ ((↑) : s → α) =ᵐ[μ.comap ((↑) : s → α)] ⇑f₀ := by
  refine (coeFn_comapSubtypeEquivₗᵢ (𝕜 := 𝕜) hs
    ((comapSubtypeEquivₗᵢ 𝕜 μ hs).symm f₀)).symm.trans ?_
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- On `μ.restrict s`, `(comapSubtypeEquivₗᵢ 𝕜 μ hs).symm f₀` is almost everywhere the zero
extension `Function.extend (↑) f₀ 0`. -/
theorem coeFn_comapSubtypeEquivₗᵢ_symm (hs : MeasurableSet s)
    (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    ⇑((comapSubtypeEquivₗᵢ 𝕜 μ hs).symm f₀) =ᵐ[μ.restrict s]
      Function.extend ((↑) : s → α) (⇑f₀) 0 := by
  rw [Filter.EventuallyEq, ae_restrict_iff_subtype hs]
  filter_upwards [coeFn_comapSubtypeEquivₗᵢ_symm_comp_subtype (𝕜 := 𝕜) hs f₀] with x hx
  exact hx.trans (Subtype.coe_injective.extend_apply (⇑f₀) 0 x).symm

variable (𝕜 μ) in
/-- **Extension by zero** from the subtype `Lᵖ` space `Lp E p (μ.comap ((↑) : s → α))` into the
ambient space `Lp E p μ`, as a linear isometry. -/
def extendByZeroComapₗᵢ (hs : MeasurableSet s) :
    Lp E p (μ.comap ((↑) : s → α)) →ₗᵢ[𝕜] Lp E p μ :=
  (TauCeti.castLpₗᵢ (𝕜 := 𝕜) (Measure.restrict_univ (μ := μ))).toLinearIsometry.comp <|
    (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs (subset_univ s)).comp
      (comapSubtypeEquivₗᵢ 𝕜 μ hs).symm.toLinearIsometry

variable (𝕜 μ p) in
/-- **Restriction to a measurable subtype** from `Lp E p μ` to `Lp E p (μ.comap ((↑) : s → α))`, as
a continuous linear map of norm at most `1`. -/
def restrictComapCLM (hs : MeasurableSet s) :
    Lp E p μ →L[𝕜] Lp E p (μ.comap ((↑) : s → α)) :=
  (comapSubtypeEquivₗᵢ 𝕜 μ hs).toLinearIsometry.toContinuousLinearMap.comp
    (LpToLpRestrictCLM α E 𝕜 μ p s)

/-- `extendByZeroComapₗᵢ` is almost everywhere `Function.extend (↑) f₀ 0`. -/
theorem coeFn_extendByZeroComapₗᵢ (hs : MeasurableSet s)
    (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    (extendByZeroComapₗᵢ 𝕜 μ hs f₀ : α → E) =ᵐ[μ] Function.extend ((↑) : s → α) (⇑f₀) 0 := by
  have h1 := (ae_imp_of_ae_restrict (TauCeti.coeFn_extendByZeroLpₗᵢ 𝕜 hs (subset_univ s)
    ((comapSubtypeEquivₗᵢ 𝕜 μ hs).symm f₀))).mono fun _ hx ↦ hx (mem_univ _)
  have h2 := (ae_eq_restrict_iff_indicator_ae_eq hs).1
    (coeFn_comapSubtypeEquivₗᵢ_symm (𝕜 := 𝕜) hs f₀)
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [extendByZeroComapₗᵢ, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, TauCeti.coeFn_castLpₗᵢ, hx1, hx2]
  by_cases hxs : x ∈ s
  · exact indicator_of_mem hxs _
  · rw [indicator_of_notMem hxs, Function.extend_apply' _ _ _ (by simpa using hxs), Pi.zero_apply]

/-- Along `(↑) : s → α`, `extendByZeroComapₗᵢ` recovers `f₀` almost everywhere. -/
theorem coeFn_extendByZeroComapₗᵢ_comp_subtype (hs : MeasurableSet s)
    (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    (extendByZeroComapₗᵢ 𝕜 μ hs f₀ : α → E) ∘ ((↑) : s → α) =ᵐ[μ.comap ((↑) : s → α)] ⇑f₀ := by
  have h := (ae_restrict_iff_subtype hs).1
    (ae_restrict_of_ae (coeFn_extendByZeroComapₗᵢ (𝕜 := 𝕜) hs f₀))
  filter_upwards [h] with x hx
  exact hx.trans (Subtype.coe_injective.extend_apply (⇑f₀) 0 x)

/-- Outside `s`, `extendByZeroComapₗᵢ` vanishes `μ.restrict sᶜ`-almost everywhere. -/
theorem coeFn_extendByZeroComapₗᵢ_restrict_compl (hs : MeasurableSet s)
    (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    (extendByZeroComapₗᵢ 𝕜 μ hs f₀ : α → E) =ᵐ[μ.restrict sᶜ] 0 := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl]
  filter_upwards [coeFn_extendByZeroComapₗᵢ (𝕜 := 𝕜) hs f₀] with x hx hxs
  exact hx.trans (Function.extend_apply' _ _ _ (by simpa using hxs))

/-- `extendByZeroComapₗᵢ` does not depend on the scalar ring `𝕜`. -/
theorem extendByZeroComapₗᵢ_eq_of_scalars (𝕜' : Type*) [NormedRing 𝕜'] [Module 𝕜' E]
    [IsBoundedSMul 𝕜' E] (hs : MeasurableSet s) (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    extendByZeroComapₗᵢ 𝕜 μ hs f₀ = extendByZeroComapₗᵢ 𝕜' μ hs f₀ :=
  Lp.ext <| (coeFn_extendByZeroComapₗᵢ (𝕜 := 𝕜) hs f₀).trans
    (coeFn_extendByZeroComapₗᵢ (𝕜 := 𝕜') hs f₀).symm

/-- `restrictComapCLM` restricts representatives to `s` almost everywhere. -/
theorem coeFn_restrictComapCLM (hs : MeasurableSet s) (f : Lp E p μ) :
    ⇑(restrictComapCLM 𝕜 μ p hs f) =ᵐ[μ.comap ((↑) : s → α)] ⇑f ∘ ((↑) : s → α) :=
  (coeFn_comapSubtypeEquivₗᵢ (𝕜 := 𝕜) hs _).trans
    ((ae_restrict_iff_subtype hs).1 (LpToLpRestrictCLM_coeFn 𝕜 s f))

/-- `restrictComapCLM` does not depend on the scalar ring `𝕜`. -/
theorem restrictComapCLM_eq_of_scalars (𝕜' : Type*) [NormedRing 𝕜'] [Module 𝕜' E]
    [IsBoundedSMul 𝕜' E] (hs : MeasurableSet s) (f : Lp E p μ) :
    restrictComapCLM 𝕜 μ p hs f = restrictComapCLM 𝕜' μ p hs f :=
  Lp.ext <| (coeFn_restrictComapCLM (𝕜 := 𝕜) hs f).trans
    (coeFn_restrictComapCLM (𝕜 := 𝕜') hs f).symm

/-- Restricting an extension by zero back to `s` recovers the original subtype `Lᵖ` element. -/
@[simp]
theorem restrictComapCLM_extendByZeroComapₗᵢ (hs : MeasurableSet s)
    (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    restrictComapCLM 𝕜 μ p hs (extendByZeroComapₗᵢ 𝕜 μ hs f₀) = f₀ :=
  Lp.ext <| (coeFn_restrictComapCLM (𝕜 := 𝕜) hs _).trans
    (coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := 𝕜) hs f₀)

/-- Extending the subtype restriction of `f` by zero recovers `f` whenever `f` vanishes almost
everywhere outside `s`. -/
theorem extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero (hs : MeasurableSet s)
    {f : Lp E p μ} (hf : (f : α → E) =ᵐ[μ.restrict sᶜ] 0) :
    extendByZeroComapₗᵢ 𝕜 μ hs (restrictComapCLM 𝕜 μ p hs f) = f := by
  refine Lp.ext (ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_)
  · rw [ae_restrict_iff_subtype hs]
    exact (coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := 𝕜) hs _).trans
      (coeFn_restrictComapCLM (𝕜 := 𝕜) hs f)
  · exact (coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := 𝕜) hs _).trans hf.symm

/-- Recognizing `extendByZeroComapₗᵢ` from ambient and subtype almost-everywhere identities. -/
theorem extendByZeroComapₗᵢ_eq_of_ae_eq (hs : MeasurableSet s)
    {f₀ : Lp E p (μ.comap ((↑) : s → α))} {f : Lp E p μ}
    (hf_on : (f : α → E) ∘ ((↑) : s → α) =ᵐ[μ.comap ((↑) : s → α)] ⇑f₀)
    (hf_off : (f : α → E) =ᵐ[μ.restrict sᶜ] 0) :
    extendByZeroComapₗᵢ 𝕜 μ hs f₀ = f := by
  have hres : restrictComapCLM 𝕜 μ p hs f = f₀ :=
    Lp.ext <| (coeFn_restrictComapCLM (𝕜 := 𝕜) hs f).trans hf_on
  rw [← hres, extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero hs hf_off]

/-- **Range of extension by zero.** An ambient `Lᵖ` element `f` lies in the range of
`extendByZeroComapₗᵢ 𝕜 μ hs` if and only if `f` vanishes `μ.restrict sᶜ`-almost everywhere. -/
theorem mem_range_extendByZeroComapₗᵢ_iff (hs : MeasurableSet s) {f : Lp E p μ} :
    f ∈ Set.range (extendByZeroComapₗᵢ (E := E) (p := p) 𝕜 μ hs) ↔
      (f : α → E) =ᵐ[μ.restrict sᶜ] 0 := by
  refine ⟨?_, fun hf ↦ ⟨restrictComapCLM 𝕜 μ p hs f,
    extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero hs hf⟩⟩
  rintro ⟨f₀, rfl⟩
  exact coeFn_extendByZeroComapₗᵢ_restrict_compl hs f₀

/-- `restrictComapCLM` is norm-nonincreasing. -/
theorem norm_restrictComapCLM_apply_le (hs : MeasurableSet s) (f : Lp E p μ) :
    ‖restrictComapCLM 𝕜 μ p hs f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_restrictComapCLM (𝕜 := 𝕜) hs f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    ((eLpNorm_comp_subtypeVal hs _ p).le.trans
      (eLpNorm_mono_measure (⇑f) Measure.restrict_le_self))

/-- `restrictComapCLM` has operator norm at most `1`. -/
theorem norm_restrictComapCLM_le {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' E]
    (hs : MeasurableSet s) :
    ‖restrictComapCLM (E := E) 𝕜' μ p hs‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa using norm_restrictComapCLM_apply_le (𝕜 := 𝕜') hs f

/-- Restricting an `Lᵖ` element that vanishes almost everywhere outside `s` preserves its norm. -/
theorem norm_restrictComapCLM_of_ae_restrict_compl_eq_zero (hs : MeasurableSet s)
    {f : Lp E p μ} (hf : (f : α → E) =ᵐ[μ.restrict sᶜ] 0) :
    ‖restrictComapCLM 𝕜 μ p hs f‖ = ‖f‖ := by
  rw [← (extendByZeroComapₗᵢ 𝕜 μ hs).norm_map,
    extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero hs hf]

/-- **Extension by zero preserves Bochner integrals.** -/
@[simp]
theorem integral_extendByZeroComapₗᵢ [NormedSpace ℝ E] (hs : MeasurableSet s)
    (f₀ : Lp E p (μ.comap ((↑) : s → α))) :
    ∫ x, extendByZeroComapₗᵢ 𝕜 μ hs f₀ x ∂μ = ∫ x : s, f₀ x ∂(μ.comap ((↑) : s → α)) := by
  rw [← integral_subtype_comap_of_ae_restrict_compl_eq_zero hs
    (coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := 𝕜) hs f₀)]
  exact integral_congr_ae (coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := 𝕜) hs f₀)

/-- Restricting an `Lᵖ` element that vanishes almost everywhere outside `s` preserves its Bochner
integral. -/
theorem integral_restrictComapCLM_of_ae_restrict_compl_eq_zero [NormedSpace ℝ E]
    (hs : MeasurableSet s) {f : Lp E p μ} (hf : (f : α → E) =ᵐ[μ.restrict sᶜ] 0) :
    ∫ x : s, restrictComapCLM 𝕜 μ p hs f x ∂(μ.comap ((↑) : s → α)) = ∫ x, f x ∂μ := by
  rw [← integral_extendByZeroComapₗᵢ (𝕜 := 𝕜) hs,
    extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero hs hf]

/-- Extension by zero is monotone on real `Lᵖ`. -/
theorem extendByZeroComapₗᵢ_mono (hs : MeasurableSet s)
    {f₀ g₀ : Lp ℝ p (μ.comap ((↑) : s → α))} (h : f₀ ≤ g₀) :
    extendByZeroComapₗᵢ ℝ μ hs f₀ ≤ extendByZeroComapₗᵢ ℝ μ hs g₀ := by
  rw [← Lp.coeFn_le] at h ⊢
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · rw [ae_restrict_iff_subtype hs]
    filter_upwards [coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := ℝ) hs f₀,
      coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := ℝ) hs g₀, h] with x hxf hxg hle
    exact hxf.trans_le (hle.trans_eq hxg.symm)
  · filter_upwards [coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := ℝ) hs f₀,
      coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := ℝ) hs g₀] with x hxf hxg
    exact hxf.trans_le hxg.symm.le

/-- Extension by zero is an order embedding on real `Lᵖ`. -/
@[simp]
theorem extendByZeroComapₗᵢ_le_iff (hs : MeasurableSet s)
    {f₀ g₀ : Lp ℝ p (μ.comap ((↑) : s → α))} :
    extendByZeroComapₗᵢ ℝ μ hs f₀ ≤ extendByZeroComapₗᵢ ℝ μ hs g₀ ↔ f₀ ≤ g₀ := by
  refine ⟨fun h ↦ ?_, extendByZeroComapₗᵢ_mono hs⟩
  rw [← Lp.coeFn_le] at h ⊢
  have hsub := (ae_restrict_iff_subtype hs).1 (ae_restrict_of_ae h)
  filter_upwards [coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := ℝ) hs f₀,
    coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := ℝ) hs g₀, hsub] with x hxf hxg hle
  exact hxf.symm.trans_le (hle.trans_eq hxg)

/-- Extension by zero preserves nonnegativity in both directions on real `Lᵖ`. -/
@[simp]
theorem extendByZeroComapₗᵢ_nonneg_iff (hs : MeasurableSet s)
    {f₀ : Lp ℝ p (μ.comap ((↑) : s → α))} :
    0 ≤ extendByZeroComapₗᵢ ℝ μ hs f₀ ↔ 0 ≤ f₀ := by
  rw [← map_zero (extendByZeroComapₗᵢ ℝ μ hs), extendByZeroComapₗᵢ_le_iff]

/-- Restriction to a measurable subtype is monotone on real `Lᵖ`. -/
theorem restrictComapCLM_mono (hs : MeasurableSet s) {f g : Lp ℝ p μ} (h : f ≤ g) :
    restrictComapCLM ℝ μ p hs f ≤ restrictComapCLM ℝ μ p hs g := by
  rw [← Lp.coeFn_le] at h ⊢
  have hsub := (ae_restrict_iff_subtype hs).1 (ae_restrict_of_ae h)
  filter_upwards [coeFn_restrictComapCLM (𝕜 := ℝ) hs f,
    coeFn_restrictComapCLM (𝕜 := ℝ) hs g, hsub] with x hxf hxg hle
  exact hxf.trans_le (hle.trans_eq hxg.symm)

/-- Restriction to a measurable subtype preserves nonnegativity on real `Lᵖ`. -/
theorem restrictComapCLM_nonneg (hs : MeasurableSet s) {f : Lp ℝ p μ} (hf : 0 ≤ f) :
    0 ≤ restrictComapCLM ℝ μ p hs f := by
  simpa using restrictComapCLM_mono hs hf

end Lp

end MeasureTheory
