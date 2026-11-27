/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Measure.Haar.Disintegration
import TauCeti.Analysis.Calculus.FDeriv.Integral
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Weak derivatives along surjective linear maps

Let `A : E → E'` be a surjective linear map between finite-dimensional real normed spaces with
additive Haar measures `μ` and `ν`, and let `V ⊆ E'` be open. A function `u` with weak derivative
`U` on `V` pulls back to `u ∘ A`, which is constant along the fibres of `A`, and the chain rule
holds weakly: `u ∘ A` has weak derivative `x ↦ U (A x) ∘L A` on `A⁻¹ V`
(`TauCeti.HasWeakFDerivOn.comp_surjective`). Local integrability pulls back in the same way
(`MeasureTheory.LocallyIntegrableOn.comp_surjective`), and conversely integrability of `g ∘ A`
near a point gives integrability of `g` near its image
(`MeasureTheory.IntegrableOn.exists_mem_nhds_integrableOn_of_comp_surjective`).

These are the tools for lifting a function of fewer variables, such as a function on the plane,
to a function on a higher-dimensional space that is constant in the remaining variables, keeping
track of its Sobolev regularity in both directions.

## The argument

For the projection `Prod.fst : E₁ × E₂ → E₁` and a product of Haar measures this is Fubini's
theorem. Write the derivative of a test function `φ` in the direction `(w₁, w₂)` as the sum of its
partial derivatives. The partial derivative in `w₁` is handled on each slice `x₂ = const`, where
`x₁ ↦ φ (x₁, x₂)` is a test function on `V`, by the weak derivative identity of `u`; the partial
derivative in `w₂` integrates to zero over each slice `x₁ = const`
(`TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable`). A general surjection `A` is the
first coordinate of the linear equivalence `ContinuousLinearMap.linearCoord : E ≃ E' × ker A`, and
weak derivatives are transported along linear equivalences
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure`).

## Main results

* `TauCeti.HasWeakFDerivOn.comp_fst`: the weak chain rule for `u ∘ Prod.fst` on `V × E₂`.
* `TauCeti.HasWeakFDerivOn.comp_surjective`: the weak chain rule for `u ∘ A` on `A⁻¹ V`.
* `MeasureTheory.LocallyIntegrableOn.comp_fst`,
  `MeasureTheory.LocallyIntegrableOn.comp_surjective`: local integrability pulls back along the
  projection and along `A`.
* `MeasureTheory.IntegrableOn.exists_mem_nhds_integrableOn_of_comp_surjective`: if `g ∘ A` is
  integrable on a neighbourhood of `x`, then `g` is integrable on a neighbourhood of `A x`.
-/

public section

open MeasureTheory Set TopologicalSpace Filter
open scoped Topology

/-! ### Local integrability along projections -/

namespace MeasureTheory.LocallyIntegrableOn

variable {X Y G : Type*} [MeasurableSpace X] [TopologicalSpace X] [LocallyCompactSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [NormedAddCommGroup G]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts ν]

/-- Local integrability on an open set `V` pulls back along the first projection to `V × Y`. -/
theorem comp_fst [LocallyCompactSpace Y] {f : X → G} {V : Set X}
    (hV : IsOpen V) (hf : LocallyIntegrableOn f V μ) :
    LocallyIntegrableOn (fun x : X × Y => f x.1) (Prod.fst ⁻¹' V) (μ.prod ν) := by
  rw [locallyIntegrableOn_iff (hV.preimage continuous_fst).isLocallyClosed]
  intro k hkV hk
  -- `k` lies in the product of its two projections, which are compact.
  have hk₁ : IsCompact (Prod.fst '' k) := hk.image continuous_fst
  have hk₂ : IsCompact (Prod.snd '' k) := hk.image continuous_snd
  have : IsFiniteMeasure (ν.restrict (Prod.snd '' k)) :=
    isFiniteMeasure_restrict.2 hk₂.measure_lt_top.ne
  have hint : IntegrableOn (fun x : X × Y => f x.1) ((Prod.fst '' k) ×ˢ (Prod.snd '' k))
      (μ.prod ν) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact (hf.integrableOn_compact_subset (by rintro _ ⟨x, hx, rfl⟩; exact hkV hx) hk₁).comp_fst _
  exact hint.mono_set fun x hx => ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hx⟩

end MeasureTheory.LocallyIntegrableOn

namespace TauCeti

/-! ### Weak derivatives along the first projection -/

section Slices

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The slice `x₁ ↦ φ (x₁, x₂)` of a differentiable function `φ` on `E₁ × E₂` has as derivative
the partial derivative of `φ` in the first variable. -/
private theorem hasFDerivAt_slice_fst {φ : E₁ × E₂ → ℝ} (hφ : Differentiable ℝ φ) (x₁ : E₁)
    (x₂ : E₂) : HasFDerivAt (fun y => φ (y, x₂))
      ((fderiv ℝ φ (x₁, x₂)).comp (ContinuousLinearMap.inl ℝ E₁ E₂)) x₁ :=
  (hφ (x₁, x₂)).hasFDerivAt.comp x₁ (hasFDerivAt_prodMk_left x₁ x₂)

/-- The slice `x₂ ↦ φ (x₁, x₂)` of a differentiable function `φ` on `E₁ × E₂` has as derivative
the partial derivative of `φ` in the second variable. -/
private theorem hasFDerivAt_slice_snd {φ : E₁ × E₂ → ℝ} (hφ : Differentiable ℝ φ) (x₁ : E₁)
    (x₂ : E₂) : HasFDerivAt (fun y => φ (x₁, y))
      ((fderiv ℝ φ (x₁, x₂)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)) x₂ :=
  (hφ (x₁, x₂)).hasFDerivAt.comp x₂ (hasFDerivAt_prodMk_right x₁ x₂)

omit [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] in
/-- The slices `x₁ ↦ φ (x₁, x₂)` of a function are supported in the first projection
of its support. -/
private theorem tsupport_slice_fst_subset (φ : E₁ × E₂ → ℝ) (x₂ : E₂) :
    tsupport (fun y => φ (y, x₂)) ⊆ Prod.fst '' tsupport φ :=
  fun y hy => ⟨(y, x₂), tsupport_comp_subset_preimage φ (Continuous.prodMk_left x₂) hy, rfl⟩

omit [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] in
private theorem hasCompactSupport_slice_fst {φ : E₁ × E₂ → ℝ} (hφc : HasCompactSupport φ)
    (x₂ : E₂) : HasCompactSupport (fun y => φ (y, x₂)) :=
  (hφc.image continuous_fst).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_slice_fst_subset φ x₂)

omit [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] in
private theorem hasCompactSupport_slice_snd {φ : E₁ × E₂ → ℝ} (hφc : HasCompactSupport φ)
    (x₁ : E₁) : HasCompactSupport (fun y => φ (x₁, y)) :=
  (hφc.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
    fun y hy => ⟨(x₁, y), tsupport_comp_subset_preimage φ (Continuous.prodMk_right x₁) hy, rfl⟩

end Slices

section Prod

variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ₁ : Measure E₁} [SFinite μ₁] {μ₂ : Measure E₂} [μ₂.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E₁] [BorelSpace E₁] in
/-- The partial derivative of a compactly supported differentiable `φ` on `E₁ × E₂` in a direction
`(0, w₂)` of the second factor, times a function of the first variable, integrates to zero: it does
so on every slice `x₁ = const`. -/
private theorem integral_fderiv_inr_smul_eq_zero {φ : E₁ × E₂ → ℝ} (hφd : Differentiable ℝ φ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) [CompleteSpace F] {u : E₁ → F} {w₂ : E₂}
    (hint : Integrable (fun x : E₁ × E₂ => fderiv ℝ φ x (0, w₂) • u x.1) (μ₁.prod μ₂)) :
    ∫ x, fderiv ℝ φ x (0, w₂) • u x.1 ∂(μ₁.prod μ₂) = 0 := by
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x₁ => ?_)
  simp only [Pi.zero_apply]
  rw [integral_smul_const]
  have h0 := integral_apply_eq_zero_of_hasFDerivAt_off_countable (μ := μ₂) countable_empty
    (hφ.comp (Continuous.prodMk_right x₁)) (hasCompactSupport_slice_snd hφc x₁)
    (fun x₂ _ => hasFDerivAt_slice_snd hφd x₁ x₂) w₂
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inr_apply] at h0
  simp [h0]

/-- **The weak chain rule along the first projection.** If `u` has weak derivative `U` on an open
set `V ⊆ E₁`, then `(x₁, x₂) ↦ u x₁` has weak derivative `(x₁, x₂) ↦ U x₁ ∘L fst` on `V × E₂`, for
the product of the measure on `E₁` with an additive Haar measure on `E₂`. -/
theorem HasWeakFDerivOn.comp_fst {V : Opens E₁} {u : E₁ → F} {U : E₁ → E₁ →L[ℝ] F}
    (h : HasWeakFDerivOn μ₁ V u U) :
    HasWeakFDerivOn (μ₁.prod μ₂) (Opens.comap (ContinuousMap.fst : C(E₁ × E₂, E₁)) V)
      (fun x => u x.1) fun x => (U x.1).comp (ContinuousLinearMap.fst ℝ E₁ E₂) := by
  have := h.completeSpace
  have hV : (Opens.comap (ContinuousMap.fst : C(E₁ × E₂, E₁)) V : Set (E₁ × E₂)) =
      Prod.fst ⁻¹' (V : Set E₁) := Opens.coe_comap _ _
  have hu := h.locallyIntegrableOn.comp_fst (ν := μ₂) V.isOpen
  refine hasWeakFDerivOn_iff.2 fun w => ?_
  have hUw := ((h.hasWeakLineDerivOn w.1).locallyIntegrableOn_deriv).comp_fst (ν := μ₂) V.isOpen
  rw [hasWeakLineDerivOn_iff (by rwa [hV]) (by simpa [hV] using hUw)]
  intro φ hφ hφc hφV
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφV' : tsupport φ ⊆ Prod.fst ⁻¹' (V : Set E₁) := hV ▸ hφV
  -- Split the derivative in the direction `w` into the two partial derivatives.
  have hsplit : ∀ x, lineDeriv ℝ φ x w =
      fderiv ℝ φ x (w.1, 0) + fderiv ℝ φ x (0, w.2) := fun x => by
    rw [(hφd x).lineDeriv_eq_fderiv, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hint₁ : Integrable (fun x : E₁ × E₂ => fderiv ℝ φ x (w.1, 0) • u x.1) (μ₁.prod μ₂) :=
    (hu.integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
      (hφc.fderiv_apply (𝕜 := ℝ) _) ((tsupport_fderiv_apply_subset ℝ _).trans hφV'))
  have hint₂ : Integrable (fun x : E₁ × E₂ => fderiv ℝ φ x (0, w.2) • u x.1) (μ₁.prod μ₂) :=
    (hu.integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
      (hφc.fderiv_apply (𝕜 := ℝ) _) ((tsupport_fderiv_apply_subset ℝ _).trans hφV'))
  have hint₃ : Integrable (fun x : E₁ × E₂ => φ x • U x.1 w.1) (μ₁.prod μ₂) :=
    hUw.integrable_smul_left_of_hasCompactSupport hφ.continuous.continuousOn hφc hφV'
  simp_rw [hsplit, add_smul]
  rw [integral_add hint₁ hint₂]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_fst']
  -- The second partial derivative integrates to zero on every slice `x₁ = const`.
  rw [integral_fderiv_inr_smul_eq_zero hφd hφ.continuous hφc hint₂, add_zero,
    integral_prod_symm _ hint₁, integral_prod_symm _ hint₃, ← integral_neg]
  -- The first partial derivative is the weak derivative identity of `u` on every slice.
  refine integral_congr_ae (ae_of_all _ fun x₂ => ?_)
  have hslice := ((hasWeakLineDerivOn_iff h.locallyIntegrableOn
    (h.hasWeakLineDerivOn w.1).locallyIntegrableOn_deriv).1 (h.hasWeakLineDerivOn w.1))
    (fun y => φ (y, x₂)) (hφ.comp (contDiff_prodMk_left x₂))
    (hasCompactSupport_slice_fst hφc x₂)
    ((tsupport_slice_fst_subset φ x₂).trans (by
      rintro _ ⟨x, hx, rfl⟩; exact hφV' hx))
  simp only
  rw [← hslice]
  refine integral_congr_ae (ae_of_all _ fun x₁ => ?_)
  simp only
  rw [((hasFDerivAt_slice_fst hφd x₁ x₂).differentiableAt).lineDeriv_eq_fderiv,
    (hasFDerivAt_slice_fst hφd x₁ x₂).fderiv]
  simp

end Prod

/-! ### Along a surjective linear map -/

section Surjective

variable {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {A : E →L[ℝ] E'}

/-- **The weak chain rule along a surjective linear map.** If `u` has weak derivative `U` on an
open set `V ⊆ E'` and `A : E → E'` is a surjective linear map, then `u ∘ A` has weak derivative
`x ↦ U (A x) ∘L A` on `A⁻¹ V`. -/
theorem HasWeakFDerivOn.comp_surjective {V : Opens E'} {u : E' → F} {U : E' → E' →L[ℝ] F}
    (h : HasWeakFDerivOn ν V u U) (hA : Function.Surjective A) :
    HasWeakFDerivOn μ (Opens.comap (A : C(E, E')) V) (u ∘ A) fun x => (U (A x)).comp A := by
  have hp := (h.comp_fst (μ₂ := (Measure.addHaar : Measure (A : E →ₗ[ℝ] E').ker))
    ).comp_continuousLinearEquiv_of_isAddHaarMeasure (μ := μ) (A.linearCoord hA)
    (U := Opens.comap (A : C(E, E')) V) fun x hx => by
      change (A.linearCoord hA x).1 ∈ V
      rw [ContinuousLinearMap.linearCoord_apply_fst]
      exact hx
  have hfst : (ContinuousLinearMap.fst ℝ E' (A : E →ₗ[ℝ] E').ker).comp
      (A.linearCoord hA : E →L[ℝ] E' × (A : E →ₗ[ℝ] E').ker) = A := by
    ext x
    simp
  convert hp using 1
  · ext x
    simp
  · ext x : 1
    rw [ContinuousLinearMap.comp_assoc, hfst]
    simp

end Surjective

end TauCeti

/-! ### Integrability along a surjective linear map -/

namespace MeasureTheory

variable {E E' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] [NormedAddCommGroup G]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {A : E →L[ℝ] E'}

/-- Local integrability on an open set `V` pulls back along a surjective linear map `A` to
`A⁻¹ V`. -/
theorem LocallyIntegrableOn.comp_surjective {g : E' → G} {V : Set E'} (hV : IsOpen V)
    (hg : LocallyIntegrableOn g V ν) (hA : Function.Surjective A) :
    LocallyIntegrableOn (g ∘ A) (A ⁻¹' V) μ := by
  set L := A.linearCoord hA
  have hp : LocallyIntegrableOn (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) (Prod.fst ⁻¹' V)
      (μ.map L) := by
    rw [A.map_linearCoord hA μ ν]
    exact (hg.comp_fst hV).smul_measure ENNReal.coe_ne_top
  intro x hx
  obtain ⟨t, ht, hgt⟩ := hp (L x) (by simpa [L] using hx)
  refine ⟨L ⁻¹' t, L.continuous.continuousWithinAt.tendsto_nhdsWithin
    (fun y hy => by simpa [L] using hy) ht, ?_⟩
  have hgL : (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) ∘ L.toHomeomorph = g ∘ A :=
    funext fun y => by simp [L]
  have := L.toHomeomorph.measurableEmbedding.integrableOn_map_iff.1 hgt
  rwa [hgL] at this

/-- If `g ∘ A` is integrable on a neighbourhood of `x`, for a surjective linear map `A`, then `g`
is integrable on a neighbourhood of `A x`. -/
theorem IntegrableOn.exists_mem_nhds_integrableOn_of_comp_surjective {g : E' → G} {s : Set E}
    {x : E} (hs : s ∈ 𝓝 x) (hg : IntegrableOn (g ∘ A) s μ) (hA : Function.Surjective A) :
    ∃ t ∈ 𝓝 (A x), IntegrableOn g t ν := by
  set L := A.linearCoord hA
  have hs' : L.symm ⁻¹' s ∈ 𝓝 (L x) :=
    L.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hs)
  obtain ⟨t₁, ht₁, t₂, ht₂, hst⟩ := mem_nhds_prod_iff.1 hs'
  refine ⟨t₁, by simpa [L] using ht₁, ?_⟩
  -- Pass to `μ.map L`, a positive multiple of the product measure.
  have hgL : (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) ∘ L.toHomeomorph = g ∘ A :=
    funext fun y => by simp [L]
  have hmap : IntegrableOn (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) (t₁ ×ˢ t₂)
      (μ.map L) := by
    refine L.toHomeomorph.measurableEmbedding.integrableOn_map_iff.2 ?_
    rw [hgL]
    refine hg.mono_set fun y hy => ?_
    simpa [L] using hst hy
  have hc : (A.linearScale hA μ ν)⁻¹ • μ.map L = ν.prod Measure.addHaar := by
    rw [A.map_linearCoord hA μ ν, smul_smul, inv_mul_cancel₀ (A.linearScale_pos hA μ ν).ne',
      one_smul]
  have hprod : IntegrableOn (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) (t₁ ×ˢ t₂)
      (ν.prod Measure.addHaar) := by
    rw [← hc, IntegrableOn, Measure.restrict_smul]
    exact hmap.integrable.smul_measure_nnreal
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  refine hprod.of_comp_fst ?_
  rw [Ne, Measure.restrict_eq_zero]
  exact (Measure.measure_pos_of_mem_nhds _ ht₂).ne'

end MeasureTheory
