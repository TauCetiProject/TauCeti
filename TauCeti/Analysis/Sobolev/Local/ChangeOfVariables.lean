/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import Mathlib.Analysis.Complex.ReImTopology

import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Change of variables in local Sobolev classes

Let `Φ` be a `C¹` map, injective with invertible derivative on an open set `Ω` of a
finite-dimensional real inner product space. Precomposition with `Φ` preserves weak
differentiability: if `Du` is a weak derivative of `u` on an open set `V` and `Φ` maps an open set
`U ⊆ Ω` into `V`, then

`D(u ∘ Φ)(x) = Du(Φ x) ∘ DΦ(x)`

weakly on `U`. No integrability beyond local integrability is assumed, and the codomain is any
complete real normed space. Locally, on a ball whose closure lies in `U`, the derivative of `Φ` is
bounded and its Jacobian is bounded below, so the first-order change of variables
`TauCeti.W1p.compL` applies to each scalar component `ℓ ∘ u`; the local identities glue
(`TauCeti.hasWeakFDerivOn_iff_locally`) and continuous linear functionals detect the vector-valued
identity (`TauCeti.hasWeakFDerivOn_of_forall_strongDual`). On a compact set `K ⊆ Ω` the `Lᵖ`
norms are controlled by `sup_K ‖DΦ‖` and `inf_K |det DΦ|`.

On planar domains this gives the invariance of the local classes `TauCeti.MemWkpLoc p U k` of
orders `k ≤ 1` under such changes of variables, for arbitrary sets `U` and `V` reaching their
boundary provided `Φ` maps `interior U` into `interior V`. In particular a `C¹` diffeomorphism
preserving the real axis and the upper half-plane preserves the half-disc classes. For real-affine
maps `z ↦ A z + b` every order is preserved: the derivative of `u (A z + b)` is
`Du (A z + b) ∘ A`, and induction places `A` in each slot of the higher derivatives. The
dilation `z ↦ 2 z` scales the first derivative by `2`, the reflection `z ↦ -conj z` preserves the
half-disc classes, and the rotation `z ↦ I z` does not preserve the real axis.

Higher orders for nonlinear `Φ` need the multiplication of local Sobolev maps by smooth
coefficients and are not treated here.

## Main declarations

* `TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`: the chain rule for weak derivatives under a
  `C¹` change of variables.
* `TauCeti.eLpNorm_comp_restrict_le`, `TauCeti.eLpNorm_comp_fderiv_restrict_le`: the `Lᵖ`
  bounds on a compact set.
* `TauCeti.MemWkpLoc.comp_contDiffOn_diffeo`: invariance of the local classes of order at most one.
* `TauCeti.MemWkpLoc.comp_contDiffOn_diffeo_halfPlane`: the half-disc version.
* `TauCeti.MemWkpLoc.comp_continuousLinearEquiv_add`: invariance of every order under real-affine
  maps.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6.
-/

public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ComplexConjugate

namespace TauCeti

/-! ### Bounds on compact sets -/

section DetBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → E} {Ω : Set E}

/-- On a nonempty compact subset of the open set where `Φ` is `C¹` with invertible derivative,
the Jacobian is bounded below by a positive constant and the derivative is bounded. -/
private theorem exists_det_bounds_of_isCompact {K : Set E} (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ 1 Φ Ω) (hdet : ∀ x ∈ Ω, (fderiv ℝ Φ x).det ≠ 0) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ c L : ℝ, 0 < c ∧ (∀ x ∈ K, c ≤ |(fderiv ℝ Φ x).det|) ∧ ∀ x ∈ K, ‖fderiv ℝ Φ x‖ ≤ L := by
  have hcont : ContinuousOn (fderiv ℝ Φ) K :=
    (hΦ.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hKΩ
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hcont
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, L, one_pos, by simp, hL⟩
  obtain ⟨y, hyK, hy⟩ := hK.exists_isMinOn hne
    ((ContinuousLinearMap.continuous_det.comp_continuousOn hcont).abs)
  exact ⟨_, L, abs_pos.2 (hdet y (hKΩ hyK)), fun x hx => hy hx, hL⟩

end DetBounds

section Bounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Φ : E → E} {Ω s : Set E} {c L : ℝ} {p : ENNReal}

/-- The pushforward bound used on a measurable subset of the open set where `Φ` is
differentiable and injective. -/
private theorem map_restrict_le_of_subset (hΩ : IsOpen Ω) (hΦ : DifferentiableOn ℝ Φ Ω)
    (hinj : InjOn Φ Ω) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ Φ x).det|) :
    (mu.restrict s).map Φ ≤ (ENNReal.ofReal c)⁻¹ • mu.restrict (Φ '' s) :=
  map_restrict_le_smul_restrict_image mu hs.nullMeasurableSet (fun x hx =>
    ((hΦ x (hsΩ hx)).differentiableAt (hΩ.mem_nhds (hsΩ hx))).hasFDerivAt.hasFDerivWithinAt)
    (hinj.mono hsΩ) hc hdet

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem aemeasurable_restrict_of_subset (hΦ : DifferentiableOn ℝ Φ Ω) (hsΩ : s ⊆ Ω)
    (hs : MeasurableSet s) : AEMeasurable Φ (mu.restrict s) :=
  (hΦ.continuousOn.mono hsΩ).aemeasurable hs

omit [NormedSpace ℝ F] in
/-- **`Lᵖ` bound for precomposition on a measurable set.** If `Φ` is differentiable and injective
on an open set containing `s`, and `c ≤ |det DΦ|` on `s` with `c > 0`, then
`‖u ∘ Φ‖_{Lᵖ(s)} ≤ c^(-1/p) ‖u‖_{Lᵖ(Φ s)}`. -/
theorem eLpNorm_comp_restrict_le (hΩ : IsOpen Ω) (hΦ : DifferentiableOn ℝ Φ Ω)
    (hinj : InjOn Φ Ω) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ Φ x).det|) (u : E → F) :
    eLpNorm (fun x => u (Φ x)) p (mu.restrict s) ≤
      (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal * eLpNorm u p (mu.restrict (Φ '' s)) :=
  eLpNorm_comp_le_of_map_le_smul (aemeasurable_restrict_of_subset hΦ hsΩ hs)
    (map_restrict_le_of_subset hΩ hΦ hinj hsΩ hs hc hdet) p

omit [NormedSpace ℝ F] in
/-- Precomposition with `Φ` maps `Lᵖ(Φ s)` into `Lᵖ(s)` under the hypotheses of
`TauCeti.eLpNorm_comp_restrict_le`. -/
theorem _root_.MeasureTheory.MemLp.comp_restrict_of_det_le {u : E → F}
    (hu : MemLp u p (mu.restrict (Φ '' s))) (hΩ : IsOpen Ω) (hΦ : DifferentiableOn ℝ Φ Ω)
    (hinj : InjOn Φ Ω) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ Φ x).det|) :
    MemLp (fun x => u (Φ x)) p (mu.restrict s) :=
  (eLpNorm_comp_restrict_le hΩ hΦ hinj hsΩ hs hc hdet u).trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')) hu)

/-- **`Lᵖ` bound for the transformed derivative on a measurable set.** If moreover
`‖DΦ‖ ≤ L` on `s`, then `x ↦ D(Φ x) ∘ DΦ(x)` satisfies
`‖D ∘ Φ ∘ DΦ‖_{Lᵖ(s)} ≤ L c^(-1/p) ‖D‖_{Lᵖ(Φ s)}`, for `D` almost everywhere strongly measurable
on `Φ s`. -/
theorem eLpNorm_comp_fderiv_restrict_le {D : E → E →L[ℝ] F} (hΩ : IsOpen Ω)
    (hΦ : DifferentiableOn ℝ Φ Ω) (hinj : InjOn Φ Ω) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s)
    (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ Φ x).det|)
    (hL : ∀ x ∈ s, ‖fderiv ℝ Φ x‖ ≤ L) (hD : AEStronglyMeasurable D (mu.restrict (Φ '' s))) :
    eLpNorm (fun x => (D (Φ x)).comp (fderiv ℝ Φ x)) p (mu.restrict s) ≤
      ENNReal.ofReal L *
        ((ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal * eLpNorm D p (mu.restrict (Φ '' s))) := by
  have hmap := map_restrict_le_of_subset (mu := mu) hΩ hΦ hinj hsΩ hs hc hdet
  have hm := aemeasurable_restrict_of_subset (mu := mu) hΦ hsΩ hs
  have hDΦ : AEStronglyMeasurable (fun x => D (Φ x)) (mu.restrict s) :=
    hD.comp_aemeasurable_of_map_absolutelyContinuous hm
      (Measure.absolutelyContinuous_of_le_smul hmap)
  have hmeas : AEStronglyMeasurable (fun x => (D (Φ x)).comp (fderiv ℝ Φ x)) (mu.restrict s) :=
    (ContinuousLinearMap.compL ℝ E E F).aestronglyMeasurable_comp₂ hDΦ
      (measurable_fderiv ℝ Φ).aestronglyMeasurable
  calc eLpNorm (fun x => (D (Φ x)).comp (fderiv ℝ Φ x)) p (mu.restrict s)
      ≤ ENNReal.ofReal L * eLpNorm (fun x => D (Φ x)) p (mu.restrict s) := by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas ?_ p
        filter_upwards [ae_restrict_mem hs] with x hx
        calc ‖(D (Φ x)).comp (fderiv ℝ Φ x)‖ ≤ ‖D (Φ x)‖ * ‖fderiv ℝ Φ x‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ L * ‖D (Φ x)‖ := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right (hL x hx) (norm_nonneg _)
    _ ≤ _ := by
        gcongr
        exact eLpNorm_comp_le_of_map_le_smul hm hmap p

/-- Precomposition with `Φ` followed by composition with `DΦ` maps `Lᵖ(Φ s)` into `Lᵖ(s)`
under the hypotheses of `TauCeti.eLpNorm_comp_fderiv_restrict_le`. -/
theorem _root_.MeasureTheory.MemLp.comp_fderiv_restrict_of_det_le {D : E → E →L[ℝ] F}
    (hD : MemLp D p (mu.restrict (Φ '' s))) (hΩ : IsOpen Ω) (hΦ : DifferentiableOn ℝ Φ Ω)
    (hinj : InjOn Φ Ω) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ Φ x).det|) (hL : ∀ x ∈ s, ‖fderiv ℝ Φ x‖ ≤ L) :
    MemLp (fun x => (D (Φ x)).comp (fderiv ℝ Φ x)) p (mu.restrict s) :=
  (eLpNorm_comp_fderiv_restrict_le hΩ hΦ hinj hsΩ hs hc hdet hL
    hD.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')) hD))

end Bounds

/-! ### The chain rule for weak derivatives -/

section ChainRule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → E}

omit [NormedSpace ℝ F] in
/-- Local integrability is preserved by precomposition with a `C¹` map, injective with
invertible derivative on an open set containing the domain. -/
private theorem locallyIntegrableOn_comp {Ω : Set E} {U V : Set E} {u : E → F}
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ Ω)
    (hdet : ∀ x ∈ Ω, (fderiv ℝ Φ x).det ≠ 0) (hUΩ : U ⊆ Ω) (hU : IsOpen U)
    (hmaps : MapsTo Φ U V) (hu : LocallyIntegrableOn u V mu) :
    LocallyIntegrableOn (fun x => u (Φ x)) U mu := by
  refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK => ?_
  obtain ⟨c, L, hc, hcK, -⟩ := exists_det_bounds_of_isCompact hΩ hΦ hdet hK (hKU.trans hUΩ)
  have hΦK : IsCompact (Φ '' K) := hK.image_of_continuousOn
    ((hΦ.continuousOn.mono hUΩ).mono hKU)
  have hiK := hu.integrableOn_compact_subset ((image_mono hKU).trans hmaps.image_subset) hΦK
  exact memLp_one_iff_integrable.1 ((memLp_one_iff_integrable.2 hiK).comp_restrict_of_det_le hΩ
    (hΦ.differentiableOn one_ne_zero) hinj (hKU.trans hUΩ) hK.measurableSet hc hcK)

/-- The transformed derivative `x ↦ D(Φ x) ∘ DΦ(x)` is locally integrable whenever `D` is. -/
private theorem locallyIntegrableOn_comp_fderiv {Ω : Set E} {U V : Set E} {D : E → E →L[ℝ] F}
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ Ω)
    (hdet : ∀ x ∈ Ω, (fderiv ℝ Φ x).det ≠ 0) (hUΩ : U ⊆ Ω) (hU : IsOpen U)
    (hmaps : MapsTo Φ U V) (hD : LocallyIntegrableOn D V mu) :
    LocallyIntegrableOn (fun x => (D (Φ x)).comp (fderiv ℝ Φ x)) U mu := by
  refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK => ?_
  obtain ⟨c, L, hc, hcK, hLK⟩ := exists_det_bounds_of_isCompact hΩ hΦ hdet hK (hKU.trans hUΩ)
  have hΦK : IsCompact (Φ '' K) := hK.image_of_continuousOn
    ((hΦ.continuousOn.mono hUΩ).mono hKU)
  have hiK := hD.integrableOn_compact_subset ((image_mono hKU).trans hmaps.image_subset) hΦK
  exact memLp_one_iff_integrable.1 ((memLp_one_iff_integrable.2 hiK).comp_fderiv_restrict_of_det_le
    hΩ (hΦ.differentiableOn one_ne_zero) hinj (hKU.trans hUΩ) hK.measurableSet hc hcK hLK)

/-- The scalar chain rule on a ball whose closure lies in `U`, from the first-order change of
variables `TauCeti.W1p.compL` at exponent one. -/
private theorem hasWeakFDerivOn_comp_ball {U V : Opens E} {u : E → ℝ} {Du : E → E →L[ℝ] ℝ}
    (hu : HasWeakFDerivOn mu V u Du) (hΦ : ContDiffOn ℝ 1 Φ U) (hinj : InjOn Φ U)
    (hdet : ∀ x ∈ (U : Set E), (fderiv ℝ Φ x).det ≠ 0) (hmaps : MapsTo Φ U V) {x : E} {r : ℝ}
    (hr : Metric.closedBall x r ⊆ U) :
    HasWeakFDerivOn mu ⟨Metric.ball x r, Metric.isOpen_ball⟩ (fun y => u (Φ y))
      (fun y => (Du (Φ y)).comp (fderiv ℝ Φ y)) := by
  set B : Opens E := ⟨Metric.ball x r, Metric.isOpen_ball⟩
  have hK : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  have hBU : (B : Set E) ⊆ U := Metric.ball_subset_closedBall.trans hr
  obtain ⟨c, L, hc, hcK, hLK⟩ := exists_det_bounds_of_isCompact U.isOpen hΦ hdet hK hr
  -- An open neighbourhood `V'` of `Φ (closedBall x r)` with compact closure in `V`.
  have hΦK : IsCompact (Φ '' Metric.closedBall x r) :=
    hK.image_of_continuousOn (hΦ.continuousOn.mono hr)
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hΦK V.isOpen
    ((image_mono hr).trans hmaps.image_subset)
  set V' : Opens E := ⟨W, hWo⟩
  have hV'V : V' ≤ V := subset_closure.trans hWV
  have hmaps' : MapsTo Φ B V' := fun y hy => hKW ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
  have hΦB : DifferentiableOn ℝ Φ B := (hΦ.differentiableOn one_ne_zero).mono hBU
  have hcB : ∀ y ∈ (B : Set E), c ≤ |(fderiv ℝ Φ y).det| := fun y hy =>
    hcK y (Metric.ball_subset_closedBall hy)
  have hLB : ∀ y ∈ (B : Set E), ‖fderiv ℝ Φ y‖ ≤ L := fun y hy =>
    hLK y (Metric.ball_subset_closedBall hy)
  -- The value and the gradient of `u` are integrable on `V'`.
  set g : E → E := fun y => (InnerProductSpace.toDual ℝ E).symm (Du y)
  have hg : ∀ y, innerSL ℝ (g y) = Du y := fun y => by
    ext v
    simp [g, InnerProductSpace.toDual_symm_apply]
  have hu1 : MemLp u 1 (mu.restrict V') := memLp_one_iff_integrable.2
    ((hu.locallyIntegrableOn.integrableOn_compact_subset hWV hWc).mono_set subset_closure)
  have hDu1 : MemLp Du 1 (mu.restrict V') := memLp_one_iff_integrable.2
    ((hu.locallyIntegrableOn_deriv.integrableOn_compact_subset hWV hWc).mono_set subset_closure)
  have hg1 : MemLp g 1 (mu.restrict V') :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
      hDu1
  have hw : HasWeakFDerivOn mu V' (hu1.toLp u) (fun y => innerSL ℝ (hg1.toLp g y)) := by
    refine ((hu.mono hV'V).congr_ae hu1.coeFn_toLp.symm).congr_ae_deriv ?_
    filter_upwards [hg1.coeFn_toLp] with y hy
    rw [hy, hg]
  set w : W1p mu V' 1 := W1p.mk (hu1.toLp u) (hg1.toLp g) hw
  have hcomp := W1p.hasWeakFDerivOn
    (W1p.compL Φ ENNReal.one_ne_top hΦB (hinj.mono hBU) hmaps' hLB hc hcB w)
  -- Almost-everywhere statements on `V'` pull back to `B` along `Φ`.
  have hpull : ∀ {P : E → Prop}, (∀ᵐ z ∂mu.restrict V', P z) → ∀ᵐ y ∂mu.restrict B, P (Φ y) :=
    fun h => ae_comp_of_map_absolutelyContinuous
      (hΦB.continuousOn.aemeasurable B.isOpen.measurableSet)
      (Measure.absolutelyContinuous_of_le_smul
        (map_restrict_le_smul_restrict_of_differentiableOn mu B.isOpen hΦB (hinj.mono hBU)
          hmaps' hc hcB)) h
  refine (hcomp.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [W1p.value_compL_ae Φ ENNReal.one_ne_top hΦB (hinj.mono hBU) hmaps' hLB hc
      hcB w, hpull hu1.coeFn_toLp] with y h1 h2
    rw [h1, W1p.value_mk, h2]
  · filter_upwards [W1p.gradient_compL_ae Φ ENNReal.one_ne_top hΦB (hinj.mono hBU) hmaps' hLB hc
      hcB w, hpull hg1.coeFn_toLp] with y h1 h2
    rw [h1, W1p.gradient_mk, h2, ← hg (Φ y)]
    ext v
    simp [ContinuousLinearMap.adjoint_inner_left]

/-- **The chain rule for weak derivatives under a `C¹` change of variables.** Let `Φ` be `C¹`
and injective on an open set `U`, with invertible derivative there, mapping `U` into an open set
`V`. If `Du` is a weak derivative of `u` on `V`, then `x ↦ Du(Φ x) ∘ DΦ(x)` is a weak derivative
of `u ∘ Φ` on `U`. The derivative of `Φ` need not be bounded on `U`, nor its Jacobian bounded
below, and the codomain may be any complete real normed space. -/
theorem HasWeakFDerivOn.comp_contDiffOn_diffeo {U V : Opens E} {u : E → F}
    {Du : E → E →L[ℝ] F} (hu : HasWeakFDerivOn mu V u Du) (hΦ : ContDiffOn ℝ 1 Φ U)
    (hinj : InjOn Φ U) (hdet : ∀ x ∈ (U : Set E), (fderiv ℝ Φ x).det ≠ 0)
    (hmaps : MapsTo Φ U V) :
    HasWeakFDerivOn mu U (fun x => u (Φ x)) (fun x => (Du (Φ x)).comp (fderiv ℝ Φ x)) := by
  have := hu.completeSpace
  have hDloc := locallyIntegrableOn_comp_fderiv U.isOpen hΦ hinj hdet subset_rfl U.isOpen hmaps
    hu.locallyIntegrableOn_deriv
  refine hasWeakFDerivOn_of_forall_strongDual
    (locallyIntegrableOn_comp U.isOpen hΦ hinj hdet subset_rfl U.isOpen hmaps
      hu.locallyIntegrableOn)
    (fun v => (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp hDloc) fun ℓ => ?_
  refine hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds hx)
  exact ⟨_, Metric.mem_ball_self hr,
    hasWeakFDerivOn_comp_ball (hu.clm_comp ℓ) hΦ hinj hdet hmaps hrU⟩

/-- **Affine changes of variables.** For `A : E ≃L[ℝ] E` and `b : E` with `x ↦ A x + b` mapping `U`
into `V`, a weak derivative `Du` of `u` on `V` gives the weak derivative `x ↦ Du (A x + b) ∘ A` of
`x ↦ u (A x + b)` on `U`. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_add {U V : Opens E} {u : E → F}
    {Du : E → E →L[ℝ] F} (hu : HasWeakFDerivOn mu V u Du) (A : E ≃L[ℝ] E) (b : E)
    (hmaps : MapsTo (fun x => A x + b) U V) :
    HasWeakFDerivOn mu U (fun x => u (A x + b)) (fun x => (Du (A x + b)).comp (A : E →L[ℝ] E)) := by
  have hfd : ∀ x, fderiv ℝ (fun x => A x + b) x = (A : E →L[ℝ] E) := fun x =>
    (A.hasFDerivAt.add_const b).fderiv
  have h := hu.comp_contDiffOn_diffeo (Φ := fun x => A x + b)
    (A.contDiff.add contDiff_const).contDiffOn
    (fun x _ y _ h => A.injective (add_right_cancel h))
    (fun x _ => by rw [hfd]; exact A.toLinearEquiv.isUnit_det'.ne_zero) hmaps
  simpa only [hfd] using h

end ChainRule

/-! ### Local Sobolev classes on planar sets -/

section Planar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ENNReal} {Φ : ℂ → ℂ} {Ω U V : Set ℂ} {k : ℕ}

omit [NormedSpace ℝ F] in
/-- Precomposition with a `C¹` map, injective with invertible derivative on an open set containing
`U` and mapping `U` into `V`, preserves local `Lᵖ` membership. -/
theorem MemLpLoc.comp_contDiffOn_diffeo {u : ℂ → F} (hu : MemLpLoc p V u) (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ Ω) (hdet : ∀ z ∈ Ω, (fderiv ℝ Φ z).det ≠ 0)
    (hUΩ : U ⊆ Ω) (hmaps : MapsTo Φ U V) : MemLpLoc p U (fun z => u (Φ z)) := by
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  obtain ⟨c, L, hc, hcK, -⟩ := exists_det_bounds_of_isCompact hΩ hΦ hdet hK (hKU.trans hUΩ)
  exact (memLpLoc_iff.1 hu _ ((image_mono hKU).trans hmaps.image_subset)
    (hK.image_of_continuousOn ((hΦ.continuousOn.mono hUΩ).mono hKU))).comp_restrict_of_det_le hΩ
      (hΦ.differentiableOn one_ne_zero) hinj (hKU.trans hUΩ) hK.measurableSet hc hcK

/-- The transformed derivative `z ↦ D(Φ z) ∘ DΦ(z)` of a locally `Lᵖ` field `D` is locally `Lᵖ`. -/
theorem MemLpLoc.comp_fderiv_contDiffOn_diffeo {D : ℂ → ℂ →L[ℝ] F} (hD : MemLpLoc p V D)
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ Ω)
    (hdet : ∀ z ∈ Ω, (fderiv ℝ Φ z).det ≠ 0) (hUΩ : U ⊆ Ω) (hmaps : MapsTo Φ U V) :
    MemLpLoc p U (fun z => (D (Φ z)).comp (fderiv ℝ Φ z)) := by
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  obtain ⟨c, L, hc, hcK, hLK⟩ :=
    exists_det_bounds_of_isCompact hΩ hΦ hdet hK (hKU.trans hUΩ)
  exact (memLpLoc_iff.1 hD _ ((image_mono hKU).trans hmaps.image_subset)
    (hK.image_of_continuousOn ((hΦ.continuousOn.mono hUΩ).mono hKU))).comp_fderiv_restrict_of_det_le
      hΩ (hΦ.differentiableOn one_ne_zero) hinj (hKU.trans hUΩ) hK.measurableSet hc hcK hLK

/-- **Change of variables in local Sobolev classes of order at most one.** Let `Φ` be `C¹` and
injective with invertible derivative on an open set `Ω ⊇ U`, mapping `U` into `V` and
`interior U` into `interior V`. Then precomposition with `Φ` maps `MemWkpLoc p V k` into
`MemWkpLoc p U k` for `k ≤ 1`. The sets `U` and `V` may reach their boundaries, as half-discs do.
The weak derivative of `u ∘ Φ` is `Du(Φ z) ∘ DΦ(z)`
(`TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`) and its local `Lᵖ` norms are controlled by
`TauCeti.eLpNorm_comp_fderiv_restrict_le`. -/
theorem MemWkpLoc.comp_contDiffOn_diffeo {u : ℂ → F} (hk : k ≤ 1) (hu : MemWkpLoc p V k u)
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ Ω)
    (hdet : ∀ z ∈ Ω, (fderiv ℝ Φ z).det ≠ 0) (hUΩ : U ⊆ Ω) (hmaps : MapsTo Φ U V)
    (hint : MapsTo Φ (interior U) (interior V)) : MemWkpLoc p U k (fun z => u (Φ z)) := by
  have hiΩ : interior U ⊆ Ω := interior_subset.trans hUΩ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact memWkpLoc_zero_iff.2
      (MemLpLoc.comp_contDiffOn_diffeo (memWkpLoc_zero_iff.1 hu) hΩ hΦ hinj hdet hUΩ hmaps)
  · obtain ⟨hLp, D, hD, hD0⟩ := memWkpLoc_succ_iff.1 hu
    refine memWkpLoc_succ_iff.2 ⟨hLp.comp_contDiffOn_diffeo hΩ hΦ hinj hdet hUΩ hmaps, _, ?_,
      memWkpLoc_zero_iff.2 (MemLpLoc.comp_fderiv_contDiffOn_diffeo (memWkpLoc_zero_iff.1 hD0)
        hΩ hΦ hinj hdet hUΩ hmaps)⟩
    exact hD.comp_contDiffOn_diffeo (hΦ.mono hiΩ) (hinj.mono hiΩ) (fun z hz => hdet z (hiΩ hz))
      (by simpa using hint)

/-- **Change of variables between open planar domains.** For open `U` and `V`, a `C¹` map
injective with invertible derivative on `U` and mapping `U` into `V` preserves the local classes
of order at most one. -/
theorem MemWkpLoc.comp_contDiffOn_diffeo_of_isOpen {U V : Opens ℂ} {u : ℂ → F} (hk : k ≤ 1)
    (hu : MemWkpLoc p V k u) (hΦ : ContDiffOn ℝ 1 Φ U) (hinj : InjOn Φ U)
    (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0) (hmaps : MapsTo Φ U V) :
    MemWkpLoc p U k (fun z => u (Φ z)) :=
  hu.comp_contDiffOn_diffeo hk U.isOpen hΦ hinj hdet subset_rfl hmaps
    (by simpa only [U.isOpen.interior_eq, V.isOpen.interior_eq] using hmaps)

/-- **Change of variables on half-discs.** Let `Φ` be `C¹` and injective with invertible
derivative on an open set `U'`, mapping `U'` into an open set `V'`, the real axis into itself and
the upper half-plane into itself. Then precomposition with `Φ` maps the half-disc class
`MemWkpLoc p (V' ∩ {0 ≤ im}) k` into `MemWkpLoc p (U' ∩ {0 ≤ im}) k` for `k ≤ 1`. -/
theorem MemWkpLoc.comp_contDiffOn_diffeo_halfPlane {U' V' : Set ℂ} {u : ℂ → F} (hk : k ≤ 1)
    (hu : MemWkpLoc p (V' ∩ {z | 0 ≤ z.im}) k u) (hU' : IsOpen U') (hV' : IsOpen V')
    (hΦ : ContDiffOn ℝ 1 Φ U') (hinj : InjOn Φ U') (hdet : ∀ z ∈ U', (fderiv ℝ Φ z).det ≠ 0)
    (hmaps : MapsTo Φ U' V') (hreal : ∀ z ∈ U', z.im = 0 → (Φ z).im = 0)
    (hupper : ∀ z ∈ U', 0 < z.im → 0 < (Φ z).im) :
    MemWkpLoc p (U' ∩ {z | 0 ≤ z.im}) k (fun z => u (Φ z)) := by
  have hint : ∀ W : Set ℂ, IsOpen W → interior (W ∩ {z | 0 ≤ z.im}) = W ∩ {z | 0 < z.im} :=
    fun W hW => by rw [interior_inter, hW.interior_eq, Complex.interior_setOfPred_le_im]
  refine hu.comp_contDiffOn_diffeo hk hU' hΦ hinj hdet inter_subset_left ?_ ?_
  · rintro z ⟨hzU, hz⟩
    refine ⟨hmaps hzU, ?_⟩
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with h | h
    · exact (hupper z hzU h).le
    · exact (hreal z hzU h.symm).ge
  · rw [hint U' hU', hint V' hV']
    exact fun z ⟨hzU, hz⟩ => ⟨hmaps hzU, hupper z hzU hz⟩

/-- **Real-affine changes of variables preserve every order.** For `A : ℂ ≃L[ℝ] ℂ`, `b : ℂ` and
`z ↦ A z + b` mapping `U` into `V`, precomposition maps `MemWkpLoc p V k` into
`MemWkpLoc p U k`. The weak derivative of `u (A z + b)` is `Du (A z + b) ∘ A`, so the `i`-th
derivative is the `i`-th derivative of `u` at `A z + b` with `A` applied in each slot. -/
theorem MemWkpLoc.comp_continuousLinearEquiv_add {u : ℂ → F} (hu : MemWkpLoc p V k u)
    (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) (hmaps : MapsTo (fun z => A z + b) U V) :
    MemWkpLoc p U k (fun z => u (A z + b)) := by
  set Φ : ℂ → ℂ := fun z => A z + b
  have hfd : ∀ z, fderiv ℝ Φ z = (A : ℂ →L[ℝ] ℂ) := fun z =>
    ((A : ℂ →L[ℝ] ℂ).hasFDerivAt.add_const b).fderiv
  have hΦ : ContDiffOn ℝ 1 Φ univ :=
    ((A : ℂ →L[ℝ] ℂ).contDiff.add contDiff_const).contDiffOn
  have hinj : InjOn Φ univ := fun z _ w _ h => A.injective (add_right_cancel h)
  have hdet : ∀ z ∈ (univ : Set ℂ), (fderiv ℝ Φ z).det ≠ 0 := fun z _ => by
    rw [hfd]
    exact (A.toLinearEquiv.isUnit_det').ne_zero
  -- `Φ` is a homeomorphism, so it maps `interior U` into `interior V`.
  have hint : MapsTo Φ (interior U) (interior V) := by
    have hh := (A.toHomeomorph.trans (Homeomorph.addRight b)).image_interior U
    intro z hz
    have : Φ z ∈ interior (Φ '' U) := hh ▸ ⟨z, hz, rfl⟩
    exact interior_mono hmaps.image_subset this
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 (MemLpLoc.comp_contDiffOn_diffeo
      (memWkpLoc_zero_iff.1 hu) isOpen_univ hΦ hinj hdet (subset_univ _) hmaps)
  | succ k ih =>
    obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    refine memWkpLoc_succ_iff.2
      ⟨hLp.comp_contDiffOn_diffeo isOpen_univ hΦ hinj hdet (subset_univ _) hmaps,
      fun z => ((ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (A : ℂ →L[ℝ] ℂ)) (D (Φ z)), ?_,
      (ih hk).clm_comp _⟩
    exact hD.comp_continuousLinearEquiv_add (U := Opens.interior U) A b (by simpa using hint)

/-! ### Checks -/

/-- The dilation `z ↦ 2 z` carries `MemWkpLoc p (ball 0 2) k` to `MemWkpLoc p (ball 0 1) k`. -/
theorem memWkpLoc_ball_one_comp_two_mul {u : ℂ → F}
    (hu : MemWkpLoc p (Metric.ball 0 2) k u) :
    MemWkpLoc p (Metric.ball 0 1) k (fun z => u (2 * z)) := by
  convert hu.comp_continuousLinearEquiv_add
    (LinearEquiv.smulOfNeZero ℝ ℂ 2 two_ne_zero).toContinuousLinearEquiv 0 ?_ using 2 with z
  · simp [Complex.real_smul]
  · intro z hz
    simp only [Metric.mem_ball, dist_zero_right, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.smulOfNeZero_apply, add_zero, norm_smul, Real.norm_ofNat] at hz ⊢
    linarith

/-- The dilation `z ↦ 2 z` scales the first weak derivative by `2`: if `Du` is a weak derivative of
`u` on `ball 0 2`, then `z ↦ 2 • Du (2 z)` is a weak derivative of `z ↦ u (2 z)` on `ball 0 1`.
Iterating, the `i`-th derivative is scaled by `2 ^ i`. -/
theorem HasWeakFDerivOn.ball_one_comp_two_mul {u : ℂ → F} {Du : ℂ → ℂ →L[ℝ] F}
    (hu : HasWeakFDerivOn volume ⟨Metric.ball 0 2, Metric.isOpen_ball⟩ u Du) :
    HasWeakFDerivOn volume ⟨Metric.ball 0 1, Metric.isOpen_ball⟩ (fun z => u (2 * z))
      (fun z => (2 : ℝ) • Du (2 * z)) := by
  set A : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ 2 two_ne_zero).toContinuousLinearEquiv
  have hA : ∀ z, A z = 2 * z := fun z => by simp [A, Complex.real_smul]
  have h := hu.comp_continuousLinearEquiv_add (U := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩) A 0
    (fun z hz => by
      simp only [SetLike.mem_coe, Opens.mem_mk, Metric.mem_ball, dist_zero_right, hA, add_zero,
        norm_mul, Complex.norm_ofNat] at hz ⊢
      linarith)
  convert h using 2 with z
  · simp [hA]
  · ext v
    simp [hA, Complex.real_smul, ← map_smul]

/-- Complex conjugation preserves the real axis and every local Sobolev class on sets it maps
into one another. -/
theorem memWkpLoc_comp_conj {u : ℂ → F} (hu : MemWkpLoc p V k u)
    (hmaps : MapsTo (conj ·) U V) : MemWkpLoc p U k (fun z => u (conj z)) := by
  simpa using hu.comp_continuousLinearEquiv_add Complex.conjCLE 0 (by simpa using hmaps)

/-- Complex conjugation maps the real axis into itself. -/
theorem mapsTo_conj_setOf_im_eq_zero :
    MapsTo (conj ·) {z : ℂ | z.im = 0} {z : ℂ | z.im = 0} := fun z hz => by
  simpa using hz

/-- The reflection `z ↦ -conj z` across the imaginary axis preserves the real axis and the upper
half-plane, hence the half-disc classes on the unit half-disc, at every order. -/
theorem memWkpLoc_halfDisc_comp_neg_conj {u : ℂ → F}
    (hu : MemWkpLoc p (Metric.ball 0 1 ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p (Metric.ball 0 1 ∩ {z | 0 ≤ z.im}) k (fun z => u (-conj z)) := by
  simpa using hu.comp_continuousLinearEquiv_add (Complex.conjCLE.trans
    (ContinuousLinearEquiv.neg ℝ)) 0 (fun z hz => by simpa using hz)

/-- The rotation `z ↦ I z` does not preserve the real axis, so it is not admissible on
half-discs. -/
theorem not_mapsTo_I_mul_setOf_im_eq_zero :
    ¬ MapsTo (fun z : ℂ => Complex.I * z) {z | z.im = 0} {z | z.im = 0} := fun h => by
  simpa using h (show (1 : ℂ) ∈ {z : ℂ | z.im = 0} by simp)

end Planar

end TauCeti
