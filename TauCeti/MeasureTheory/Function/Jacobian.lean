/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# Change of variables: pushforward bounds, `Lᵖ` bounds and affine invariance of set integrals

Let `f` be injective and differentiable on a null-measurable subset `s` of a finite-dimensional real
normed space with an additive Haar measure `μ`. Mathlib's change of variables formula
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` says that `f` pushes the measure
`|det f'| μ` on `s` forward to `μ` on `f '' s`. If the Jacobian is bounded below, `c ≤ |det f'|`
on `s` with `c > 0`, then `f` pushes `μ` on `s` forward to at most `c⁻¹ μ` on `f '' s`
(`MeasureTheory.map_restrict_le_smul_restrict_image`).

For `f` differentiable on an open set `s` and mapping it into `t`, the same bound holds with the
Fréchet derivative `fderiv ℝ f` as Jacobian and `μ` on `t` in place of `μ` on `f '' s`
(`MeasureTheory.map_restrict_le_smul_restrict_of_differentiableOn`).

Such a pushforward bound `μ.map f ≤ C • ν` gives the `eLpNorm` estimate for precomposition with
`f` (`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). For a change of variables no upper bound on
the Jacobian is needed, but a Jacobian that may vanish gives no such bound. On a measurable set `s`
inside an open set where `f` is differentiable, with `f` injective on `s` and given constants
`c ≤ |det Df|` and `‖Df‖ ≤ L` on `s`, this bounds the `Lᵖ(s)` norms of `u ∘ f` and of the
transformed derivative `x ↦ D (f x) ∘ Df x` by those of `u` and `D` on `f '' s`
(`MeasureTheory.eLpNorm_comp_restrict_le`, `MeasureTheory.eLpNorm_comp_fderiv_restrict_le`).
Such constants exist on every compact set on which a `C¹` map has invertible derivative
(`MeasureTheory.exists_det_bounds_of_isCompact`), so precomposition with a map that is `C¹`,
injective and with invertible derivative on an open set preserves local integrability
(`MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`).

A continuous affine map `T` carrying a measurable set `s` of finite measure onto itself preserves
integrals over `s`. When `s` is not null, the linear part of `T` has determinant `±1`, because the
image of `s` has `|det|` times the measure of `s`, so the change of variables formula has no
Jacobian factor
(`ContinuousAffineMap.setIntegral_comp_of_image_eq`). This is how a symmetry of a polytope, such as
a permutation of the vertices of a simplex, acts on integrals over it.

## Main declarations

* `MeasureTheory.map_restrict_le_smul_restrict_image`: the pushforward of `μ` on `s` is at most
  `c⁻¹ μ` on `f '' s`.
* `MeasureTheory.map_restrict_le_smul_restrict_of_differentiableOn`: the same for `f`
  differentiable on an open set `s` and mapping it into `t`, with `μ` on `t` as the target.
* `MeasureTheory.exists_det_bounds_of_isCompact`: Jacobian and derivative bounds on a compact
  set.
* `MeasureTheory.eLpNorm_comp_restrict_le`, `MeasureTheory.eLpNorm_comp_fderiv_restrict_le`: the
  `Lᵖ` bounds for precomposition on a measurable set, given such constants.
* `MeasureTheory.MemLp.comp_restrict_of_isCompact`,
  `MeasureTheory.MemLp.comp_fderiv_restrict_of_isCompact`: precomposition on a compact set.
* `MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`,
  `MeasureTheory.LocallyIntegrableOn.comp_fderiv_contDiffOn_diffeo`: local integrability is
  preserved.
* `ContinuousAffineMap.setIntegral_comp_of_image_eq`: integrals over `s` are invariant under a
  continuous affine map carrying `s` onto itself, when `s` has finite measure.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {s t : Set E} {f : E → E} {f' : E → E →L[ℝ] E} {c : ℝ}

/-- **Pushforward bound from a Jacobian lower bound.** If `f` is injective and differentiable on
a null-measurable set `s`, and `c ≤ |det f'|` on `s` with `c > 0`, then `f` pushes `μ` restricted to
`s` forward to at most `c⁻¹` times `μ` restricted to `f '' s`. -/
theorem map_restrict_le_smul_restrict_image (hs : NullMeasurableSet s μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(f' x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ.restrict (f '' s) := by
  -- Replace `f` by a measurable function `g` agreeing with it a.e. on `s`, so that
  -- `Measure.map_mono` applies.
  have hcont : ContinuousOn f s := fun x hx => (hf' x hx).differentiableWithinAt.continuousWithinAt
  have hfm : AEMeasurable f (μ.restrict s) := hcont.aemeasurable₀ hs
  set g : E → E := hfm.mk f
  have hg : Measurable g := hfm.measurable_mk
  have hfg : f =ᵐ[μ.restrict s] g := hfm.ae_eq_mk
  -- Mathlib's change of variables: `f` pushes `|det f'| μ` on `s` forward to `μ` on `f '' s`.
  set W := (μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|
  have hW : W.map f = μ.restrict (f '' s) := map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf
  rw [← hW, Measure.map_congr hfg,
    Measure.map_congr (hfg.filter_mono (withDensity_absolutelyContinuous _ _).ae_le),
    ← Measure.map_smul _ hg.aemeasurable]
  -- It remains to compare `μ` on `s` with `c⁻¹ |det f'| μ` on `s`.
  refine Measure.map_mono (Measure.le_iff.2 fun t ht => ?_) hg
  have hc0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  rw [_root_.smul_apply, smul_eq_mul, withDensity_apply _ ht, ← ENNReal.mul_le_iff_le_inv hc0
    ENNReal.ofReal_ne_top, ← setLIntegral_const]
  exact lintegral_mono_ae ((ae_restrict_of_ae (ae_restrict_mem₀ hs)).mono fun x hx =>
    ENNReal.ofReal_le_ofReal (hdet x hx))

/-- **Pushforward bound for a map differentiable on an open set.** If `f` is injective and
differentiable on an open set `s`, maps `s` into `t`, and `c ≤ |det (fderiv ℝ f x)|` on `s` with
`c > 0`, then `f` pushes `μ` restricted to `s` forward to at most `c⁻¹` times `μ` restricted to
`t`. -/
theorem map_restrict_le_smul_restrict_of_differentiableOn (hs : IsOpen s)
    (hf : DifferentiableOn ℝ f s) (hinj : InjOn f s) (hmaps : MapsTo f s t) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ.restrict t :=
  (map_restrict_le_smul_restrict_image μ hs.measurableSet.nullMeasurableSet (fun x hx =>
    ((hf x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt) hinj hc
      hdet).trans (by gcongr; exact hmaps.image_subset)

/-! ### Jacobian bounds on compact sets and `Lᵖ` bounds for precomposition -/

section Precomposition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [NormedAddCommGroup F]
  {f : E → E} {Ω s K U V : Set E} {c L : ℝ} {p : ℝ≥0∞}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Jacobian bounds on a compact set.** If `f` is `C¹` on an open set `Ω` and its derivative is
invertible on a compact set `K ⊆ Ω`, then on `K` the Jacobian is bounded below by a positive
constant and the derivative is bounded. -/
theorem exists_det_bounds_of_isCompact (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hdet : ∀ x ∈ K, (fderiv ℝ f x).det ≠ 0) :
    ∃ c L : ℝ, 0 < c ∧ (∀ x ∈ K, c ≤ |(fderiv ℝ f x).det|) ∧ ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ L := by
  have hcont : ContinuousOn (fderiv ℝ f) K :=
    (hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hKΩ
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hcont
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, L, one_pos, by simp, hL⟩
  obtain ⟨y, hyK, hy⟩ := hK.exists_isMinOn hne
    ((ContinuousLinearMap.continuous_det.comp_continuousOn hcont).abs)
  exact ⟨_, L, abs_pos.2 (hdet y hyK), fun x hx => hy hx, hL⟩

variable [μ.IsAddHaarMeasure]

/-- **Pushforward bound on a subset of an open set of differentiability.** If `f` is
differentiable on an open set `Ω`, injective on a measurable set `s ⊆ Ω`, and
`c ≤ |det (fderiv ℝ f x)|` on `s` with `c > 0`, then `f` pushes `μ` restricted to `s` forward to
at most `c⁻¹` times `μ` restricted to `f '' s`. -/
theorem map_restrict_le_smul_restrict_image_of_differentiableOn (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℝ f Ω) (hinj : InjOn f s) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s)
    (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ.restrict (f '' s) :=
  map_restrict_le_smul_restrict_image μ hs.nullMeasurableSet (fun x hx =>
    ((hf x (hsΩ hx)).differentiableAt (hΩ.mem_nhds (hsΩ hx))).hasFDerivAt.hasFDerivWithinAt)
    hinj hc hdet

/-- **`Lᵖ` bound for precomposition on a measurable set.** Under the hypotheses of
`MeasureTheory.map_restrict_le_smul_restrict_image_of_differentiableOn`,
`‖u ∘ f‖_{Lᵖ(s)} ≤ c^(-1/p) ‖u‖_{Lᵖ(f s)}`. -/
theorem eLpNorm_comp_restrict_le (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω)
    (hinj : InjOn f s) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) (u : E → F) :
    eLpNorm (fun x => u (f x)) p (μ.restrict s) ≤
      (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal * eLpNorm u p (μ.restrict (f '' s)) :=
  eLpNorm_comp_le_of_map_le_smul ((hf.continuousOn.mono hsΩ).aemeasurable hs)
    (map_restrict_le_smul_restrict_image_of_differentiableOn hΩ hf hinj hsΩ hs hc hdet) p

/-- Precomposition with `f` maps `Lᵖ(f s)` into `Lᵖ(s)` under the hypotheses of
`MeasureTheory.eLpNorm_comp_restrict_le`. -/
theorem MemLp.comp_restrict_of_le_abs_det {u : E → F} (hu : MemLp u p (μ.restrict (f '' s)))
    (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω) (hinj : InjOn f s) (hsΩ : s ⊆ Ω)
    (hs : MeasurableSet s) (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) :
    MemLp (fun x => u (f x)) p (μ.restrict s) :=
  (eLpNorm_comp_restrict_le hΩ hf hinj hsΩ hs hc hdet u).trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')) hu)

variable [NormedSpace ℝ F]

/-- **`Lᵖ` bound for the transformed derivative on a measurable set.** If moreover
`‖fderiv ℝ f‖ ≤ L` on `s`, then for `D` almost everywhere strongly measurable on `f s`,
`‖D ∘ f ∘ Df‖_{Lᵖ(s)} ≤ L c^(-1/p) ‖D‖_{Lᵖ(f s)}`. -/
theorem eLpNorm_comp_fderiv_restrict_le {D : E → E →L[ℝ] F} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℝ f Ω) (hinj : InjOn f s) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s)
    (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|)
    (hL : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ L) (hD : AEStronglyMeasurable D (μ.restrict (f '' s))) :
    eLpNorm (fun x => (D (f x)).comp (fderiv ℝ f x)) p (μ.restrict s) ≤
      ENNReal.ofReal L *
        ((ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal * eLpNorm D p (μ.restrict (f '' s))) := by
  have hmap := map_restrict_le_smul_restrict_image_of_differentiableOn (μ := μ) hΩ hf hinj hsΩ
    hs hc hdet
  have hm : AEMeasurable f (μ.restrict s) := (hf.continuousOn.mono hsΩ).aemeasurable hs
  have hDf : AEStronglyMeasurable (fun x => D (f x)) (μ.restrict s) :=
    (hD.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)).comp_aemeasurable hm
  have hmeas : AEStronglyMeasurable (fun x => (D (f x)).comp (fderiv ℝ f x)) (μ.restrict s) :=
    (ContinuousLinearMap.compL ℝ E E F).aestronglyMeasurable_comp₂ hDf
      (measurable_fderiv ℝ f).aestronglyMeasurable
  calc eLpNorm (fun x => (D (f x)).comp (fderiv ℝ f x)) p (μ.restrict s)
      ≤ ENNReal.ofReal L * eLpNorm (fun x => D (f x)) p (μ.restrict s) := by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas ?_ p
        filter_upwards [ae_restrict_mem hs] with x hx
        calc ‖(D (f x)).comp (fderiv ℝ f x)‖ ≤ ‖D (f x)‖ * ‖fderiv ℝ f x‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ L * ‖D (f x)‖ := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right (hL x hx) (norm_nonneg _)
    _ ≤ _ := by
        gcongr
        exact eLpNorm_comp_le_of_map_le_smul hm hmap p

/-- Precomposition with `f` followed by composition with `fderiv ℝ f` maps `Lᵖ(f s)` into
`Lᵖ(s)` under the hypotheses of `MeasureTheory.eLpNorm_comp_fderiv_restrict_le`. -/
theorem MemLp.comp_fderiv_restrict_of_le_abs_det {D : E → E →L[ℝ] F}
    (hD : MemLp D p (μ.restrict (f '' s))) (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω)
    (hinj : InjOn f s) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) (hL : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ L) :
    MemLp (fun x => (D (f x)).comp (fderiv ℝ f x)) p (μ.restrict s) :=
  (eLpNorm_comp_fderiv_restrict_le hΩ hf hinj hsΩ hs hc hdet hL
    hD.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')) hD))

omit [NormedSpace ℝ F] in
/-- **Precomposition on a compact set.** If `f` is `C¹` on an open set `Ω`, and injective with
invertible derivative on a compact set `K ⊆ Ω`, then precomposition with `f` maps `Lᵖ(f K)` into
`Lᵖ(K)`. -/
theorem MemLp.comp_restrict_of_isCompact {u : E → F} (hu : MemLp u p (μ.restrict (f '' K)))
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hinj : InjOn f K)
    (hdet : ∀ x ∈ K, (fderiv ℝ f x).det ≠ 0) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    MemLp (fun x => u (f x)) p (μ.restrict K) := by
  obtain ⟨c, L, hc, hcK, -⟩ := exists_det_bounds_of_isCompact hΩ hf hK hKΩ hdet
  exact hu.comp_restrict_of_le_abs_det hΩ (hf.differentiableOn one_ne_zero) hinj hKΩ
    hK.measurableSet hc hcK

/-- **The transformed derivative on a compact set.** Under the hypotheses of
`MeasureTheory.MemLp.comp_restrict_of_isCompact`, `x ↦ D (f x) ∘ fderiv ℝ f x` is in `Lᵖ(K)`
whenever `D` is in `Lᵖ(f K)`. -/
theorem MemLp.comp_fderiv_restrict_of_isCompact {D : E → E →L[ℝ] F}
    (hD : MemLp D p (μ.restrict (f '' K))) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hinj : InjOn f K) (hdet : ∀ x ∈ K, (fderiv ℝ f x).det ≠ 0) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    MemLp (fun x => (D (f x)).comp (fderiv ℝ f x)) p (μ.restrict K) := by
  obtain ⟨c, L, hc, hcK, hLK⟩ := exists_det_bounds_of_isCompact hΩ hf hK hKΩ hdet
  exact hD.comp_fderiv_restrict_of_le_abs_det hΩ (hf.differentiableOn one_ne_zero) hinj hKΩ
    hK.measurableSet hc hcK hLK

omit [NormedSpace ℝ F] in
/-- Local integrability is preserved by precomposition with a map that is `C¹`, injective and
with invertible derivative on an open set `U`, mapping `U` into `V`. -/
theorem LocallyIntegrableOn.comp_contDiffOn_diffeo {u : E → F} (hu : LocallyIntegrableOn u V μ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hinj : InjOn f U)
    (hdet : ∀ x ∈ U, (fderiv ℝ f x).det ≠ 0) (hmaps : MapsTo f U V) :
    LocallyIntegrableOn (fun x => u (f x)) U μ := by
  refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK => ?_
  refine memLp_one_iff_integrable.1 (MemLp.comp_restrict_of_isCompact ?_ hU hf (hinj.mono hKU)
    (fun x hx => hdet x (hKU hx)) hK hKU)
  exact memLp_one_iff_integrable.2 (hu.integrableOn_compact_subset
    ((image_mono hKU).trans hmaps.image_subset)
    (hK.image_of_continuousOn (hf.continuousOn.mono hKU)))

/-- The transformed derivative `x ↦ D (f x) ∘ fderiv ℝ f x` is locally integrable on `U` whenever
`D` is locally integrable on `V`, under the hypotheses of
`MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`. -/
theorem LocallyIntegrableOn.comp_fderiv_contDiffOn_diffeo {D : E → E →L[ℝ] F}
    (hD : LocallyIntegrableOn D V μ) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hinj : InjOn f U)
    (hdet : ∀ x ∈ U, (fderiv ℝ f x).det ≠ 0) (hmaps : MapsTo f U V) :
    LocallyIntegrableOn (fun x => (D (f x)).comp (fderiv ℝ f x)) U μ := by
  refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK => ?_
  refine memLp_one_iff_integrable.1 (MemLp.comp_fderiv_restrict_of_isCompact ?_ hU hf
    (hinj.mono hKU) (fun x hx => hdet x (hKU hx)) hK hKU)
  exact memLp_one_iff_integrable.2 (hD.integrableOn_compact_subset
    ((image_mono hKU).trans hmaps.image_subset)
    (hK.image_of_continuousOn (hf.continuousOn.mono hKU)))

end Precomposition

end MeasureTheory

namespace ContinuousAffineMap

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E}

/-- **Integrals over a set are invariant under an affine self-map of it.** If a continuous affine
map `T` carries a measurable set `s` of finite measure onto itself, then
`∫ x in s, g (T x) ∂μ = ∫ x in s, g x ∂μ` for every `g`. -/
theorem setIntegral_comp_of_image_eq (T : E →ᴬ[ℝ] E) (hs : MeasurableSet s) (hμ : μ s ≠ ∞)
    (hT : T '' s = s) (g : E → F) :
    ∫ x in s, g (T x) ∂μ = ∫ x in s, g x ∂μ := by
  -- On a null set both integrals vanish.
  by_cases h₀ : μ s = 0
  · simp [Measure.restrict_eq_zero.2 h₀]
  have hd : ∀ x ∈ s, HasFDerivWithinAt T T.contLinear s x := fun _ _ ↦ T.hasFDerivWithinAt
  -- A singular linear part would collapse `s` to a null set.
  have hdet : (T.contLinear : E →L[ℝ] E).det ≠ 0 := fun h ↦
    h₀ (hT ▸ addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hd fun _ _ ↦ h)
  have hinj : InjOn T s := by
    intro x _ y _ hxy
    have hL := Module.End.isUnit_iff _ |>.1 <|
      (LinearMap.isUnit_iff_isUnit_det (T.contLinear : E →ₗ[ℝ] E)).2 hdet.isUnit
    rw [← sub_eq_zero, ← vsub_eq_sub, ← T.contLinear_apply_vsub, vsub_eq_sub] at hxy
    exact sub_eq_zero.1 (hL.1 (by simpa using hxy))
  -- Comparing the measures of `s` and of its image `T '' s = s` forces `|det| = 1`.
  have habs : |(T.contLinear : E →L[ℝ] E).det| = 1 := by
    have h := lintegral_abs_det_fderiv_eq_addHaar_image μ hs hd hinj
    rw [hT, setLIntegral_const] at h
    exact ENNReal.ofReal_eq_one.1 ((ENNReal.mul_eq_right h₀ hμ).1 h)
  calc ∫ x in s, g (T x) ∂μ = ∫ x in s, |(T.contLinear : E →L[ℝ] E).det| • g (T x) ∂μ := by
        simp [habs]
    _ = ∫ x in T '' s, g x ∂μ :=
        (integral_image_eq_integral_abs_det_fderiv_smul μ hs hd hinj g).symm
    _ = ∫ x in s, g x ∂μ := by rw [hT]

end ContinuousAffineMap
