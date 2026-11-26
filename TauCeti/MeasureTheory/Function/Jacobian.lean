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
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# Change of variables: pushforward bounds, `Lᵖ` bounds and affine invariance of set integrals

Let `f` be injective and differentiable on a null-measurable subset `s` of a finite-dimensional real
normed space with an additive Haar measure `μ`. Mathlib's change of variables formula
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` says that `f` pushes the measure
`|det f'| μ` on `s` forward to `μ` on `f '' s`. Mathlib states the corresponding lower-integral
formula on measurable sets only; it holds on null-measurable sets as well
(`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul₀`). If the Jacobian is bounded
below, `c ≤ |det f'|` on `s` with `c > 0`, then `f` pushes `μ` on `s` forward to at most `c⁻¹ μ`
on `f '' s` (`MeasureTheory.map_restrict_le_smul_restrict_image`).

For `f` differentiable on an open set `s` and mapping it into `t`, the same bound holds with the
Fréchet derivative `fderiv ℝ f` as Jacobian and `μ` on `t` in place of `μ` on `f '' s`
(`MeasureTheory.map_restrict_le_smul_restrict_of_differentiableOn`). If moreover `f` is injective
and its derivative is invertible on `s`, then almost-everywhere properties on `t` pull back along
`f` to almost-everywhere properties on `s` (`MeasureTheory.ae_restrict_comp_of_differentiableOn`).
They also pull back whenever `f` has a differentiable left inverse on `t`
(`MeasureTheory.ae_restrict_comp_of_leftInvOn`).
Conversely, if `f` is `μ`-almost everywhere measurable and admits a differentiable left inverse `g`
with `|det Dg| ≤ J` everywhere, then `μ.map f ≤ J • μ`
(`MeasureTheory.map_addHaar_le_smul_of_leftInverse`). More locally, without differentiability of
`f`, if `f` is almost everywhere measurable on `s` and maps `s` into an open set `t`, a
differentiable left inverse `g` on `t` still controls the pushforward of `μ` on `s` by an upper
bound on `|det Dg|` or on `‖Dg‖ ^ n` along `f '' s`
(`MeasureTheory.map_restrict_le_smul_restrict_of_leftInvOn`,
`MeasureTheory.map_restrict_le_smul_restrict_of_leftInvOn_of_norm_fderiv_le`).

Such a pushforward bound `μ.map f ≤ C • ν` gives the `eLpNorm` estimate for precomposition with
`f` (`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). For a change of variables no upper bound on
the Jacobian is needed, but a Jacobian that may vanish gives no such bound. On a measurable set `s`
inside an open set where `f` is differentiable, with `f` injective on `s` and given constants
`c ≤ |det Df|` and `‖Df‖ ≤ L` on `s`, this bounds the `Lᵖ(s)` norms of `u ∘ f` and of the
transformed derivative `x ↦ D (f x) ∘ Df x` by those of `u` and `D` on `f '' s`
(`MeasureTheory.eLpNorm_comp_restrict_le`, `MeasureTheory.eLpNorm_comp_fderiv_restrict_le`).
Such constants exist on every compact set on which a `C¹` map has invertible derivative
(`MeasureTheory.exists_det_bounds_of_isCompact`). Injectivity is not needed on a compact set: by
the inverse function theorem the map is injective near each of its points, and `Lᵖ` membership on
finitely many such pieces gives it on the whole set
(`MeasureTheory.memLp_restrict_of_forall_injOn`). So precomposition with a map that is `C¹` with
invertible derivative on a compact set maps `Lᵖ` of its image into `Lᵖ` of the set
(`MeasureTheory.MemLp.comp_restrict_of_isCompact`), and on an open set it preserves local
integrability (`MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`). The map need not be
injective, as `z ↦ z²` on `ℂ ∖ {0}` is not. For a bijection `φ`, a bound
`‖Dφ⁻¹‖ ≤ A` on the derivative of its inverse gives the Jacobian lower bound `A^{-n} ≤ |det Dφ|`
everywhere, in dimension `n` (`Equiv.inv_pow_le_abs_det_fderiv`).

A continuous affine map `T` carrying a set `s` of finite measure onto itself preserves
integrals over `s`. When `s` is not null, the linear part of `T` has determinant `±1`, because the
image of `s` has `|det|` times the measure of `s`, so the change of variables formula has no
Jacobian factor
(`ContinuousAffineMap.setIntegral_comp_of_image_eq`). This is how a symmetry of a polytope, such as
a permutation of the vertices of a simplex, acts on integrals over it.

## Main declarations

* `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul₀`: the change of variables
  formula for lower integrals on a null-measurable set.
* `MeasureTheory.map_restrict_le_smul_restrict_image`: the pushforward of `μ` on `s` is at most
  `c⁻¹ μ` on `f '' s`.
* `MeasureTheory.map_restrict_le_smul_restrict_of_differentiableOn`: the same for `f`
  differentiable on an open set `s` and mapping it into `t`, with `μ` on `t` as the target.
* `MeasureTheory.map_addHaar_le_smul_of_leftInverse`: the pushforward `μ.map f` is at most `J • μ`
  when `f` admits a differentiable left inverse `g` with `|det (fderiv ℝ g)| ≤ J`.
* `MeasureTheory.map_restrict_le_smul_restrict_of_leftInvOn`,
  `MeasureTheory.map_restrict_le_smul_restrict_of_leftInvOn_of_norm_fderiv_le`: pushforward bounds
  on `s` for an almost-everywhere measurable `f` from a differentiable left inverse `g` on an open
  set `t`, without differentiability of `f`.
* `MeasureTheory.ae_restrict_comp_of_differentiableOn`: almost-everywhere properties pull back
  along a map that is injective with invertible derivative on an open set.
* `MeasureTheory.exists_det_bounds_of_isCompact`: Jacobian and derivative bounds on a compact
  set.
* `MeasureTheory.memLp_restrict_of_forall_injOn`: `Lᵖ` membership on a compact set from its
  measurable pieces on which a `C¹` map with invertible derivative is injective.
* `MeasureTheory.eLpNorm_comp_restrict_le`, `MeasureTheory.eLpNorm_comp_fderiv_restrict_le`: the
  `Lᵖ` bounds for precomposition on a measurable set, given such constants.
* `MeasureTheory.MemLp.comp_restrict_of_isCompact`,
  `MeasureTheory.MemLp.comp_fderiv_restrict_of_isCompact`: precomposition on a compact set, with
  no injectivity assumption.
* `MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`,
  `MeasureTheory.LocallyIntegrableOn.comp_fderiv_contDiffOn_diffeo`: local integrability is
  preserved, again with no injectivity assumption.
* `ContinuousAffineMap.setIntegral_comp_of_image_eq`: integrals over `s` are invariant under a
  continuous affine map carrying `s` onto itself, when `s` has finite measure.
* `Equiv.inv_pow_le_abs_det_fderiv`: if `‖Dφ⁻¹(φ x)‖ ≤ L`, then `|det Dφ(x)| ≥ L^{-n}` in
  dimension `n`.
* `Equiv.inv_max_one_pow_le_abs_det_fderiv`: if `‖Dφ⁻¹‖ ≤ L` everywhere, then
  `|det Dφ| ≥ (max 1 L)^{-n}` everywhere.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {Ω s t : Set E} {f : E → E} {f' : E → E →L[ℝ] E} {c : ℝ}

/-- **Change of variables on a null-measurable set.** If `f` is injective and differentiable on
a null-measurable set `s`, then the lower integral of `g` over `f '' s` is the lower integral of
`|det f'| * g ∘ f` over `s`. -/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul₀ (hs : NullMeasurableSet s μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  -- Pass to a measurable subset `u` with the same measure; the images of `u` and `s` differ by
  -- the image of a null set, which is null since `f` is differentiable on it.
  obtain ⟨u, hus, hu, hsu⟩ := hs.exists_measurable_subset_ae_eq
  have himage : f '' u =ᵐ[μ] f '' s :=
    (Filter.EventuallySubset.of_subset (image_mono hus)).antisymm <| ae_subset.2 <|
      measure_mono_null (subset_image_sdiff _ s u) <|
        addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
          (fun x hx ↦ (hf' x hx.1).differentiableWithinAt.mono sdiff_subset)
          (ae_subset.1 hsu.symm.subset)
  rw [← setLIntegral_congr himage, ← setLIntegral_congr hsu,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hu (fun x hx ↦ (hf' x (hus hx)).mono hus)
      (hf.mono hus) g]

/-- **Pushforward bound from a Jacobian lower bound.** If `f` is injective and differentiable on
a null-measurable set `s`, and `c ≤ |det f'|` on `s` with `c > 0`, then `f` pushes `μ` restricted to
`s` forward to at most `c⁻¹` times `μ` restricted to `f '' s`. -/
theorem map_restrict_le_smul_restrict_image (hs : NullMeasurableSet s μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(f' x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ.restrict (f '' s) := by
  have hfm : AEMeasurable f (μ.restrict s) :=
    ContinuousOn.aemeasurable₀ (fun x hx ↦ (hf' x hx).continuousWithinAt) hs
  have hWm := hfm.mono_ac (withDensity_absolutelyContinuous _ fun x ↦ ENNReal.ofReal |(f' x).det|)
  -- Mathlib's change of variables: `f` pushes `|det f'| μ` on `s` forward to `μ` on `f '' s`.
  rw [← map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf, ← Measure.map_smul _ hWm]
  -- It remains to compare `μ` on `s` with `c⁻¹ |det f'| μ` on `s`.
  refine Measure.map_mono_of_aemeasurable (Measure.le_iff.2 fun t ht ↦ ?_) (hWm.smul_measure _)
  rw [_root_.smul_apply, smul_eq_mul, withDensity_apply _ ht,
    ← ENNReal.mul_le_iff_le_inv (by simpa using hc) ENNReal.ofReal_ne_top, ← setLIntegral_const]
  exact lintegral_mono_ae ((ae_restrict_of_ae (ae_restrict_mem₀ hs)).mono fun x hx =>
    ENNReal.ofReal_le_ofReal (hdet x hx))

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

/-- **Pushforward bound for a map differentiable on an open set.** If `f` is injective and
differentiable on an open set `s`, maps `s` into `t`, and `c ≤ |det (fderiv ℝ f x)|` on `s` with
`c > 0`, then `f` pushes `μ` restricted to `s` forward to at most `c⁻¹` times `μ` restricted to
`t`. -/
theorem map_restrict_le_smul_restrict_of_differentiableOn (hs : IsOpen s)
    (hf : DifferentiableOn ℝ f s) (hinj : InjOn f s) (hmaps : MapsTo f s t) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ.restrict t :=
  (map_restrict_le_smul_restrict_image_of_differentiableOn μ hs hf hinj subset_rfl
    hs.measurableSet hc hdet).trans (by gcongr; exact hmaps.image_subset)

/-- **Pushforward bound from a Jacobian upper bound on a left inverse.** If `f` is `μ`-almost
everywhere measurable and admits a differentiable left inverse `g` with `|det (fderiv ℝ g y)| ≤ J`
everywhere, then `f` pushes `μ` forward to at most `J • μ`. -/
theorem map_addHaar_le_smul_of_leftInverse {g : E → E} {J : ℝ} (hf : AEMeasurable f μ)
    (hg : Differentiable ℝ g) (hgf : Function.LeftInverse g f)
    (hJ : ∀ y, |(fderiv ℝ g y).det| ≤ J) :
    μ.map f ≤ ENNReal.ofReal J • μ := by
  refine Measure.le_iff.2 fun t ht ↦ ?_
  rw [Measure.map_apply_of_aemeasurable hf ht]
  calc μ (f ⁻¹' t)
      ≤ μ (g '' t) := measure_mono fun x hx ↦ ⟨f x, hx, hgf x⟩
    _ ≤ ∫⁻ y in t, ENNReal.ofReal |(fderiv ℝ g y).det| ∂μ :=
        addHaar_image_le_lintegral_abs_det_fderiv μ ht
          fun y _ ↦ (hg y).hasFDerivAt.hasFDerivWithinAt
    _ ≤ ∫⁻ _ in t, ENNReal.ofReal J ∂μ :=
        setLIntegral_mono' ht fun y _ ↦ ENNReal.ofReal_le_ofReal (hJ y)
    _ = (ENNReal.ofReal J • μ) t := by simp

/-- **Pushforward bound from a differentiable left inverse.** If `f` is almost everywhere
measurable on `s`, `g` is differentiable on an open set `t`, `f` maps `s` into `t` with
`g (f x) = x` on `s`, and `|det (fderiv ℝ g (f x))| ≤ M` on `s`, then `f` pushes `μ` restricted
to `s` forward to at most `M` times `μ` restricted to `t`. Neither measurability of `s` nor
differentiability of `f` is needed. -/
theorem map_restrict_le_smul_restrict_of_leftInvOn {g : E → E} {M : ℝ}
    (hf : AEMeasurable f (μ.restrict s)) (ht : IsOpen t) (hg : DifferentiableOn ℝ g t)
    (hmaps : MapsTo f s t) (hgf : LeftInvOn g f s)
    (hdet : ∀ x ∈ s, |(fderiv ℝ g (f x)).det| ≤ M) :
    (μ.restrict s).map f ≤ ENNReal.ofReal M • μ.restrict t := by
  set W : Set E := t ∩ {y | |(fderiv ℝ g y).det| ≤ M}
  have hW : MeasurableSet W := ht.measurableSet.inter
    (measurableSet_le (continuous_abs.measurable.comp
      (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ g)))
      measurable_const)
  refine Measure.le_iff.2 fun B hB ↦ ?_
  have hsub : f ⁻¹' B ∩ s ⊆ g '' (B ∩ W) := fun x ⟨hxB, hxs⟩ ↦
    ⟨f x, ⟨hxB, hmaps hxs, hdet x hxs⟩, hgf hxs⟩
  have hg' : ∀ y ∈ B ∩ W, HasFDerivWithinAt g (fderiv ℝ g y) (B ∩ W) y := fun y hy ↦
    ((hg y hy.2.1).differentiableAt (ht.mem_nhds hy.2.1)).hasFDerivAt.hasFDerivWithinAt
  calc ((μ.restrict s).map f) B
      = (μ.restrict s) (f ⁻¹' B) := Measure.map_apply_of_aemeasurable hf hB
    _ = μ (f ⁻¹' B ∩ s) := Measure.restrict_apply₀ (hf.nullMeasurable hB)
    _ ≤ μ (g '' (B ∩ W)) := measure_mono hsub
    _ ≤ ∫⁻ y in B ∩ W, ENNReal.ofReal |(fderiv ℝ g y).det| ∂μ :=
        addHaar_image_le_lintegral_abs_det_fderiv μ (hB.inter hW) hg'
    _ ≤ ∫⁻ _ in B ∩ W, ENNReal.ofReal M ∂μ :=
        setLIntegral_mono measurable_const fun _ hy ↦ ENNReal.ofReal_le_ofReal hy.2.2
    _ = ENNReal.ofReal M * μ (B ∩ W) := setLIntegral_const (B ∩ W) _
    _ ≤ ENNReal.ofReal M * μ (B ∩ t) := by
        gcongr; exact inter_subset_left
    _ = (ENNReal.ofReal M • μ.restrict t) B := by
        rw [_root_.smul_apply, smul_eq_mul, Measure.restrict_apply hB]

/-- **Pushforward bound from an operator-norm bound on a left inverse.** If `f` is almost
everywhere measurable on `s`, `g` is differentiable on an open set `t`, `f` maps `s` into `t`
with `g (f x) = x` on `s`, and `‖fderiv ℝ g (f x)‖ ≤ L` on `s`, then `f` pushes `μ` restricted to
`s` forward to at most `L ^ finrank ℝ E` times `μ` restricted to `t`. -/
theorem map_restrict_le_smul_restrict_of_leftInvOn_of_norm_fderiv_le {g : E → E} {L : ℝ}
    (hf : AEMeasurable f (μ.restrict s)) (ht : IsOpen t) (hg : DifferentiableOn ℝ g t)
    (hmaps : MapsTo f s t) (hgf : LeftInvOn g f s) (hL : ∀ x ∈ s, ‖fderiv ℝ g (f x)‖ ≤ L) :
    (μ.restrict s).map f ≤ ENNReal.ofReal (L ^ Module.finrank ℝ E) • μ.restrict t :=
  map_restrict_le_smul_restrict_of_leftInvOn μ hf ht hg hmaps hgf fun x hx ↦
    (fderiv ℝ g (f x)).abs_det_le_opNorm_pow.trans
      (pow_le_pow_left₀ (norm_nonneg _) (hL x hx) _)

/-- **Null sets pull back along a map with invertible derivative.** If `f` is injective and
differentiable on an open set `s`, with invertible derivative there, and maps `s` into `t`, then a
property holding `μ`-almost everywhere on `t` holds at `f x` for `μ`-almost every `x ∈ s`: the
pushforward of `|det f'| μ` on `s` is `μ` on `f '' s`, and the density is positive. -/
theorem ae_restrict_comp_of_differentiableOn {P : E → Prop} (hs : IsOpen s)
    (hf : DifferentiableOn ℝ f s) (hinj : InjOn f s) (hdet : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0)
    (hmaps : MapsTo f s t) (h : ∀ᵐ y ∂μ.restrict t, P y) : ∀ᵐ x ∂μ.restrict s, P (f x) := by
  have hf' : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x := fun x hx =>
    ((hf x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  have himage : ∀ᵐ y ∂μ.restrict (f '' s), P y :=
    ae_restrict_of_ae_restrict_of_subset hmaps.image_subset h
  rw [← map_withDensity_abs_det_fderiv_eq_addHaar μ hs.measurableSet.nullMeasurableSet hf'
    hinj] at himage
  have hdens := aemeasurable_ofReal_abs_det_fderivWithin μ hs.measurableSet hf'
  have hfm : AEMeasurable f ((μ.restrict s).withDensity
      fun x => ENNReal.ofReal |(fderiv ℝ f x).det|) :=
    (hf.continuousOn.aemeasurable hs.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  refine (withDensity_absolutelyContinuous' hdens ?_).ae_le (ae_of_ae_map hfm himage)
  filter_upwards [self_mem_ae_restrict hs.measurableSet] with x hx
  simpa using hdet x hx

/-- **Null sets pull back along a map with a differentiable left inverse.** If `f` maps a
measurable set `s` into a measurable set `t`, and `g` is differentiable on `t` with `g (f x) = x`
on `s`, then a property holding `μ`-almost everywhere on `t` holds at `f x` for `μ`-almost every
`x ∈ s`: the exceptional points of `s` lie in the image under `g` of a null subset of `t`, and a
differentiable map carries null sets to null sets. -/
theorem ae_restrict_comp_of_leftInvOn {P : E → Prop} {g : E → E} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hg : DifferentiableOn ℝ g t) (hmaps : MapsTo f s t)
    (hinv : ∀ x ∈ s, g (f x) = x) (h : ∀ᵐ y ∂μ.restrict t, P y) :
    ∀ᵐ x ∂μ.restrict s, P (f x) := by
  rw [ae_iff, Measure.restrict_apply' ht] at h
  rw [ae_iff, Measure.restrict_apply' hs]
  refine measure_mono_null ?_
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ (hg.mono inter_subset_right) h)
  rintro x ⟨hP, hx⟩
  exact ⟨f x, ⟨hP, hmaps hx⟩, hinv x hx⟩

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

omit [BorelSpace E] in
/-- **Patching `Lᵖ` membership over pieces of injectivity.** Let `f` be `C¹` on an open set `Ω`
with invertible derivative on a compact set `K ⊆ Ω`. If a function `g` is `Lᵖ` on every measurable
subset of `K` on which `f` is injective, then `g` is `Lᵖ` on `K`. -/
theorem memLp_restrict_of_forall_injOn [OpensMeasurableSpace E] {G : Type*}
    [NormedAddCommGroup G] {g : E → G} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hdet : ∀ x ∈ K, (fderiv ℝ f x).det ≠ 0)
    (hg : ∀ s ⊆ K, MeasurableSet s → InjOn f s → MemLp g p (μ.restrict s)) :
    MemLp g p (μ.restrict K) := by
  refine hK.memLp_restrict_of_forall_nhdsWithin fun x hx => ?_
  obtain ⟨V, hV, hinj⟩ := (hf.contDiffAt (hΩ.mem_nhds (hKΩ hx))).exists_mem_nhds_injOn one_ne_zero
    ⟨_, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ (hdet x hx)⟩
  obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.1 hV
  exact ⟨K ∩ W, inter_mem_nhdsWithin K (hW.mem_nhds hxW), hg _ inter_subset_left
    (hK.isClosed.measurableSet.inter hW.measurableSet) (hinj.mono (inter_subset_right.trans hWV))⟩

variable [μ.IsAddHaarMeasure]

/-- **`Lᵖ` bound for precomposition on a measurable set.** Under the hypotheses of
`MeasureTheory.map_restrict_le_smul_restrict_image_of_differentiableOn`,
`‖u ∘ f‖_{Lᵖ(s)} ≤ c^(-1/p) ‖u‖_{Lᵖ(f s)}`. -/
theorem eLpNorm_comp_restrict_le (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω)
    (hinj : InjOn f s) (hsΩ : s ⊆ Ω) (hs : MeasurableSet s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) (u : E → F) :
    eLpNorm (fun x => u (f x)) p (μ.restrict s) ≤
      (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal * eLpNorm u p (μ.restrict (f '' s)) :=
  eLpNorm_comp_le_of_map_le_smul ((hf.continuousOn.mono hsΩ).aemeasurable hs)
    (map_restrict_le_smul_restrict_image_of_differentiableOn μ hΩ hf hinj hsΩ hs hc hdet) p

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
/-- **Precomposition on a compact set.** If `f` is `C¹` on an open set `Ω`, with invertible
derivative on a compact set `K ⊆ Ω`, then precomposition with `f` maps `Lᵖ(f K)` into `Lᵖ(K)`.
The map `f` need not be injective on `K`. -/
theorem MemLp.comp_restrict_of_isCompact {u : E → F} (hu : MemLp u p (μ.restrict (f '' K)))
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hdet : ∀ x ∈ K, (fderiv ℝ f x).det ≠ 0)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    MemLp (fun x => u (f x)) p (μ.restrict K) := by
  obtain ⟨c, L, hc, hcK, -⟩ := exists_det_bounds_of_isCompact hΩ hf hK hKΩ hdet
  refine memLp_restrict_of_forall_injOn hΩ hf hK hKΩ hdet fun s hsK hs hinj => ?_
  have hus := hu.mono_measure (Measure.restrict_mono (image_mono hsK) le_rfl)
  exact hus.comp_restrict_of_le_abs_det hΩ (hf.differentiableOn one_ne_zero) hinj (hsK.trans hKΩ)
    hs hc fun x hx => hcK x (hsK hx)

/-- **The transformed derivative on a compact set.** Under the hypotheses of
`MeasureTheory.MemLp.comp_restrict_of_isCompact`, `x ↦ D (f x) ∘ fderiv ℝ f x` is in `Lᵖ(K)`
whenever `D` is in `Lᵖ(f K)`. -/
theorem MemLp.comp_fderiv_restrict_of_isCompact {D : E → E →L[ℝ] F}
    (hD : MemLp D p (μ.restrict (f '' K))) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hdet : ∀ x ∈ K, (fderiv ℝ f x).det ≠ 0) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    MemLp (fun x => (D (f x)).comp (fderiv ℝ f x)) p (μ.restrict K) := by
  obtain ⟨c, L, hc, hcK, hLK⟩ := exists_det_bounds_of_isCompact hΩ hf hK hKΩ hdet
  refine memLp_restrict_of_forall_injOn hΩ hf hK hKΩ hdet fun s hsK hs hinj => ?_
  have hDs := hD.mono_measure (Measure.restrict_mono (image_mono hsK) le_rfl)
  exact hDs.comp_fderiv_restrict_of_le_abs_det hΩ (hf.differentiableOn one_ne_zero) hinj
    (hsK.trans hKΩ) hs hc (fun x hx => hcK x (hsK hx)) fun x hx => hLK x (hsK hx)

omit [NormedSpace ℝ F] in
/-- Local integrability is preserved by precomposition with a map that is `C¹` with invertible
derivative on an open set `U`, mapping `U` into `V`. The map need not be injective. -/
theorem LocallyIntegrableOn.comp_contDiffOn_diffeo {u : E → F} (hu : LocallyIntegrableOn u V μ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hdet : ∀ x ∈ U, (fderiv ℝ f x).det ≠ 0)
    (hmaps : MapsTo f U V) :
    LocallyIntegrableOn (fun x => u (f x)) U μ := by
  refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK => ?_
  refine memLp_one_iff_integrable.1 (MemLp.comp_restrict_of_isCompact ?_ hU hf
    (fun x hx => hdet x (hKU hx)) hK hKU)
  exact memLp_one_iff_integrable.2 (hu.integrableOn_compact_subset
    ((image_mono hKU).trans hmaps.image_subset)
    (hK.image_of_continuousOn (hf.continuousOn.mono hKU)))

/-- The transformed derivative `x ↦ D (f x) ∘ fderiv ℝ f x` is locally integrable on `U` whenever
`D` is locally integrable on `V`, under the hypotheses of
`MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`. -/
theorem LocallyIntegrableOn.comp_fderiv_contDiffOn_diffeo {D : E → E →L[ℝ] F}
    (hD : LocallyIntegrableOn D V μ) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hdet : ∀ x ∈ U, (fderiv ℝ f x).det ≠ 0) (hmaps : MapsTo f U V) :
    LocallyIntegrableOn (fun x => (D (f x)).comp (fderiv ℝ f x)) U μ := by
  refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK => ?_
  refine memLp_one_iff_integrable.1 (MemLp.comp_fderiv_restrict_of_isCompact ?_ hU hf
    (fun x hx => hdet x (hKU hx)) hK hKU)
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
map `T` carries a set `s` of finite measure onto itself, then
`∫ x in s, g (T x) ∂μ = ∫ x in s, g x ∂μ` for every `g`. -/
theorem setIntegral_comp_of_image_eq (T : E →ᴬ[ℝ] E) (hμ : μ s ≠ ∞)
    (hT : T '' s = s) (g : E → F) :
    ∫ x in s, g (T x) ∂μ = ∫ x in s, g x ∂μ := by
  -- On a null set both integrals vanish.
  by_cases h₀ : μ s = 0
  · simp [Measure.restrict_eq_zero.2 h₀]
  have hd : ∀ x ∈ s, HasFDerivWithinAt T T.contLinear s x := fun _ _ ↦ T.hasFDerivWithinAt
  -- A singular linear part would collapse `s` to a null set.
  have hdet : T.contLinear.det ≠ 0 := fun h ↦
    h₀ (hT ▸ addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hd fun _ _ ↦ h)
  have hinj : Function.Injective T := T.toAffineMap.linear_injective_iff.1
    ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hdet.isUnit)).1
  have hT0 : (T : E → E) = (fun y ↦ y + T 0) ∘ T.contLinear := T.decomp
  -- Comparing the measures of `s` and of its image `T '' s = s` forces `|det| = 1`.
  have habs : |T.contLinear.det| = 1 := by
    have h : μ (T '' s) = ENNReal.ofReal |T.contLinear.det| * μ s := by
      rw [hT0, Set.image_comp, Set.image_add_right, measure_preimage_add_right]
      exact Measure.addHaar_image_continuousLinearMap μ _ s
    rw [hT] at h
    exact ENNReal.ofReal_eq_one.1 ((ENNReal.mul_eq_right h₀ hμ).1 h.symm)
  -- Hence `T` preserves `μ`, and it is a measurable embedding.
  have hmp := measurePreserving_of_abs_det_eq_one μ T habs
  have hpre : T ⁻¹' s = s := by simpa [hT] using hinj.preimage_image s
  rw [← hmp.setIntegral_preimage_emb (T.continuous.measurableEmbedding hinj) g s, hpre]

end ContinuousAffineMap

/-- **A lower bound for the Jacobian determinant.** If a bijection `φ` of a finite-dimensional real
normed space is differentiable at `x`, its inverse is differentiable at `φ x`, and
`‖Dφ⁻¹(φ x)‖ ≤ L`, then `|det Dφ(x)| ≥ L^{-n}` in dimension `n`. -/
theorem Equiv.inv_pow_le_abs_det_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : E ≃ E) {x : E} (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ φ.symm (φ x)) {L : ℝ} (hL : ‖fderiv ℝ φ.symm (φ x)‖ ≤ L) :
    (L ^ Module.finrank ℝ E)⁻¹ ≤ |(fderiv ℝ φ x).det| := by
  have h := φ.det_fderiv_symm_mul_det_fderiv (y := φ x) (by rwa [φ.symm_apply_apply]) hψ
  rw [φ.symm_apply_apply] at h
  have hle : |(fderiv ℝ φ.symm (φ x)).det| ≤ L ^ Module.finrank ℝ E :=
    (ContinuousLinearMap.abs_det_le_opNorm_pow _).trans (pow_le_pow_left₀ (norm_nonneg _) hL _)
  have hpos : 0 < |(fderiv ℝ φ.symm (φ x)).det| := abs_pos.2 (left_ne_zero_of_mul_eq_one h)
  rw [eq_inv_of_mul_eq_one_left (by rw [← abs_mul, mul_comm, h, abs_one] :
    |(fderiv ℝ φ x).det| * |(fderiv ℝ φ.symm (φ x)).det| = 1)]
  exact inv_anti₀ hpos hle

/-- **A uniform lower bound for the Jacobian determinant.** If a bijection `φ` of a
finite-dimensional real normed space and its inverse are differentiable and `‖Dφ⁻¹‖ ≤ L`
everywhere, then `|det Dφ| ≥ (max 1 L)^{-n}` everywhere, in dimension `n`. The bound is positive
and depends only on `L` and `n`. -/
theorem Equiv.inv_max_one_pow_le_abs_det_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : E ≃ E) (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ φ.symm) {L : ℝ} (hL : ∀ y, ‖fderiv ℝ φ.symm y‖ ≤ L) (x : E) :
    (max 1 L ^ Module.finrank ℝ E)⁻¹ ≤ |(fderiv ℝ φ x).det| :=
  φ.inv_pow_le_abs_det_fderiv (hφ x) (hψ _) ((hL _).trans (le_max_right 1 L))
