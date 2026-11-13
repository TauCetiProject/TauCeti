/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.InnerProductSpace.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import TauCeti.Data.Set.Function
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Reflection in an affine hyperplane

For a vector `ν` and a real number `c`, `TauCeti.hyperplaneReflection ν c` is the affine isometry

`x ↦ x - (2 (⟪x, ν⟫ - c) / ‖ν‖²) ν`

of a real inner product space, the reflection in the hyperplane `{x | ⟪x, ν⟫ = c}` when `ν ≠ 0`
(for `ν = 0` it is the identity). Its linear part is the reflection `(ℝ ∙ ν)ᗮ.reflection` in the
parallel hyperplane through the origin, so its derivative at every point is this linear
reflection. It is an involution, fixes the hyperplane pointwise and exchanges the two open
half-spaces `{x | c < ⟪x, ν⟫}` and `{x | ⟪x, ν⟫ < c}`, since `⟪ρ x, ν⟫ = 2c - ⟪x, ν⟫`.

This is the reflection used to extend functions defined on one side of a flat boundary to the
other side, by odd or even reflection. It is Mathlib's `EuclideanGeometry.reflection` in the
affine hyperplane `{x | ⟪x, ν⟫ = c}`, written out for the parametrisation of half-spaces by a
normal vector and an offset.

## Main declarations

* `TauCeti.hyperplaneReflection`: the reflection in the hyperplane `{x | ⟪x, ν⟫ = c}`.
* `TauCeti.hyperplaneReflection_apply`: the explicit formula.
* `TauCeti.hyperplaneReflection_hyperplaneReflection`: it is an involution.
* `TauCeti.inner_hyperplaneReflection`: it reverses the signed height `⟪x, ν⟫ - c`.
* `TauCeti.hyperplaneReflection_eq_self_iff`: its fixed points are the points of the hyperplane.
* `TauCeti.hyperplaneReflection_eq_self_of_mem_closure`: it fixes the points of the closure of the
  open half-space `{x | c < ⟪x, ν⟫}` outside it.
* `TauCeti.fderiv_hyperplaneReflection` and `TauCeti.abs_det_fderiv_hyperplaneReflection`: its
  derivative is the linear reflection, of determinant `±1`.
* `TauCeti.measurePreserving_hyperplaneReflection`: it preserves every additive Haar measure, and
  its restriction to every measurable set it maps into itself
  (`TauCeti.measurePreserving_restrict_hyperplaneReflection`).
* `TauCeti.aestronglyMeasurable_piecewise_comp_hyperplaneReflection`: a field equal to `f` above
  the hyperplane and to `G ∘ f ∘ ρ` below it is measurable when `f` is measurable above it.
* `TauCeti.memLp_indicator_sub_indicator_comp_hyperplaneReflection` and
  `TauCeti.eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le`: the odd reflection
  `x ↦ 1_H f x - 1_H f (ρ x)` of a function `f` given on one side `H` of the hyperplane lies in
  `Lᵖ` with at most twice the norm of `f`.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The **reflection in the affine hyperplane** `{x | ⟪x, ν⟫ = c}`: the affine isometry
`x ↦ x - (2 (⟪x, ν⟫ - c) / ‖ν‖²) ν`, whose linear part is the reflection `(ℝ ∙ ν)ᗮ.reflection` in
the parallel hyperplane through the origin. For `ν = 0` it is the identity. -/
def hyperplaneReflection (ν : F) (c : ℝ) : F ≃ᵃⁱ[ℝ] F :=
  (ℝ ∙ ν)ᗮ.reflection.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ F ((2 * (c / ‖ν‖ ^ 2)) • ν))

/-- The hyperplane reflection is the linear reflection `(ℝ ∙ ν)ᗮ.reflection` followed by the
translation by `(2 c / ‖ν‖²) ν`. -/
theorem hyperplaneReflection_eq_reflection_add (ν : F) (c : ℝ) (x : F) :
    hyperplaneReflection ν c x = (ℝ ∙ ν)ᗮ.reflection x + (2 * (c / ‖ν‖ ^ 2)) • ν := by
  simp [hyperplaneReflection, add_comm]

theorem hyperplaneReflection_apply (ν : F) (c : ℝ) (x : F) :
    hyperplaneReflection ν c x = x - (2 * ((⟪x, ν⟫_ℝ - c) / ‖ν‖ ^ 2)) • ν := by
  simp only [hyperplaneReflection, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv, AffineIsometryEquiv.coe_constVAdd, vadd_eq_add,
    reflection_orthogonal_singleton_apply_div_norm_sq, real_inner_comm ν x]
  rw [sub_div, mul_sub, sub_smul]
  abel

/-- The hyperplane reflection reverses the signed height `⟪x, ν⟫ - c` above the hyperplane. -/
theorem inner_hyperplaneReflection {ν : F} (hν : ν ≠ 0) (c : ℝ) (x : F) :
    ⟪hyperplaneReflection ν c x, ν⟫_ℝ = 2 * c - ⟪x, ν⟫_ℝ := by
  rw [hyperplaneReflection_apply, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
    RCLike.conj_to_real]
  field_simp
  ring

/-- The hyperplane reflection is an involution. -/
@[simp]
theorem hyperplaneReflection_hyperplaneReflection (ν : F) (c : ℝ) (x : F) :
    hyperplaneReflection ν c (hyperplaneReflection ν c x) = x := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp [hyperplaneReflection_apply]
  rw [hyperplaneReflection_apply (x := hyperplaneReflection ν c x), inner_hyperplaneReflection hν,
    hyperplaneReflection_apply, sub_sub, ← add_smul, sub_eq_self, smul_eq_zero]
  left
  ring

/-- The hyperplane reflection is an involution. -/
theorem hyperplaneReflection_involutive (ν : F) (c : ℝ) :
    Function.Involutive (hyperplaneReflection ν c) :=
  hyperplaneReflection_hyperplaneReflection ν c

/-- The inverse of the hyperplane reflection is itself. -/
@[simp]
theorem hyperplaneReflection_symm (ν : F) (c : ℝ) :
    (hyperplaneReflection ν c).symm = hyperplaneReflection ν c := by
  ext x
  rw [AffineIsometryEquiv.symm_apply_eq, hyperplaneReflection_hyperplaneReflection]

/-- The hyperplane reflection fixes every point of the hyperplane `{x | ⟪x, ν⟫ = c}`. -/
theorem hyperplaneReflection_eq_self_of_inner_eq {ν : F} {c : ℝ} {x : F} (hx : ⟪x, ν⟫_ℝ = c) :
    hyperplaneReflection ν c x = x := by
  rw [hyperplaneReflection_apply, hx, sub_self, zero_div, mul_zero, zero_smul, sub_zero]

/-- For `ν ≠ 0` the fixed points of the hyperplane reflection are the points of the hyperplane
`{x | ⟪x, ν⟫ = c}`. -/
theorem hyperplaneReflection_eq_self_iff {ν : F} (hν : ν ≠ 0) (c : ℝ) {x : F} :
    hyperplaneReflection ν c x = x ↔ ⟪x, ν⟫_ℝ = c := by
  have hν2 : ‖ν‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hν)
  rw [hyperplaneReflection_apply, sub_eq_self, smul_eq_zero, or_iff_left hν, mul_eq_zero,
    or_iff_right two_ne_zero, div_eq_zero_iff, or_iff_left hν2, sub_eq_zero]

/-- Points of the closure of an open half-space `H = {x | c < ⟪x, ν⟫}` outside `H` lie on the
hyperplane, where the reflection is the identity. -/
theorem hyperplaneReflection_eq_self_of_mem_closure {ν : F} {c : ℝ} {H : Set F}
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) {x : F} (hxc : x ∈ closure H) (hxH : x ∉ H) :
    hyperplaneReflection ν c x = x := by
  have hset : H = {x | c < ⟪x, ν⟫_ℝ} := Set.ext hH
  have hle : c ≤ ⟪x, ν⟫_ℝ := by
    rw [hset] at hxc
    exact closure_lt_subset_le continuous_const (continuous_id.inner continuous_const) hxc
  exact hyperplaneReflection_eq_self_of_inner_eq
    (le_antisymm (not_lt.1 fun h => hxH ((hH x).2 h)) hle)

/-- The hyperplane reflection maps the open half-space `{x | c < ⟪x, ν⟫}` onto the opposite
open half-space `{x | ⟪x, ν⟫ < c}`, and conversely. -/
theorem inner_hyperplaneReflection_lt_iff {ν : F} (hν : ν ≠ 0) (c : ℝ) {x : F} :
    ⟪hyperplaneReflection ν c x, ν⟫_ℝ < c ↔ c < ⟪x, ν⟫_ℝ := by
  rw [inner_hyperplaneReflection hν]
  constructor <;> intro h <;> linarith

/-- The derivative of the hyperplane reflection at every point is its linear part
`(ℝ ∙ ν)ᗮ.reflection`. -/
theorem hasFDerivAt_hyperplaneReflection (ν : F) (c : ℝ) (x : F) :
    HasFDerivAt (hyperplaneReflection ν c) ((ℝ ∙ ν)ᗮ.reflection : F →L[ℝ] F) x := by
  rw [funext (hyperplaneReflection_eq_reflection_add ν c)]
  exact ((ℝ ∙ ν)ᗮ.reflection : F →L[ℝ] F).hasFDerivAt.add_const _

theorem differentiable_hyperplaneReflection (ν : F) (c : ℝ) :
    Differentiable ℝ (hyperplaneReflection ν c) :=
  fun x => (hasFDerivAt_hyperplaneReflection ν c x).differentiableAt

@[simp]
theorem fderiv_hyperplaneReflection (ν : F) (c : ℝ) (x : F) :
    fderiv ℝ (hyperplaneReflection ν c) x = ((ℝ ∙ ν)ᗮ.reflection : F →L[ℝ] F) :=
  (hasFDerivAt_hyperplaneReflection ν c x).fderiv

/-- The derivative of the hyperplane reflection has determinant of absolute value one. -/
theorem abs_det_fderiv_hyperplaneReflection [FiniteDimensional ℝ F] (ν : F) (c : ℝ) (x : F) :
    |(fderiv ℝ (hyperplaneReflection ν c) x).det| = 1 := by
  rw [fderiv_hyperplaneReflection, ContinuousLinearMap.det]
  exact (congrArg abs ((ℝ ∙ ν)ᗮ.det_reflection (𝕜 := ℝ))).trans (by simp)

/-- The hyperplane reflection preserves every additive Haar measure: it is a linear reflection,
of determinant `±1`, followed by a translation. -/
theorem measurePreserving_hyperplaneReflection [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] (ν : F) (c : ℝ) :
    MeasurePreserving (hyperplaneReflection ν c) μ μ := by
  have hdet := (ℝ ∙ ν)ᗮ.det_reflection (𝕜 := ℝ)
  have hS : MeasurePreserving (ℝ ∙ ν)ᗮ.reflection μ μ := by
    refine ⟨(ℝ ∙ ν)ᗮ.reflection.continuous.measurable, ?_⟩
    simpa [hdet] using Measure.map_linearMap_addHaar_eq_smul_addHaar μ
      (f := (ℝ ∙ ν)ᗮ.reflection.toLinearMap) (by simp [hdet])
  rw [funext (hyperplaneReflection_eq_reflection_add ν c)]
  exact (measurePreserving_add_right μ _).comp hS

/-- The hyperplane reflection preserves the restriction of an additive Haar measure to a
measurable set that it maps into itself. -/
theorem measurePreserving_restrict_hyperplaneReflection [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure] {ν : F} {c : ℝ}
    {V : Set F} (hV : Set.MapsTo (hyperplaneReflection ν c) V V) (hVm : MeasurableSet V) :
    MeasurePreserving (hyperplaneReflection ν c) (μ.restrict V) (μ.restrict V) := by
  have hpre : hyperplaneReflection ν c ⁻¹' V = V :=
    (congrFun (hyperplaneReflection_involutive ν c).image_eq_preimage_symm V).symm.trans
      (hV.image_eq_of_involutive (hyperplaneReflection_involutive ν c))
  simpa only [hpre] using
    (measurePreserving_hyperplaneReflection μ ν c).restrict_preimage hVm

/-- A field equal to `f` on the closed half-space `{x | c ≤ ⟪x, ν⟫}` and to `G ∘ f ∘ ρ` below
it, for a continuous `G`, is a.e. strongly measurable on a measurable set `U` that `ρ` maps into
itself, as soon as `f` is a.e. strongly measurable on the part `U ∩ H` of `U` above the
hyperplane, where `H = {x | c < ⟪x, ν⟫}`. -/
theorem aestronglyMeasurable_piecewise_comp_hyperplaneReflection [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure] {β : Type*}
    [TopologicalSpace β] {ν : F} (hν : ν ≠ 0) {c : ℝ} {H U : Set F}
    (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ) (hUm : MeasurableSet U)
    (hU : Set.MapsTo (hyperplaneReflection ν c) U U) {f : F → β} {G : β → β}
    (hG : Continuous G) (hf : AEStronglyMeasurable f (μ.restrict (U ∩ H))) :
    AEStronglyMeasurable
      ({x | ⟪x, ν⟫_ℝ < c}.piecewise (fun x => G (f (hyperplaneReflection ν c x))) f)
      (μ.restrict U) := by
  have hS : MeasurableSet {x : F | ⟪x, ν⟫_ℝ < c} :=
    measurableSet_lt (continuous_id.inner continuous_const).measurable measurable_const
  have hHm : MeasurableSet H := by
    rw [show H = {x | c < ⟪x, ν⟫_ℝ} from Set.ext hH]
    exact measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable
  refine AEStronglyMeasurable.piecewise hS.nullMeasurableSet ?_ ?_
  · -- Below the hyperplane, `ρ` carries the measure onto the part of `U` above it.
    have hpre : hyperplaneReflection ν c ⁻¹' (U ∩ H) = {x | ⟪x, ν⟫_ℝ < c} ∩ U := by
      have hlt (x : F) : c < ⟪hyperplaneReflection ν c x, ν⟫_ℝ ↔ ⟪x, ν⟫_ℝ < c := by
        simpa only [hyperplaneReflection_hyperplaneReflection] using
          (inner_hyperplaneReflection_lt_iff hν c (x := hyperplaneReflection ν c x)).symm
      ext x
      refine ⟨fun hx => ⟨(hlt x).1 ((hH _).1 hx.2), ?_⟩,
        fun hx => ⟨hU hx.2, (hH _).2 ((hlt x).2 hx.1)⟩⟩
      simpa only [hyperplaneReflection_hyperplaneReflection] using hU hx.1
    have hmp := (measurePreserving_hyperplaneReflection μ ν c).restrict_preimage
      (hUm.inter hHm)
    rw [hpre] at hmp
    rw [Measure.restrict_restrict hS]
    exact hG.comp_aestronglyMeasurable (hf.comp_measurePreserving hmp)
  · -- Above the hyperplane the field is `f`; the hyperplane itself is null.
    rw [Measure.restrict_restrict hS.compl]
    refine hf.mono_measure (Measure.restrict_congr_set ?_).le
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (Measure.addHaar_setOf_inner_eq μ hν c)] with x hx
    have hx' : ⟪x, ν⟫_ℝ ≠ c := hx
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, hH]
    constructor
    · exact fun h => ⟨h.2, lt_of_le_of_ne h.1 (Ne.symm hx')⟩
    · exact fun h => ⟨h.2.le, h.1⟩

/-! ### Odd reflection of a function -/

section OddReflection

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {μ : Measure F}
  [μ.IsAddHaarMeasure] {ν : F} {c : ℝ} {H U : Set F} {E : Type*} [NormedAddCommGroup E]
  {f : F → E} {p : ENNReal}

/-- **The odd reflection of an `Lᵖ` function.** Let `U` be a measurable set mapped into itself by
the hyperplane reflection `ρ` and let `H` be measurable. If `f ∈ Lᵖ(U ∩ H)`, then the odd
reflection `x ↦ 1_H f x - 1_H f (ρ x)` lies in `Lᵖ(U)`. When `H` and `ρ H` are disjoint, for
instance when `H` is an open half-space bounded by the hyperplane, it equals `f` on `H` and
`-f ∘ ρ` on `ρ H`. -/
theorem memLp_indicator_sub_indicator_comp_hyperplaneReflection (hHm : MeasurableSet H)
    (hUm : MeasurableSet U) (hU : Set.MapsTo (hyperplaneReflection ν c) U U)
    (hf : MemLp f p (μ.restrict (U ∩ H))) :
    MemLp (fun x => H.indicator f x - H.indicator f (hyperplaneReflection ν c x)) p
      (μ.restrict U) := by
  have hg : MemLp (H.indicator f) p (μ.restrict U) := by
    rw [memLp_indicator_iff_restrict hHm.nullMeasurableSet, Measure.restrict_restrict hHm,
      Set.inter_comm]
    exact hf
  exact hg.sub (hg.comp_measurePreserving (measurePreserving_restrict_hyperplaneReflection hU hUm))

/-- **The norm of the odd reflection.** Let `U` be a measurable set mapped into itself by the
hyperplane reflection `ρ`, let `H` be measurable and let `1 ≤ p`. The odd reflection
`x ↦ 1_H f x - 1_H f (ρ x)` of a function `f` has `Lᵖ(U)` norm at most `2 ‖f‖_{Lᵖ(U ∩ H)}`. -/
theorem eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le (hp : 1 ≤ p)
    (hHm : MeasurableSet H) (hUm : MeasurableSet U)
    (hU : Set.MapsTo (hyperplaneReflection ν c) U U) :
    eLpNorm (fun x => H.indicator f x - H.indicator f (hyperplaneReflection ν c x)) p
      (μ.restrict U) ≤ 2 * eLpNorm f p (μ.restrict (U ∩ H)) := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict (U ∩ H))
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]
  have hρ := measurePreserving_restrict_hyperplaneReflection (μ := μ) hU hUm
  have hg : AEStronglyMeasurable (H.indicator f) (μ.restrict U) := by
    rw [aestronglyMeasurable_indicator_iff hHm, Measure.restrict_restrict hHm, Set.inter_comm]
    exact hf
  have hnorm : eLpNorm (H.indicator f) p (μ.restrict U) = eLpNorm f p (μ.restrict (U ∩ H)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hHm.nullMeasurableSet,
      Measure.restrict_restrict hHm, Set.inter_comm]
  calc eLpNorm (fun x => H.indicator f x - H.indicator f (hyperplaneReflection ν c x)) p
        (μ.restrict U)
      ≤ eLpNorm (H.indicator f) p (μ.restrict U) +
          eLpNorm (H.indicator f ∘ hyperplaneReflection ν c) p (μ.restrict U) :=
        eLpNorm_sub_le hp
    _ = 2 * eLpNorm f p (μ.restrict (U ∩ H)) := by
        rw [eLpNorm_comp_measurePreserving hg hρ, hnorm, two_mul]

end OddReflection

end TauCeti
