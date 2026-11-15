/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import Mathlib.Order.Disjointed
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Positivity
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# Integrating functions against the Riemannian volume form

On an oriented Riemannian manifold `M`, a function `f : M → ℝ` is integrated as the top form
`f vol`, where `vol = TauCeti.riemannianVolumeForm o` is the Riemannian volume form of the
orientation `o`: `∫_M f vol = integralTopForm o (fun x ↦ f x • vol x)`. This file records the
basic properties of this integral that pointwise estimates need: in every dimension (including
dimension zero) it is nonnegative on nonnegative functions, it commutes with constant factors, and
on a compact manifold it is additive and monotone on continuous functions, with equality in
`∫_M f vol ≤ ∫_M g vol` when `f ≤ g` if and only if `f = g` everywhere.

## Main results

* `TauCeti.integralTopForm_smul_riemannianVolumeForm_nonneg`: `0 ≤ f` gives `0 ≤ ∫_M f vol`.
* `TauCeti.integralTopForm_mul_smul_riemannianVolumeForm`: `∫_M c f vol = c ∫_M f vol`.
* `TauCeti.isSmoothForm_smul_riemannianVolumeForm`: `f vol` is a continuous top form when `f`
  is continuous.
* `TauCeti.integralTopForm_add_smul_riemannianVolumeForm`: on a compact manifold,
  `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_mono`: on a compact manifold, `f ≤ g`
  gives `∫_M f vol ≤ ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_pos_iff`: on a compact manifold, a continuous
  nonnegative `f` has `0 < ∫_M f vol` if and only if `0 < f x` for some `x`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_eq_zero_iff`: on a compact manifold, a
  continuous nonnegative `f` has `∫_M f vol = 0` if and only if `f = 0` everywhere.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_eq_iff_of_le`: on a compact manifold,
  continuous functions with `f ≤ g` satisfy `∫_M f vol = ∫_M g vol` if and only if `f = g`
  everywhere.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6 and Proposition 15.29.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ} (o : Manifold.Orientation I M (Fin m))

/-- The integral `∫_M f vol` of a nonnegative function against the Riemannian volume form is
nonnegative in every dimension, including dimension `0`. -/
theorem integralTopForm_smul_riemannianVolumeForm_nonneg {f : M → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) := by
  rcases m with _ | m
  · set φ : RoughForm I M ℝ 0 := fun x ↦ f x • riemannianVolumeForm o x
    by_cases hi : IntegrableTopForm φ
    swap
    · rw [integralTopForm_eq_zero_of_not_integrable o φ hi]
    let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    have : LocallyCompactSpace H := I.locallyCompactSpace
    obtain ⟨l, rfl⟩ := o.exists_lift
    have hm : Module.finrank ℝ E = 0 := by simpa using l.card_eq.symm
    set σ : Fin (Module.finrank ℝ E) ≃ Fin 0 := finCongr hm
    set b := (Module.finBasis ℝ E).reindex σ
    obtain ⟨n, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
    rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hu i).1)
      (fun i ↦ (hu i).2.1) hcover, Finset.mul_sum]
    refine Finset.sum_nonneg fun i _ ↦ ?_
    rw [← integral_const_mul]
    refine integral_nonneg fun y ↦ ?_
    dsimp only [Pi.zero_apply]
    by_cases hy : y ∈ (extChartAt I (α i)).target
    · set x := (extChartAt I (α i)).symm y
      have hx : x ∈ (extChartAt I (α i)).source := (extChartAt I (α i)).map_target hy
      have hx' : x ∈ (chartAt H (α i)).source := by simpa only [extChartAt_source] using hx
      have hsign := signBasis_mul_signAt_mul_riemannianVolumeForm_chartLocalFrame l σ hx'
      have hval : φ x (fun j ↦
          mfderivWithin 𝓘(ℝ, E) I (extChartAt I (α i)).symm (Set.range I) y (b j)) =
          f x * riemannianVolumeForm (Manifold.Orientation.mk l) x
            (fun j ↦ Riemannian.Tensor.chartLocalFrame (I := I) (α i) (σ.symm j) x) := by
        rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        congr 2
        funext j
        exact j.elim0
      rw [RoughForm.signedInChartAt_apply, dite_eq_left hy, RoughForm.inChartAt_apply, hval]
      calc 0 ≤ chartVolumeDensity (I := I) (α i) x * f x :=
            mul_nonneg (chartVolumeDensity_nonneg _ _) (hf x)
        _ = _ := by rw [← hsign]; ring
    · rw [RoughForm.signedInChartAt_apply, dite_eq_right hy, mul_zero]
  · refine integralTopForm_nonneg o fun x c hc ↦ ?_
    let := o.fact_finrank_tangentSpace x
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, riemannianVolumeForm_apply]
    exact mul_nonneg (hf x) (Orientation.volumeForm_apply_pos_iff.2 hc).le

/-- Constant factors come out of the integral against the Riemannian volume form:
`∫_M c f vol = c ∫_M f vol`. -/
theorem integralTopForm_mul_smul_riemannianVolumeForm (c : ℝ) (f : M → ℝ) :
    integralTopForm o (fun x ↦ (c * f x) • riemannianVolumeForm o x) =
      c * integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_smul]
  congr 1
  funext x
  rw [Pi.smul_apply, mul_smul]

section Continuous

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- For a continuous function `f`, the top form `f vol` is continuous. -/
theorem isSmoothForm_smul_riemannianVolumeForm {f : M → ℝ} (hf : Continuous f) :
    IsSmoothForm I 0 (fun x ↦ f x • riemannianVolumeForm o x) := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  exact (isSmoothForm_riemannianVolumeForm o).fun_smul (contMDiff_zero_iff.2 hf)

variable [CompactSpace M]

/-- On a compact oriented Riemannian manifold, the integral against the Riemannian volume form is
additive on continuous functions: `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol`. -/
theorem integralTopForm_add_smul_riemannianVolumeForm {f g : M → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    integralTopForm o (fun x ↦ (f x + g x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) +
        integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_add_of_compactSpace o (isSmoothForm_smul_riemannianVolumeForm o hf)
    (isSmoothForm_smul_riemannianVolumeForm o hg)]
  congr 1
  funext x
  rw [Pi.add_apply, add_smul]

/-- **Monotonicity of the integral against the Riemannian volume form**: on a compact oriented
Riemannian manifold, continuous functions with `f ≤ g` satisfy `∫_M f vol ≤ ∫_M g vol`. -/
theorem integralTopForm_smul_riemannianVolumeForm_mono {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  have h :=
    integralTopForm_add_smul_riemannianVolumeForm o (g := fun x ↦ g x - f x) hf (hg.sub hf)
  simp only [add_sub_cancel] at h
  rw [h, le_add_iff_nonneg_right]
  exact integralTopForm_smul_riemannianVolumeForm_nonneg o fun x ↦ sub_nonneg.2 (hfg x)

/-- On a compact oriented Riemannian manifold, a continuous nonnegative function `f` has strictly
positive integral against `riemannianVolumeForm o` if and only if `0 < f x` at some point `x`. -/
theorem integralTopForm_smul_riemannianVolumeForm_pos_iff {f : M → ℝ}
    (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x) :
    0 < integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) ↔ ∃ x, 0 < f x := by
  refine ⟨fun h ↦ ?_, fun hpos ↦ ?_⟩
  · by_contra! hle
    have hzero : (fun x ↦ f x • riemannianVolumeForm o x) = 0 := by
      funext x
      simp [le_antisymm (hle x) (hnn x)]
    rw [hzero, integralTopForm_zero] at h
    exact lt_irrefl 0 h
  · let : MeasurableSpace M := borel M
    have : BorelSpace M := ⟨rfl⟩
    have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 0)
    have hc : HasCompactSupport f := .of_compactSpace f
    have hint : Integrable f (riemannianVolume I M) := hf.integrable_of_hasCompactSupport hc
    rw [integralTopForm_smul_riemannianVolumeForm o hf hc,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hf.aestronglyMeasurable]
    exact ENNReal.toReal_pos (lintegral_riemannianVolume_pos hf hpos).ne' hint.lintegral_lt_top.ne

/-- On a compact oriented Riemannian manifold, a continuous nonnegative function `f` has zero
integral against `riemannianVolumeForm o` if and only if `f = 0` everywhere. -/
theorem integralTopForm_smul_riemannianVolumeForm_eq_zero_iff {f : M → ℝ}
    (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) = 0 ↔ ∀ x, f x = 0 := by
  rw [le_antisymm_iff, and_iff_left (integralTopForm_smul_riemannianVolumeForm_nonneg o hnn),
    ← not_lt, integralTopForm_smul_riemannianVolumeForm_pos_iff o hf hnn, not_exists]
  exact forall_congr' fun x ↦ ⟨fun h ↦ le_antisymm (not_lt.1 h) (hnn x), fun h ↦ by simp [h]⟩

/-- On a compact oriented Riemannian manifold, continuous functions with `f ≤ g` have equal
integrals against `riemannianVolumeForm o` if and only if `f = g` everywhere. -/
theorem integralTopForm_smul_riemannianVolumeForm_eq_iff_of_le {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) =
        integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) ↔
      ∀ x, f x = g x := by
  have h :=
    integralTopForm_add_smul_riemannianVolumeForm o (g := fun x ↦ g x - f x) hf (hg.sub hf)
  simp only [add_sub_cancel] at h
  rw [h, left_eq_add,
    integralTopForm_smul_riemannianVolumeForm_eq_zero_iff o (f := fun x ↦ g x - f x) (hg.sub hf)
      (fun x ↦ sub_nonneg.2 (hfg x))]
  exact forall_congr' fun x ↦ sub_eq_zero.trans eq_comm

end Continuous

end TauCeti

