/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Atoms
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stieltjes inversion for the resolvent transform

A finite measure `μ` on the real line is recovered from its resolvent transform
`m(z) = ∫ (x - z)⁻¹ dμ(x)` on the upper half-plane. For `a < b`, the **Stieltjes inversion
formula** reads
`π⁻¹ ∫_a^b Im m(s + iη) ds → μ (a, b) + (μ {a} + μ {b}) / 2` as `η` decreases to `0`.
Together with the recovery of atoms in `TauCeti.MeasureTheory.Measure.ResolventTransform.Atoms`,
it shows that two finite measures with the same transform on the upper half-plane are equal. This
uniqueness identifies a limiting spectral law from its transform, for example a law whose
transform solves a self-consistent equation.

For fixed `η > 0` the integral over `[a, b]` is computed exactly by Fubini's theorem: the
imaginary part of the kernel integrates to a difference of arctangents, giving
`∫_a^b Im m(s + iη) ds = ∫ (arctan ((b - x) / η) - arctan ((a - x) / η)) dμ(x)`. As `η ↓ 0`
the integrand, divided by `π`, tends to `1` on `(a, b)`, to `1 / 2` at the endpoints and to `0`
outside `[a, b]`, and is bounded by `1`; dominated convergence gives the formula.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not `(z - x)⁻¹`.

## Main results

* `MeasureTheory.intervalIntegral_im_resolventTransform`: the exact interval integral of the
  imaginary part of the transform along a horizontal line.
* `MeasureTheory.tendsto_inv_pi_mul_intervalIntegral_im_resolventTransform`: the Stieltjes
  inversion formula, with the half-atom terms at the endpoints.
* `MeasureTheory.Measure.ext_of_resolventTransform`: a finite measure on `ℝ` is determined by its
  resolvent transform on the upper half-plane.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, §2.4.1, Theorem 2.4.3.
-/

public section

noncomputable section

open Filter Complex Set Real
open scoped Topology Interval

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- **The transform integrated along a horizontal line.** For `η > 0`, the integral of
`Im m(s + iη)` over `s ∈ [a, b]` is the integral against `μ` of the angle
`arctan ((b - x) / η) - arctan ((a - x) / η)` subtended by `[a, b]` at `x + iη`. -/
theorem intervalIntegral_im_resolventTransform (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ s in a..b, (resolventTransform μ (s + η * I)).im =
      ∫ x, (arctan ((b - x) / η) - arctan ((a - x) / η)) ∂μ := by
  have hkernel (s : ℝ) : (resolventTransform μ (s + η * I)).im =
      ∫ x, η / ((x - s) ^ 2 + η ^ 2) ∂μ := by
    simp [im_resolventTransform]
  have hinner (x : ℝ) : ∫ s in a..b, η / ((x - s) ^ 2 + η ^ 2) =
      arctan ((b - x) / η) - arctan ((a - x) / η) := by
    rw [← integral_div_sq_add_sq, ← intervalIntegral.integral_comp_sub_right
      (fun u : ℝ => η / (η ^ 2 + u ^ 2)) x]
    congr 1
    ext s
    ring_nf
  have : IsFiniteMeasure (volume.restrict (Ι a b)) := Real.isFiniteMeasure_restrict_Ioc _ _
  simp_rw [hkernel]
  rw [intervalIntegral_integral_swap]
  · simp_rw [hinner]
  · refine Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) η⁻¹
      (ae_of_all _ fun p => ?_)
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc η / ((p.2 - p.1) ^ 2 + η ^ 2) ≤ η / η ^ 2 :=
          div_le_div_of_nonneg_left hη.le (by positivity) (by nlinarith [sq_nonneg (p.2 - p.1)])
      _ = η⁻¹ := by field_simp

/-- The normalized angle subtended by `[a, b]` at `x + iη` tends, as `η ↓ 0`, to `1` on `(a, b)`,
to `1 / 2` at the endpoints and to `0` outside `[a, b]`. -/
private theorem tendsto_inv_pi_mul_arctan_sub_arctan {a b : ℝ} (hab : a < b) (x : ℝ) :
    Tendsto (fun η : ℝ => π⁻¹ * (arctan ((b - x) / η) - arctan ((a - x) / η))) (𝓝[>] 0)
      (𝓝 ((Ioo a b).indicator 1 x +
        (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2)) := by
  have key {L₁ L₂ : ℝ} (h₁ : Tendsto (fun η : ℝ => arctan ((b - x) / η)) (𝓝[>] 0) (𝓝 L₁))
      (h₂ : Tendsto (fun η : ℝ => arctan ((a - x) / η)) (𝓝[>] 0) (𝓝 L₂))
      (hL : π⁻¹ * (L₁ - L₂) = (Ioo a b).indicator 1 x +
        (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2) :
      Tendsto (fun η : ℝ => π⁻¹ * (arctan ((b - x) / η) - arctan ((a - x) / η))) (𝓝[>] 0)
        (𝓝 ((Ioo a b).indicator 1 x +
          (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2)) :=
    hL ▸ (h₁.sub h₂).const_mul π⁻¹
  rcases lt_trichotomy x a with hxa | rfl | hax
  · refine key (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith))
      (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith)) ?_
    simp [hxa.ne, (hxa.trans hab).ne, not_lt.2 hxa.le]
  · refine key (L₂ := 0) (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith)) (by simp) ?_
    simp [hab.ne]
    field_simp
  · rcases lt_trichotomy x b with hxb | rfl | hbx
    · refine key (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith))
        (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith)) ?_
      simp [hax, hxb, hax.ne', hxb.ne]
    · refine key (L₁ := 0) (by simp) (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith)) ?_
      simp [hab.ne']
      field_simp
    · refine key (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith))
        (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith)) ?_
      simp [hbx.ne', (hab.trans hbx).ne', not_lt.2 hbx.le]

/-- **Stieltjes inversion formula.** For a finite measure `μ` on `ℝ` and `a < b`,
`π⁻¹ ∫_a^b Im m(s + iη) ds` tends to `μ (a, b) + (μ {a} + μ {b}) / 2` as `η` decreases to `0`,
where `m` is the resolvent transform of `μ`. -/
theorem tendsto_inv_pi_mul_intervalIntegral_im_resolventTransform {a b : ℝ} (hab : a < b) :
    Tendsto (fun η : ℝ => π⁻¹ * ∫ s in a..b, (resolventTransform μ (s + η * I)).im) (𝓝[>] 0)
      (𝓝 (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2)) := by
  have hlimit : ∫ x, ((Ioo a b).indicator 1 x +
      (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2) ∂μ =
      μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2 := by
    have hI (s : Set ℝ) (hs : MeasurableSet s) : Integrable (s.indicator (1 : ℝ → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hs
    rw [← integral_indicator_one measurableSet_Ioo,
      ← integral_indicator_one (measurableSet_singleton a),
      ← integral_indicator_one (measurableSet_singleton b),
      ← integral_add (hI _ (measurableSet_singleton a)) (hI _ (measurableSet_singleton b)),
      ← integral_div, ← integral_add (hI _ measurableSet_Ioo)]
    exact ((hI _ (measurableSet_singleton a)).add (hI _ (measurableSet_singleton b))).div_const 2
  rw [← hlimit]
  have hdom : Tendsto
      (fun η : ℝ => ∫ x, π⁻¹ * (arctan ((b - x) / η) - arctan ((a - x) / η)) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, ((Ioo a b).indicator 1 x +
        (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun η => (by fun_prop : Continuous fun x : ℝ =>
        π⁻¹ * (arctan ((b - x) / η) - arctan ((a - x) / η))).aestronglyMeasurable)
      (Eventually.of_forall fun η => ae_of_all _ fun x => ?_) (integrable_const 1)
      (ae_of_all _ (tendsto_inv_pi_mul_arctan_sub_arctan hab))
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos pi_pos, inv_mul_le_iff₀ pi_pos, mul_one,
      abs_sub_le_iff]
    constructor <;> linarith [neg_pi_div_two_lt_arctan ((b - x) / η),
      arctan_lt_pi_div_two ((b - x) / η), neg_pi_div_two_lt_arctan ((a - x) / η),
      arctan_lt_pi_div_two ((a - x) / η)]
  refine hdom.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [intervalIntegral_im_resolventTransform a b hη, integral_const_mul]

/-- **Uniqueness of the resolvent transform.** Two finite measures on `ℝ` whose resolvent
transforms agree on the upper half-plane are equal. -/
theorem Measure.ext_of_resolventTransform {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : EqOn (resolventTransform μ) (resolventTransform ν) {z : ℂ | 0 < z.im}) : μ = ν := by
  have hline {η : ℝ} (hη : 0 < η) (s : ℝ) :
      resolventTransform μ (s + η * I) = resolventTransform ν (s + η * I) :=
    h (by simpa using hη)
  have hatom (a : ℝ) : μ.real {a} = ν.real {a} := by
    refine tendsto_nhds_unique (tendsto_mul_im_resolventTransform a)
      ((tendsto_mul_im_resolventTransform (μ := ν) a).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [hline hη]
  refine Measure.ext_of_Ioc μ ν fun a b hab => ?_
  have hIoo : μ.real (Ioo a b) = ν.real (Ioo a b) := by
    have hν : Tendsto (fun η : ℝ => π⁻¹ * ∫ s in a..b, (resolventTransform μ (s + η * I)).im)
        (𝓝[>] 0) (𝓝 (ν.real (Ioo a b) + (ν.real {a} + ν.real {b}) / 2)) :=
      (tendsto_inv_pi_mul_intervalIntegral_im_resolventTransform hab).congr' <| by
        filter_upwards [self_mem_nhdsWithin] with η hη
        simp only [hline hη]
    have := tendsto_nhds_unique (tendsto_inv_pi_mul_intervalIntegral_im_resolventTransform hab) hν
    rw [hatom a, hatom b] at this
    linarith
  have hIoc : μ.real (Ioc a b) = ν.real (Ioc a b) := by
    have hd : Disjoint (Ioo a b) {b} := disjoint_singleton_right.2 (by simp)
    rw [← Ioo_union_right hab, measureReal_union (μ := μ) hd (measurableSet_singleton b),
      measureReal_union (μ := ν) hd (measurableSet_singleton b), hIoo, hatom b]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).1 hIoc

end MeasureTheory
