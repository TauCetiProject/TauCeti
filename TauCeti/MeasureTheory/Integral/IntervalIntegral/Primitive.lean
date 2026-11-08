/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Topology.Order.Interval

/-!
# Primitives of integrable functions on the line

Facts about the primitive `t ↦ ∫ s in t₀..t, f s` of a vector-valued function `f`, which are
used to identify weak derivatives on an interval with ordinary primitives.

* `TauCeti.intervalIntegral.exists_continuous_primitive_Icc`: a continuous integrand on a closed
  interval has a globally continuous primitive with the prescribed derivative there and the
  expected increments between points of the interval.
* `TauCeti.intervalIntegral.continuousOn_primitive_interval_of_locallyIntegrableOn`: if `f` is
  only locally integrable on an open interval, its primitive based at a point of the interval is
  continuous on the interval.
  Mathlib's `intervalIntegral.continuousOn_primitive_interval'` covers a compact interval on which
  `f` is integrable.
* `TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo`: if `f` is
  integrable on the open interval `(a, b)`, its primitive based at a point of `[a, b]` is
  continuous on the closed interval `[a, b]`.
* `TauCeti.intervalIntegral.eLpNorm_primitive_le` and
  `TauCeti.intervalIntegral.eLpNorm_primitive_le_mul_eLpNorm`: on a bounded interval `(a, b)`,
  the primitive based at a point of `[a, b]` is bounded by the `L¹(a, b)` norm of `f`, so its
  `Lᵖ(a, b)` norm is at most `(b - a) ^ (1 / p) ‖f‖₁`, and hence at most `(b - a) ‖f‖_p`.
* `TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le`: integration by parts
  between a `C¹` real function `φ` and the primitive of an integrable `f`, which need not be
  differentiable anywhere:
  `∫ t in a..b, φ' t • ∫ s in a..t, f s = φ b • ∫ s in a..b, f s - ∫ t in a..b, φ t • f t`.
  It is proved by exchanging the order of integration (Fubini's theorem), so no differentiation of
  the primitive is needed.
-/

public section

open MeasureTheory Set Filter
open scoped Interval

namespace TauCeti

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ}

/-- The primitive `t ↦ ∫ s in t₀..t, f s ∂μ` of a function locally integrable on the open interval
`Ioo a b`, based at a point `t₀` of the interval, is continuous on the interval. -/
theorem continuousOn_primitive_interval_of_locallyIntegrableOn {μ : Measure ℝ}
    [NullSingletonClass μ] {t₀ : ℝ} (hf : LocallyIntegrableOn f (Ioo a b) μ)
    (ht₀ : t₀ ∈ Ioo a b) :
    ContinuousOn (fun t ↦ ∫ s in t₀..t, f s ∂μ) (Ioo a b) := by
  intro x hx
  -- `f` is integrable on a compact interval `[α, β] ⊆ (a, b)` whose interior contains `x, t₀`.
  obtain ⟨α, β, hsub, hαβ⟩ := (Set.toFinite {x, t₀}).isCompact.exists_Icc_between
    (insert_nonempty _ _) (insert_subset hx (singleton_subset_iff.2 ht₀))
  have hx' := hsub (mem_insert _ _)
  have ht₀' := hsub (mem_insert_of_mem _ rfl)
  have hle : α ≤ β := (hx'.1.trans hx'.2).le
  have hint : IntervalIntegrable f μ α β :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).2 <|
      hf.integrableOn_compact_subset hαβ isCompact_Icc
  have hcont := _root_.intervalIntegral.continuousOn_primitive_interval' (a := t₀) hint
    (by rw [uIcc_of_le hle]; exact Ioo_subset_Icc_self ht₀')
  rw [uIcc_of_le hle] at hcont
  exact (hcont.continuousAt (Icc_mem_nhds hx'.1 hx'.2)).continuousWithinAt

/-- The primitive `t ↦ ∫ s in t₀..t, f s ∂μ` of a function integrable on the open interval
`Ioo a b`, based at a point `t₀` of `Icc a b`, is continuous on the closed interval `Icc a b`. -/
theorem continuousOn_primitive_interval_of_integrableOn_Ioo {μ : Measure ℝ}
    [NullSingletonClass μ] {t₀ : ℝ} (hf : IntegrableOn f (Ioo a b) μ) (ht₀ : t₀ ∈ Icc a b) :
    ContinuousOn (fun t ↦ ∫ s in t₀..t, f s ∂μ) (Icc a b) := by
  have hab : a ≤ b := ht₀.1.trans ht₀.2
  simpa [uIcc_of_le hab] using _root_.intervalIntegral.continuousOn_primitive_interval'
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hf) (uIcc_of_le hab ▸ ht₀)

/-- The `Lᵖ(a, b)` norm of the primitive `t ↦ ∫ s in t₀..t, f s` of a function integrable on
`(a, b)`, based at a point `t₀` of `[a, b]`, is at most `(b - a) ^ (1 / p)` times the `L¹(a, b)`
norm of `f`: the primitive is bounded by `∫ s in (a, b), ‖f s‖` at every point. -/
theorem eLpNorm_primitive_le {p : ENNReal} {t₀ : ℝ} (hf : IntegrableOn f (Ioo a b))
    (ht₀ : t₀ ∈ Icc a b) :
    eLpNorm (fun t ↦ ∫ s in t₀..t, f s) p (volume.restrict (Ioo a b)) ≤
      volume (Ioo a b) ^ p.toReal⁻¹ * eLpNorm f 1 (volume.restrict (Ioo a b)) := by
  have hf' : IntegrableOn f (Icc a b) := by rwa [integrableOn_Icc_iff_integrableOn_Ioo]
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖∫ s in t₀..t, f s‖ ≤ ∫ s in Ioo a b, ‖f s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    -- The oriented interval between `t₀` and `t` lies in `[a, b]`.
    have hsub : Ι t₀ t ⊆ Icc a b := uIoc_subset_uIcc.trans
      (uIcc_subset_Icc ht₀ (Ioo_subset_Icc_self ht))
    calc ‖∫ s in t₀..t, f s‖ ≤ ∫ s in Ι t₀ t, ‖f s‖ :=
          _root_.intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Icc a b, ‖f s‖ :=
          setIntegral_mono_set hf'.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
            hsub.eventuallyLE
      _ = ∫ s in Ioo a b, ‖f s‖ := integral_Icc_eq_integral_Ioo
  have hm : AEStronglyMeasurable (fun t ↦ ∫ s in t₀..t, f s) (volume.restrict (Ioo a b)) :=
    ((continuousOn_primitive_interval_of_integrableOn_Ioo hf ht₀).mono
      Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  calc eLpNorm (fun t ↦ ∫ s in t₀..t, f s) p (volume.restrict (Ioo a b))
      ≤ volume.restrict (Ioo a b) univ ^ p.toReal⁻¹ *
          ENNReal.ofReal (∫ s in Ioo a b, ‖f s‖) := eLpNorm_le_of_ae_bound hm hbound
    _ = volume (Ioo a b) ^ p.toReal⁻¹ * eLpNorm f 1 (volume.restrict (Ioo a b)) := by
      rw [Measure.restrict_apply_univ, ofReal_integral_norm_eq_lintegral_enorm hf,
        eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]

/-- The `Lᵖ(a, b)` norm of the primitive `t ↦ ∫ s in t₀..t, f s`, based at a point `t₀` of
`[a, b]`, is at most `b - a` times the `Lᵖ(a, b)` norm of `f`, for `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_primitive_le_mul_eLpNorm {p : ENNReal} (hp : 1 ≤ p) {t₀ : ℝ}
    (hf : IntegrableOn f (Ioo a b)) (ht₀ : t₀ ∈ Icc a b) :
    eLpNorm (fun t ↦ ∫ s in t₀..t, f s) p (volume.restrict (Ioo a b)) ≤
      ENNReal.ofReal (b - a) * eLpNorm f p (volume.restrict (Ioo a b)) := by
  rcases (ht₀.1.trans ht₀.2).eq_or_lt with rfl | hab
  · simp
  have hne : volume (Ioo a b) ≠ 0 := by simp [hab]
  -- Hölder's inequality on the bounded interval turns the `L¹` bound into an `Lᵖ` bound.
  calc eLpNorm (fun t ↦ ∫ s in t₀..t, f s) p (volume.restrict (Ioo a b))
      ≤ volume (Ioo a b) ^ p.toReal⁻¹ * eLpNorm f 1 (volume.restrict (Ioo a b)) :=
        eLpNorm_primitive_le hf ht₀
    _ ≤ volume (Ioo a b) ^ p.toReal⁻¹ * (eLpNorm f p (volume.restrict (Ioo a b)) *
          volume (Ioo a b) ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)) := by
        gcongr
        simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
    _ = ENNReal.ofReal (b - a) * eLpNorm f p (volume.restrict (Ioo a b)) := by
        -- The two powers of the interval length combine to its first power.
        have hpow : volume (Ioo a b) ^ p.toReal⁻¹ *
            volume (Ioo a b) ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal) =
              ENNReal.ofReal (b - a) := by
          rw [← ENNReal.rpow_add _ _ hne measure_Ioo_lt_top.ne]
          simp
        rw [← hpow]
        ring

variable [CompleteSpace E]

/-- A continuous integrand on a nonempty closed interval has a globally continuous primitive
whose derivative agrees with the integrand throughout that interval, including its endpoints.
The primitive increments are the oriented integrals between points of the interval. -/
theorem exists_continuous_primitive_Icc (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ∃ F : ℝ → E, Continuous F ∧ (∀ x ∈ Icc a b, HasDerivAt F (f x) x) ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, F y - F x = ∫ z in x..y, f z := by
  -- Holding endpoint values constant gives a continuous integrand on the whole line.
  obtain ⟨g, hg, hgf⟩ := hf.exists_continuous_eqOn_Icc hab
  let F : ℝ → E := fun t ↦ ∫ x in a..t, g x
  refine ⟨F, (_root_.intervalIntegral.differentiable_integral_of_continuous hg).continuous,
    ?_, ?_⟩
  · intro x hx
    rw [← hgf hx]
    exact _root_.intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a x)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  · intro x hx y hy
    calc
      F y - F x = ∫ z in x..y, g z :=
        _root_.intervalIntegral.integral_interval_sub_left
          (hg.intervalIntegrable a y) (hg.intervalIntegrable a x)
      _ = _ := _root_.intervalIntegral.integral_congr (hgf.mono (uIcc_subset_Icc hx hy))

/-- **Integration by parts against a primitive.** For `a ≤ b`, `f` integrable on `[a, b]` and a
`C¹` function `φ : ℝ → ℝ`,
`∫ t in a..b, φ' t • ∫ s in a..t, f s = φ b • ∫ s in a..b, f s - ∫ t in a..b, φ t • f t`. -/
theorem integral_deriv_smul_primitive_eq_sub_of_le {φ : ℝ → ℝ} (hab : a ≤ b)
    (hφ : ContDiff ℝ 1 φ) (hf : IntervalIntegrable f volume a b) :
    ∫ t in a..b, deriv φ t • ∫ s in a..t, f s =
      φ b • (∫ s in a..b, f s) - ∫ t in a..b, φ t • f t := by
  -- Both sides are iterated integrals of `G t s = φ' t • 1_{s < t} f s` over `[a, b]²`, in the
  -- two possible orders.
  have hφd : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  set G : ℝ → ℝ → E := fun t s ↦ deriv φ t • (Iio t).indicator f s with hG_def
  have hGi : IntegrableOn (Function.uncurry G) (Ι a b ×ˢ Ι a b) := by
    rw [uIoc_of_le hab]
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      hφd.continuousOn
    have hfi : Integrable f (volume.restrict (Ioc a b)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine Integrable.mono' ((integrable_const C).mul_prod hfi.norm) ?_ ?_
    · have heq : Function.uncurry G = fun p : ℝ × ℝ ↦
          deriv φ p.1 • {p : ℝ × ℝ | p.2 < p.1}.indicator (fun p ↦ f p.2) p := by
        ext ⟨t, s⟩
        simp [G, indicator]
      have hm : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ f p.2)
          ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
        hfi.aestronglyMeasurable.comp_snd
      rw [heq]
      exact (hφd.comp continuous_fst).aestronglyMeasurable.smul
        (hm.indicator (measurableSet_lt measurable_snd measurable_fst))
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      simp only [Function.uncurry, G, norm_smul]
      have hCp := hC p.1 (Ioc_subset_Icc_self hp.1)
      exact mul_le_mul hCp (norm_indicator_le_norm_self _ _) (norm_nonneg _)
        ((norm_nonneg _).trans hCp)
  -- Integrating in `s` first gives `φ' t • ∫ s in a..t, f s`.
  have hleft : EqOn (fun t ↦ ∫ s in a..b, G t s) (fun t ↦ deriv φ t • ∫ s in a..t, f s)
      (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hset : Ioc a b ∩ Iio t = Ioo a t := by
      ext s
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, by linarith [ht.2]⟩, h.2⟩⟩
    simp only [hG_def, _root_.intervalIntegral.integral_smul]
    rw [_root_.intervalIntegral.integral_of_le hab, _root_.intervalIntegral.integral_of_le ht.1,
      setIntegral_indicator measurableSet_Iio, hset, integral_Ioc_eq_integral_Ioo]
  -- Integrating in `t` first gives `(φ b - φ s) • f s`.
  have hright : EqOn (fun s ↦ ∫ t in a..b, G t s) (fun s ↦ φ b • f s - φ s • f s)
      (uIcc a b) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hGs : ∀ t, G t s = (Ioi s).indicator (deriv φ) t • f s := by
      intro t
      by_cases hst : s < t <;> simp [G, indicator, hst]
    calc ∫ t in a..b, G t s = (∫ t in a..b, (Ioi s).indicator (deriv φ) t) • f s := by
          simp only [hGs, _root_.intervalIntegral.integral_smul_const]
      -- The indicator cuts `[a, b]` down to `[s, b]`.
      _ = (∫ t in s..b, deriv φ t) • f s := by
          rw [_root_.intervalIntegral.integral_of_le hab, setIntegral_indicator measurableSet_Ioi,
            Ioc_inter_Ioi, sup_eq_right.2 hs.1, ← _root_.intervalIntegral.integral_of_le hs.2]
      _ = φ b • f s - φ s • f s := by
          rw [_root_.intervalIntegral.integral_deriv_eq_sub
            (fun x _ ↦ (hφ.differentiable one_ne_zero) x) (hφd.intervalIntegrable _ _), sub_smul]
  rw [← _root_.intervalIntegral.integral_congr hleft,
    intervalIntegral_intervalIntegral_swap hGi,
    _root_.intervalIntegral.integral_congr hright,
    _root_.intervalIntegral.integral_sub ?_ ?_, _root_.intervalIntegral.integral_smul]
  · exact hf.smul (φ b)
  · exact hf.continuousOn_smul hφ.continuous.continuousOn

end intervalIntegral

end TauCeti
