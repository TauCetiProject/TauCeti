/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Real random variables with a bounded integral metric

`TauCeti.L0 μ` is a distinct presentation of the native almost-everywhere quotient
`MeasureTheory.AEEqFun Ω ℝ μ`. On a finite measure space its distance is the integral
of `|f - g| / (1 + |f - g|)`. The separate carrier permits this metric without changing
any structures on `AEEqFun` or on the native `Lp` spaces.
-/

public section

noncomputable section

open MeasureTheory Filter Set

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Real random variables modulo almost-everywhere equality, with a separate carrier for
the topology of convergence in measure. No additional quotient is taken. -/
structure L0 (μ : Measure Ω) where
  /-- The underlying native almost-everywhere equivalence class. -/
  toAEEqFun : Ω →ₘ[μ] ℝ

namespace L0

/-- Forgetting the wrapper is an equivalence with the native almost-everywhere quotient. -/
def equivAEEqFun : L0 μ ≃ (Ω →ₘ[μ] ℝ) where
  toFun := toAEEqFun
  invFun := L0.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence forgets the wrapper. -/
theorem equivAEEqFun_apply (f : L0 μ) : equivAEEqFun f = f.toAEEqFun := (rfl)

/-- The inverse equivalence wraps a native almost-everywhere equivalence class. -/
@[simp]
theorem toAEEqFun_equivAEEqFun_symm (f : Ω →ₘ[μ] ℝ) :
    (equivAEEqFun.symm f).toAEEqFun = f := (rfl)

instance : CoeFun (L0 μ) (fun _ ↦ Ω → ℝ) := ⟨fun f ↦ f.toAEEqFun⟩

/-- The chosen representative of a real random variable is strongly measurable. -/
theorem stronglyMeasurable (f : L0 μ) : StronglyMeasurable f :=
  f.toAEEqFun.stronglyMeasurable

/-- The chosen representative of a real random variable is measurable. -/
theorem measurable (f : L0 μ) : Measurable f := f.toAEEqFun.measurable

/-- Almost-everywhere equality of representatives characterizes equality in `L0`. -/
@[ext]
theorem ext {f g : L0 μ} (h : f =ᵐ[μ] g) : f = g :=
  equivAEEqFun.injective (AEEqFun.ext h)

/-- Construct a real random variable from an almost-everywhere strongly measurable function. -/
def ofFun (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) : L0 μ :=
  ⟨AEEqFun.mk f hf⟩

/-- Forgetting a constructed random variable gives the native quotient constructor. -/
@[simp]
theorem toAEEqFun_ofFun (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    (ofFun f hf).toAEEqFun = AEEqFun.mk f hf := (rfl)

/-- The representative of `ofFun f hf` agrees almost everywhere with `f`. -/
theorem coeFn_ofFun (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    (ofFun f hf : Ω → ℝ) =ᵐ[μ] f := AEEqFun.coeFn_mk f hf

/-- Equality between constructed random variables is exactly almost-everywhere equality. -/
@[simp]
theorem ofFun_eq_ofFun {f g : Ω → ℝ} {hf : AEStronglyMeasurable f μ}
    {hg : AEStronglyMeasurable g μ} : ofFun f hf = ofFun g hg ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact AEEqFun.mk_eq_mk.mp (congrArg toAEEqFun h)
  · intro h
    apply equivAEEqFun.injective
    exact AEEqFun.mk_eq_mk.mpr h

/-- Reconstructing a random variable from its chosen representative gives the original variable. -/
@[simp]
theorem ofFun_coeFn (f : L0 μ) : ofFun f f.stronglyMeasurable.aestronglyMeasurable = f := by
  apply equivAEEqFun.injective
  exact AEEqFun.mk_coeFn _

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- The bounded distance integrand is integrable on a finite measure space. -/
theorem integrable_distIntegrand (f g : L0 μ) :
    Integrable (fun x ↦ |f x - g x| / (1 + |f x - g x|)) μ := by
  apply (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · exact ((f.stronglyMeasurable.sub g.stronglyMeasurable).norm.div
      (stronglyMeasurable_const.add
        (f.stronglyMeasurable.sub g.stronglyMeasurable).norm)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by linarith [abs_nonneg (f x - g x)])

private theorem distIntegrand_triangle (a b c : ℝ) :
    |a - c| / (1 + |a - c|) ≤
      |a - b| / (1 + |a - b|) + |b - c| / (1 + |b - c|) := by
  have hab := abs_nonneg (a - b)
  have hbc := abs_nonneg (b - c)
  have ht : |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
  have hm : |a - c| / (1 + |a - c|) ≤
      (|a - b| + |b - c|) / (1 + (|a - b| + |b - c|)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  refine hm.trans ?_
  rw [add_div]
  exact add_le_add
    (div_le_div_of_nonneg_left hab (by positivity) (by linarith))
    (div_le_div_of_nonneg_left hbc (by positivity) (by linarith))

/-- The bounded integral distance on real random variables over a finite measure space. -/
instance instMetricSpace : MetricSpace (L0 μ) where
  dist f g := ∫ x, |f x - g x| / (1 + |f x - g x|) ∂μ
  dist_self f := by simp
  dist_comm f g := by simp only [abs_sub_comm]
  dist_triangle f g h := by
    rw [← integral_add (integrable_distIntegrand f g) (integrable_distIntegrand g h)]
    exact integral_mono (integrable_distIntegrand f h)
      ((integrable_distIntegrand f g).add (integrable_distIntegrand g h))
      (fun x ↦ distIntegrand_triangle (f x) (g x) (h x))
  eq_of_dist_eq_zero {f g} h := by
    apply ext
    have hzero := (integral_eq_zero_iff_of_nonneg
      (fun x ↦ by positivity) (integrable_distIntegrand f g)).1 h
    filter_upwards [hzero] with x hx
    have := (div_eq_zero_iff).1 hx
    rcases this with h | h
    · exact sub_eq_zero.mp (abs_eq_zero.mp h)
    · have := abs_nonneg (f x - g x)
      linarith

/-- The metric is the bounded integral of the difference of representatives. -/
theorem dist_def (f g : L0 μ) :
    dist f g = ∫ x, |f x - g x| / (1 + |f x - g x|) ∂μ := (rfl)

/-- The integral formula is independent of the supplied representatives. -/
theorem dist_ofFun (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    dist (ofFun f hf) (ofFun g hg) = ∫ x, |f x - g x| / (1 + |f x - g x|) ∂μ := by
  rw [dist_def]
  apply integral_congr_ae
  filter_upwards [coeFn_ofFun f hf, coeFn_ofFun g hg] with x hx hy
  rw [hx, hy]

/-- Every distance is bounded by the total mass of the finite measure. -/
theorem dist_le_measure_univ (f g : L0 μ) : dist f g ≤ μ.real univ := by
  rw [dist_def]
  simpa using integral_mono (integrable_distIntegrand f g) (integrable_const (1 : ℝ))
    (fun x ↦ (div_le_one (by positivity)).2 (by linarith [abs_nonneg (f x - g x)]))

end FiniteMeasure
end L0
end TauCeti
