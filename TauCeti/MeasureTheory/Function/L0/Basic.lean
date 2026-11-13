/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Defs

/-!
# Random variables with a bounded integral pseudometric

`TauCeti.L0 E μ` is a distinct presentation of the native almost-everywhere quotient
`MeasureTheory.AEEqFun Ω E μ`, for any topological space `E`. When `E` is a pseudometric
space and `μ` is finite, its distance is the integral of `dist f g / (1 + dist f g)`.
This is a metric when `E` is separated. The separate carrier permits these structures without
changing any structures on `AEEqFun` or on the native `Lp` spaces.
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Random variables modulo almost-everywhere equality, with a separate carrier for
the topology of convergence in measure. No additional quotient is taken. -/
structure L0 (E : Type*) [TopologicalSpace E] (μ : Measure Ω) where
  /-- The underlying native almost-everywhere equivalence class. -/
  toAEEqFun : Ω →ₘ[μ] E

namespace L0

section Topological

variable {E : Type*} [TopologicalSpace E]

/-- Forgetting the wrapper is an equivalence with the native almost-everywhere quotient. -/
def equivAEEqFun : L0 E μ ≃ (Ω →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := L0.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence forgets the wrapper. -/
@[simp]
theorem equivAEEqFun_apply (f : L0 E μ) : equivAEEqFun f = f.toAEEqFun := (rfl)

/-- Wrapping the underlying equivalence class recovers the random variable. -/
@[simp]
theorem equivAEEqFun_symm_toAEEqFun (f : L0 E μ) :
    equivAEEqFun.symm f.toAEEqFun = f := (rfl)

/-- The underlying almost-everywhere class determines a random variable. -/
theorem toAEEqFun_injective : Function.Injective (toAEEqFun : L0 E μ → (Ω →ₘ[μ] E)) :=
  equivAEEqFun.injective

/-- Equality of underlying classes is equality of random variables. -/
@[simp]
theorem toAEEqFun_inj {f g : L0 E μ} : f.toAEEqFun = g.toAEEqFun ↔ f = g :=
  toAEEqFun_injective.eq_iff

/-- The inverse equivalence wraps a native almost-everywhere equivalence class. -/
@[simp]
theorem toAEEqFun_equivAEEqFun_symm (f : Ω →ₘ[μ] E) :
    (equivAEEqFun.symm f).toAEEqFun = f := (rfl)

instance : CoeFun (L0 E μ) (fun _ ↦ Ω → E) := ⟨fun f ↦ f.toAEEqFun⟩

/-- The chosen representative of a random variable is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable (f : L0 E μ) : StronglyMeasurable f :=
  f.toAEEqFun.stronglyMeasurable

/-- The chosen representative of a random variable is measurable. -/
@[fun_prop]
theorem measurable [PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : L0 E μ) : Measurable f := f.toAEEqFun.measurable

/-- The chosen representative is almost-everywhere strongly measurable. -/
@[fun_prop]
theorem aestronglyMeasurable (f : L0 E μ) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

/-- The chosen representative is almost-everywhere measurable. -/
@[fun_prop]
theorem aemeasurable [PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : L0 E μ) : AEMeasurable f μ := f.measurable.aemeasurable

/-- Almost-everywhere equality of representatives characterizes equality in `L0`. -/
@[ext]
theorem ext {f g : L0 E μ} (h : f =ᵐ[μ] g) : f = g :=
  equivAEEqFun.injective (AEEqFun.ext h)

/-- Construct a random variable from an almost-everywhere strongly measurable function. -/
def ofFun (f : Ω → E) (hf : AEStronglyMeasurable f μ) : L0 E μ :=
  ⟨AEEqFun.mk f hf⟩

/-- Forgetting a constructed random variable gives the native quotient constructor. -/
@[simp]
theorem toAEEqFun_ofFun (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    (ofFun f hf).toAEEqFun = AEEqFun.mk f hf := (rfl)

/-- The representative of `ofFun f hf` agrees almost everywhere with `f`. -/
theorem coeFn_ofFun (f : Ω → E) (hf : AEStronglyMeasurable f μ) :
    (ofFun f hf : Ω → E) =ᵐ[μ] f := AEEqFun.coeFn_mk f hf

/-- Equality between constructed random variables is exactly almost-everywhere equality. -/
@[simp]
theorem ofFun_eq_ofFun {f g : Ω → E} {hf : AEStronglyMeasurable f μ}
    {hg : AEStronglyMeasurable g μ} : ofFun f hf = ofFun g hg ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact AEEqFun.mk_eq_mk.mp (congrArg toAEEqFun h)
  · intro h
    apply equivAEEqFun.injective
    exact AEEqFun.mk_eq_mk.mpr h

/-- Reconstructing a random variable from its chosen representative gives the original variable. -/
@[simp]
theorem ofFun_coeFn (f : L0 E μ) : ofFun f f.stronglyMeasurable.aestronglyMeasurable = f := by
  apply equivAEEqFun.injective
  exact AEEqFun.mk_coeFn _

end Topological

section FiniteMeasure

variable {E : Type*} [PseudoMetricSpace E] [IsFiniteMeasure μ]

/-- The bounded distance integrand is integrable on a finite measure space. -/
theorem integrable_dist_div_one_add_dist (f g : L0 E μ) :
    Integrable (fun x ↦ dist (f x) (g x) / (1 + dist (f x) (g x))) μ := by
  apply (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · exact ((f.stronglyMeasurable.dist g.stronglyMeasurable).div
      (stronglyMeasurable_const.add
        (f.stronglyMeasurable.dist g.stronglyMeasurable))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by linarith [dist_nonneg (x := f x) (y := g x)])

/-- The bounded integral distance on random variables over a finite measure space. -/
instance instPseudoMetricSpace : PseudoMetricSpace (L0 E μ) where
  dist f g := ∫ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ∂μ
  dist_self f := by simp
  dist_comm f g := by simp only [dist_comm]
  dist_triangle f g h := by
    rw [← integral_add (integrable_dist_div_one_add_dist f g)
      (integrable_dist_div_one_add_dist g h)]
    exact integral_mono (integrable_dist_div_one_add_dist f h)
      ((integrable_dist_div_one_add_dist f g).add
        (integrable_dist_div_one_add_dist g h))
      (fun x ↦ Metric.dist_div_one_add_dist_le (f x) (g x) (h x))

/-- A separated target makes the bounded integral pseudometric a metric. -/
instance instMetricSpace [T0Space E] : MetricSpace (L0 E μ) where
  toPseudoMetricSpace := instPseudoMetricSpace
  eq_of_dist_eq_zero {f g} h := by
    apply ext
    have hzero := (integral_eq_zero_iff_of_nonneg
      (fun x ↦ by positivity) (integrable_dist_div_one_add_dist f g)).1 h
    filter_upwards [hzero] with x hx
    have hd : dist (f x) (g x) = 0 := (div_eq_zero_iff).1 hx |>.resolve_right (by positivity)
    exact (Metric.inseparable_iff.2 hd).eq

/-- The pseudometric is the bounded integral of the distance between representatives. -/
theorem dist_def (f g : L0 E μ) :
    dist f g = ∫ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ∂μ := (rfl)

/-- The integral formula is independent of the supplied representatives. -/
theorem dist_ofFun (f g : Ω → E) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    dist (ofFun f hf) (ofFun g hg) = ∫ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ∂μ := by
  rw [dist_def]
  apply integral_congr_ae
  filter_upwards [coeFn_ofFun f hf, coeFn_ofFun g hg] with x hx hy
  rw [hx, hy]

/-- Every distance is bounded by the total mass of the finite measure. -/
theorem dist_le_measureReal_univ (f g : L0 E μ) : dist f g ≤ μ.real univ := by
  rw [dist_def]
  simpa using integral_mono (integrable_dist_div_one_add_dist f g) (integrable_const (1 : ℝ))
    (fun x ↦ (div_le_one (by positivity)).2 (by linarith [dist_nonneg (x := f x) (y := g x)]))

end FiniteMeasure
end L0
end TauCeti
