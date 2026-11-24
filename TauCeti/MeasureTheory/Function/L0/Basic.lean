/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Defs

/-!
# Random variables with a bounded integral pseudometric

`TauCeti.L0 E μ` is a distinct presentation of the native almost-everywhere quotient
`MeasureTheory.AEEqFun Ω E μ`, for any topological space `E`. When `E` is a pseudometric
space and `μ` is finite, its distance is the integral of `dist f g / (1 + dist f g)`.
This is a metric when `E` is separated. The separate carrier permits these structures without
changing any structures on `AEEqFun` or on the native `Lp` spaces. Constants and continuous
unary and binary post-composition are available for arbitrary topological codomains, and on
finite measure spaces `L0.const μ` is `(μ univ).toNNReal`-Lipschitz with all distances strictly
below `μ.real univ` when `μ ≠ 0`.
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

/-- An inhabited codomain induces an inhabited `L0` space via the default constant class. -/
instance instInhabited [Inhabited E] : Inhabited (L0 E μ) :=
  ⟨⟨default⟩⟩

/-- Over an empty domain, `L0 E μ` is a subsingleton. -/
instance instSubsingleton [IsEmpty Ω] : Subsingleton (L0 E μ) :=
  ⟨fun _ _ ↦ ext (ae_of_all _ isEmptyElim)⟩

/-- When `μ = 0`, `L0 E μ` is a subsingleton. -/
theorem subsingleton_of_measure_zero (hμ : μ = 0) : Subsingleton (L0 E μ) :=
  ⟨fun _ _ ↦ ext (by simp [EventuallyEq, hμ])⟩

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

/-- The random variable represented by a constant function. -/
def const (μ : Measure Ω) (c : E) : L0 E μ := ⟨AEEqFun.const Ω c⟩

/-- Forgetting a constant random variable gives the native constant class. -/
@[simp]
theorem toAEEqFun_const (c : E) : (const μ c).toAEEqFun = AEEqFun.const Ω c := (rfl)

/-- A constant random variable is almost everywhere equal to its constant value. -/
theorem coeFn_const (c : E) : (const μ c : Ω → E) =ᵐ[μ] fun _ ↦ c :=
  AEEqFun.coeFn_const Ω c

/-- On a nonzero measure space, the chosen representative of `const μ c` is identically `c`. -/
theorem coeFn_const_eq [NeZero μ] (c : E) (x : Ω) : const μ c x = c :=
  AEEqFun.coeFn_const_eq Ω c x

/-- Constructing a random variable from a constant function gives `const`. -/
@[simp]
theorem ofFun_const (c : E) : ofFun (fun _ : Ω ↦ c) aestronglyMeasurable_const = const μ c :=
  (rfl)

variable {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]

/-- Apply a continuous map to a random variable. -/
def comp (g : E → F) (hg : Continuous g) (f : L0 E μ) : L0 F μ :=
  ⟨AEEqFun.comp g hg f.toAEEqFun⟩

/-- Forgetting composition gives composition on the native quotient. -/
@[simp]
theorem toAEEqFun_comp (g : E → F) (hg : Continuous g) (f : L0 E μ) :
    (comp g hg f).toAEEqFun = AEEqFun.comp g hg f.toAEEqFun := (rfl)

/-- Composition agrees almost everywhere with composition of representatives. -/
theorem coeFn_comp (g : E → F) (hg : Continuous g) (f : L0 E μ) :
    (comp g hg f : Ω → F) =ᵐ[μ] g ∘ f := AEEqFun.coeFn_comp g hg f.toAEEqFun

/-- Composition commutes with the constructor from a measurable representative. -/
@[simp]
theorem comp_ofFun (g : E → F) (hg : Continuous g) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) :
    comp g hg (ofFun f hf) = ofFun (g ∘ f) (hg.comp_aestronglyMeasurable hf) := (rfl)

/-- Composition with the identity leaves a random variable unchanged. -/
@[simp]
theorem comp_id (f : L0 E μ) : comp id continuous_id f = f := by
  apply toAEEqFun_injective
  exact AEEqFun.comp_id f.toAEEqFun

/-- Iterated continuous composition agrees with composition by the composite map. -/
theorem comp_comp (g : F → G) (g' : E → F) (hg : Continuous g) (hg' : Continuous g')
    (f : L0 E μ) : comp g hg (comp g' hg' f) = comp (g ∘ g') (hg.comp hg') f := by
  apply toAEEqFun_injective
  exact AEEqFun.comp_comp g g' hg hg' f.toAEEqFun

/-- A continuous map sends a constant random variable to its constant value. -/
@[simp]
theorem comp_const (g : E → F) (hg : Continuous g) (c : E) :
    comp g hg (const μ c) = const μ (g c) := by
  apply toAEEqFun_injective
  exact AEEqFun.comp_mk g hg (fun _ : Ω ↦ c) aestronglyMeasurable_const

/-- Apply a continuous function of two variables to random variables. -/
def comp₂ (g : E → F → G) (hg : Continuous (Function.uncurry g))
    (f₁ : L0 E μ) (f₂ : L0 F μ) : L0 G μ :=
  ⟨AEEqFun.comp₂ g hg f₁.toAEEqFun f₂.toAEEqFun⟩

/-- Forgetting binary composition gives binary composition on the native quotient. -/
@[simp]
theorem toAEEqFun_comp₂ (g : E → F → G) (hg : Continuous (Function.uncurry g))
    (f₁ : L0 E μ) (f₂ : L0 F μ) :
    (comp₂ g hg f₁ f₂).toAEEqFun = AEEqFun.comp₂ g hg f₁.toAEEqFun f₂.toAEEqFun := (rfl)

/-- Binary composition agrees almost everywhere with the representative operation. -/
theorem coeFn_comp₂ (g : E → F → G) (hg : Continuous (Function.uncurry g))
    (f₁ : L0 E μ) (f₂ : L0 F μ) :
    (comp₂ g hg f₁ f₂ : Ω → G) =ᵐ[μ] fun x ↦ g (f₁ x) (f₂ x) :=
  AEEqFun.coeFn_comp₂ g hg f₁.toAEEqFun f₂.toAEEqFun

/-- Binary composition commutes with construction from measurable representatives. -/
@[simp]
theorem comp₂_ofFun_ofFun (g : E → F → G) (hg : Continuous (Function.uncurry g))
    (f₁ : Ω → E) (f₂ : Ω → F) (hf₁ : AEStronglyMeasurable f₁ μ)
    (hf₂ : AEStronglyMeasurable f₂ μ) :
    comp₂ g hg (ofFun f₁ hf₁) (ofFun f₂ hf₂) =
      ofFun (fun x ↦ g (f₁ x) (f₂ x)) (hg.comp_aestronglyMeasurable (hf₁.prodMk hf₂)) := (rfl)

/-- A continuous binary map sends constant random variables to its constant value. -/
@[simp]
theorem comp₂_const_const (g : E → F → G) (hg : Continuous (Function.uncurry g))
    (c : E) (d : F) : comp₂ g hg (const μ c) (const μ d) = const μ (g c d) := by
  apply toAEEqFun_injective
  exact AEEqFun.comp₂_mk_mk g hg (fun _ : Ω ↦ c) (fun _ : Ω ↦ d)
    aestronglyMeasurable_const aestronglyMeasurable_const

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

/-- The distance between constant random variables is the bounded target distance
multiplied by the total mass. -/
theorem dist_const (c d : E) :
    dist (const μ c) (const μ d) = μ.real univ * (dist c d / (1 + dist c d)) := by
  rw [← ofFun_const, ← ofFun_const, dist_ofFun]
  simp

/-- Embedding a constant value into `L0 E μ` is `(μ univ).toNNReal`-Lipschitz on a finite
measure space. -/
theorem lipschitzWith_const :
    LipschitzWith (μ univ).toNNReal (const μ : E → L0 E μ) :=
  LipschitzWith.of_dist_le_mul fun a b ↦ by
    rw [dist_const, measureReal_def, ENNReal.toReal]
    exact mul_le_mul_of_nonneg_left
      (div_le_self dist_nonneg (le_add_of_nonneg_right dist_nonneg)) (NNReal.coe_nonneg _)

/-- On the zero measure, every `L⁰` distance is `0`. -/
theorem dist_eq_zero_of_measure_zero (hμ : μ = 0) (f g : L0 E μ) : dist f g = 0 := by
  have := subsingleton_of_measure_zero (E := E) hμ
  rw [Subsingleton.elim f g, dist_self]

/-- Every distance is bounded by the total mass of the finite measure. -/
theorem dist_le_measureReal_univ (f g : L0 E μ) : dist f g ≤ μ.real univ := by
  rw [dist_def]
  simpa using integral_mono (integrable_dist_div_one_add_dist f g) (integrable_const (1 : ℝ))
    (fun x ↦ (div_le_one (by positivity)).2 (by linarith [dist_nonneg (x := f x) (y := g x)]))

/-- On a nonzero finite measure space, the distance between any two elements of `L0 E μ` is
strictly smaller than the total mass `μ.real univ`. -/
theorem dist_lt_measureReal_univ [NeZero μ] (f g : L0 E μ) : dist f g < μ.real univ := by
  refine lt_of_le_of_ne (dist_le_measureReal_univ f g) fun heq ↦ ?_
  have hone : ∫ _ : Ω, (1 : ℝ) ∂μ = μ.real univ := by simp
  rw [dist_def, ← hone, integral_eq_iff_of_ae_le (integrable_dist_div_one_add_dist f g)
    (integrable_const 1) (ae_of_all _ fun _ ↦ div_one_add_le_one dist_nonneg)] at heq
  have hbot : ∀ᵐ _ ∂μ, False :=
    heq.mono fun _ hx ↦ (div_one_add_lt_one dist_nonneg).ne hx
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hbot))

/-- On a probability space, the convergence-in-measure distance is strictly bounded by `1`. -/
theorem dist_lt_one [IsProbabilityMeasure μ] (f g : L0 E μ) : dist f g < 1 := by
  simpa using dist_lt_measureReal_univ f g

end FiniteMeasure

/-- Norm form of the bounded-integral distance on `L0 E μ` when `E` is a seminormed additive
group. -/
theorem dist_eq_integral_norm_div_one_add {E : Type*} [SeminormedAddCommGroup E]
    [IsFiniteMeasure μ] (f g : L0 E μ) :
    dist f g = ∫ x, ‖f x - g x‖ / (1 + ‖f x - g x‖) ∂μ := by
  simp_rw [dist_def, dist_eq_norm]

/-- Absolute-value form of the bounded-integral distance on `L0 ℝ μ`. -/
theorem dist_eq_integral_abs_div_one_add [IsFiniteMeasure μ] (f g : L0 ℝ μ) :
    dist f g = ∫ x, |f x - g x| / (1 + |f x - g x|) ∂μ := by
  simp_rw [dist_def, Real.dist_eq]

end L0
end TauCeti
