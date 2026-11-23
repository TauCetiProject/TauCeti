/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Sets.Opens
public import TauCeti.MeasureTheory.Function.Lp.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Norm inequalities in `Lᵖ` spaces

This file contains norm estimates for `Lᵖ` functions derived from almost-everywhere pointwise
bounds.

## Main declarations

* `MeasureTheory.Lp.normLp`: the pointwise norm `x ↦ ‖f x‖` bundled as an element of `Lp ℝ p μ`.
* `MeasureTheory.Lp.norm_le_add_of_ae_norm_le`: an `Lᵖ` norm bound from pointwise domination by a
  two-term linear combination.
* `MeasureTheory.Lp.ofReal_norm_add_mul_norm` and `MeasureTheory.memLp_of_eLpNorm_add_mul_ne_top`:
  the cost `‖g‖ + t ‖h‖` of a pair of `Lᵖ` functions in terms of `eLpNorm`, and a pair of
  functions of finite cost `‖f₀‖_{p₀} + t ‖f₁‖_{p₁}`, `t > 0`, lies in `L^{p₀} × L^{p₁}`.
* `MeasureTheory.MemLp.monotoneOn_setIntegral_ball_inter_norm_sq`: for `g ∈ L²(U)`, the `L²` mass
  of `g` on `ball z t ∩ H` is nondecreasing in the radius while the ball stays inside `U`.
* `MeasureTheory.L1.norm_eq_integral_of_nonneg`: the norm of a nonnegative real `L¹` function is
  its integral.
* `MeasureTheory.Lp.integral_norm_rpow_eq_norm_rpow`: for `0 < p < ∞`, the integral of the `p`-th
  power of the pointwise norm of an `Lᵖ` function is the `p`-th power of its `Lᵖ` norm.
* `MeasureTheory.Lp.integral_norm_sq_eq_norm_sq`: the integral of the squared pointwise
  norm of an `L²` function is its squared `L²` norm.
* `MeasureTheory.Lp.integral_norm_mul_norm_le`: Cauchy–Schwarz, `∫ ‖f‖ ‖g‖ ≤ ‖f‖₂ ‖g‖₂` for
  `L²` functions.
* `MeasureTheory.MemLp.norm_toLp_sq`: the same for the class of a square-integrable function.
* `MeasureTheory.integral_norm_sq_eq_toReal_eLpNorm_sq`: the integral of the squared pointwise
  norm of any a.e. strongly measurable function is its squared `L²` seminorm, as a real number.
* `MeasureTheory.MemLp.eLpNorm_two_eq_ofReal_sqrt_integral`: the `L²` seminorm of a
  square-integrable function is the square root of the integral of its squared norm.
* `MeasureTheory.tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub`: L² convergence implies
  convergence of the integral of the squared norm.
* `MeasureTheory.integral_norm_sq_le_three_mul`: `∫ ‖f₁ + f₂ + f₃‖² ≤ 3 (∫ ‖f₁‖² + ∫ ‖f₂‖² +
  ∫ ‖f₃‖²)` for `f₁, f₂, f₃ ∈ L²`.
* `MeasureTheory.integral_norm_sq_le_sq_mul_of_norm_le`: `‖f‖ ≤ c ‖g‖` almost everywhere gives
  `∫ ‖f‖² ≤ c² ∫ ‖g‖²`, and `MeasureTheory.memLp_clm_apply_and_integral_norm_sq_le` is its instance
  for operators bounded by `c` applied to `f`.
* `LipschitzWith.tendsto_integral_norm_sub_sq`: if `∫ ‖f i - g‖² → 0` with integrable integrands,
  then the Bochner integrals `∫ ‖T (f i) - T g‖²` tend to `0` for Lipschitz `T`.
* `MeasureTheory.lpNorm_congr_ae`: the `Lᵖ` norm of a function depends only on its almost
  everywhere class.
* `MeasureTheory.Lp.norm_eq_lpNorm_of_ae_eq`: the norm of an element of `Lᵖ(ν)` is the `Lᵖ` norm of
  any representative.
* `MeasureTheory.Lp.memLp_of_restrict_coe_opens_top` and
  `MeasureTheory.Lp.norm_eq_lpNorm_of_restrict_coe_opens_top`: an element of `Lᵖ` over the whole
  space, written as the top open set, is an `Lᵖ` function for the measure itself, with the same
  norm.
* `MeasureTheory.lpNorm_le_norm_of_ae_eq_of_le`: for `ν ≤ ν'`, the `Lᵖ(ν)` norm of a
  representative of an element of `Lᵖ(ν')` is at most its norm.
* `MeasureTheory.Lp.ae_norm_le_norm_top` and `MeasureTheory.Lp.norm_top_le_of_ae_bound`: an `L∞`
  function is bounded almost everywhere by its norm, and an almost everywhere bound bounds the
  norm, for any measure.
* `MeasureTheory.Lp.norm_toLp_memLp_top_const_le`: the `L∞` class of a constant `c` has norm at
  most `‖c‖`.
* `MeasureTheory.Lp.norm_le_norm_top_of_ae_eq_of_continuousAt`: when the measure is positive on
  open sets, a representative of an `L∞` class is bounded by its norm at every point where it is
  continuous.
* `MeasureTheory.Lp.ae_eq_max_min_norm_top`: a representative of a real `L∞` class agrees almost
  everywhere with its truncation to `[-‖f‖, ‖f‖]`.
* `MeasureTheory.Lp.measure_lt_norm_ne_zero`: every level strictly below the `L∞` norm is
  exceeded on a set of nonzero measure.
* `MeasureTheory.Lp.exists_measurableSet_mul_norm_lt_norm_apply_measure_lt_top`: on a σ-finite
  measure space, every nonnegative level strictly below the `L∞` norm of an operator-valued
  function is witnessed at a single vector on a measurable set of positive finite measure.
* `MeasureTheory.Lp.integral_norm_le_mul_norm`: on a finite measure space, the `L¹` norm of an
  `Lᵖ` function, `1 ≤ p`, is at most `μ(univ)^{1 - 1/p}` times its `Lᵖ` norm.
* `MeasureTheory.MemLp.integral_norm_le_mul_eLpNorm`: the same bound for a function in `Lᵖ`.
* `MeasureTheory.Lp.norm_integral_le_of_ae_norm_le_mul`: the resulting bound on the integral of a
  function dominated pointwise by a multiple of the norm of an `Lᵖ` function.
* `MeasureTheory.Lp.setIntegral_norm_sq_le_norm_sq`: so its integral over a subset of the set it
  lives on is at most its squared `L²` norm.
* `MeasureTheory.MemLp.norm_toLp_le_of_ae_bound`: on a finite measure space, a function in `Lᵖ`
  bounded almost everywhere in norm by `C ≥ 0` has `Lᵖ` norm at most
  `measureUnivNNReal μ ^ p.toReal⁻¹ * C`.
* `MeasureTheory.MemLp.norm_toLp_le_of_eLpNorm_le`: an `eLpNorm` bound `‖g‖_p ≤ B ‖u‖_p` against
  a representative `u` of `v ∈ Lᵖ` is the norm bound `‖g‖ ≤ B ‖v‖`.
* `TauCeti.Lp.isBounded_range_of_ae_bound` and `TauCeti.isBounded_range_toLp_of_ae_bound`: on a
  finite measure space, a family in `Lᵖ` (`1 ≤ p`) with a uniform almost-everywhere pointwise norm
  bound has bounded range.
* `MeasureTheory.MemLp.norm_toLp_le_measureReal_rpow_mul`: on a set `s` of finite measure, a
  function bounded by `M` has `Lᵖ(s)` norm at most `μ(s)^{1/p} M`, `1 ≤ p < ∞`.
* `MeasureTheory.memLp_and_eLpNorm_le_of_norm_le_add`: a function vanishing off a measurable set
  `s` and dominated there by `c₁ ‖g₁‖ + c₂ ‖g₂‖` with `g₁, g₂ ∈ Lʳ(s)` lies in `Lʳ`, with the
  matching norm bound.
* `MeasureTheory.Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion`: classes in `Lᵖ` on finitely many
  sets with a common representative glue to a class on any set they cover, with norm at most the
  sum of their norms.
* `MeasureTheory.Lp.norm_le_mul_norm_of_ae_eq_smul`: multiplying an `Lᵖ` class by a function
  bounded by `C` multiplies its norm by at most `C`.
* `MeasureTheory.MemLp.eLpNorm_rpow_toReal_eq_enorm_integral`: for `0 < q < ∞`, the `q`-th power of
  the `L^q` norm of `f` is the norm of the integral of `‖f‖ ^ q`.
* `MeasureTheory.memLp_top_inv_of_ae_le_norm` and
  `MeasureTheory.memLp_top_inv_sub_of_ae_le_norm_sub`: an almost-everywhere strongly measurable
  function into a normed division ring bounded away from zero (or from a scalar `z`) almost
  everywhere has essentially bounded reciprocal (`MemLp · ∞ μ`).
-/

public section

namespace MeasureTheory.Lp

open scoped ENNReal

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

/-- Pointwise norm `x ↦ ‖f x‖` bundled as an element of `Lp ℝ p μ`. -/
noncomputable def normLp [NormedAddCommGroup E] (f : Lp E p μ) : Lp ℝ p μ :=
  (Lp.memLp f).norm.toLp fun x ↦ ‖f x‖

/-- `Lp.normLp f` equals `x ↦ ‖f x‖` almost everywhere. -/
theorem coeFn_normLp [NormedAddCommGroup E] (f : Lp E p μ) :
    normLp f =ᵐ[μ] fun x ↦ ‖f x‖ :=
  (Lp.memLp f).norm.coeFn_toLp

/-- `Lp.normLp f` is nonnegative in `Lp ℝ p μ`. -/
@[simp]
theorem normLp_nonneg [NormedAddCommGroup E] (f : Lp E p μ) : 0 ≤ normLp f := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_normLp f] with x hx
  rw [Pi.zero_apply, hx]
  exact norm_nonneg _

/-- Taking `Lp.normLp` preserves the `Lᵖ` norm. -/
@[simp]
theorem norm_normLp [NormedAddCommGroup E] (f : Lp E p μ) : ‖normLp f‖ = ‖f‖ := by
  rw [normLp, Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), ← Lp.norm_def]

/-- On `Lp ℝ p μ`, `Lp.normLp` agrees with the lattice absolute value `|f|`. -/
@[simp]
theorem normLp_real_eq_abs (f : Lp ℝ p μ) : normLp f = |f| := by
  refine Lp.ext ?_
  filter_upwards [coeFn_normLp f, Lp.coeFn_abs f] with x h₁ h₂
  rw [h₁, h₂, Real.norm_eq_abs]

/-- `Lp.normLp` sends `0` to `0`. -/
@[simp]
theorem normLp_zero [NormedAddCommGroup E] : normLp (0 : Lp E p μ) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_normLp (0 : Lp E p μ), Lp.coeFn_zero E p μ,
    Lp.coeFn_zero ℝ p μ] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  simp

/-- `Lp.normLp f` vanishes if and only if `f` vanishes. -/
@[simp]
theorem normLp_eq_zero [NormedAddCommGroup E] (f : Lp E p μ) : normLp f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ Lp.ext ?_, fun h ↦ h ▸ normLp_zero⟩
  filter_upwards [coeFn_normLp f, Lp.ext_iff.mp h, Lp.coeFn_zero ℝ p μ,
    Lp.coeFn_zero E p μ] with x h₁ h₂ h₃ h₄
  rw [h₄, Pi.zero_apply]
  exact norm_eq_zero.mp (by rw [← h₁, h₂, h₃, Pi.zero_apply])

/-- `Lp.normLp` is invariant under negation. -/
@[simp]
theorem normLp_neg [NormedAddCommGroup E] (f : Lp E p μ) : normLp (-f) = normLp f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_normLp (-f), Lp.coeFn_neg f, coeFn_normLp f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  simp

/-- `Lp.normLp` is invariant under the pointwise `star` involution. -/
@[simp]
theorem normLp_star [NormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]
    (f : Lp E p μ) : normLp (star f) = normLp f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_normLp (star f), Lp.coeFn_star f, coeFn_normLp f] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- Taking `Lp.normLp` after `Lp.ofRealLI` gives `|f|`. -/
@[simp]
theorem normLp_ofRealLI {𝕜 : Type*} [RCLike 𝕜] [Fact (1 ≤ p)] (f : Lp ℝ p μ) :
    normLp (ofRealLI 𝕜 p μ f) = |f| := by
  refine Lp.ext ?_
  filter_upwards [coeFn_normLp (ofRealLI 𝕜 p μ f), coeFn_ofRealLI (𝕜 := 𝕜) f,
    Lp.coeFn_abs f] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- `Lp.normLp` pulls scalar multiplication out as multiplication by `‖c‖`. -/
@[simp]
theorem normLp_smul {𝕜 : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [NormSMulClass 𝕜 E] (c : 𝕜) (f : Lp E p μ) :
    normLp (c • f) = ‖c‖ • normLp f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_normLp (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul ‖c‖ (normLp f), coeFn_normLp f] with x h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄, norm_smul]

end MeasureTheory.Lp

namespace TauCeti

open MeasureTheory
open scoped ENNReal NNReal

/-- On a finite measure space, a family in `Lᵖ` (`1 ≤ p`) with a uniform almost-everywhere
pointwise norm bound has bounded range. -/
theorem Lp.isBounded_range_of_ae_bound {ι : Sort*} {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : ι → Lp E p μ} {C : ℝ} (hfC : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C) :
    Bornology.IsBounded (Set.range f) :=
  isBounded_iff_forall_norm_le.2 ⟨measureUnivNNReal μ ^ p.toReal⁻¹ * max C 0,
    Set.forall_mem_range.2 fun i ↦ Lp.norm_le_of_ae_bound (le_max_right C 0)
      ((hfC i).mono fun _ hx ↦ hx.trans (le_max_left C 0))⟩

/-- On a finite measure space, a family of `Lᵖ` functions (`1 ≤ p`) with a uniform
almost-everywhere pointwise norm bound defines a bounded subset of `Lᵖ`. -/
theorem isBounded_range_toLp_of_ae_bound {ι : Sort*} {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : ι → α → E} (hf : ∀ i, MemLp (f i) p μ) {C : ℝ} (hfC : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C) :
    Bornology.IsBounded (Set.range fun i ↦ (hf i).toLp (f i)) :=
  Lp.isBounded_range_of_ae_bound fun i ↦
    (hf i).coeFn_toLp.mp ((hfC i).mono fun _ hx hxy ↦ hxy ▸ hx)

end TauCeti

namespace MeasureTheory

open Filter
open scoped ENNReal NNReal Topology

/-- The norm of an `Lᵖ` function dominated pointwise by a two-term combination of two other
`Lᵖ` functions obeys the same bound in norm. -/
theorem Lp.norm_le_add_of_ae_norm_le {alpha F G H : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H] {m : Measure alpha}
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : Lp F q m} {g : Lp G q m} {h : Lp H q m} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hle : ∀ᵐ z ∂m, ‖f z‖ ≤ a * ‖g z‖ + b * ‖h z‖) :
    ‖f‖ ≤ a * ‖g‖ + b * ‖h‖ := by
  calc ‖f‖ ≤ ‖a • Lp.normLp g + b • Lp.normLp h‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [hle, Lp.coeFn_normLp g, Lp.coeFn_normLp h,
          Lp.coeFn_add (a • Lp.normLp g) (b • Lp.normLp h),
          Lp.coeFn_smul a (Lp.normLp g), Lp.coeFn_smul b (Lp.normLp h)]
          with z hz hA hB hadd hsA hsB
        simp only [hadd, Pi.add_apply, hsA, hsB, Pi.smul_apply, smul_eq_mul, hA, hB]
        exact hz.trans (Real.le_norm_self _)
    _ ≤ ‖a • Lp.normLp g‖ + ‖b • Lp.normLp h‖ := norm_add_le _ _
    _ = a * ‖g‖ + b * ‖h‖ := by
        simp only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, Lp.norm_normLp]

/-- The `Lᵖ` norm of a function depends only on its almost everywhere class. -/
theorem lpNorm_congr_ae {alpha F : Type*} [MeasurableSpace alpha] [NormedAddCommGroup F]
    {ν : Measure alpha} {p : ℝ≥0∞} {f g : alpha → F} (h : f =ᵐ[ν] g) :
    lpNorm f p ν = lpNorm g p ν := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae h]

/-- The norm of an element of `Lᵖ(ν)` is the `Lᵖ` norm of any of its representatives. -/
theorem Lp.norm_eq_lpNorm_of_ae_eq {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {ν : Measure alpha} {p : ℝ≥0∞} {f : Lp F p ν} {g : alpha → F}
    (h : f =ᵐ[ν] g) : ‖f‖ = lpNorm g p ν := by
  rw [← lpNorm_congr_ae h, Lp.norm_def, toReal_eLpNorm]

/-- An element of `Lᵖ` over the whole space, written as the top open set, is an `Lᵖ` function for
the measure itself. -/
theorem Lp.memLp_of_restrict_coe_opens_top {alpha F : Type*} [MeasurableSpace alpha]
    [TopologicalSpace alpha] [NormedAddCommGroup F] {ν : Measure alpha} {p : ℝ≥0∞}
    (f : Lp F p (ν.restrict ((⊤ : TopologicalSpace.Opens alpha) : Set alpha))) :
    MemLp f p ν :=
  (congrArg (fun μ => MemLp f p μ) (Measure.restrict_coe_opens_top ν)).mp (Lp.memLp f)

/-- The norm of an element of `Lᵖ` over the whole space, written as the top open set, is its `Lᵖ`
norm for the measure itself. -/
theorem Lp.norm_eq_lpNorm_of_restrict_coe_opens_top {alpha F : Type*} [MeasurableSpace alpha]
    [TopologicalSpace alpha] [NormedAddCommGroup F] {ν : Measure alpha} {p : ℝ≥0∞}
    (f : Lp F p (ν.restrict ((⊤ : TopologicalSpace.Opens alpha) : Set alpha))) :
    ‖f‖ = lpNorm f p ν :=
  (Lp.norm_eq_lpNorm_of_ae_eq EventuallyEq.rfl).trans
    (congrArg (lpNorm f p) (Measure.restrict_coe_opens_top ν))

/-- The `Lᵖ(ν)` norm of a function agreeing `ν`-almost everywhere with an element of `Lᵖ(ν')`, for
`ν ≤ ν'`, is at most the norm of that element. -/
theorem lpNorm_le_norm_of_ae_eq_of_le {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {ν ν' : Measure alpha} {p : ℝ≥0∞} {f : alpha → F} {g : Lp F p ν'}
    (hν : ν ≤ ν') (h : f =ᵐ[ν] g) : lpNorm f p ν ≤ ‖g‖ := by
  rw [lpNorm_congr_ae h, ← toReal_eLpNorm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_measure _ hν)

/-- An `L∞` function is bounded almost everywhere by its norm. -/
theorem Lp.ae_norm_le_norm_top {alpha F : Type*} [MeasurableSpace alpha] [NormedAddCommGroup F]
    {m : Measure alpha} (f : Lp F ∞ m) : ∀ᵐ x ∂m, ‖f x‖ ≤ ‖f‖ := by
  simpa [Lp.norm_def, toReal_eLpNorm] using ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- If the measure is positive on nonempty open sets, a representative of an `L∞` class is
bounded by its norm at every point where it is continuous. -/
theorem Lp.norm_le_norm_top_of_ae_eq_of_continuousAt {alpha F : Type*} [TopologicalSpace alpha]
    [MeasurableSpace alpha] [NormedAddCommGroup F] {m : Measure alpha} [m.IsOpenPosMeasure]
    {f : Lp F ∞ m} {g : alpha → F} (hfg : f =ᵐ[m] g) {x : alpha} (hg : ContinuousAt g x) :
    ‖g x‖ ≤ ‖f‖ := by
  by_contra! h
  -- The points near `x` where `‖g‖` exceeds `‖f‖` form a set of positive but null measure.
  have hae : ∀ᵐ y ∂m, ¬‖f‖ < ‖g y‖ := by
    filter_upwards [hfg, Lp.ae_norm_le_norm_top f] with y hy h
    exact not_lt_of_ge (hy ▸ h)
  exact (m.measure_pos_of_mem_nhds (hg.norm.eventually (lt_mem_nhds h))).ne'
    (measure_eq_zero_iff_ae_notMem.2 hae)

/-- An almost everywhere bound on an `L∞` function bounds its norm, whatever the measure. Compare
`MeasureTheory.Lp.norm_le_of_ae_bound`, which needs a finite measure. -/
theorem Lp.norm_top_le_of_ae_bound {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {m : Measure alpha} {f : Lp F ∞ m} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᵐ x ∂m, ‖f x‖ ≤ c) : ‖f‖ ≤ c := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_le_of_le_ofReal hc (eLpNormEssSup_le_of_ae_bound h)

/-- The `L∞` class of the constant function `c` has norm at most `‖c‖`, whatever the measure. -/
theorem Lp.norm_toLp_memLp_top_const_le {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {m : Measure alpha} (c : F) :
    ‖(memLp_top_const (μ := m) c).toLp _‖ ≤ ‖c‖ := by
  refine Lp.norm_top_le_of_ae_bound (norm_nonneg c) ?_
  filter_upwards [(memLp_top_const (μ := m) c).coeFn_toLp] with x hx
  rw [hx]

/-- A representative `g` of a real `L∞` class `f` agrees almost everywhere with its truncation to
`[-‖f‖, ‖f‖]`. The truncation is bounded everywhere by `‖f‖` (`TauCeti.abs_max_min_le`). -/
theorem Lp.ae_eq_max_min_norm_top {alpha : Type*} [MeasurableSpace alpha] {m : Measure alpha}
    {f : Lp ℝ ∞ m} {g : alpha → ℝ} (hg : f =ᵐ[m] g) :
    g =ᵐ[m] fun x => max (-‖f‖) (min ‖f‖ (g x)) := by
  filter_upwards [hg, Lp.ae_norm_le_norm_top f] with x h hx
  rw [h, Real.norm_eq_abs, abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Every nonnegative level strictly below the `L∞` norm of `f` is exceeded by `‖f‖` on a set
of nonzero measure. -/
theorem Lp.measure_lt_norm_ne_zero {alpha F : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup F] {m : Measure alpha} {f : Lp F ∞ m} {c : ℝ} (hc_nonneg : 0 ≤ c)
    (hc : c < ‖f‖) : m {x | c < ‖f x‖} ≠ 0 := by
  intro hms
  have hae : ∀ᵐ x ∂m, ‖f x‖ ≤ c :=
    (measure_eq_zero_iff_ae_notMem.mp hms).mono fun x hx ↦ le_of_not_gt hx
  exact (not_lt_of_ge (Lp.norm_top_le_of_ae_bound hc_nonneg hae)) hc

/-- The norm of a nonnegative real `L¹` function is its integral. -/
theorem L1.norm_eq_integral_of_nonneg {alpha : Type*} [MeasurableSpace alpha] {m : Measure alpha}
    {f : Lp ℝ 1 m} (hf : 0 ≤ f) : ‖f‖ = ∫ x, f x ∂m := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (((Lp.coeFn_nonneg f).2 hf).mono fun x hx => Real.norm_of_nonneg hx)

/-- For `0 < p < ∞`, the integral of the `p`-th power of the pointwise norm of an `Lᵖ` function
is the `p`-th power of its `Lᵖ` norm. -/
theorem Lp.integral_norm_rpow_eq_norm_rpow {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (f : Lp F p m) :
    ∫ x, ‖f x‖ ^ p.toReal ∂m = ‖f‖ ^ p.toReal := by
  have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂m :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal hp0 hp (Lp.aestronglyMeasurable f),
    ← Real.rpow_mul h_nonneg, inv_mul_cancel₀ (ENNReal.toReal_pos hp0 hp).ne', Real.rpow_one]

/-- The integral of the squared pointwise norm of an `L²` function is its squared `L²` norm. -/
theorem Lp.integral_norm_sq_eq_norm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] (f : Lp F 2 m) :
    ∫ x, ‖f x‖ ^ 2 ∂m = ‖f‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    Lp.integral_norm_rpow_eq_norm_rpow (by norm_num) (by norm_num) f

/-- **Cauchy–Schwarz for `L²` functions.** For `f, g ∈ L²`, possibly with different codomains,
`∫ ‖f‖ ‖g‖ ≤ ‖f‖₂ ‖g‖₂`. -/
theorem Lp.integral_norm_mul_norm_le {alpha E F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup E] [NormedAddCommGroup F] (f : Lp E 2 m)
    (g : Lp F 2 m) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂m ≤ ‖f‖ * ‖g‖ := by
  have hf : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (2 : ℝ)) m := by
    simpa using (Lp.memLp f).norm
  have hg : MemLp (fun x => ‖g x‖) (ENNReal.ofReal (2 : ℝ)) m := by
    simpa using (Lp.memLp g).norm
  simpa only [norm_norm, Real.rpow_two, ← Real.sqrt_eq_rpow, Lp.integral_norm_sq_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_norm] using
    integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf hg

/-- The `L²` seminorm of a square-integrable function is the square root of the integral of its
squared pointwise norm. -/
theorem MemLp.eLpNorm_two_eq_ofReal_sqrt_integral {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] {f : alpha → F} (hf : MemLp f 2 m) :
    eLpNorm f 2 m = ENNReal.ofReal √(∫ x, ‖f x‖ ^ 2 ∂m) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div]

/-- The squared `L²` norm of the class of a square-integrable function is the integral of its
squared pointwise norm. -/
theorem MemLp.norm_toLp_sq {alpha F : Type*} [MeasurableSpace alpha] {m : Measure alpha}
    [NormedAddCommGroup F] {f : alpha → F} (hf : MemLp f 2 m) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂m := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- The integral of the squared pointwise norm of an a.e. strongly measurable function is the
square of the real part of its `L²` seminorm. Both sides vanish when the function is not square
integrable. -/
theorem integral_norm_sq_eq_toReal_eLpNorm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [SeminormedAddGroup F] {f : alpha → F} (hf : AEStronglyMeasurable f m) :
    ∫ x, ‖f x‖ ^ 2 ∂m = (eLpNorm f 2 m).toReal ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _)
      ((continuous_norm.comp_aestronglyMeasurable hf).pow 2),
    ← ENNReal.toReal_pow, TauCeti.eLpNorm_two_sq_eq_lintegral hf]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- L² convergence implies convergence of the integral of the squared norm, for any measure
and any normed additive group of values. -/
theorem tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub {α F ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α} {f : α → F}
    {g : ι → α → F} {l : Filter ι} (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (ht : Tendsto (fun i ↦ eLpNorm (g i - f) 2 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, ‖g i x‖ ^ 2 ∂μ) l (𝓝 (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  have hLp : Tendsto (fun i ↦ (hg i).toLp (g i)) l (𝓝 (hf.toLp f)) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp] using ht
  simpa only [MemLp.norm_toLp_sq] using hLp.norm.pow 2

/-- If `f = f₁ + f₂ + f₃` almost everywhere with `f₁, f₂, f₃ ∈ L²`, then
`∫ ‖f‖² ≤ 3 (∫ ‖f₁‖² + ∫ ‖f₂‖² + ∫ ‖f₃‖²)`. -/
theorem integral_norm_sq_le_three_mul {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f f₁ f₂ f₃ : α → E} (h₁ : MemLp f₁ 2 μ) (h₂ : MemLp f₂ 2 μ)
    (h₃ : MemLp f₃ 2 μ) (hf : ∀ᵐ x ∂μ, f x = f₁ x + f₂ x + f₃ x) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤
      3 * (∫ x, ‖f₁ x‖ ^ 2 ∂μ + ∫ x, ‖f₂ x‖ ^ 2 ∂μ + ∫ x, ‖f₃ x‖ ^ 2 ∂μ) := by
  have i₁ := (memLp_two_iff_integrable_sq_norm h₁.aestronglyMeasurable).1 h₁
  have i₂ := (memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).1 h₂
  have i₃ := (memLp_two_iff_integrable_sq_norm h₃.aestronglyMeasurable).1 h₃
  have e : ∫ x, 3 * (‖f₁ x‖ ^ 2 + ‖f₂ x‖ ^ 2 + ‖f₃ x‖ ^ 2) ∂μ =
      3 * (∫ x, ‖f₁ x‖ ^ 2 ∂μ + ∫ x, ‖f₂ x‖ ^ 2 ∂μ + ∫ x, ‖f₃ x‖ ^ 2 ∂μ) := by
    have i₁₂ : Integrable (fun x ↦ ‖f₁ x‖ ^ 2 + ‖f₂ x‖ ^ 2) μ := i₁.add i₂
    rw [integral_const_mul, integral_add i₁₂ i₃, integral_add i₁ i₂]
  rw [← e]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity)
    (((i₁.add i₂).add i₃).const_mul 3) ?_
  filter_upwards [hf] with x hx
  simpa only [hx] using TauCeti.norm_add_add_sq_le_three_mul (f₁ x) (f₂ x) (f₃ x)

/-- If `‖f‖ ≤ c ‖g‖` almost everywhere with `f, g ∈ L²`, then `∫ ‖f‖² ≤ c² ∫ ‖g‖²`. -/
theorem integral_norm_sq_le_sq_mul_of_norm_le {α E F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : α → F}
    {c : ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hle : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ c ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_ae ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf)
    (((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg).const_mul _) ?_
  filter_upwards [hle] with x hx
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

/-- Applying continuous linear maps `B x` with `‖B x‖ ≤ c` almost everywhere to `f ∈ L²` gives
`x ↦ B x (f x) ∈ L²`, with `∫ ‖B x (f x)‖² ≤ c² ∫ ‖f‖²`. -/
theorem memLp_clm_apply_and_integral_norm_sq_le {α 𝕜 E F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {B : α → E →L[𝕜] F} {f : α → E} {c : ℝ}
    (hB : AEStronglyMeasurable B μ) (hc : ∀ᵐ x ∂μ, ‖B x‖ ≤ c) (hf : MemLp f 2 μ) :
    MemLp (fun x ↦ B x (f x)) 2 μ ∧ ∫ x, ‖B x (f x)‖ ^ 2 ∂μ ≤ c ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hle : ∀ᵐ x ∂μ, ‖B x (f x)‖ ≤ c * ‖f x‖ := by
    filter_upwards [hc] with x hx
    exact ((B x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hm : MemLp (fun x ↦ B x (f x)) 2 μ :=
    hf.of_le_mul ((isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := E) (F := F)).continuous
      |>.comp_aestronglyMeasurable (hB.prodMk hf.aestronglyMeasurable)) hle
  exact ⟨hm, integral_norm_sq_le_sq_mul_of_norm_le hm hf hle⟩

/-- **Lipschitz maps and mean-square integrals.** If `T` is Lipschitz, `‖f i - g‖²` is
eventually integrable and `∫ ‖f i - g‖² → 0` along `l`, then the Bochner integrals
`∫ ‖T (f i) - T g‖²` tend to `0`.

The transformed integrands are not asserted to be integrable: they are dominated by
`K² ‖f i - g‖²`, so they are integrable whenever they are a.e. strongly measurable (for instance
when every `f i` and `g` is), and only then does the conclusion express convergence of
`T ∘ f i` to `T ∘ g` in `L²`; a non-integrable integrand gives the junk value `0` instead. -/
theorem _root_.LipschitzWith.tendsto_integral_norm_sub_sq {α ι E F : Type*} [MeasurableSpace α]
    {μ : Measure α} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {K : ℝ≥0} {T : E → F}
    (hT : LipschitzWith K T) {l : Filter ι} {f : ι → α → E} {g : α → E}
    (hint : ∀ᶠ i in l, Integrable (fun x ↦ ‖f i x - g x‖ ^ 2) μ)
    (h : Tendsto (fun i ↦ ∫ x, ‖f i x - g x‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, ‖T (f i x) - T (g x)‖ ^ 2 ∂μ) l (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun i ↦ integral_nonneg fun _ ↦ by positivity) ?_
    (by simpa using h.const_mul ((K : ℝ) ^ 2))
  filter_upwards [hint] with i hi
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity) (hi.const_mul _)
    (ae_of_all _ fun x ↦ ?_)
  simp only [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hT.norm_sub_le _ _) 2

/-- On a finite measure space, the `L¹` norm of an `Lᵖ` function, `1 ≤ p`, is at most
`μ(univ)^{1 - 1/p}` times its `Lᵖ` norm. -/
theorem Lp.integral_norm_le_mul_norm {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [IsFiniteMeasure m] [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp F p m) :
    ∫ x, ‖f x‖ ∂m ≤ (m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := by
  have hexp := ENNReal.one_sub_one_div_toReal_nonneg (Fact.out : 1 ≤ p)
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := p) (μ := m) Fact.out
    (Lp.aestronglyMeasurable f)
  rw [ENNReal.toReal_one, div_one] at h
  rw [integral_norm_eq_lintegral_eNorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f), Lp.norm_def, mul_comm,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
    (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top m _))) h

/-- On a finite measure space, the `L¹` norm of a function in `Lᵖ`, `1 ≤ p`, is at most
`μ(univ)^{1 - 1/p}` times its `Lᵖ` norm. This is `MeasureTheory.Lp.integral_norm_le_mul_norm`
for a representative. -/
theorem MemLp.integral_norm_le_mul_eLpNorm {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [IsFiniteMeasure m] [NormedAddCommGroup F] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : alpha → F} (hf : MemLp f p m) :
    ∫ x, ‖f x‖ ∂m ≤ (m Set.univ ^ (1 - 1 / p.toReal)).toReal * (eLpNorm f p m).toReal := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have h := Lp.integral_norm_le_mul_norm (hf.toLp f)
  rwa [integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by rw [hx]), Lp.norm_toLp] at h

/-- On a finite measure space, a function dominated pointwise by `K ‖f‖` for an `Lᵖ` function
`f`, `1 ≤ p`, has norm of its integral at most `K μ(univ)^{1 - 1/p} ‖f‖`. -/
theorem Lp.norm_integral_le_of_ae_norm_le_mul {alpha F G : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [IsFiniteMeasure m] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp F p m) {g : alpha → G} {K : ℝ}
    (hg : ∀ᵐ x ∂m, ‖g x‖ ≤ K * ‖f x‖) :
    ‖∫ x, g x ∂m‖ ≤ K * (m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := by
  rcases le_or_gt 0 K with hK | hK
  · calc ‖∫ x, g x ∂m‖ ≤ ∫ x, K * ‖f x‖ ∂m :=
          norm_integral_le_of_norm_le (((Lp.memLp f).integrable Fact.out).norm.const_mul K) hg
      _ = K * ∫ x, ‖f x‖ ∂m := integral_const_mul _ _
      _ ≤ K * ((m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖) := by
          gcongr
          exact Lp.integral_norm_le_mul_norm f
      _ = K * (m Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := (mul_assoc _ _ _).symm
  · -- a negative constant forces `f` and `g` to vanish almost everywhere
    have hf : ∀ᵐ x ∂m, ‖f x‖ = 0 := hg.mono fun x hx ↦ by
      nlinarith [norm_nonneg (g x), norm_nonneg (f x)]
    have hf0 : ‖f‖ = 0 := by
      rw [norm_eq_zero, Lp.eq_zero_iff_ae_eq_zero]
      exact hf.mono fun x hx ↦ norm_eq_zero.1 hx
    have hg0 : ∀ᵐ x ∂m, g x = 0 := hg.mp (hf.mono fun x hx hgx ↦ by
      rw [hx, mul_zero] at hgx
      exact norm_le_zero_iff.1 hgx)
    rw [hf0, mul_zero, integral_eq_zero_of_ae hg0]
    simp

/-- For an `L²` function `f` on `t`, the integral of `‖f‖²` over a subset `s ⊆ t` is at most the
squared `L²` norm of `f`. -/
theorem Lp.setIntegral_norm_sq_le_norm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] {s t : Set alpha} (f : Lp F 2 (m.restrict t))
    (hst : s ⊆ t) : ∫ x in s, ‖f x‖ ^ 2 ∂m ≤ ‖f‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  exact setIntegral_mono_set ((Lp.memLp f).integrable_norm_pow two_ne_zero)
    (ae_of_all _ fun _ => by positivity) hst.eventuallySubset

/-- On a finite measure space, a function in `Lᵖ` bounded almost everywhere in norm by `C ≥ 0` has
`Lᵖ` norm at most `measureUnivNNReal μ ^ p.toReal⁻¹ * C`. -/
theorem MemLp.norm_toLp_le_of_ae_bound {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} {f : α → E} (hf : MemLp f p μ) {C : ℝ}
    (hC : 0 ≤ C) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C :=
  Lp.norm_le_of_ae_bound hC (hf.coeFn_toLp.mp (hfC.mono fun _ hx hxy ↦ hxy ▸ hx))

/-- The cost `‖g‖ + t ‖h‖` of a pair of `Lᵖ` functions, `t ≥ 0`, in terms of `eLpNorm`. -/
theorem Lp.ofReal_norm_add_mul_norm {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p q : ℝ≥0∞} (g : Lp E p μ) (h : Lp E q μ) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (‖g‖ + t * ‖h‖) = eLpNorm g p μ + ENNReal.ofReal t * eLpNorm h q μ := by
  rw [Lp.norm_def, Lp.norm_def, ENNReal.ofReal_add ENNReal.toReal_nonneg
    (mul_nonneg ht ENNReal.toReal_nonneg), ENNReal.ofReal_mul ht,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g), ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h)]

/-- A splitting of finite cost `‖f₀‖_{p₀} + t ‖f₁‖_{p₁}`, with `t > 0`, is a pair of `L^{p₀}` and
`L^{p₁}` functions. -/
theorem memLp_of_eLpNorm_add_mul_ne_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p₀ p₁ : ℝ≥0∞} {f₀ f₁ : α → E} {t : ℝ} (ht : 0 < t)
    (hfin : eLpNorm f₀ p₀ μ + ENNReal.ofReal t * eLpNorm f₁ p₁ μ ≠ ∞) :
    MemLp f₀ p₀ μ ∧ MemLp f₁ p₁ μ := by
  obtain ⟨hfin₀, hfin₁⟩ := ENNReal.add_ne_top.1 hfin
  refine ⟨memLp_iff.2 hfin₀.lt_top, memLp_iff.2 (lt_top_iff_ne_top.2 fun htop => hfin₁ ?_)⟩
  rw [htop, ENNReal.mul_top (by simpa using ht)]

/-- An `eLpNorm` bound `‖g‖_p ≤ B ‖u‖_p`, with `u` a representative of `v ∈ Lᵖ`, is the norm
bound `‖g‖ ≤ B ‖v‖` in `Lᵖ`. -/
theorem MemLp.norm_toLp_le_of_eLpNorm_le {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ : Measure α} {p : ℝ≥0∞} {g : α → F}
    (hg : MemLp g p μ) {u : α → E} {v : Lp E p μ} (hv : u =ᵐ[μ] v) {B : ℝ≥0}
    (h : eLpNorm g p μ ≤ B * eLpNorm u p μ) : ‖hg.toLp g‖ ≤ B * ‖v‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, ← eLpNorm_congr_ae hv, ← ENNReal.coe_toReal,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    ((eLpNorm_congr_ae hv).trans_ne (Lp.eLpNorm_ne_top v))) h

section Restrict

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F] {g : X → F}
  {s t : Set X}

/-- For a function `g` in `L²(U)` and `ball z R ⊆ U`, the `L²` mass `∫_{B(z, t) ∩ H} ‖g‖²` is
nondecreasing in the radius `t ≤ R`, for any set `H`. -/
theorem MemLp.monotoneOn_setIntegral_ball_inter_norm_sq [PseudoMetricSpace X] {U H : Set X}
    {z : X} {R : ℝ} (hg : MemLp g 2 (μ.restrict U)) (hball : Metric.ball z R ⊆ U) :
    MonotoneOn (fun t => ∫ x in Metric.ball z t ∩ H, ‖g x‖ ^ 2 ∂μ) (Set.Iic R) :=
  fun _ _ t ht hst => setIntegral_mono_set
    ((hg.mono_measure (Measure.restrict_mono (Set.inter_subset_left.trans
      ((Metric.ball_subset_ball ht).trans hball)) le_rfl)).integrable_norm_pow two_ne_zero)
    (ae_of_all _ fun _ => by positivity)
    (Set.inter_subset_inter_left _ (Metric.ball_subset_ball hst)).eventuallySubset

/-- On a set `s` of finite measure, a function in `Lᵖ(s)`, `1 ≤ p < ∞`, bounded almost
everywhere on `s` by `M` has `Lᵖ(s)` norm at most `μ(s)^{1/p} M`. Unlike
`MeasureTheory.Lp.norm_le_of_ae_bound`, no sign condition on `M` is needed. -/
theorem MemLp.norm_toLp_le_measureReal_rpow_mul {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hs : μ s ≠ ⊤) (hg : MemLp g p (μ.restrict s)) {M : ℝ}
    (hgM : ∀ᵐ x ∂μ.restrict s, ‖g x‖ ≤ M) :
    ‖hg.toLp g‖ ≤ μ.real s ^ p.toReal⁻¹ * M := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · -- On a null set both sides vanish.
    have hp0 : p.toReal⁻¹ ≠ 0 :=
      inv_ne_zero (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp).ne'
    rw [Lp.norm_toLp, Measure.restrict_eq_zero.2 h0, eLpNorm_measure_zero, measureReal_def, h0,
      ENNReal.toReal_zero, Real.zero_rpow hp0, zero_mul]
  · -- Otherwise the bound holds at some point, so `0 ≤ M`.
    have : (ae (μ.restrict s)).NeBot := ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
    obtain ⟨x, hx⟩ := hgM.exists
    have h := hg.norm_toLp_le_of_ae_bound ((norm_nonneg _).trans hx) hgM
    rwa [← measureReal_restrict_apply_univ]

/-- **Gluing `Lᵖ` classes along a finite cover.** For `1 ≤ p`, let finitely many sets `u i` cover
`s`. If each `f i ∈ Lᵖ(u i)` agrees almost everywhere on `u i` with one function `g`, then some
class in `Lᵖ(s)` agrees almost everywhere on `s` with `g` and has norm at most `∑ᵢ ‖f i‖`. -/
theorem Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion {ι : Type*} [Fintype ι] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u : ι → Set X} (hs : s ⊆ ⋃ i, u i) (f : ∀ i, Lp F p (μ.restrict (u i)))
    (hf : ∀ i, f i =ᵐ[μ.restrict (u i)] g) :
    ∃ G : Lp F p (μ.restrict s), G =ᵐ[μ.restrict s] g ∧ ‖G‖ ≤ ∑ i, ‖f i‖ := by
  have hg : ∀ i, MemLp g p (μ.restrict (u i)) := fun i => (Lp.memLp (f i)).ae_eq (hf i)
  have hgs := MemLp.restrict_of_subset_iUnion hs hg
  refine ⟨hgs.toLp g, hgs.coeFn_toLp, ?_⟩
  have hfi : ∀ i, ‖f i‖ = (eLpNorm g p (μ.restrict (u i))).toReal :=
    fun i => by rw [Lp.norm_def, eLpNorm_congr_ae (hf i)]
  rw [Lp.norm_toLp]
  simp only [hfi]
  rw [← ENNReal.toReal_sum fun i _ => (hg i).eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => (hg i).eLpNorm_ne_top)
    (eLpNorm_restrict_le_sum_of_subset_iUnion g Fact.out hs)

/-- An `Lʳ` bound for a function vanishing off a measurable set `s`: if `‖f‖ ≤ c₁ ‖g₁‖ + c₂ ‖g₂‖`
on `s` with `c₁, c₂ ≥ 0` and `g₁, g₂ ∈ Lʳ(s)`, then `f ∈ Lʳ` with
`‖f‖_r ≤ c₁ ‖g₁‖_{r,s} + c₂ ‖g₂‖_{r,s}`. -/
theorem memLp_and_eLpNorm_le_of_norm_le_add {G₁ G₂ : Type*} [NormedAddCommGroup G₁]
    [NormedAddCommGroup G₂] (hs : MeasurableSet s) {r : ℝ≥0∞} (hr : 1 ≤ r) {f : X → F}
    {g₁ : X → G₁} {g₂ : X → G₂} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (hf0 : ∀ x ∉ s, f x = 0)
    (hg₁ : MemLp g₁ r (μ.restrict s)) (hg₂ : MemLp g₂ r (μ.restrict s))
    (hfg : ∀ x ∈ s, ‖f x‖ ≤ c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖) :
    MemLp f r μ ∧ eLpNorm f r μ ≤
      ENNReal.ofReal c₁ * eLpNorm g₁ r (μ.restrict s) +
        ENNReal.ofReal c₂ * eLpNorm g₂ r (μ.restrict s) := by
  have hsupp : Function.support f ⊆ s := fun x hx => by_contra fun h => hx (hf0 x h)
  have hg : MemLp (fun x => c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖) r (μ.restrict s) :=
    (hg₁.norm.const_mul c₁).add (hg₂.norm.const_mul c₂)
  have hle : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ ‖c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖‖ :=
    ae_restrict_of_forall_mem hs fun x hx => (hfg x hx).trans (Real.le_norm_self _)
  have hfs : MemLp f r (μ.restrict s) := hg.of_le hf hle
  refine ⟨by simpa only [Set.indicator_eq_self.2 hsupp] using
    (memLp_indicator_iff_restrict hs.nullMeasurableSet).2 hfs, ?_⟩
  have hfm : AEStronglyMeasurable f μ := by
    simpa only [Set.indicator_eq_self.2 hsupp] using
      (aestronglyMeasurable_indicator_iff hs).2 hf
  rw [← eLpNorm_restrict_eq_of_support_subset hfm hsupp]
  exact TauCeti.eLpNorm_le_mul_add_mul_of_ae_norm_le hr hf hg₁.aestronglyMeasurable
    hg₂.aestronglyMeasurable (A := c₁.toNNReal) (B := c₂.toNNReal)
    (ae_restrict_of_forall_mem hs fun x hx => by
      simpa only [Real.coe_toNNReal _ hc₁, Real.coe_toNNReal _ hc₂] using hfg x hx)

end Restrict

section Smul

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]

/-- **Multiplication by a bounded function.** If `‖ψ‖ ≤ C` almost everywhere and `v = ψ • u`
almost everywhere for `u, v ∈ Lᵖ`, then `‖v‖ ≤ C ‖u‖`. -/
theorem Lp.norm_le_mul_norm_of_ae_eq_smul {𝕜 : Type*} [SeminormedAddGroup 𝕜] [SMulZeroClass 𝕜 F]
    [IsBoundedSMul 𝕜 F] {p : ℝ≥0∞} {ψ : X → 𝕜} {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C)
    {u v : Lp F p μ} (hv : v =ᵐ[μ] fun x ↦ ψ x • u x) :
    ‖v‖ ≤ C * ‖u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [hv, hC] with x hx hCx
  rw [hx]
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right hCx (norm_nonneg _))

end Smul

section IntegralRpow

variable {α 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

/-- For `0 < q < ∞`, the `q`-th power of the `L^q` norm of `f` is the norm of the integral of
`‖f‖ ^ q`. -/
theorem MemLp.eLpNorm_rpow_toReal_eq_enorm_integral {V : Type*} [NormedAddCommGroup V]
    {f : α → V} {q : ℝ≥0∞} (hf : MemLp f q μ) (hq0 : q ≠ 0) (hq : q ≠ ∞) :
    eLpNorm f q μ ^ q.toReal = ‖∫ x, ((‖f x‖ ^ q.toReal : ℝ) : 𝕜) ∂μ‖ₑ := by
  have hr := ENNReal.toReal_pos hq0 hq
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ q.toReal ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [hf.eLpNorm_eq_integral_rpow_norm hq0 hq, ENNReal.ofReal_rpow_of_nonneg
    (Real.rpow_nonneg hI _) hr.le, Real.rpow_inv_rpow hI hr.ne', integral_ofReal, ← ofReal_norm,
    RCLike.norm_ofReal, abs_of_nonneg hI]

end IntegralRpow

section OperatorNorm
variable {α 𝕜 E F : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a σ-finite measure space, every nonnegative `c < ‖A‖` is witnessed by a single vector
`u : E` and a measurable set `t` with `0 < μ t < ∞` on which `c * ‖u‖ < ‖A x u‖`. -/
theorem Lp.exists_measurableSet_mul_norm_lt_norm_apply_measure_lt_top [SigmaFinite μ]
    (A : Lp (E →L[𝕜] F) ∞ μ) {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt : c < ‖A‖) :
    ∃ (u : E) (t : Set α), MeasurableSet t ∧ (∀ x ∈ t, c * ‖u‖ < ‖A x u‖) ∧ 0 < μ t ∧ μ t < ∞ := by
  obtain ⟨C, hC_count, hC_sub⟩ := (Lp.stronglyMeasurable A).isSeparable_range
  set δ := (‖A‖ - c) / 3 with hδ_def
  have hδ : 0 < δ := by linarith [hδ_def]
  set S : Set (E →L[𝕜] F) := {B ∈ C | c + δ < ‖B‖}
  have : Countable S := (hC_count.mono (Set.sep_subset _ _)).to_subtype
  choose u hu using fun B : S ↦ show ∃ u : E, (c + δ) * ‖u‖ < ‖(B : E →L[𝕜] F) u‖ by
    by_contra! h; exact (not_le_of_gt B.property.2) ((B : E →L[𝕜] F).opNorm_le_bound
        (by linarith) h)
  have hcover : {x | c + 2 * δ < ‖A x‖} ⊆ ⋃ B : S, {x | c * ‖u B‖ < ‖A x (u B)‖} := fun x hx ↦ by
    obtain ⟨B, hBC, hdist⟩ := Metric.mem_closure_iff.mp (hC_sub ⟨x, rfl⟩) δ hδ
    rw [dist_comm, _root_.dist_eq_norm] at hdist
    have hBS : B ∈ S := ⟨hBC, by
      have := norm_sub_le B (B - A x); rw [sub_sub_cancel] at this; linarith [Set.mem_ofPred.mp hx]⟩
    set v := u ⟨B, hBS⟩
    have htri : ‖B v‖ ≤ ‖(B - A x) v‖ + ‖A x v‖ := by
      simpa only [sub_apply, sub_add_cancel] using norm_add_le ((B - A x) v) (A x v)
    have hle := ((B - A x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hdist.le (norm_nonneg _))
    exact Set.mem_iUnion.mpr ⟨⟨B, hBS⟩, Set.mem_ofPred.mpr (by nlinarith [hu ⟨B, hBS⟩])⟩
  have hμ_union : μ (⋃ B : S, {x | c * ‖u B‖ < ‖A x (u B)‖}) ≠ 0 :=
    mt (measure_mono_null hcover) (Lp.measure_lt_norm_ne_zero (by linarith) (by linarith [hδ_def]))
  obtain ⟨B, hμs⟩ : ∃ B : S, μ {x | c * ‖u B‖ < ‖A x (u B)‖} ≠ 0 := by
    by_contra! hzero; exact hμ_union (measure_iUnion_null hzero)
  have hs : MeasurableSet {x | c * ‖u B‖ < ‖A x (u B)‖} := measurableSet_lt measurable_const
    (((ContinuousLinearMap.apply 𝕜 F (u B)).continuous.norm.comp_stronglyMeasurable
      (Lp.stronglyMeasurable A)).measurable)
  obtain ⟨t, ht, hts, h1, h2⟩ := Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  exact ⟨u B, t, ht, hts, h1, h2⟩

end OperatorNorm
section Inv

variable {α 𝕜 : Type*} [MeasurableSpace α] [NormedDivisionRing 𝕜] {μ : Measure α}

/-- If an almost-everywhere strongly measurable function `f : α → 𝕜` into a normed division ring
satisfies `ε ≤ ‖f x‖` almost everywhere for some `ε > 0`, then its pointwise inverse `x ↦ (f x)⁻¹`
is essentially bounded (`MemLp · ∞ μ`). -/
theorem memLp_top_inv_of_ae_le_norm {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) {ε : ℝ}
    (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x‖) :
    MemLp (fun x ↦ (f x)⁻¹) ∞ μ := by
  refine memLp_top_of_bound hf.inv₀ ε⁻¹ ?_
  filter_upwards [hbound] with x hx
  rw [norm_inv]
  exact inv_anti₀ hε hx

/-- If an almost-everywhere strongly measurable function `f : α → 𝕜` into a normed division ring
satisfies `ε ≤ ‖f x - z‖` almost everywhere for some `ε > 0`, then `x ↦ (z - f x)⁻¹` is
essentially bounded (`MemLp · ∞ μ`). -/
theorem memLp_top_inv_sub_of_ae_le_norm_sub {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) {z : 𝕜}
    {ε : ℝ} (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    MemLp (fun x ↦ (z - f x)⁻¹) ∞ μ :=
  memLp_top_inv_of_ae_le_norm (aestronglyMeasurable_const.sub hf) hε
    (hbound.mono fun x hx ↦ norm_sub_rev (f x) z ▸ hx)

end Inv

end MeasureTheory
