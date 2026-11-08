/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Additional lemmas for the Bochner integral

This file records general-purpose lemmas for Bochner integrals, including bridges between
real-valued Bochner integrals and extended-nonnegative Lebesgue integrals, as well as inequalities
for set and probability integrals.

## Continuous additive maps

* `AddMonoidHom.integral_comp_comm` commutes integration with a continuous additive map
  between real Banach spaces.

## Counting measures of multisets

* `Multiset.integrable_sum_map_dirac` and `Multiset.integral_sum_map_dirac`: every function is
  integrable against the counting measure `∑_{x ∈ s} δₓ` of a multiset `s`, with integral the sum
  of its values over `s`. Its measure-level facts are in `TauCeti.MeasureTheory.Measure.Dirac`.

## Measures carried by the roots of a polynomial

* `measure_compl_roots_eq_zero_of_integral_norm_eval_sq_eq_zero`: a measure against which the
  integrable function `|p|²` has integral zero is carried by the roots of the nonzero
  polynomial `p`.

## Positive parts

* `ofReal_integral_le_lintegral_ofReal` bounds the positive part of a real-valued
  function's integral by the integral of its pointwise positive part.
* `lintegral_ofReal_eq_one` gives a probability density (almost everywhere nonnegative, with
  integral one) total extended mass one.
* `ofReal_integral_add_ofReal_integral_le` adds the positive parts of two integrals whose
  integrands sum, almost everywhere, to at most a third integrable function.
* `toReal_lintegral_coe_eq_integral` identifies `(∫⁻ ω, (f ω : ℝ≥0∞) ∂μ).toReal` with
  `∫ ω, (f ω : ℝ) ∂μ` for any almost-everywhere measurable `f : Ω → ℝ≥0`.

## Exponentials

* `integrable_exp_neg_of_ae_nonneg` shows that the negative exponential of an almost-everywhere
  nonnegative function is integrable on a finite measure space.

## Set and probability integrals

* `setIntegral_norm_add_sq_le` integrates the pointwise bound
  `‖g + h‖² ≤ 2 ‖g‖² + 2 ‖h‖²` over a set.
* `setIntegral_norm_sub_sq_le_add_of_le` transfers a square-mean decay estimate from `K` on a
  pair of sets `s ⊆ S` to any `f` close to `K` in square mean on `S`.
* `sq_setIntegral_le_measureReal_mul_setIntegral_sq` is Cauchy--Schwarz for a real-valued set
  integral, in squared form.
* `setIntegral_le_setIntegral_sq_mul_of_eqOn` compares an integral over a set with a weighted
  integral over a larger set, for a weight in `[0, 1]` almost everywhere on the larger set and
  equal to one on the smaller set.
* The set-integral inequality specializes to the second-moment lower bound for a real-valued
  function on a probability space.
* `integral_max_sub_sq_le_mul_measureReal` bounds the integral of the squared truncation
  `((f - l)⁺)²` of a function `f ≤ M` by `(M - l)²` times the measure of `{l ≤ f}`.

## `L¹` convergence

`L¹` convergence is often produced in the Bochner form `∫ ω, ‖f i ω - g ω‖ ∂μ → 0` but consumed
in the seminorm form `eLpNorm (f i - g) 1 μ → 0` (for instance by
`MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`).

* `tendsto_eLpNorm_one_of_tendsto_integral_norm_sub` converts the former into the latter.
* `tendsto_lintegral_enorm_of_tendsto_integral_norm` converts the vanishing of the
  integrals of `‖f j‖` over sets `B j`, for `f j` integrable on `B j`, into that of the lower
  Lebesgue integrals of `‖f j‖ₑ`.

The conversion is `MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm`, whose home is
`Mathlib.MeasureTheory.Integral.Bochner.Basic`, plus continuity of `ENNReal.ofReal` at `0`.

* `tendsto_integral_smul_of_tendsto_lintegral_enorm_sub` turns `L¹(s)` convergence into
  convergence of integrals against an almost everywhere bounded scalar multiplier vanishing
  almost everywhere outside `s`.

## Tail lower bounds

A function on the real line whose norm stays above a positive constant on a set of infinite
measure cannot be integrable there.

* `not_integrableOn_Ioi_of_eventually_le_norm` is the half-line form, and
  `not_integrable_of_eventually_le_atTop` is its real-valued Lebesgue-integrability consequence.
* `not_memLp_of_tendsto_norm_atTop` and `not_memLp_of_tendsto_norm_atBot`: a function whose norm
  tends to infinity at one end of the line lies in no `Lᵖ` with `0 < p < ∞`.

## Reflection across the origin

* `integrable_comp_abs` extends integrability on the positive half-line to an even function on the
  whole real line by reflection.

## Kernel averages on the real line

* `integral_kernel_mem_Icc_of_antitoneOn` squeezes the average of a function against a probability
  density supported in `[-ε, 0]` between the function's values at `t + ε` and `t`, given only
  antitonicity on the sampled interval `[t, t + ε]`.

## Almost-everywhere disjoint finite unions

Mathlib's `MeasureTheory.integral_biUnion_finset` splits an integral over a finite union into a
sum, but asks for genuinely measurable and genuinely disjoint pieces. A family of translates of
a fundamental domain need satisfy neither: they overlap on a null set, and
`MeasureTheory.IsFundamentalDomain` records its pieces as `MeasureTheory.NullMeasurableSet`,
pairwise `MeasureTheory.AEDisjoint`, rather than as disjoint measurable sets.

* `integral_biUnion_finset₀` is the almost-everywhere form, in the `₀` convention of
  `MeasureTheory.lintegral_biUnion_finset₀`.

Adapted from the AINTLIB `LeanModularForms` project,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>, commit
`6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`, Apache-2.0 —
`HeckeRIngs/GL2/AdjointTheory/SummandAdjoint.lean`, `setIntegral_biUnion_finset_ae`, where it is
stated for the same purpose. The name here follows the Mathlib lemma it weakens rather than that
source's.
-/

public section

noncomputable section

open MeasureTheory Filter TopologicalSpace

open scoped ENNReal NNReal Function Topology

/-- Integration commutes with a continuous additive map between real Banach spaces. -/
theorem AddMonoidHom.integral_comp_comm {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure X} (T : E →+ F) (hT : Continuous T) {f : X → E} (hf : Integrable f μ) :
    ∫ x, T (f x) ∂μ = T (∫ x, f x ∂μ) := by
  simpa only [AddMonoidHom.coe_toRealLinearMap] using
    (T.toRealLinearMap hT).integral_comp_comm hf

namespace Multiset

variable {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [NormedAddCommGroup E]

/-- Every function is integrable against the counting measure `∑_{x ∈ s} δₓ` of a multiset. -/
theorem integrable_sum_map_dirac (s : Multiset X) (g : X → E) :
    Integrable g (s.map Measure.dirac).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simpa only [map_cons, sum_cons] using (integrable_dirac enorm_lt_top).add_measure ih

/-- The integral against the counting measure of a multiset is the sum over the multiset. -/
@[simp]
theorem integral_sum_map_dirac [NormedSpace ℝ E] [CompleteSpace E] (s : Multiset X) (g : X → E) :
    ∫ x, g x ∂(s.map Measure.dirac).sum = (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [map_cons, sum_cons]
    rw [integral_add_measure (integrable_dirac enorm_lt_top) (integrable_sum_map_dirac s g),
      integral_dirac, ih]

end Multiset

namespace TauCeti

namespace MeasureTheory

/-- The negative exponential of an almost-everywhere nonnegative, almost-everywhere measurable
function is integrable on a finite measure space. -/
theorem integrable_exp_neg_of_ae_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    Integrable (fun x ↦ Real.exp (-f x)) μ :=
  (integrable_const 1).mono' hf.neg.exp.aestronglyMeasurable <| by
    filter_upwards [hf0] with x hx
    simpa [Real.abs_exp] using hx

/-- An even function obtained by composing with absolute value is integrable on the whole real
line whenever the original function is integrable on the positive half-line. -/
theorem integrable_comp_abs {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntegrableOn f (Set.Ioi 0)) : Integrable fun x : ℝ => f |x| := by
  have hIoi : IntegrableOn (fun x : ℝ => f |x|) (Set.Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have hIic : IntegrableOn (fun x : ℝ => f |x|) (Set.Iic 0) := by
    have hIoi' : IntegrableOn (fun x : ℝ => f |x|) (Set.Ioi (-(0 : ℝ))) := by
      simpa only [neg_zero] using hIoi
    have hIio : IntegrableOn (fun x : ℝ => f |-x|) (Set.Iio 0) :=
      hIoi'.comp_neg_Iio (μ := volume) (c := 0)
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    simpa only [abs_neg] using hIio
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- A function whose norm is eventually at least a positive constant at `atTop` is not integrable
on any right half-line: it is bounded below in norm on a set of infinite measure. -/
theorem not_integrableOn_Ioi_of_eventually_le_norm {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {ε : ℝ} (hε : 0 < ε) (c : ℝ) (hf : ∀ᶠ x in atTop, ε ≤ ‖f x‖) :
    ¬ IntegrableOn f (Set.Ioi c) := by
  intro hint
  obtain ⟨a, ha⟩ := eventually_atTop.mp hf
  have htail : IntegrableOn f (Set.Ioi (max a c)) :=
    hint.mono_set (Set.Ioi_subset_Ioi (le_max_right a c))
  have hconst : IntegrableOn (fun _ : ℝ => ε) (Set.Ioi (max a c)) volume := by
    refine Integrable.mono' htail.norm (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos hε] using ha x ((le_max_left a c).trans hx.le)
  rw [integrableOn_const_iff] at hconst
  simp [Real.volume_Ioi, hε.ne'] at hconst

/-- A real function that is eventually at least a positive constant at `atTop` is not Lebesgue
integrable. -/
theorem not_integrable_of_eventually_le_atTop {f : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ᶠ x in atTop, ε ≤ f x) : ¬ Integrable f volume := fun hint =>
  not_integrableOn_Ioi_of_eventually_le_norm hε 0
    (hf.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx.trans (le_abs_self _))
    hint.integrableOn

/-- A function on the real line whose norm tends to infinity at `+∞` lies in no `Lᵖ` with
`0 < p < ∞`: the integrand `‖f‖ ^ p` is eventually at least `1`. -/
theorem not_memLp_of_tendsto_norm_atTop {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hf : Tendsto (fun x => ‖f x‖) atTop atTop) :
    ¬ MemLp f p volume := fun hmem =>
  not_integrableOn_Ioi_of_eventually_le_norm one_pos 0
    ((hf.eventually_ge_atTop 1).mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.one_le_rpow hx ENNReal.toReal_nonneg)
    (hmem.integrable_norm_rpow hp0 hp).integrableOn

/-- A function on the real line whose norm tends to infinity at `-∞` lies in no `Lᵖ` with
`0 < p < ∞`. -/
theorem not_memLp_of_tendsto_norm_atBot {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hf : Tendsto (fun x => ‖f x‖) atBot atTop) :
    ¬ MemLp f p volume := fun hmem =>
  not_memLp_of_tendsto_norm_atTop hp0 hp (hf.comp tendsto_neg_atTop_atBot)
    (hmem.comp_measurePreserving (Measure.measurePreserving_neg volume))

/-- Integrating `‖g + h‖² ≤ 2 ‖g‖² + 2 ‖h‖²` over a set: if `‖g‖²` and `‖h‖²` are integrable on
`s`, then `∫_s ‖g + h‖² ≤ 2 ∫_s ‖g‖² + 2 ∫_s ‖h‖²`. -/
theorem setIntegral_norm_add_sq_le {X F : Type*} [MeasurableSpace X] {μ : Measure X}
    [SeminormedAddGroup F] {g h : X → F} {s : Set X}
    (hg : IntegrableOn (fun x => ‖g x‖ ^ 2) s μ) (hh : IntegrableOn (fun x => ‖h x‖ ^ 2) s μ) :
    ∫ x in s, ‖g x + h x‖ ^ 2 ∂μ ≤ 2 * ∫ x in s, ‖g x‖ ^ 2 ∂μ + 2 * ∫ x in s, ‖h x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg.const_mul 2) (hh.const_mul 2)]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
    ((hg.const_mul 2).add (hh.const_mul 2)) (ae_of_all _ fun x => ?_)
  have := (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (g x) (h x)) 2).trans add_sq_le
  simpa only [Pi.add_apply, mul_add] using this

/-- **Transferring a square-mean decay estimate.** Let `s ⊆ S`, and suppose that `K` satisfies the
decay estimate `∫_s ‖K - k‖² ≤ D q ∫_S ‖K - c‖²` with `0 ≤ D` and `0 ≤ q ≤ 1`, and that the
constant `b` approximates `f` on `s` at least as well as `k` does. Then `f` inherits the decay of
`K` up to the distance between them:
`∫_s ‖f - b‖² ≤ 4 D q ∫_S ‖f - c‖² + (4 D + 2) ∫_S ‖f - K‖²`.
This is the comparison step of Campanato's method, with `K` a harmonic replacement of `f` and
`b`, `k` the best constants of `f`, `K` on `s`. -/
theorem setIntegral_norm_sub_sq_le_add_of_le {X F : Type*} [MeasurableSpace X] {μ : Measure X}
    [SeminormedAddCommGroup F] {f K : X → F} {s S : Set X} {b k c : F} {D q : ℝ}
    (hsS : s ⊆ S) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hfc : IntegrableOn (fun x => ‖f x - c‖ ^ 2) S μ)
    (hKk : IntegrableOn (fun x => ‖K x - k‖ ^ 2) s μ)
    (hfK : IntegrableOn (fun x => ‖f x - K x‖ ^ 2) S μ)
    (hbest : ∫ x in s, ‖f x - b‖ ^ 2 ∂μ ≤ ∫ x in s, ‖f x - k‖ ^ 2 ∂μ)
    (hdecay : ∫ x in s, ‖K x - k‖ ^ 2 ∂μ ≤ D * q * ∫ x in S, ‖K x - c‖ ^ 2 ∂μ) :
    ∫ x in s, ‖f x - b‖ ^ 2 ∂μ ≤
      4 * D * q * (∫ x in S, ‖f x - c‖ ^ 2 ∂μ) + (4 * D + 2) * ∫ x in S, ‖f x - K x‖ ^ 2 ∂μ := by
  -- On `s`, split `f - k` into `K - k` and `f - K`.
  have h1 : ∫ x in s, ‖f x - k‖ ^ 2 ∂μ ≤
      2 * (∫ x in s, ‖K x - k‖ ^ 2 ∂μ) + 2 * ∫ x in s, ‖f x - K x‖ ^ 2 ∂μ := by
    simpa only [sub_add_sub_cancel'] using setIntegral_norm_add_sq_le hKk (hfK.mono_set hsS)
  -- On `S`, split `K - c` into `f - c` and `K - f`.
  have h2 : ∫ x in S, ‖K x - c‖ ^ 2 ∂μ ≤
      2 * (∫ x in S, ‖f x - c‖ ^ 2 ∂μ) + 2 * ∫ x in S, ‖f x - K x‖ ^ 2 ∂μ := by
    have hKf : IntegrableOn (fun x => ‖K x - f x‖ ^ 2) S μ := by
      simpa only [norm_sub_rev (f _)] using hfK
    simpa only [sub_add_sub_cancel', norm_sub_rev (K _) (f _)] using
      setIntegral_norm_add_sq_le hfc hKf
  have h3 : ∫ x in s, ‖f x - K x‖ ^ 2 ∂μ ≤ ∫ x in S, ‖f x - K x‖ ^ 2 ∂μ :=
    setIntegral_mono_set hfK (ae_of_all _ fun _ => by positivity) hsS.eventuallyLE
  have hE0 : 0 ≤ ∫ x in S, ‖f x - K x‖ ^ 2 ∂μ :=
    setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ => by positivity)
  have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hD hq0)
  have h5 := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hE0 hq1) hD
  linarith

/-- Cauchy--Schwarz for a real-valued set integral over a set of finite measure, in squared form. -/
theorem sq_setIntegral_le_measureReal_mul_setIntegral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (S : Set Ω) (hS_top : μ S ≠ ⊤)
    (hf : IntegrableOn f S μ) (hf_sq : IntegrableOn (fun x => f x ^ 2) S μ) :
    (∫ x in S, f x ∂μ) ^ 2 ≤ μ.real S * ∫ x in S, f x ^ 2 ∂μ := by
  by_cases hS : μ S = 0
  · rw [Measure.restrict_eq_zero.mpr hS]
    simp
  · have hS_pos : 0 < μ.real S := ENNReal.toReal_pos hS hS_top
    have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      Even.convexOn_pow (by norm_num : Even 2)
    have hjensen := hconv.map_set_average_le (continuous_pow 2).continuousOn isClosed_univ
      hS hS_top (ae_of_all _ fun _ => Set.mem_univ _) hf hf_sq
    simp only [setAverage_eq, smul_eq_mul, mul_pow] at hjensen
    have hkey := mul_le_mul_of_nonneg_left hjensen (sq_nonneg (μ.real S))
    field_simp at hkey
    exact hkey

/-- A weight `ψ` with values in `[0, 1]` almost everywhere on `s` that equals one on a measurable
set `t ⊆ s` bounds the integral over `t` of a function nonnegative almost everywhere on `s` by
its `ψ²`-weighted integral over `s`. -/
theorem setIntegral_le_setIntegral_sq_mul_of_eqOn {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s t : Set X} {f ψ : X → ℝ} (hf : IntegrableOn f s μ)
    (hf0 : 0 ≤ᵐ[μ.restrict s] f) (hψ : AEStronglyMeasurable ψ (μ.restrict s))
    (hψ01 : ∀ᵐ x ∂μ.restrict s, ψ x ∈ Set.Icc 0 1)
    (ht : MeasurableSet t) (hψ1 : Set.EqOn ψ 1 t) (hts : t ⊆ s) :
    ∫ x in t, f x ∂μ ≤ ∫ x in s, ψ x ^ 2 * f x ∂μ := by
  have hint : IntegrableOn (fun x => ψ x ^ 2 * f x) s μ :=
    hf.bdd_mul (hψ.pow 2) (c := 1) (by
      filter_upwards [hψ01] with x ⟨h0, h1⟩
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
      exact pow_le_one₀ h0 h1)
  calc
    ∫ x in t, f x ∂μ = ∫ x in t, ψ x ^ 2 * f x ∂μ :=
      setIntegral_congr_fun ht fun x hx => by rw [hψ1 hx, Pi.one_apply, one_pow, one_mul]
    _ ≤ ∫ x in s, ψ x ^ 2 * f x ∂μ :=
      setIntegral_mono_set hint
        (hf0.mono fun x hx => mul_nonneg (sq_nonneg _) hx) hts.eventuallyLE

/-- On a finite measure space where `f ≤ M` almost everywhere, the integral of the squared
truncation `((f - l)⁺)²` is at most `(M - l)²` times the measure of the upper level set
`{l ≤ f}`. In De Giorgi's method this turns a measure estimate for upper level sets into an `L²`
estimate for truncations. -/
theorem integral_max_sub_sq_le_mul_measureReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {l M : ℝ} (hM : ∀ᵐ x ∂μ, f x ≤ M) :
    ∫ x, max (f x - l) 0 ^ 2 ∂μ ≤ (M - l) ^ 2 * μ.real {x | l ≤ f x} := by
  have hS : MeasurableSet {x | l ≤ f x} := measurableSet_le measurable_const hf
  calc ∫ x, max (f x - l) 0 ^ 2 ∂μ
      ≤ ∫ x, {x | l ≤ f x}.indicator (fun _ => (M - l) ^ 2) x ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          ((integrable_const _).indicator hS) ?_
        filter_upwards [hM] with x hx
        by_cases hlx : l ≤ f x
        · rw [Set.indicator_of_mem (by exact hlx)]
          exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (by linarith)) 2
        · rw [Set.indicator_of_notMem (by exact hlx), max_eq_right (by linarith)]
          norm_num
    _ = (M - l) ^ 2 * μ.real {x | l ≤ f x} := by
        rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]

/-- The positive part of the integral of a real-valued function is at most the integral of its
pointwise positive part. No integrability or pointwise sign assumption on `f` is needed. -/
theorem ofReal_integral_le_lintegral_ofReal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hf : Integrable f μ
  · calc
      ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
        ENNReal.ofReal_mono <| integral_mono hf hf.pos_part fun x ↦ le_max_left _ _
      _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part <|
          Filter.Eventually.of_forall fun x ↦ le_max_right (f x) 0
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by simp
  · rw [integral_undef hf]
    simp

/-- A probability density `ρ`, almost everywhere nonnegative with `∫ ρ = 1`, has total extended
mass one: `∫⁻ ofReal (ρ t) dμ = 1`. -/
theorem lintegral_ofReal_eq_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ} (hρ0 : 0 ≤ᵐ[μ] ρ) (hρ1 : ∫ t, ρ t ∂μ = 1) :
    ∫⁻ t, ENNReal.ofReal (ρ t) ∂μ = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one hρ1) hρ0, hρ1,
    ENNReal.ofReal_one]

/-- Positive parts of integrals add up under an almost-everywhere bound: for integrable `F`, `G`,
`N` with `0 ≤ F ≤ N` and `F + G ≤ N` almost everywhere, the positive parts of `∫ F` and `∫ G` sum
to at most the positive part of `∫ N`. The function `G` may take negative values, in which case
`∫ G` may be negative and its positive part is `0`. -/
theorem ofReal_integral_add_ofReal_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F G N : Ω → ℝ} (hF : Integrable F μ) (hG : Integrable G μ) (hN : Integrable N μ)
    (hF0 : 0 ≤ᵐ[μ] F) (hFN : F ≤ᵐ[μ] N) (hFG : ∀ᵐ x ∂μ, F x + G x ≤ N x) :
    ENNReal.ofReal (∫ x, F x ∂μ) + ENNReal.ofReal (∫ x, G x ∂μ) ≤
      ENNReal.ofReal (∫ x, N x ∂μ) := by
  rcases le_total 0 (∫ x, G x ∂μ) with hG0 | hG0
  · rw [← ENNReal.ofReal_add (integral_nonneg_of_ae hF0) hG0, ← integral_add hF hG]
    exact ENNReal.ofReal_le_ofReal (integral_mono_ae (hF.add hG) hN hFG)
  · rw [ENNReal.ofReal_of_nonpos hG0, add_zero]
    exact ENNReal.ofReal_le_ofReal (integral_mono_ae hF hN hFN)

/-- The real value of the extended Lebesgue integral of an almost-everywhere measurable
`ℝ≥0`-valued function equals its Bochner integral. Neither finiteness of the measure nor
integrability is required: when the function is not integrable, both sides vanish. -/
theorem toReal_lintegral_coe_eq_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ≥0} (hf : AEMeasurable f μ) :
    (∫⁻ ω, (f ω : ℝ≥0∞) ∂μ).toReal = ∫ ω, (f ω : ℝ) ∂μ := by
  simpa using (integral_toReal hf.coe_nnreal_ennreal (.of_forall fun _ ↦ ENNReal.coe_lt_top)).symm

/-- **`L¹` convergence in Bochner form is `eLpNorm _ 1` convergence.** If `∫ ‖f i - g‖ → 0` along
`l` and the differences `f i - g` are eventually integrable, then `eLpNorm (f i - g) 1 μ → 0`. -/
theorem tendsto_eLpNorm_one_of_tendsto_integral_norm_sub {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {l : Filter ι} {f : ι → Ω → E} {g : Ω → E}
    (hf : ∀ᶠ i in l, Integrable (f i - g) μ)
    (h : Tendsto (fun i => ∫ ω, ‖f i ω - g ω‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i - g) 1 μ) l (𝓝 0) := by
  refine Tendsto.congr' ?_ (by
    simpa only [ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp h)
  filter_upwards [hf] with i hi
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  simp only [Function.comp_apply, Pi.sub_apply]

/-- If the integrals of `‖f j‖` over the sets `B j` tend to zero, so do the lower Lebesgue
integrals of `‖f j‖ₑ`. -/
theorem tendsto_lintegral_enorm_of_tendsto_integral_norm {α E ι : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α} {l : Filter ι} {f : ι → α → E} {B : ι → Set α}
    (hf : ∀ j, IntegrableOn (f j) (B j) μ)
    (h : Tendsto (fun j ↦ ∫ x in B j, ‖f j x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun j ↦ ∫⁻ x in B j, ‖f j x‖ₑ ∂μ) l (𝓝 0) := by
  refine (ENNReal.tendsto_ofReal h).congr' (.of_forall fun j ↦ ?_) |>.trans ?_
  · exact ofReal_integral_norm_eq_lintegral_enorm (hf j)
  · rw [ENNReal.ofReal_zero]

/-- If `a i → b` in `L¹(s)`, then the integrals `∫ x, c x • a i x ∂μ` converge to
`∫ x, c x • b x ∂μ` for an almost everywhere bounded scalar multiplier `c` vanishing
almost everywhere outside `s`.
The approximating pairings need only be eventually integrable, and the limiting pairing
needs only to be almost everywhere strongly measurable. -/
theorem tendsto_integral_smul_of_tendsto_lintegral_enorm_sub {α 𝕜 F ι : Type*}
    [MeasurableSpace α] [NormedField 𝕜] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace 𝕜 F] {μ : Measure α} {s : Set α} {l : Filter ι}
    {c : α → 𝕜} {K : ℝ}
    (hK : ∀ᵐ x ∂μ, ‖c x‖ ≤ K) (hcsupp : ∀ᵐ x ∂μ, x ∉ s → c x = 0)
    {a : ι → α → F} {b : α → F} (ha : ∀ᶠ i in l, Integrable (fun x => c x • a i x) μ)
    (hb : AEStronglyMeasurable (fun x => c x • b x) μ)
    (hab : Tendsto (fun i => ∫⁻ x in s, ‖a i x - b x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, c x • a i x ∂μ) l (𝓝 (∫ x, c x • b x ∂μ)) := by
  refine tendsto_integral_of_L1 (fun x => c x • b x) hb ha ?_
  have hlim : Tendsto (fun i => ENNReal.ofReal K * ∫⁻ x in s, ‖a i x - b x‖ₑ ∂μ) l
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hab
      (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun i => ?_
  calc ∫⁻ x, ‖c x • a i x - c x • b x‖ₑ ∂μ
      ≤ ∫⁻ x, s.indicator (fun x => ENNReal.ofReal K * ‖a i x - b x‖ₑ) x ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hK, hcsupp] with x hxK hxsupp
        rw [← smul_sub]
        by_cases hxs : x ∈ s
        · rw [Set.indicator_of_mem hxs, enorm_smul]
          gcongr
          simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hxK
        · simp [Set.indicator_of_notMem hxs, hxsupp hxs]
    _ ≤ ∫⁻ x in s, ENNReal.ofReal K * ‖a i x - b x‖ₑ ∂μ :=
        lintegral_indicator_le _ _
    _ = ENNReal.ofReal K * ∫⁻ x in s, ‖a i x - b x‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Averaging against a kernel supported in `[-ε, 0]` samples only `[t, t + ε]`.** If `ψ` is a
nonnegative probability density with respect to `μ` vanishing outside `[-ε, 0]`, and `F` is antitone
on `[t, t + ε]`, then the average `∫ s, ψ s * F (t - s) ∂μ` lies between `F (t + ε)` and `F t`.

Use this to bound a mollification of a monotone function by two of its values. No separate
integrability hypotheses or sign assumption on `ε` are needed. -/
theorem integral_kernel_mem_Icc_of_antitoneOn {μ : Measure ℝ} {ψ F : ℝ → ℝ} {ε t : ℝ}
    (hFanti : AntitoneOn F (Set.Icc t (t + ε))) (hψ0 : ∀ s, 0 ≤ ψ s)
    (hψint : ∫ s, ψ s ∂μ = 1)
    (hsupp : ∀ s : ℝ, ψ s ≠ 0 → s ∈ Set.Icc (-ε) 0) :
    (∫ s, ψ s * F (t - s) ∂μ) ∈ Set.Icc (F (t + ε)) (F t) := by
  have hψi : Integrable ψ μ := integrable_of_integral_eq_one hψint
  have hε : 0 ≤ ε := by
    obtain ⟨s, hs⟩ := exists_ne_zero_of_integral_ne_zero (hψint ▸ one_ne_zero)
    have := hsupp s hs
    linarith [this.1, this.2]
  have hmass : ∀ c : ℝ, ∫ s, ψ s * c ∂μ = c := by
    intro c
    rw [integral_mul_const, hψint, one_mul]
  have hsample : ∀ s : ℝ, -ε ≤ s → s ≤ 0 → t - s ∈ Set.Icc t (t + ε) := fun s h1 h2 =>
    ⟨by linarith, by linarith⟩
  have hlo : t ∈ Set.Icc t (t + ε) := ⟨le_rfl, by linarith⟩
  have hhi : t + ε ∈ Set.Icc t (t + ε) := ⟨by linarith, le_rfl⟩
  have hbounds (s : ℝ) : ψ s * F (t + ε) ≤ ψ s * F (t - s) ∧
      ψ s * F (t - s) ≤ ψ s * F t := by
    by_cases hs : ψ s = 0
    · simp [hs]
    obtain ⟨hs1, hs2⟩ := hsupp s hs
    exact ⟨mul_le_mul_of_nonneg_left
      (hFanti (hsample s hs1 hs2) hhi (by linarith)) (hψ0 s),
      mul_le_mul_of_nonneg_left (hFanti hlo (hsample s hs1 hs2) (by linarith)) (hψ0 s)⟩
  -- Monotonicity gives measurability on the sampled interval. Cutting off outside it
  -- does not change the weighted integrand, which lies between two integrable functions.
  have hmono : MonotoneOn (fun s => F (t - s)) (Set.Icc (-ε) 0) := by
    intro x hx y hy hxy
    exact hFanti (hsample y hy.1 hy.2) (hsample x hx.1 hx.2) (by linarith)
  have hmeas :=
    (aemeasurable_restrict_of_monotoneOn (μ := μ) measurableSet_Icc hmono).aestronglyMeasurable
  have hprod : AEStronglyMeasurable (fun s => ψ s * F (t - s)) μ := by
    refine (hψi.aestronglyMeasurable.mul
      ((aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hmeas)).congr
        (ae_of_all μ fun s => ?_)
    by_cases hs : ψ s = 0
    · simp [hs]
    · simp only [Pi.mul_apply, Set.indicator_of_mem (hsupp s hs)]
  have hintF := integrable_of_le_of_le hprod (ae_of_all μ fun s => (hbounds s).1)
    (ae_of_all μ fun s => (hbounds s).2) (hψi.mul_const _) (hψi.mul_const _)
  constructor
  · rw [← hmass (F (t + ε))]
    exact integral_mono (hψi.mul_const _) hintF fun s => (hbounds s).1
  · rw [← hmass (F t)]
    exact integral_mono hintF (hψi.mul_const _) fun s => (hbounds s).2

/-- **A Bochner integral over a finite almost-everywhere disjoint union splits as a sum.**

The almost-everywhere counterpart of `MeasureTheory.integral_biUnion_finset`, which asks for
genuinely measurable and genuinely disjoint pieces: here the pieces need only be
`MeasureTheory.NullMeasurableSet` and pairwise `MeasureTheory.AEDisjoint`, which is what
`MeasureTheory.IsFundamentalDomain` supplies for a family of translates of a fundamental domain.

Integrability is asked for once, on the union, rather than on each piece. The two are equivalent
— `MeasureTheory.integrableOn_finset_iUnion` — and the union is the form
`MeasureTheory.integral_iUnion_ae` consumes. -/
theorem integral_biUnion_finset₀ {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure X} {f : X → E} (s : Finset ι) {t : ι → Set X}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : ∀ i ∈ s, NullMeasurableSet (t i) μ)
    (hf : IntegrableOn f (⋃ i ∈ s, t i) μ) :
    ∫ x in ⋃ i ∈ s, t i, f x ∂μ = ∑ i ∈ s, ∫ x in t i, f x ∂μ := by
  have hcoe : (⋃ i ∈ s, t i) = ⋃ i : (↑s : Set ι), t (i : ι) := by
    simp only [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  rw [hcoe] at hf ⊢
  rw [integral_iUnion_ae (s := fun i : (↑s : Set ι) ↦ t (i : ι))
    (fun i ↦ hm (i : ι) i.2) (hd.subtype _ _) hf]
  exact Finset.tsum_subtype' s fun i ↦ ∫ x in t i, f x ∂μ

open Polynomial in
/-- A measure against which the integrable function `|p|²` has integral zero is carried by the
roots of the nonzero polynomial `p`. -/
theorem measure_compl_roots_eq_zero_of_integral_norm_eval_sq_eq_zero {𝕜 : Type*} [NormedField 𝕜]
    [DecidableEq 𝕜] [MeasurableSpace 𝕜] {ρ : Measure 𝕜} {p : 𝕜[X]} (hp : p ≠ 0)
    (hint : Integrable (fun w ↦ ‖p.eval w‖ ^ 2) ρ) (h : ∫ w, ‖p.eval w‖ ^ 2 ∂ρ = 0) :
    ρ (↑p.roots.toFinset)ᶜ = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun w ↦ by positivity) hint).1 h
  refine measure_mono_null (fun w hw ↦ ?_) (ae_iff.1 hae)
  have hw' : p.eval w ≠ 0 := fun h0 ↦ hw (by simp [mem_roots hp, h0])
  simpa using hw'

end MeasureTheory

end TauCeti
