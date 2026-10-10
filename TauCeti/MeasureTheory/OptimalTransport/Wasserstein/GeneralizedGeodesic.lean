/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CompleteSquare
public import TauCeti.MeasureTheory.OptimalTransport.Gluing
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic

/-!
# Generalized geodesics in the Wasserstein space

The squared quadratic Wasserstein distance `ν ↦ W₂ (μ, ν) ^ 2` from a fixed law `μ` is in general
not convex along the Wasserstein geodesics of `ℝ²`; along them it satisfies the reverse,
semiconcavity inequality instead. It is, however, convex along a different family of curves
joining two laws `ν₀` and `ν₁`, the
*generalized geodesics based at `μ`*. These are built from a single measure `γ` on `X × X × X`,
read as the joint law of a triple `(x, y₀, y₁)`, whose projection to `(x, y₀)` is an optimal
coupling of `μ` and `ν₀` and whose projection to `(x, y₁)` is an optimal coupling of `μ` and `ν₁`
(`TauCeti.IsGeneralizedGeodesicPlan`). Such a three-plan exists on every Polish metric space, by
gluing two optimal couplings along their common first marginal
(`TauCeti.exists_isGeneralizedGeodesicPlan`). In a real inner product space the generalized
geodesic of `γ` is the curve of laws of `(1 - t) • y₀ + t • y₁` under `γ`
(`TauCeti.generalizedGeodesic`), which runs from `ν₀` at `t = 0` to `ν₁` at `t = 1`.

Along it, for `t ∈ [0, 1]`,

`W₂ (μ, ν_t) ^ 2 + t (1 - t) ∫ ‖y₀ - y₁‖ ^ 2 dγ ≤ (1 - t) W₂ (μ, ν₀) ^ 2 + t W₂ (μ, ν₁) ^ 2`,

and since `γ` projects to a coupling of `ν₀` and `ν₁`, the integral may be replaced by the smaller
`W₂ (ν₀, ν₁) ^ 2`: the function `ν ↦ W₂ (μ, ν) ^ 2 / 2` is `1`-convex along generalized geodesics
based at `μ`. The reason is the pointwise Hilbert identity
`‖x - ((1 - t) a + t b)‖ ^ 2 + t (1 - t) ‖a - b‖ ^ 2 = (1 - t) ‖x - a‖ ^ 2 + t ‖x - b‖ ^ 2`,
integrated against `γ`, together with the coupling of `μ` and `ν_t` that `γ` provides. All
statements are inequalities in `[0, ∞]` and need no moment hypotheses.

This convexity is the estimate on which the theory of minimizing movements in the quadratic
Wasserstein space rests: it makes the penalized functional of each implicit Euler step strictly
convex along the generalized geodesics based at the previous step, which is what yields uniqueness
of the step and the discrete energy estimates.

## Main definitions

* `TauCeti.IsGeneralizedGeodesicPlan p γ μ ν₀ ν₁`: the measure `γ` on `X × X × X` projects to
  `p`-optimal couplings of `μ` with `ν₀` and of `μ` with `ν₁`.
* `TauCeti.generalizedGeodesic γ t`: the law of `(1 - t) • y₀ + t • y₁` under `γ`.

## Main statements

* `TauCeti.exists_isGeneralizedGeodesicPlan`: on a Polish metric space, every finite base measure
  `μ` and two measures coupled with it carry such a three-plan, for every nonzero exponent.
* `TauCeti.IsGeneralizedGeodesicPlan.generalizedGeodesic_zero` and
  `TauCeti.IsGeneralizedGeodesicPlan.generalizedGeodesic_one`: the generalized geodesic runs from
  `ν₀` to `ν₁`.
* `TauCeti.wassersteinEDist_generalizedGeodesic_sq_add_le`: the convexity inequality for an
  arbitrary three-plan with first marginal `μ`, against the three transport integrals of the plan.
* `TauCeti.IsGeneralizedGeodesicPlan.wassersteinEDist_sq_add_le` and
  `TauCeti.IsGeneralizedGeodesicPlan.wassersteinEDist_sq_add_wassersteinEDist_sq_le`: the
  convexity of `ν ↦ W₂ (μ, ν) ^ 2` along generalized geodesics based at `μ`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §7.3 for the semiconcavity along geodesics,
  §9.1 for the failure of convexity, and §9.2, Lemma 9.2.1 and Definition 9.2.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §7.3.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section ThreePlan

variable {X : Type*} [MeasurableSpace X] [EDist X] {p : ℝ≥0∞} {γ : Measure (X × X × X)}
  {μ ν₀ ν₁ : Measure X}

/-- A measure `γ` on `X × X × X`, read as the joint law of a triple `(x, y₀, y₁)`, is a
*generalized-geodesic plan* from `ν₀` to `ν₁` based at `μ` for the exponent `p` if its projection
to `(x, y₀)` is a coupling of `μ` and `ν₀` realizing `W_p (μ, ν₀)`, and its projection to
`(x, y₁)` is a coupling of `μ` and `ν₁` realizing `W_p (μ, ν₁)`. -/
structure IsGeneralizedGeodesicPlan (p : ℝ≥0∞) (γ : Measure (X × X × X))
    (μ ν₀ ν₁ : Measure X) : Prop where
  /-- The projection to the first two coordinates couples `μ` and `ν₀`. -/
  isCoupling_left : IsCoupling (γ.map (Prod.map id Prod.fst)) μ ν₀
  /-- The projection to the first two coordinates realizes `W_p (μ, ν₀)`. -/
  eLpNorm_left :
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (γ.map (Prod.map id Prod.fst)) =
      wassersteinEDist p μ ν₀
  /-- The projection to the first and last coordinates couples `μ` and `ν₁`. -/
  isCoupling_right : IsCoupling (γ.map (Prod.map id Prod.snd)) μ ν₁
  /-- The projection to the first and last coordinates realizes `W_p (μ, ν₁)`. -/
  eLpNorm_right :
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (γ.map (Prod.map id Prod.snd)) =
      wassersteinEDist p μ ν₁

namespace IsGeneralizedGeodesicPlan

/-- The first marginal of a generalized-geodesic plan based at `μ` is `μ`. -/
theorem fst_eq (hγ : IsGeneralizedGeodesicPlan p γ μ ν₀ ν₁) : γ.fst = μ := by
  rw [← hγ.isCoupling_left.fst_eq, Measure.fst, Measure.fst,
    Measure.map_map measurable_fst (measurable_id.prodMap measurable_fst)]
  rfl

/-- The projection of a generalized-geodesic plan to its last two coordinates couples `ν₀` and
`ν₁`. -/
theorem isCoupling_snd (hγ : IsGeneralizedGeodesicPlan p γ μ ν₀ ν₁) : IsCoupling γ.snd ν₀ ν₁ := by
  constructor
  · rw [← hγ.isCoupling_left.snd_eq, Measure.snd, Measure.fst, Measure.snd,
      Measure.map_map measurable_fst measurable_snd,
      Measure.map_map measurable_snd (measurable_id.prodMap measurable_fst)]
    rfl
  · rw [← hγ.isCoupling_right.snd_eq, Measure.snd, Measure.snd, Measure.snd,
      Measure.map_map measurable_snd measurable_snd,
      Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd)]
    rfl

end IsGeneralizedGeodesicPlan

end ThreePlan

section Polish

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {p : ℝ≥0∞}

/-- **Existence of generalized-geodesic plans.** On a Polish metric space and for a nonzero
exponent `p`, a finite base measure `μ` and two measures `ν₀` and `ν₁` that are each coupled with
it carry a generalized-geodesic plan from `ν₀` to `ν₁` based at `μ`: two optimal couplings out of
`μ` glue along their common first marginal. -/
theorem exists_isGeneralizedGeodesicPlan (hp : p ≠ 0) (μ ν₀ ν₁ : Measure X) [IsFiniteMeasure μ]
    (h₀ : ∃ π, IsCoupling π μ ν₀) (h₁ : ∃ π, IsCoupling π μ ν₁) :
    ∃ γ : Measure (X × X × X), IsGeneralizedGeodesicPlan p γ μ ν₀ ν₁ := by
  have hopt (ν : Measure X) (h : ∃ π, IsCoupling π μ ν) : ∃ π, IsCoupling π μ ν ∧
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π = wassersteinEDist p μ ν := by
    rcases eq_or_ne p ∞ with rfl | hp'
    · exact exists_isCoupling_eLpNorm_top_eq_wassersteinEDist μ ν h
    · exact exists_isCoupling_eLpNorm_eq_wassersteinEDist hp hp' μ ν h
  obtain ⟨π₀, hπ₀, hπ₀opt⟩ := hopt ν₀ h₀
  obtain ⟨π₁, hπ₁, hπ₁opt⟩ := hopt ν₁ h₁
  have : IsFiniteMeasure π₁ := hπ₁.isFiniteMeasure
  obtain ⟨γ, hγ₀, hγ₁⟩ := π₀.exists_glue_of_fst_eq (hπ₀.fst_eq.trans hπ₁.fst_eq.symm)
  exact ⟨γ, ⟨hγ₀ ▸ hπ₀, hγ₀ ▸ hπ₀opt, hγ₁ ▸ hπ₁, hγ₁ ▸ hπ₁opt⟩⟩

end Polish

section Interpolation

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]

/-- The **generalized geodesic** of a measure `γ` on `E × E × E`, read as the joint law of a triple
`(x, y₀, y₁)`: at time `t`, the law of `(1 - t) • y₀ + t • y₁` under `γ`. When `γ` is a
generalized-geodesic plan from `ν₀` to `ν₁` based at `μ`, this is the generalized geodesic from `ν₀`
to `ν₁` based at `μ`. -/
def generalizedGeodesic (γ : Measure (E × E × E)) (t : ℝ) : Measure E :=
  γ.map fun w ↦ (1 - t) • w.2.1 + t • w.2.2

/-- The generalized geodesic at time `t` is the pushforward of `γ` along
`(x, y₀, y₁) ↦ (1 - t) • y₀ + t • y₁`. -/
theorem generalizedGeodesic_def (γ : Measure (E × E × E)) (t : ℝ) :
    generalizedGeodesic γ t = γ.map fun w ↦ (1 - t) • w.2.1 + t • w.2.2 := by
  rw [generalizedGeodesic]

/-- The generalized geodesic of a probability measure is a curve of probability measures. -/
instance isProbabilityMeasure_generalizedGeodesic (γ : Measure (E × E × E))
    [IsProbabilityMeasure γ] (t : ℝ) : IsProbabilityMeasure (generalizedGeodesic γ t) := by
  rw [generalizedGeodesic_def]
  infer_instance

/-- At time `0` the generalized geodesic is the law of the middle coordinate. -/
@[simp]
theorem generalizedGeodesic_zero (γ : Measure (E × E × E)) :
    generalizedGeodesic γ 0 = γ.snd.fst := by
  simp only [generalizedGeodesic_def, sub_zero, one_smul, zero_smul, add_zero]
  rw [Measure.fst, Measure.snd, Measure.map_map measurable_fst measurable_snd]
  rfl

/-- At time `1` the generalized geodesic is the law of the last coordinate. -/
@[simp]
theorem generalizedGeodesic_one (γ : Measure (E × E × E)) :
    generalizedGeodesic γ 1 = γ.snd.snd := by
  simp only [generalizedGeodesic_def, sub_self, zero_smul, one_smul, zero_add]
  rw [Measure.snd, Measure.snd, Measure.map_map measurable_snd measurable_snd]
  rfl

variable [EDist E] {p : ℝ≥0∞} {γ : Measure (E × E × E)} {μ ν₀ ν₁ : Measure E}

/-- The generalized geodesic of a generalized-geodesic plan starts at `ν₀`. -/
theorem IsGeneralizedGeodesicPlan.generalizedGeodesic_zero
    (hγ : IsGeneralizedGeodesicPlan p γ μ ν₀ ν₁) : generalizedGeodesic γ 0 = ν₀ := by
  rw [TauCeti.generalizedGeodesic_zero, hγ.isCoupling_snd.fst_eq]

/-- The generalized geodesic of a generalized-geodesic plan ends at `ν₁`. -/
theorem IsGeneralizedGeodesicPlan.generalizedGeodesic_one
    (hγ : IsGeneralizedGeodesicPlan p γ μ ν₀ ν₁) : generalizedGeodesic γ 1 = ν₁ := by
  rw [TauCeti.generalizedGeodesic_one, hγ.isCoupling_snd.snd_eq]

end Interpolation

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {t : ℝ}

/-- The pointwise identity behind the convexity of the squared distance along generalized
geodesics, in `ℝ≥0∞`: for `t ∈ [0, 1]`,
`d(x, (1 - t) a + t b) ^ 2 + t (1 - t) d(a, b) ^ 2 = (1 - t) d(x, a) ^ 2 + t d(x, b) ^ 2`. -/
private theorem edist_smul_add_smul_sq_add (ht : t ∈ Icc (0 : ℝ) 1) (x a b : E) :
    edist x ((1 - t) • a + t • b) ^ 2 + ENNReal.ofReal (t * (1 - t)) * edist a b ^ 2 =
      ENNReal.ofReal (1 - t) * edist x a ^ 2 + ENNReal.ofReal t * edist x b ^ 2 := by
  have h₀ : 0 ≤ t := ht.1
  have h₁ : 0 ≤ 1 - t := sub_nonneg.2 ht.2
  have key := mul_norm_sq_add_mul_norm_sub_sq (a := 1 - t) (b := t) (by simp) (b - a) (x - a)
  rw [sub_add_cancel, one_mul, div_one, div_one, sub_sub_sub_cancel_right, norm_sub_rev b x,
    norm_sub_rev b a, show x - a - t • (b - a) = x - ((1 - t) • a + t • b) by module] at key
  simp only [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_mul (mul_nonneg h₀ h₁), ← ENNReal.ofReal_mul h₁, ← ENNReal.ofReal_mul h₀,
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg (mul_nonneg h₀ h₁) (by positivity)),
    ← ENNReal.ofReal_add (mul_nonneg h₁ (by positivity)) (mul_nonneg h₀ (by positivity))]
  congr 1
  linarith

end Pointwise

section Quadratic

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] {μ ν : Measure X}

/-- Every coupling bounds the squared quadratic Wasserstein distance by its transport integral. -/
private theorem wassersteinEDist_two_sq_le {π : Measure (X × X)} (hπ : IsCoupling π μ ν) :
    wassersteinEDist 2 μ ν ^ 2 ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by
  have h := wassersteinEDist_rpow_eq_transportCost (X := X) measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top μ ν
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h ▸ transportCost_le_lintegral hπ _

/-- The squared `L²` seminorm of the ground distance is its quadratic transport integral. -/
private theorem eLpNorm_edist_two_sq (π : Measure (X × X)) :
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) 2 π ^ 2 = ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by
  simpa using eLpNorm_rpow_eq_lintegral two_ne_zero ENNReal.ofNat_ne_top
    (measurable_edist (α := X)).aemeasurable (μ := π)

end Quadratic

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {γ : Measure (E × E × E)} {μ ν₀ ν₁ : Measure E}
  {t : ℝ}

/-- **Convexity of the squared distance along the generalized geodesic of a three-plan.** For a
measure `γ` on `E × E × E` whose first marginal is `μ`, and `t ∈ [0, 1]`,
`W₂ (μ, ν_t) ^ 2 + t (1 - t) ∫ ‖y₀ - y₁‖ ^ 2 dγ ≤ (1 - t) ∫ ‖x - y₀‖ ^ 2 dγ + t ∫ ‖x - y₁‖ ^ 2 dγ`,
where `ν_t = generalizedGeodesic γ t`. No optimality of `γ` is needed. -/
theorem wassersteinEDist_generalizedGeodesic_sq_add_le (hγ : γ.fst = μ) (ht : t ∈ Icc (0 : ℝ) 1) :
    wassersteinEDist 2 μ (generalizedGeodesic γ t) ^ 2 +
        ENNReal.ofReal (t * (1 - t)) * ∫⁻ w, edist w.2.1 w.2.2 ^ 2 ∂γ ≤
      ENNReal.ofReal (1 - t) * ∫⁻ w, edist w.1 w.2.1 ^ 2 ∂γ +
        ENNReal.ofReal t * ∫⁻ w, edist w.1 w.2.2 ^ 2 ∂γ := by
  have hf : Measurable fun w : E × E × E ↦ (1 - t) • w.2.1 + t • w.2.2 := by fun_prop
  -- The plan couples its base marginal `μ` with the generalized geodesic at time `t`.
  have hπ : IsCoupling (γ.map fun w ↦ (w.1, (1 - t) • w.2.1 + t • w.2.2)) μ
      (generalizedGeodesic γ t) := by
    constructor
    · rw [← hγ, Measure.fst, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
      rfl
    · rw [Measure.snd, Measure.map_map measurable_snd (by fun_prop), generalizedGeodesic_def]
      rfl
  calc wassersteinEDist 2 μ (generalizedGeodesic γ t) ^ 2 +
        ENNReal.ofReal (t * (1 - t)) * ∫⁻ w, edist w.2.1 w.2.2 ^ 2 ∂γ
      ≤ ∫⁻ w, edist w.1 ((1 - t) • w.2.1 + t • w.2.2) ^ 2 ∂γ +
          ENNReal.ofReal (t * (1 - t)) * ∫⁻ w, edist w.2.1 w.2.2 ^ 2 ∂γ := by
        grw [wassersteinEDist_two_sq_le hπ, lintegral_map (by fun_prop) (by fun_prop)]
    _ = ∫⁻ w, (ENNReal.ofReal (1 - t) * edist w.1 w.2.1 ^ 2 +
          ENNReal.ofReal t * edist w.1 w.2.2 ^ 2) ∂γ := by
        rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_add_left (by fun_prop)]
        exact lintegral_congr fun w ↦ edist_smul_add_smul_sq_add ht w.1 w.2.1 w.2.2
    _ = _ := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_const_mul _ (by fun_prop)]

namespace IsGeneralizedGeodesicPlan

/-- **The squared distance is convex along generalized geodesics.** Along the generalized geodesic
`ν_t` of a quadratic generalized-geodesic plan `γ` from `ν₀` to `ν₁` based at `μ`, and for
`t ∈ [0, 1]`,
`W₂ (μ, ν_t) ^ 2 + t (1 - t) ∫ ‖y₀ - y₁‖ ^ 2 dγ ≤ (1 - t) W₂ (μ, ν₀) ^ 2 + t W₂ (μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_sq_add_le (hγ : IsGeneralizedGeodesicPlan 2 γ μ ν₀ ν₁)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    wassersteinEDist 2 μ (generalizedGeodesic γ t) ^ 2 +
        ENNReal.ofReal (t * (1 - t)) * ∫⁻ w, edist w.2.1 w.2.2 ^ 2 ∂γ ≤
      ENNReal.ofReal (1 - t) * wassersteinEDist 2 μ ν₀ ^ 2 +
        ENNReal.ofReal t * wassersteinEDist 2 μ ν₁ ^ 2 := by
  have h₀ : ∫⁻ w, edist w.1 w.2.1 ^ 2 ∂γ = wassersteinEDist 2 μ ν₀ ^ 2 := by
    rw [← hγ.eLpNorm_left, eLpNorm_edist_two_sq,
      lintegral_map (by fun_prop) (measurable_id.prodMap measurable_fst)]
    rfl
  have h₁ : ∫⁻ w, edist w.1 w.2.2 ^ 2 ∂γ = wassersteinEDist 2 μ ν₁ ^ 2 := by
    rw [← hγ.eLpNorm_right, eLpNorm_edist_two_sq,
      lintegral_map (by fun_prop) (measurable_id.prodMap measurable_snd)]
    rfl
  rw [← h₀, ← h₁]
  exact wassersteinEDist_generalizedGeodesic_sq_add_le hγ.fst_eq ht

/-- **`ν ↦ W₂ (μ, ν) ^ 2 / 2` is `1`-convex along generalized geodesics based at `μ`.** Along the
generalized geodesic `ν_t` of a quadratic generalized-geodesic plan from `ν₀` to `ν₁` based at
`μ`, and for `t ∈ [0, 1]`,
`W₂ (μ, ν_t) ^ 2 + t (1 - t) W₂ (ν₀, ν₁) ^ 2 ≤ (1 - t) W₂ (μ, ν₀) ^ 2 + t W₂ (μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_sq_add_wassersteinEDist_sq_le (hγ : IsGeneralizedGeodesicPlan 2 γ μ ν₀ ν₁)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    wassersteinEDist 2 μ (generalizedGeodesic γ t) ^ 2 +
        ENNReal.ofReal (t * (1 - t)) * wassersteinEDist 2 ν₀ ν₁ ^ 2 ≤
      ENNReal.ofReal (1 - t) * wassersteinEDist 2 μ ν₀ ^ 2 +
        ENNReal.ofReal t * wassersteinEDist 2 μ ν₁ ^ 2 := by
  refine le_trans ?_ (hγ.wassersteinEDist_sq_add_le ht)
  gcongr
  calc wassersteinEDist 2 ν₀ ν₁ ^ 2 ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂γ.snd :=
        wassersteinEDist_two_sq_le hγ.isCoupling_snd
    _ = ∫⁻ w, edist w.2.1 w.2.2 ^ 2 ∂γ := lintegral_map (by fun_prop) measurable_snd

end IsGeneralizedGeodesicPlan

end InnerProductSpace

end TauCeti
