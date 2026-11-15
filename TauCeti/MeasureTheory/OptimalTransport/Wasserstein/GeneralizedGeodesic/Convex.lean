/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Basic
import TauCeti.Data.EReal.Operations
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete

/-!
# Convexity along generalized geodesics and the Jordan–Kinderlehrer–Otto step

Let `E` be a separable Hilbert space and `φ` an energy on the quadratic Wasserstein space
`P₂(E)`. One step of the *Jordan–Kinderlehrer–Otto scheme* (JKO scheme) for the Wasserstein
gradient flow of `φ`, with time step `τ > 0`, started at a law `μ`, chooses a minimizer of

`ν ↦ φ ν + W₂ (μ, ν) ^ 2 / (2τ)`,

that is, a point of the resolvent `TauCeti.moreauYosidaResolvent φ τ μ` of the metric theory of
gradient flows, taken in `P₂(E)`. Ordinary displacement convexity of `φ` is not the hypothesis
that makes this step unique, because `ν ↦ W₂ (μ, ν) ^ 2` is not convex along Wasserstein
geodesics. It is, however, `2`-convex along the *generalized geodesics based at `μ`*, the
interpolations `ν_t = ((1 - t) • y₀ + t • y₁)₊ γ` of a three-plan `γ` of `(x, y₀, y₁)` whose
projections to `(x, y₀)` and `(x, y₁)` are optimal couplings out of `μ`
(`TauCeti.IsGeneralizedGeodesicPlan.dist_sq_add_le`). This file introduces the matching convexity
notion for energies and proves that it makes the JKO step exist and be unique.

An energy `φ` is *`m`-convex along generalized geodesics based at `μ`*
(`TauCeti.GeneralizedGeodesicallyConvex m φ μ`) if any two laws `ν₀` and `ν₁` of its effective
domain are joined by the generalized geodesic of some such plan `γ` along which

`φ ν_t ≤ (1 - t) φ ν₀ + t φ ν₁ - (m / 2) t (1 - t) ∫ ‖y₀ - y₁‖² dγ`.

The integral is the quadratic cost of the coupling of `ν₀` and `ν₁` carried by `γ`; it is at least
`W₂ (ν₀, ν₁) ^ 2`, with equality when `ν₀ = μ`
(`TauCeti.IsGeneralizedGeodesicPlan.integral_norm_sub_sq_snd_eq_dist_sq`). If `φ` has this
property, then the penalized functional of the JKO step is `(m + 1 / τ)`-convex along the same
curves (`TauCeti.GeneralizedGeodesicallyConvex.add_edist_sq_div`), so for `1 + m τ > 0` the JKO
step is unique (`TauCeti.GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent`) and,
when `φ` is lower semicontinuous in `P₂(E)`, automatically coercive and nonempty by completeness of
`P₂(E)` without narrow compactness (`TauCeti.GeneralizedGeodesicallyConvex.moreauYosida_ne_bot` and
`TauCeti.GeneralizedGeodesicallyConvex.moreauYosidaResolvent_nonempty`).
Since `W₂ (ν₀, ν₁) ^ 2` is at most the plan cost, the same convexity holds with `W₂ (ν₀, ν₁) ^ 2`
when `1 + m τ ≥ 0`. If `φ` is convex along generalized geodesics based at every law, it therefore
satisfies the convexity hypothesis `TauCeti.PenalizedConvex` of the metric theory of gradient flows
(`TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex`), and JKO steps satisfy the discrete
variational inequality of `TauCeti.Analysis.GradientFlow.MoreauYosida.Convex`.

## Main definitions

* `TauCeti.ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ`: the convexity inequality along
  a fixed three-plan, with the quadratic cost of its endpoint coupling as the correction.
* `TauCeti.GeneralizedGeodesicallyConvex m φ μ`: the energy `φ` on `P₂(E)` is `m`-convex along
  generalized geodesics based at `μ`.

## Main results

* `TauCeti.IsGeneralizedGeodesicPlan.dist_sq_add_le`: the convexity of the squared Wasserstein
  distance from the base point along a generalized geodesic, as an inequality of real numbers.
* `TauCeti.IsGeneralizedGeodesicPlan.integral_norm_sub_sq_snd_eq_dist_sq` and
  `TauCeti.IsGeneralizedGeodesicPlan.dist_le_mul`: when the initial law coincides with the base law
  `μ`, the coupling cost is `W₂ (μ, ν₁) ^ 2` and `W₂ (μ, ν_t) ≤ t W₂ (μ, ν₁)`.
* `TauCeti.GeneralizedGeodesicallyConvex.add_edist_sq_div`: the penalized functional
  `ν ↦ φ ν + W₂ (μ, ν) ^ 2 / (2τ)` of an energy that is `m`-convex along generalized geodesics
  based at `μ` is `(m + 1 / τ)`-convex along them.
* `TauCeti.GeneralizedGeodesicallyConvex.eq_of_mem_moreauYosidaResolvent` and
  `TauCeti.GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent`: uniqueness of the
  JKO step when `1 + m τ > 0`.
* `TauCeti.GeneralizedGeodesicallyConvex.exists_forall_sub_add_le`,
  `TauCeti.GeneralizedGeodesicallyConvex.moreauYosida_ne_bot`, and
  `TauCeti.GeneralizedGeodesicallyConvex.moreauYosidaResolvent_nonempty`: quadratic lower bounds,
  coercivity, and existence of the JKO step when `1 + m τ > 0` and `φ` is lower semicontinuous.
* `TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex`: convexity along generalized geodesics
  based at every law is the convexity hypothesis `TauCeti.PenalizedConvex` of the metric theory,
  so JKO steps satisfy its discrete variational inequality.

## Implementation notes

The JKO step is not given a separate definition: on `P₂(E)` with its Wasserstein metric it is the
resolvent `TauCeti.moreauYosidaResolvent φ τ μ`, whose penalty `edist μ ν ^ 2 / (2τ)` is
`W₂ (μ, ν) ^ 2 / (2τ)`.

The convexity inequality is stated, as in Ambrosio–Gigli–Savaré, with the cost
`∫ ‖y₀ - y₁‖² dγ` of the coupling carried by the plan rather than with the smaller
`W₂ (ν₀, ν₁) ^ 2`. For `m ≤ 0` this is weaker than the same inequality with `W₂ (ν₀, ν₁) ^ 2`, for
`m ≥ 0` it is stronger, and at `m = 0` the two agree.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.2, Definition 9.2.4 and Lemma 9.2.7, and
  Chapter 4, Assumption 4.0.1.
* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1--17.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

section Convexity

variable [NormedSpace ℝ E] {m m' : ℝ}
  {φ : WassersteinSpace 2 E → EReal} {μ : WassersteinSpace 2 E}

/-- The energy `φ` satisfies the `m`-convexity inequality along the interpolation of the fixed
three-plan `γ`, with endpoint laws `ν₀`, `ν₁`. The correction uses the quadratic cost of `γ.snd`.
This predicate alone does not require that `γ` is a generalized-geodesic plan. -/
def ConvexAlongGeneralizedGeodesicPlan (m : ℝ) (φ : WassersteinSpace 2 E → EReal)
    (ν₀ ν₁ : WassersteinSpace 2 E) (γ : Measure (E × E × E)) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ ν : WassersteinSpace 2 E,
    ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t →
    φ ν ≤ ((1 - t : ℝ) : EReal) * φ ν₀ + (t : EReal) * φ ν₁ -
      ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal)

/-- The defining inequality for convexity along a fixed three-plan. -/
theorem convexAlongGeneralizedGeodesicPlan_def {ν₀ ν₁ : WassersteinSpace 2 E}
    {γ : Measure (E × E × E)} :
    ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ ↔
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ ν : WassersteinSpace 2 E,
        ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t →
        φ ν ≤ ((1 - t : ℝ) : EReal) * φ ν₀ + (t : EReal) * φ ν₁ -
          ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal) :=
  Iff.rfl

/-- Convexity along a fixed three-plan persists with a smaller parameter. -/
theorem ConvexAlongGeneralizedGeodesicPlan.mono {ν₀ ν₁ : WassersteinSpace 2 E}
    {γ : Measure (E × E × E)} (h : ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ)
    (hm : m' ≤ m) : ConvexAlongGeneralizedGeodesicPlan m' φ ν₀ ν₁ γ := by
  intro t ht ν hν
  refine (h t ht ν hν).trans (EReal.sub_le_sub le_rfl ?_)
  apply EReal.coe_le_coe_iff.2
  have : 0 ≤ t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd :=
    mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (integral_nonneg fun _ ↦ by positivity)
  nlinarith

/-- The energy `φ` on `P₂(E)` is *`m`-convex along generalized geodesics based at `μ`*: any two
laws `ν₀` and `ν₁` with `φ ν₀ ≠ ⊤` and `φ ν₁ ≠ ⊤` (energy `⊥` is allowed) carry a quadratic
generalized-geodesic plan `γ` from `ν₀` to `ν₁` based at `μ` along whose generalized geodesic
`ν_t`, for every `t ∈ [0, 1]`,
`φ ν_t ≤ (1 - t) φ ν₀ + t φ ν₁ - (m / 2) t (1 - t) ∫ ‖y₀ - y₁‖² dγ`.
The law `ν_t` lies in `P₂(E)` (`TauCeti.exists_coe_eq_generalizedGeodesic`); the integral is the
quadratic cost of the coupling `γ.snd` of `ν₀` and `ν₁`. -/
def GeneralizedGeodesicallyConvex (m : ℝ) (φ : WassersteinSpace 2 E → EReal)
    (μ : WassersteinSpace 2 E) : Prop :=
  ∀ ⦃ν₀ ν₁ : WassersteinSpace 2 E⦄, φ ν₀ ≠ ⊤ → φ ν₁ ≠ ⊤ → ∃ γ : Measure (E × E × E),
    IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E) ∧
    ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ

/-- The defining condition of convexity along generalized geodesics. -/
theorem generalizedGeodesicallyConvex_def :
    GeneralizedGeodesicallyConvex m φ μ ↔
      ∀ ⦃ν₀ ν₁ : WassersteinSpace 2 E⦄, φ ν₀ ≠ ⊤ → φ ν₁ ≠ ⊤ → ∃ γ : Measure (E × E × E),
        IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
          ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E) ∧
        ConvexAlongGeneralizedGeodesicPlan m φ ν₀ ν₁ γ :=
  Iff.rfl

/-- Convexity along generalized geodesics with a parameter `m` implies it for every smaller
parameter. -/
theorem GeneralizedGeodesicallyConvex.mono (h : GeneralizedGeodesicallyConvex m φ μ)
    (hm : m' ≤ m) : GeneralizedGeodesicallyConvex m' φ μ := fun _ _ h₀ h₁ ↦
  (h h₀ h₁).imp fun _ hγ ↦ ⟨hγ.1, hγ.2.mono hm⟩

end Convexity

section Hilbert

variable [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

variable [InnerProductSpace ℝ E] {γ : Measure (E × E × E)} {t : ℝ}

/-- **The squared distance is convex along generalized geodesics**, in `P₂(E)`. Along the
generalized geodesic `ν_t` of a quadratic generalized-geodesic plan `γ` from `ν₀` to `ν₁` based at
`μ`, and for `t ∈ [0, 1]`,
`W₂ (μ, ν_t) ^ 2 + t (1 - t) ∫ ‖y₀ - y₁‖² dγ ≤ (1 - t) W₂ (μ, ν₀) ^ 2 + t W₂ (μ, ν₁) ^ 2`. -/
theorem IsGeneralizedGeodesicPlan.dist_sq_add_le {μ ν₀ ν₁ ν : WassersteinSpace 2 E}
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E))
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hν : ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t) :
    dist μ ν ^ 2 + t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd ≤
      (1 - t) * dist μ ν₀ ^ 2 + t * dist μ ν₁ ^ 2 := by
  have hπ := hγ.isCoupling_snd
  have : IsProbabilityMeasure γ.snd := hπ.isProbabilityMeasure
  have hi := integrable_norm_sub_sq_of_hasFiniteMoment (hπ.fst_eq ▸ ν₀.hasFiniteMoment)
    (hπ.snd_eq ▸ ν₁.hasFiniteMoment)
  have hW := hγ.wassersteinEDist_sq_add_le ht
  have hsnd : ∫⁻ w, edist w.2.1 w.2.2 ^ 2 ∂γ = ∫⁻ z, edist z.1 z.2 ^ 2 ∂γ.snd :=
    (lintegral_map (f := fun z : E × E ↦ edist z.1 z.2 ^ 2) (by fun_prop) measurable_snd).symm
  have hd (ρ : WassersteinSpace 2 E) : wassersteinEDist 2 ((μ : ProbabilityMeasure E) : Measure E)
      ((ρ : ProbabilityMeasure E) : Measure E) ^ 2 = ENNReal.ofReal (dist μ ρ ^ 2) := by
    rw [← WassersteinSpace.edist_def, edist_dist, ENNReal.ofReal_pow dist_nonneg]
  have ht' : 0 ≤ 1 - t := sub_nonneg.2 ht.2
  have hI : 0 ≤ ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd := integral_nonneg fun _ ↦ by positivity
  rw [← hν, hsnd, lintegral_edist_sq_eq_ofReal_integral hi, hd, hd, hd,
    ← ENNReal.ofReal_mul (mul_nonneg ht.1 ht'), ← ENNReal.ofReal_mul ht',
    ← ENNReal.ofReal_mul ht.1, ← ENNReal.ofReal_add (sq_nonneg _)
      (mul_nonneg (mul_nonneg ht.1 ht') hI),
    ← ENNReal.ofReal_add (mul_nonneg ht' (sq_nonneg _)) (mul_nonneg ht.1 (sq_nonneg _)),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg ht' (sq_nonneg _))
      (mul_nonneg ht.1 (sq_nonneg _)))] at hW
  exact hW

variable {m : ℝ} {φ : WassersteinSpace 2 E → EReal} {μ : WassersteinSpace 2 E} {τ : ℝ≥0}

/-- **The penalized functional of the JKO step is convex along generalized geodesics.** If `φ` is
`m`-convex along generalized geodesics based at `μ`, then for a time step `τ > 0` the functional
`ν ↦ φ ν + W₂ (μ, ν) ^ 2 / (2τ)` minimized by the JKO step from `μ` is `(m + 1 / τ)`-convex along
generalized geodesics based at `μ`, along the same plans. -/
theorem GeneralizedGeodesicallyConvex.add_edist_sq_div (h : GeneralizedGeodesicallyConvex m φ μ)
    (hτ : 0 < τ) :
    GeneralizedGeodesicallyConvex (m + (τ : ℝ)⁻¹)
      (fun ν ↦ φ ν + (edist μ ν ^ 2 / (2 * τ) : ℝ≥0∞)) μ := by
  intro ν₀ ν₁ h₀ h₁
  simp only [coe_edist_sq_div_eq_coe_dist_sq_div hτ] at h₀ h₁ ⊢
  obtain ⟨γ, hγ, hconv⟩ := h (EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _)
    (EReal.coe_ne_top _) |>.1 h₀) (EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _)
    (EReal.coe_ne_top _) |>.1 h₁)
  refine ⟨γ, hγ, fun t ht ν hν ↦ ?_⟩
  have hd := hγ.dist_sq_add_le ht hν
  have ht' : 0 ≤ 1 - t := sub_nonneg.2 ht.2
  set I := ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd
  set A := ((1 - t : ℝ) : EReal) * φ ν₀ + (t : EReal) * φ ν₁
  -- The penalty is a real number satisfying the convexity inequality with parameter `1 / τ`.
  have hreal : dist μ ν ^ 2 / (2 * τ) - m / 2 * t * (1 - t) * I ≤
      (1 - t) * (dist μ ν₀ ^ 2 / (2 * τ)) + t * (dist μ ν₁ ^ 2 / (2 * τ)) -
        (m + (τ : ℝ)⁻¹) / 2 * t * (1 - t) * I := by
    have key : (1 - t) * (dist μ ν₀ ^ 2 / (2 * τ)) + t * (dist μ ν₁ ^ 2 / (2 * τ)) -
        (m + (τ : ℝ)⁻¹) / 2 * t * (1 - t) * I -
        (dist μ ν ^ 2 / (2 * τ) - m / 2 * t * (1 - t) * I) =
        ((1 - t) * dist μ ν₀ ^ 2 + t * dist μ ν₁ ^ 2 - (dist μ ν ^ 2 + t * (1 - t) * I)) /
          (2 * τ) := by
      field_simp
      ring
    have : 0 ≤ ((1 - t) * dist μ ν₀ ^ 2 + t * dist μ ν₁ ^ 2 - (dist μ ν ^ 2 + t * (1 - t) * I)) /
        (2 * τ) := div_nonneg (sub_nonneg.2 hd) (by positivity)
    linarith
  calc φ ν + ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal)
      ≤ A - ((m / 2 * t * (1 - t) * I : ℝ) : EReal) + ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal) :=
        by gcongr; exact hconv t ht ν hν
    _ = A + ((dist μ ν ^ 2 / (2 * τ) - m / 2 * t * (1 - t) * I : ℝ) : EReal) := by
        rw [EReal.sub_coe_add_eq_add_sub, EReal.coe_sub, add_sub_assoc]
    _ ≤ A + (((1 - t) * (dist μ ν₀ ^ 2 / (2 * τ)) + t * (dist μ ν₁ ^ 2 / (2 * τ)) -
          (m + (τ : ℝ)⁻¹) / 2 * t * (1 - t) * I : ℝ) : EReal) :=
        by gcongr
    _ = ((1 - t : ℝ) : EReal) * (φ ν₀ + ((dist μ ν₀ ^ 2 / (2 * τ) : ℝ) : EReal)) +
          (t : EReal) * (φ ν₁ + ((dist μ ν₁ ^ 2 / (2 * τ) : ℝ) : EReal)) -
          (((m + (τ : ℝ)⁻¹) / 2 * t * (1 - t) * I : ℝ) : EReal) := by
        rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 ht') (EReal.coe_ne_top _),
          EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 ht.1) (EReal.coe_ne_top _),
          add_add_add_comm, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_sub,
          ← add_sub_assoc]

/-- **Uniqueness of the JKO step.** Let `φ` be `m`-convex along generalized geodesics based at `μ`,
and let `τ > 0` be a time step with `1 + m τ > 0`. Two minimizers `ν₀` and `ν₁` of
`ν ↦ φ ν + W₂ (μ, ν) ^ 2 / (2τ)`, the first of finite energy, are equal. -/
theorem GeneralizedGeodesicallyConvex.eq_of_mem_moreauYosidaResolvent
    (h : GeneralizedGeodesicallyConvex m φ μ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    {ν₀ ν₁ : WassersteinSpace 2 E} (h₀ : ν₀ ∈ moreauYosidaResolvent φ τ μ)
    (h₁ : ν₁ ∈ moreauYosidaResolvent φ τ μ) (htop : φ ν₀ ≠ ⊤) (hbot : φ ν₀ ≠ ⊥) : ν₀ = ν₁ := by
  rw [mem_moreauYosidaResolvent_iff_isMinOn, isMinOn_univ_iff] at h₀ h₁
  have hψ₁ := le_antisymm (h₁ ν₀) (h₀ ν₁)
  have hψ₀ : φ ν₀ + ((edist μ ν₀ ^ 2 / (2 * τ) : ℝ≥0∞) : EReal) ≠ ⊤ := by
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
    exact EReal.add_ne_top htop (EReal.coe_ne_top _)
  -- The penalized functional is `(m + 1 / τ)`-convex along a generalized geodesic joining the two
  -- minimizers; at its midpoint it would fall below the minimum unless the plan has zero cost.
  obtain ⟨γ, hγ, hconv⟩ := h.add_edist_sq_div hτ hψ₀ (hψ₁ ▸ hψ₀)
  obtain ⟨ν, hν⟩ := exists_coe_eq_generalizedGeodesic hγ.isCoupling_snd (1 / 2)
  have hle := (h₀ ν).trans (hconv (1 / 2) ⟨by norm_num, by norm_num⟩ ν hν)
  beta_reduce at hle
  rw [hψ₁] at hle
  simp only [coe_edist_sq_div_eq_coe_dist_sq_div hτ] at hle
  lift φ ν₀ to ℝ using ⟨htop, hbot⟩ with a
  simp only [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hle
  have hpos : 0 < m + (τ : ℝ)⁻¹ := by
    have : m + (τ : ℝ)⁻¹ = (1 + m * τ) / τ := by field_simp; ring
    rw [this]
    positivity
  have hI : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd ≤ 0 := by nlinarith
  have hd := WassersteinSpace.dist_sq_le_integral hγ.isCoupling_snd
  exact dist_le_zero.1 (by nlinarith [dist_nonneg (x := ν₀) (y := ν₁)])

/-- **Uniqueness of the JKO step.** Let `φ` be an energy on `P₂(E)` that never takes the value `⊥`
and is finite somewhere, and that is `m`-convex along generalized geodesics based at `μ`. Then for
every time step `τ > 0` with `1 + m τ > 0`, the JKO step from `μ`, that is, the set of minimizers of
`ν ↦ φ ν + W₂ (μ, ν) ^ 2 / (2τ)`, has at most one element. -/
theorem GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent
    (h : GeneralizedGeodesicallyConvex m φ μ) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    (hbot : ∀ ν, φ ν ≠ ⊥) (hdom : ∃ ν, φ ν ≠ ⊤) : (moreauYosidaResolvent φ τ μ).Subsingleton := by
  obtain ⟨ν', hν'⟩ := hdom
  intro ν₀ h₀ ν₁ h₁
  refine h.eq_of_mem_moreauYosidaResolvent hτ hmτ h₀ h₁
    (apply_ne_top_of_mem_moreauYosidaResolvent h₀ ?_) (hbot ν₀)
  refine ne_top_of_le_ne_top ?_ (moreauYosida_le φ τ (edist_ne_top μ ν'))
  rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
  exact EReal.add_ne_top hν' (EReal.coe_ne_top _)

/-- Along the generalized geodesic of a three-plan whose last two marginals are `ν₀` and `ν₁`,
`W₂ (ν₀, ν_t) ^ 2 ≤ t ^ 2 ∫ ‖y₀ - y₁‖ ^ 2 dγ` for every `t : ℝ`. -/
theorem dist_sq_le_mul_integral_of_generalizedGeodesic {ν₀ ν₁ ν : WassersteinSpace 2 E}
    (hπ : IsCoupling γ.snd ((ν₀ : ProbabilityMeasure E) : Measure E)
      ((ν₁ : ProbabilityMeasure E) : Measure E))
    (hν : ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t) :
    dist ν₀ ν ^ 2 ≤ t ^ 2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd := by
  let f : E × E → E × E := fun z ↦ (z.1, (1 - t) • z.1 + t • z.2)
  have hf : Measurable f := by fun_prop
  have hπ' : IsCoupling (γ.snd.map f) ((ν₀ : ProbabilityMeasure E) : Measure E)
      ((ν : ProbabilityMeasure E) : Measure E) := by
    constructor
    · rw [Measure.fst, Measure.map_map measurable_fst hf]
      exact hπ.fst_eq
    · rw [Measure.snd, Measure.map_map measurable_snd hf, Measure.snd,
        Measure.map_map (by fun_prop) measurable_snd, hν, generalizedGeodesic_def]
      rfl
  calc dist ν₀ ν ^ 2 ≤ ∫ w, ‖w.1 - w.2‖ ^ 2 ∂(γ.snd.map f) :=
        WassersteinSpace.dist_sq_le_integral hπ'
    _ = ∫ z, ‖z.1 - ((1 - t) • z.1 + t • z.2)‖ ^ 2 ∂γ.snd :=
        integral_map hf.aemeasurable (by fun_prop)
    _ = ∫ z, t ^ 2 * ‖z.1 - z.2‖ ^ 2 ∂γ.snd := by
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        dsimp only
        have hsub : z.1 - ((1 - t) • z.1 + t • z.2) = t • (z.1 - z.2) := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ = t ^ 2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd := integral_const_mul (t ^ 2) _

/-- Along a quadratic generalized-geodesic plan from `μ` to `ν` based at `μ` itself, the quadratic
cost of the endpoint coupling `γ.snd` equals `W₂ (μ, ν) ^ 2`. -/
theorem IsGeneralizedGeodesicPlan.integral_norm_sub_sq_snd_eq_dist_sq
    {μ ν : WassersteinSpace 2 E}
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E)) :
    ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd = dist μ ν ^ 2 := by
  refine le_antisymm ?_ (WassersteinSpace.dist_sq_le_integral hγ.isCoupling_snd)
  set I := ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd
  by_contra! hlt
  have hI : 0 < I := (sq_nonneg _).trans_lt hlt
  set s := min (1 / 2 : ℝ) ((I - dist μ ν ^ 2) / (2 * I))
  have hs0 : 0 < s := lt_min (by norm_num) (div_pos (sub_pos.2 hlt) (by positivity))
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  obtain ⟨ρ, hρ⟩ := exists_coe_eq_generalizedGeodesic hγ.isCoupling_snd s
  have hd := hγ.dist_sq_add_le ⟨hs0.le, hs1.trans (by norm_num)⟩ hρ
  rw [dist_self, zero_pow two_ne_zero, mul_zero, zero_add] at hd
  have hle : (1 - s) * I ≤ dist μ ν ^ 2 := by nlinarith [sq_nonneg (dist μ ρ)]
  have hsI : s * I ≤ (I - dist μ ν ^ 2) / 2 := by
    calc s * I ≤ (I - dist μ ν ^ 2) / (2 * I) * I :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hI.le
      _ = (I - dist μ ν ^ 2) / 2 := by
          have := hI.ne'
          field_simp
  linarith

/-- Along a quadratic generalized-geodesic plan from `μ` to `ν₁` based at `μ` itself,
`W₂ (μ, ν_t) ≤ t W₂ (μ, ν₁)` for every `t ≥ 0`. -/
theorem IsGeneralizedGeodesicPlan.dist_le_mul {μ ν₁ ν : WassersteinSpace 2 E}
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((μ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E))
    (ht : 0 ≤ t)
    (hν : ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t) :
    dist μ ν ≤ t * dist μ ν₁ := by
  have hd := dist_sq_le_mul_integral_of_generalizedGeodesic hγ.isCoupling_snd hν
  rw [hγ.integral_norm_sub_sq_snd_eq_dist_sq, ← mul_pow] at hd
  exact (sq_le_sq₀ dist_nonneg (mul_nonneg ht dist_nonneg)).1 hd

/-- Pointwise curve selection for the penalized functional at a single base law `μ`. -/
private theorem GeneralizedGeodesicallyConvex.exists_convexAlong_add_dist_sq_div
    (h : GeneralizedGeodesicallyConvex m φ μ) (hτ : 0 < τ) (hmτ : 0 ≤ 1 + m * τ)
    {ν₀ ν₁ : WassersteinSpace 2 E} (h₀ : φ ν₀ ≠ ⊤) (h₁ : φ ν₁ ≠ ⊤) :
    ∃ c : ℝ → WassersteinSpace 2 E, c 0 = ν₀ ∧ c 1 = ν₁ ∧
      ConvexAlong (m + (τ : ℝ)⁻¹) (fun ν ↦ φ ν + ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal)) c := by
  have hΦ {ν : WassersteinSpace 2 E} (hν : φ ν ≠ ⊤) :
      φ ν + ((edist μ ν ^ 2 / (2 * τ) : ℝ≥0∞) : EReal) ≠ ⊤ := by
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
    exact EReal.add_ne_top hν (EReal.coe_ne_top _)
  obtain ⟨γ, hγ, hconv⟩ := h.add_edist_sq_div hτ (hΦ h₀) (hΦ h₁)
  have hπ := hγ.isCoupling_snd
  -- Select the laws along the generalized geodesic; its endpoints are `ν₀` and `ν₁`.
  choose c hc using exists_coe_eq_generalizedGeodesic hπ
  have hc₀ : c 0 = ν₀ := WassersteinSpace.ext <| ProbabilityMeasure.toMeasure_injective <| by
    rw [hc, generalizedGeodesic_zero, hπ.fst_eq]
  have hc₁ : c 1 = ν₁ := WassersteinSpace.ext <| ProbabilityMeasure.toMeasure_injective <| by
    rw [hc, generalizedGeodesic_one, hπ.snd_eq]
  refine ⟨c, hc₀, hc₁, convexAlong_def.2 fun t ht ↦ ?_⟩
  have hle := hconv t ht (c t) (hc t)
  simp only [coe_edist_sq_div_eq_coe_dist_sq_div hτ] at hle
  rw [hc₀, hc₁]
  refine hle.trans (EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.2 ?_))
  -- The plan cost bounds `W₂ (ν₀, ν₁) ^ 2`, and the convexity parameter is nonnegative.
  have hk : 0 ≤ (m + (τ : ℝ)⁻¹) / 2 * t * (1 - t) := by
    have hτ' : (0 : ℝ) < τ := hτ
    have hm : m + (τ : ℝ)⁻¹ = (1 + m * τ) / τ := by field_simp; ring
    exact mul_nonneg (mul_nonneg (div_nonneg (hm ▸ div_nonneg hmτ hτ'.le) zero_le_two) ht.1)
      (sub_nonneg.2 ht.2)
  exact mul_le_mul_of_nonneg_left (WassersteinSpace.dist_sq_le_integral hπ) hk

/-- **Convexity along generalized geodesics gives penalized convexity.** If `φ` is `m`-convex along
generalized geodesics based at every law of `P₂(E)`, then for every time step `τ > 0` with
`1 + m τ ≥ 0` it is penalized convex with parameter `m`: the penalized functional
`ν ↦ φ ν + W₂ (μ, ν) ^ 2 / (2τ)` is `(m + 1 / τ)`-convex along a generalized geodesic based at `μ`.
So JKO steps satisfy the discrete variational inequality
`TauCeti.PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent` and the estimates for
minimizing movements that follow from it. -/
theorem penalizedConvex_of_generalizedGeodesicallyConvex
    (h : ∀ μ, GeneralizedGeodesicallyConvex m φ μ) (hτ : 0 < τ) (hmτ : 0 ≤ 1 + m * τ) :
    PenalizedConvex m τ φ :=
  penalizedConvex_def.2 fun μ _ _ h₀ h₁ ↦ (h μ).exists_convexAlong_add_dist_sq_div hτ hmτ h₀ h₁

/-- **Quadratic lower bound from convexity along generalized geodesics.** If `φ` is `m`-convex
along generalized geodesics based at `μ`, and is finite and lower semicontinuous at `μ`, then `φ`
satisfies a global lower bound `c - a W₂ (μ, ν) + (m / 2) W₂ (μ, ν) ^ 2 ≤ φ ν`. -/
theorem GeneralizedGeodesicallyConvex.exists_forall_sub_add_le
    (h : GeneralizedGeodesicallyConvex m φ μ) (hμ : φ μ ≠ ⊤) (hμ_bot : φ μ ≠ ⊥)
    (hlsc : LowerSemicontinuousAt φ μ) :
    ∃ c a : ℝ, ∀ ν, ((c - a * dist μ ν + m / 2 * dist μ ν ^ 2 : ℝ) : EReal) ≤ φ ν :=
  exists_forall_sub_add_le_of_lowerSemicontinuousAt hμ hμ_bot hlsc fun ν hν ↦ by
    obtain ⟨γ, hγ, hconv⟩ := h hμ hν
    have hπ := hγ.isCoupling_snd
    choose c hc using exists_coe_eq_generalizedGeodesic hπ
    have hc₀ : c 0 = μ := WassersteinSpace.ext <| ProbabilityMeasure.toMeasure_injective <| by
      rw [hc, generalizedGeodesic_zero, hπ.fst_eq]
    have hc₁ : c 1 = ν := WassersteinSpace.ext <| ProbabilityMeasure.toMeasure_injective <| by
      rw [hc, generalizedGeodesic_one, hπ.snd_eq]
    refine ⟨c, hc₀, hc₁, fun t ht ↦ hγ.dist_le_mul ht.1 (hc t), convexAlong_def.2 fun t ht ↦ ?_⟩
    have hle := hconv t ht (c t) (hc t)
    rwa [hγ.integral_norm_sub_sq_snd_eq_dist_sq, ← hc₀, ← hc₁] at hle

/-- Along a quadratic generalized-geodesic plan from `ν₀` to `ν` based at `μ`, evaluating at
`s = r / (2 (W₂(μ, ν₀) + W₂(μ, ν)) + r)` gives a law `ρ` at distance at most `r` from `ν₀`. -/
private lemma IsGeneralizedGeodesicPlan.exists_coe_eq_generalizedGeodesic_dist_le
    {μ ν₀ ν : WassersteinSpace 2 E} {r : ℝ} (hr0 : 0 < r)
    (hγ : IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
      ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E)) :
    let s := r / (2 * (dist μ ν₀ + dist μ ν) + r)
    s ∈ Icc (0 : ℝ) 1 ∧ ∃ ρ : WassersteinSpace 2 E,
      ((ρ : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ s ∧ dist ν₀ ρ ≤ r := by
  obtain ⟨ρm, hρm⟩ := exists_coe_eq_generalizedGeodesic hγ.isCoupling_snd (1 / 2)
  have hIm := hγ.dist_sq_add_le ⟨by norm_num, by norm_num⟩ hρm
  have hd₀ : 0 ≤ dist μ ν₀ := dist_nonneg
  have hd₁ : 0 ≤ dist μ ν := dist_nonneg
  have hI_le : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd ≤ (2 * (dist μ ν₀ + dist μ ν)) ^ 2 := by
    nlinarith [sq_nonneg (dist μ ρm)]
  set S := 2 * (dist μ ν₀ + dist μ ν) + r
  have hS0 : 0 < S := by positivity
  set s := r / S
  have hs : s ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hr0 hS0).le, (div_le_one hS0).2 (le_add_of_nonneg_left (by positivity))⟩
  obtain ⟨ρ, hρ⟩ := exists_coe_eq_generalizedGeodesic hγ.isCoupling_snd s
  refine ⟨hs, ρ, hρ, (sq_le_sq₀ dist_nonneg hr0.le).1 ?_⟩
  refine (dist_sq_le_mul_integral_of_generalizedGeodesic hγ.isCoupling_snd hρ).trans ?_
  refine (mul_le_mul_of_nonneg_left hI_le (sq_nonneg s)).trans ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity)
    ((mul_le_mul_of_nonneg_left (by linarith) hs.1).trans_eq (div_mul_cancel₀ r hS0.ne')) 2

/-- Real-algebra step turning `r / (2 D + r) * (q₀ - q) ≤ Δ` into an affine bound in `D`. -/
private lemma sub_le_add_of_div_mul_le {q₀ q Δ r D : ℝ} (hr0 : 0 < r) (hD : 0 ≤ D)
    (h : r / (2 * D + r) * (q₀ - q) ≤ Δ) :
    q₀ - q ≤ Δ + 2 * Δ / r * D := by
  have hS0 : 0 < 2 * D + r := by positivity
  have hmul := mul_le_mul_of_nonneg_right h hS0.le
  rw [mul_right_comm, div_mul_cancel₀ r hS0.ne'] at hmul
  have hring : Δ * (2 * D + r) = r * (Δ + 2 * Δ / r * D) := by field_simp; ring
  exact le_of_mul_le_mul_left (hmul.trans_eq hring) hr0

/-- Quadratic lower bound with coefficient `-(1 / τ₁)` when `1 + m τ₁ ≥ 0` and `φ` is finite at
some law `ν₀`, even if `φ μ = ⊤`. -/
private theorem GeneralizedGeodesicallyConvex.exists_forall_sub_add_neg_inv_le
    (h : GeneralizedGeodesicallyConvex m φ μ) (hφ : LowerSemicontinuous φ)
    (hbot : ∀ ν, φ ν ≠ ⊥) {τ₁ : ℝ≥0} (hτ₁ : 0 < τ₁) (hmτ₁ : 0 ≤ 1 + m * τ₁)
    {ν₀ : WassersteinSpace 2 E} (hν₀ : φ ν₀ ≠ ⊤) :
    ∃ C B : ℝ, ∀ ν,
      ((C - B * dist μ ν + -(τ₁ : ℝ)⁻¹ / 2 * dist μ ν ^ 2 : ℝ) : EReal) ≤ φ ν := by
  set c₀ := (φ ν₀).toReal
  have hc₀ : φ ν₀ = c₀ := (EReal.coe_toReal hν₀ (hbot ν₀)).symm
  have hlt : ((c₀ - 1 : ℝ) : EReal) < φ ν₀ := by rw [hc₀, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨r', hr'0, hr'⟩ := Metric.mem_nhds_iff.1 (hφ ν₀ ((c₀ - 1 : ℝ) : EReal) hlt)
  set r := r' / 2
  have hr0 : 0 < r := half_pos hr'0
  set q₀ := c₀ + dist μ ν₀ ^ 2 / (2 * τ₁)
  set Δ := dist μ ν₀ ^ 2 / (2 * τ₁) + 1
  refine ⟨q₀ - Δ - 2 * Δ / r * dist μ ν₀, 2 * Δ / r, fun ν ↦ ?_⟩
  rcases eq_or_ne (φ ν) ⊤ with hν | hν
  · simp [hν]
  have hΦ {w : WassersteinSpace 2 E} (hw : φ w ≠ ⊤) :
      φ w + ((edist μ w ^ 2 / (2 * τ₁) : ℝ≥0∞) : EReal) ≠ ⊤ := by
    rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ₁]
    exact EReal.add_ne_top hw (EReal.coe_ne_top _)
  obtain ⟨γ, hγ, hconv⟩ := h.add_edist_sq_div hτ₁ (hΦ hν₀) (hΦ hν)
  set s := r / (2 * (dist μ ν₀ + dist μ ν) + r)
  obtain ⟨hs, ρ, hρ, hdρ⟩ := hγ.exists_coe_eq_generalizedGeodesic_dist_le hr0
  have hlow : ((c₀ - 1 : ℝ) : EReal) ≤ φ ρ + ((dist μ ρ ^ 2 / (2 * τ₁) : ℝ) : EReal) :=
    ((hr' (Metric.mem_ball'.2 (hdρ.trans_lt (half_lt_self hr'0)))).le).trans
      (le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity)))
  have hup := hconv s hs ρ hρ
  simp only [coe_edist_sq_div_eq_coe_dist_sq_div hτ₁] at hup
  set q := (φ ν).toReal + dist μ ν ^ 2 / (2 * τ₁)
  have hq : φ ν + ((dist μ ν ^ 2 / (2 * τ₁) : ℝ) : EReal) = q := by
    rw [← EReal.coe_toReal hν (hbot ν), EReal.coe_add]
  have hq₀ : φ ν₀ + ((dist μ ν₀ ^ 2 / (2 * τ₁) : ℝ) : EReal) = q₀ := by rw [hc₀, EReal.coe_add]
  rw [hq₀, hq] at hup
  set I := ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd
  have hm_nonneg : 0 ≤ (m + (τ₁ : ℝ)⁻¹) / 2 * s * (1 - s) * I := by
    have hτ₁' : (0 : ℝ) < τ₁ := hτ₁
    have hm : m + (τ₁ : ℝ)⁻¹ = (1 + m * τ₁) / τ₁ := by field_simp; ring
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (div_nonneg (hm ▸ div_nonneg hmτ₁ hτ₁'.le) zero_le_two) hs.1) (sub_nonneg.2 hs.2))
      (integral_nonneg fun _ ↦ by positivity)
  have hreal : c₀ - 1 ≤ (1 - s) * q₀ + s * q - (m + (τ₁ : ℝ)⁻¹) / 2 * s * (1 - s) * I := by
    exact_mod_cast hlow.trans hup
  have hdiv := sub_le_add_of_div_mul_le hr0 (add_nonneg dist_nonneg dist_nonneg)
    (by linarith : s * (q₀ - q) ≤ Δ)
  rw [← EReal.coe_toReal hν (hbot ν), EReal.coe_le_coe_iff]
  have hpen : -(τ₁ : ℝ)⁻¹ / 2 * dist μ ν ^ 2 = -(dist μ ν ^ 2 / (2 * τ₁)) := by ring
  linarith

/-- **Coercivity of energies convex along generalized geodesics.** If `φ` is `m`-convex along
generalized geodesics based at `μ`, lower semicontinuous, and never takes the value `⊥`, then
`φ_τ(ρ) > -∞` for every law `ρ` and every time step `τ` with `1 + m τ > 0`. -/
theorem GeneralizedGeodesicallyConvex.moreauYosida_ne_bot
    (h : GeneralizedGeodesicallyConvex m φ μ) (hφ : LowerSemicontinuous φ)
    (hbot : ∀ ν, φ ν ≠ ⊥) (hmτ : 0 < 1 + m * τ) (ρ : WassersteinSpace 2 E) :
    moreauYosida φ τ ρ ≠ ⊥ := by
  by_cases hdom : ∃ ν₀, φ ν₀ ≠ ⊤
  · obtain ⟨ν₀, hν₀⟩ := hdom
    set δ : ℝ := (1 + m * τ) / (2 * (|m| + 1))
    have hδ : 0 < δ := by positivity
    set τ₁ : ℝ≥0 := τ + Real.toNNReal δ
    have hτ₁_coe : (τ₁ : ℝ) = τ + δ := by simp [τ₁, Real.coe_toNNReal _ hδ.le]
    have hττ₁ : (τ : ℝ) < τ₁ := by linarith
    have hτ₁ : 0 < τ₁ := NNReal.coe_pos.1 (by linarith [NNReal.coe_nonneg τ])
    have hmτ₁ : 0 ≤ 1 + m * τ₁ := by
      have : (|m| + 1) * δ = (1 + m * τ) / 2 := by dsimp [δ]; field_simp
      rw [hτ₁_coe]
      nlinarith [neg_abs_le m]
    obtain ⟨C, B, hCB⟩ := h.exists_forall_sub_add_neg_inv_le hφ hbot hτ₁ hmτ₁ hν₀
    refine moreauYosida_ne_bot_of_forall_sub_add_le hCB ?_ ρ
    have hinv : 1 + -(τ₁ : ℝ)⁻¹ * τ = (τ₁ - τ) / τ₁ := by
      have := (NNReal.coe_pos.2 hτ₁).ne'
      field_simp
      ring
    rw [hinv]
    exact div_pos (sub_pos.2 hττ₁) (NNReal.coe_pos.2 hτ₁)
  · push Not at hdom
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0)
      (le_moreauYosida_iff.2 fun ν _ ↦ by simp [hdom ν])

/-- **Existence of the JKO step under convexity along generalized geodesics.** Let `φ` be a lower
semicontinuous energy on `P₂(E)` that is `m`-convex along generalized geodesics based at `μ`. Then
for every time step `τ` with `1 + m τ > 0`, the JKO step `moreauYosidaResolvent φ τ μ` is
nonempty, without any narrow compactness assumption. -/
theorem GeneralizedGeodesicallyConvex.moreauYosidaResolvent_nonempty
    (h : GeneralizedGeodesicallyConvex m φ μ) (hφ : LowerSemicontinuous φ)
    (hmτ : 0 < 1 + m * τ) : (moreauYosidaResolvent φ τ μ).Nonempty := by
  by_cases hbot : ∀ ν, φ ν ≠ ⊥
  · exact moreauYosidaResolvent_nonempty_of_forall_exists_convexAlong hφ hmτ
      (fun hτ _ _ h₀ h₁ ↦ h.exists_convexAlong_add_dist_sq_div (pos_iff_ne_zero.2 hτ) hmτ.le h₀ h₁)
      (h.moreauYosida_ne_bot hφ hbot hmτ μ)
  · push Not at hbot
    obtain ⟨ν, hν⟩ := hbot
    exact ⟨ν, mem_moreauYosidaResolvent_iff_isMinOn.2 (isMinOn_univ_iff.2 fun z ↦ by simp [hν])⟩

/-- **Existence of JKO sequences under convexity along generalized geodesics.** Let `φ` be a lower
semicontinuous energy on `P₂(E)` that is `m`-convex along generalized geodesics based at every law.
Then for every time step `τ` with `1 + m τ > 0` and every initial law `μ₀`, there exists a JKO
sequence `u` with `u 0 = μ₀` and `u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)`. -/
theorem exists_forall_mem_moreauYosidaResolvent_of_generalizedGeodesicallyConvex
    (h : ∀ μ, GeneralizedGeodesicallyConvex m φ μ) (hφ : LowerSemicontinuous φ)
    (hmτ : 0 < 1 + m * τ) (μ₀ : WassersteinSpace 2 E) :
    ∃ u : ℕ → WassersteinSpace 2 E, u 0 = μ₀ ∧
      ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) := by
  choose f hf using fun μ ↦ (h μ).moreauYosidaResolvent_nonempty hφ hmτ
  exact ⟨fun n ↦ f^[n] μ₀, rfl, fun n ↦ by simpa only [Function.iterate_succ_apply'] using hf _⟩

end Hilbert

end TauCeti
