/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MoreauYosida.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Basic
import TauCeti.Data.EReal.Operations

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
notion for energies and proves that it makes the JKO step unique.

An energy `φ` is *`m`-convex along generalized geodesics based at `μ`*
(`TauCeti.GeneralizedGeodesicallyConvex m φ μ`) if any two laws `ν₀` and `ν₁` of its effective
domain are joined by the generalized geodesic of some such plan `γ` along which

`φ ν_t ≤ (1 - t) φ ν₀ + t φ ν₁ - (m / 2) t (1 - t) ∫ ‖y₀ - y₁‖² dγ`.

The integral is the quadratic cost of the coupling of `ν₀` and `ν₁` carried by `γ`; it is at least
`W₂ (ν₀, ν₁) ^ 2`. If `φ` has this property, then the penalized functional of the JKO step is
`(m + 1 / τ)`-convex along the same curves
(`TauCeti.GeneralizedGeodesicallyConvex.add_edist_sq_div`), so the JKO step is unique as soon as
`1 + m τ > 0` (`TauCeti.GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent`): the
midpoint of the generalized geodesic joining two minimizers would otherwise do strictly better.

## Main definitions

* `TauCeti.GeneralizedGeodesicallyConvex m φ μ`: the energy `φ` on `P₂(E)` is `m`-convex along
  generalized geodesics based at `μ`.

## Main results

* `TauCeti.IsGeneralizedGeodesicPlan.dist_sq_add_le`: the convexity of the squared Wasserstein
  distance from the base point along a generalized geodesic, as an inequality of real numbers.
* `TauCeti.GeneralizedGeodesicallyConvex.add_edist_sq_div`: the penalized functional
  `ν ↦ φ ν + W₂ (μ, ν) ^ 2 / (2τ)` of an energy that is `m`-convex along generalized geodesics
  based at `μ` is `(m + 1 / τ)`-convex along them.
* `TauCeti.GeneralizedGeodesicallyConvex.eq_of_mem_moreauYosidaResolvent` and
  `TauCeti.GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent`: uniqueness of the
  JKO step when `1 + m τ > 0`.

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
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ ν : WassersteinSpace 2 E,
      ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t →
      φ ν ≤ ((1 - t : ℝ) : EReal) * φ ν₀ + (t : EReal) * φ ν₁ -
        ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal)

/-- The defining condition of convexity along generalized geodesics. -/
theorem generalizedGeodesicallyConvex_def :
    GeneralizedGeodesicallyConvex m φ μ ↔
      ∀ ⦃ν₀ ν₁ : WassersteinSpace 2 E⦄, φ ν₀ ≠ ⊤ → φ ν₁ ≠ ⊤ → ∃ γ : Measure (E × E × E),
        IsGeneralizedGeodesicPlan 2 γ ((μ : ProbabilityMeasure E) : Measure E)
          ((ν₀ : ProbabilityMeasure E) : Measure E) ((ν₁ : ProbabilityMeasure E) : Measure E) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ ν : WassersteinSpace 2 E,
          ((ν : ProbabilityMeasure E) : Measure E) = generalizedGeodesic γ t →
          φ ν ≤ ((1 - t : ℝ) : EReal) * φ ν₀ + (t : EReal) * φ ν₁ -
            ((m / 2 * t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd : ℝ) : EReal) :=
  Iff.rfl

/-- Convexity along generalized geodesics with a parameter `m` implies it for every smaller
parameter. -/
theorem GeneralizedGeodesicallyConvex.mono (h : GeneralizedGeodesicallyConvex m φ μ)
    (hm : m' ≤ m) : GeneralizedGeodesicallyConvex m' φ μ := fun _ _ h₀ h₁ ↦
  (h h₀ h₁).imp fun γ hγ ↦ ⟨hγ.1, fun t ht ν hν ↦ (hγ.2 t ht ν hν).trans <|
    EReal.sub_le_sub le_rfl <| EReal.coe_le_coe_iff.2 <| by
      have : 0 ≤ t * (1 - t) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd :=
        mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (integral_nonneg fun _ ↦ by positivity)
      nlinarith⟩

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
    have hτ' : (0 : ℝ) < τ := hτ
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
    have hτ' : (0 : ℝ) < τ := hτ
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

end Hilbert

end TauCeti
