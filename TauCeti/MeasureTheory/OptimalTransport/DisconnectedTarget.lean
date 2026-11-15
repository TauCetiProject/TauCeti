/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.Probability.Distributions.Uniform.Ball.Support
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# Brenier maps onto a disconnected target

Caffarelli's regularity theory for the Brenier map assumes a convex target, and that assumption
cannot simply be dropped: smooth positive densities alone do not make the optimal map continuous.
This file records the basic counterexample, with a disconnected target, on a finite-dimensional
real inner product space `E`. The source is the uniform law `uniformBallMeasure c R` on an open
ball, whose density is constant and positive on the ball. The target is the equal-weight mixture
of the uniform laws on two balls with disjoint closures; for positive radii its density is
constant and positive on each of the two balls, and the statements also allow either radius to
vanish, when that component is a point mass. Brenier's theorem
gives an optimal transport map, the gradient of a convex function, unique up to almost everywhere
equality, and that map has no representative continuous on the source ball.

The obstruction is topological rather than variational: no transport map from the connected ball
onto the split target is continuous on the ball, by
`ProbabilityTheory.HasLaw.measure_eq_zero_or_measure_eq_zero_of_continuousOn`, since a continuous
map would carry the ball into a single one of the two pieces.

## Main results

* `TauCeti.not_continuousOn_of_hasLaw_uniformBallMeasure` — no map transporting the uniform law
  on a ball onto the mixture of uniform laws on two separated balls is continuous on the ball;
* `TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_not_continuousOn` — the Brenier
  map between these laws exists, and no map almost everywhere equal to it is continuous on the
  source ball.

## References

* L. A. Caffarelli, *The regularity of mappings with a convex potential*, J. Amer. Math. Soc. 5
  (1992), 99–104.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften
  338, Springer, 2009, chapter 12.
-/

public section

open MeasureTheory ProbabilityTheory Metric Set TauCeti.Probability
open scoped ENNReal Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {a b c : E} {R r r' : ℝ}

/-- **No continuous transport onto two separated balls.** Let `R > 0`, `r, r' ≥ 0`, and let the
closed balls `closedBall a r` and `closedBall b r'` be disjoint, `r + r' < dist a b`. Then no map
`T` pushing the uniform law on `ball c R` forward to the equal-weight mixture of the uniform laws
on `ball a r` and `ball b r'` is continuous on `ball c R`. -/
theorem not_continuousOn_of_hasLaw_uniformBallMeasure (hR : 0 < R) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hab : r + r' < dist a b) {T : E → E}
    (hT : HasLaw T ((2 : ℝ≥0∞)⁻¹ • (uniformBallMeasure a r + uniformBallMeasure b r'))
      (uniformBallMeasure c R)) :
    ¬ContinuousOn T (ball c R) := by
  have := isProbabilityMeasure_uniformBallMeasure (c := a) hr
  have := isProbabilityMeasure_uniformBallMeasure (c := b) hr'
  have hnull (d : E) (ρ : ℝ) : uniformBallMeasure d ρ (closedBall d ρ)ᶜ = 0 :=
    ae_iff.1 (ae_mem_closedBall_uniformBallMeasure d ρ)
  intro hTc
  refine (hT.measure_eq_zero_or_measure_eq_zero_of_continuousOn (convex_ball c R).isPreconnected
    (ae_mem_ball_uniformBallMeasure hR)
    (ball_subset_closedBall.trans (support_uniformBallMeasure c R).ge) hTc isClosed_closedBall
    isClosed_closedBall (closedBall_disjoint_closedBall hab) ?_).elim ?_ ?_
  · simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul, compl_union]
    rw [measure_mono_null inter_subset_left (hnull a r),
      measure_mono_null inter_subset_right (hnull b r'), add_zero, mul_zero]
  · simp [prob_compl_eq_zero_iff measurableSet_closedBall |>.1 (hnull a r)]
  · simp [prob_compl_eq_zero_iff measurableSet_closedBall |>.1 (hnull b r')]

/-- **A split target makes the Brenier map discontinuous.** Let `R > 0`, `r, r' ≥ 0` and
`r + r' < dist a b`, let `μ` be the uniform law on `ball c R` and let `ν` be the equal-weight
mixture of the uniform laws on `ball a r` and `ball b r'`. Then there is a convex, lower
semicontinuous `u : E → EReal` that never takes the value `⊥` whose gradient
`∇ (fun x => (u x).toReal)` is an optimal transport map from `μ` to `ν` for the quadratic cost
`‖x - y‖ ^ 2 / 2`, unique up to `μ`-almost everywhere equality by
`TauCeti.exists_isKantorovichOptimalTransportMap_gradient`; and no map that agrees with it
`μ`-almost everywhere is continuous on `ball c R`. -/
theorem exists_isKantorovichOptimalTransportMap_gradient_and_not_continuousOn (hR : 0 < R)
    (hr : 0 ≤ r) (hr' : 0 ≤ r') (hab : r + r' < dist a b) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        (uniformBallMeasure c R) ((2 : ℝ≥0∞)⁻¹ • (uniformBallMeasure a r + uniformBallMeasure b r'))
        (∇ fun x => (u x).toReal) ∧
      ∀ S : E → E, S =ᵐ[uniformBallMeasure c R] (∇ fun x => (u x).toReal) →
        ¬ContinuousOn S (ball c R) := by
  set ν := (2 : ℝ≥0∞)⁻¹ • (uniformBallMeasure a r + uniformBallMeasure b r')
  have := isProbabilityMeasure_uniformBallMeasure (c := c) hR.le
  have := isProbabilityMeasure_uniformBallMeasure (c := a) hr
  have := isProbabilityMeasure_uniformBallMeasure (c := b) hr'
  have : IsProbabilityMeasure ν := by
    simp only [ν, smul_add]
    exact TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul ENNReal.inv_two_add_inv_two _ _
  -- The quadratic cost is finite: both laws have finite second moments.
  have hν2 : MemLp id 2 ν := ((memLp_id_uniformBallMeasure a r 2).add_measure
    (memLp_id_uniformBallMeasure b r' 2)).smul_measure (ENNReal.inv_ne_top.2 two_ne_zero)
  have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (uniformBallMeasure c R) ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (transportCost_le_lintegral (isCoupling_prod _ _) _)
    rw [(isCoupling_prod _ _).lintegral_norm_sub_sq_div_two (memLp_id_uniformBallMeasure c R 2)
      hν2]
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, hconv, hlsc, hbot, -, hopt, -⟩ := exists_isKantorovichOptimalTransportMap_gradient
    (uniformBallMeasure_absolutelyContinuous hR.ne') hfin
  exact ⟨u, hconv, hlsc, hbot, hopt, fun S hS =>
    not_continuousOn_of_hasLaw_uniformBallMeasure hR hr hr' hab (hopt.toHasLaw.congr hS)⟩

end TauCeti
