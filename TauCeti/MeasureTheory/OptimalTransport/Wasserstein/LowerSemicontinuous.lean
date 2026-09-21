/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
-- Proof-only: weak lower semicontinuity of the optimal transport cost, and `W_∞` as the supremum
-- of the finite-exponent distances.
import TauCeti.MeasureTheory.OptimalTransport.Stability
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Infinity.Basic

/-!
# Lower semicontinuity of the Wasserstein distance under weak convergence

On a Polish ground space the `p`-Wasserstein distance is a lower semicontinuous function of the
pair of laws for the weak topology on `ProbabilityMeasure X × ProbabilityMeasure X`: if
`μₙ ⇀ μ` and `νₙ ⇀ ν`, then

`W_p (μ, ν) ≤ liminf W_p (μₙ, νₙ)`.

The inequality can be strict — for `μₙ = (1 - 1 / n) δ₀ + (1 / n) δₙ` on `ℝ` one has `μₙ ⇀ δ₀`
while `W₁ (μₙ, δ₀) = 1` — so weak convergence does not make `W_p` continuous; that needs the
convergence of `p`-moments as well. Lower semicontinuity is what the direct method consumes
whenever a Wasserstein distance appears in a functional to be minimised over weakly compact sets
of laws.

For a positive finite exponent the distance is a continuous increasing function of the optimal
transport cost of `edist ^ p` (`TauCeti.wassersteinEDist_rpow_eq_transportCost`), and that cost is
weakly lower semicontinuous in the marginals by `TauCeti.lowerSemicontinuous_transportCost`; at
exponent zero the distance between probability measures vanishes. These arguments need only an
extended pseudometric whose topology is Polish. The endpoint `p = ∞` follows on a Polish metric
space from `TauCeti.wassersteinEDist_top_eq_iSup`, since a supremum of lower semicontinuous
functions is lower semicontinuous.

## Main statements

* `TauCeti.lowerSemicontinuous_wassersteinEDist_of_ne_top` — lower semicontinuity for every finite
  exponent, on an extended pseudometric space with Polish topology;
* `TauCeti.lowerSemicontinuous_wassersteinEDist` — lower semicontinuity for every exponent,
  including `p = ∞`, on a Polish metric space;
* `TauCeti.wassersteinEDist_le_liminf` — its form along weakly convergent families of laws.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  `W_p` is shown to be lower semicontinuous under weak convergence.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, §7.1.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

section Finite

variable {X : Type*} [PseudoEMetricSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  {p : ℝ≥0∞}

/-- **The Wasserstein distance is weakly lower semicontinuous**, for every finite exponent: on an
extended pseudometric space whose topology is Polish, `(μ, ν) ↦ W_p (μ, ν)` is lower
semicontinuous on `ProbabilityMeasure X × ProbabilityMeasure X`. -/
theorem lowerSemicontinuous_wassersteinEDist_of_ne_top (hp : p ≠ ∞) :
    LowerSemicontinuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      wassersteinEDist p q.1.toMeasure q.2.toMeasure := by
  rcases eq_or_ne p 0 with rfl | hp0
  · -- At exponent `0` every objective vanishes, so the distance of two probability laws is `0`.
    have h0 : (fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
        wassersteinEDist 0 q.1.toMeasure q.2.toMeasure) = fun _ ↦ 0 :=
      funext fun q ↦ nonpos_iff_eq_zero.1 <|
        (wassersteinEDist_le (isCoupling_prod q.1.toMeasure q.2.toMeasure) 0).trans_eq
          eLpNorm_exponent_zero
    rw [h0]
    exact lowerSemicontinuous_const
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- `W_p` is the `1 / p`-th power of the optimal transport cost of `edist ^ p`.
  have heq : (fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      wassersteinEDist p q.1.toMeasure q.2.toMeasure) =
      (fun t : ℝ≥0∞ ↦ t ^ p.toReal⁻¹) ∘ fun q ↦
        transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) q.1.toMeasure q.2.toMeasure := by
    funext q
    rw [Function.comp_apply, ← wassersteinEDist_rpow_eq_transportCost hp0 hp,
      ENNReal.rpow_rpow_inv hr.ne']
  rw [heq]
  exact ENNReal.continuous_rpow_const.comp_lowerSemicontinuous
    (lowerSemicontinuous_transportCost
      (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous)
    (ENNReal.monotone_rpow_of_nonneg (inv_nonneg.2 hr.le))

end Finite

section Metric

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X]

/-- **The Wasserstein distance is weakly lower semicontinuous**, for every exponent including
`p = ∞`: on a Polish metric space, `(μ, ν) ↦ W_p (μ, ν)` is lower semicontinuous on
`ProbabilityMeasure X × ProbabilityMeasure X`. -/
theorem lowerSemicontinuous_wassersteinEDist (p : ℝ≥0∞) :
    LowerSemicontinuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      wassersteinEDist p q.1.toMeasure q.2.toMeasure := by
  rcases eq_or_ne p ∞ with rfl | hp
  · simp_rw [wassersteinEDist_top_eq_iSup]
    exact lowerSemicontinuous_iSup fun p ↦
      lowerSemicontinuous_wassersteinEDist_of_ne_top ENNReal.coe_ne_top
  · exact lowerSemicontinuous_wassersteinEDist_of_ne_top hp

/-- **Weak limits do not increase the Wasserstein distance**: on a Polish metric space, if
`μₙ ⇀ μ` and `νₙ ⇀ ν` along a filter `l`, then `W_p (μ, ν) ≤ liminf W_p (μₙ, νₙ)` for every
exponent `p`, including `p = ∞`. -/
theorem wassersteinEDist_le_liminf {ι : Type*} {l : Filter ι} {μs νs : ι → ProbabilityMeasure X}
    {μ ν : ProbabilityMeasure X} (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (p : ℝ≥0∞) :
    wassersteinEDist p μ.toMeasure ν.toMeasure ≤
      liminf (fun i ↦ wassersteinEDist p (μs i).toMeasure (νs i).toMeasure) l :=
  le_of_forall_lt_imp_le_of_dense fun a ha ↦ le_liminf_of_le (by isBoundedDefault) <|
    ((hμ.prodMk_nhds hν).eventually (lowerSemicontinuous_wassersteinEDist p (μ, ν) a ha)).mono
      fun _ h ↦ h.le

end Metric

end TauCeti
