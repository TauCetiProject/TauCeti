/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.UniformIntegrable
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence

/-!
# Wasserstein convergence and convergence of moments

On the finite-moment Wasserstein space `TauCeti.WassersteinSpace p X` over a separable Borel
pseudometric space, convergence in the `p`-Wasserstein distance forces convergence of the
`p`-moments, and the `p`-moments are then uniformly integrable along the convergent family.
Together with `TauCeti.WassersteinSpace.continuous_toProbabilityMeasure`, which gives weak
convergence, this is the necessity half of the classical characterization of `W_p` convergence,
for a finite exponent `1 ≤ p < ∞`, as weak convergence together with convergence of `p`-moments.

The moment of a law about a basepoint `x` is its Wasserstein distance from the Dirac law at `x`
(`TauCeti.wassersteinEDist_dirac_left`), so the triangle inequality makes it a continuous
function on the Wasserstein space; this holds for every exponent, including `p = ∞`, in its
`eLpNorm` form. Uniform integrability of the tails then follows from the general criterion
`TauCeti.exists_setLIntegral_le_of_tendsto_lintegral` for integrals of unbounded continuous
functions along weakly convergent families.

## Main statements

* `TauCeti.WassersteinSpace.continuous_eLpNorm_edist` — the `L^p` norm of the distance to a
  basepoint is continuous on the Wasserstein space;
* `TauCeti.WassersteinSpace.continuous_lintegral_edist_rpow` — for `p < ∞`, so is the `p`-moment
  `∫⁻ y, edist x y ^ p`;
* `TauCeti.WassersteinSpace.exists_setLIntegral_edist_rpow_le` — along a `W_p`-convergent family
  the `p`-moments have uniformly small tails.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Definition 6.8
  and Theorem 6.9.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, Proposition 7.1.5.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace WassersteinSpace

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- The `L^p` norm of the distance to a basepoint, that is the `p`-th root of the `p`-moment
about that basepoint, is continuous on the Wasserstein space: it is the Wasserstein distance from
the Dirac law at the basepoint. -/
theorem continuous_eLpNorm_edist (x : X) :
    Continuous fun μ : WassersteinSpace p X ↦
      eLpNorm (fun y ↦ edist x y) p ((μ : ProbabilityMeasure X) : Measure X) := by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun μ ν ↦ ?_
  rw [one_mul, edist_comm, edist_def, ← wassersteinEDist_dirac_left measurable_edist,
    ← wassersteinEDist_dirac_left measurable_edist]
  exact wassersteinEDist_triangle measurable_edist Fact.out _ _ _

/-- For a finite exponent `p`, the `p`-moment `∫⁻ y, edist x y ^ p` about a basepoint is a
continuous function on the `p`-Wasserstein space. -/
theorem continuous_lintegral_edist_rpow (hp : p ≠ ∞) (x : X) :
    Continuous fun μ : WassersteinSpace p X ↦
      ∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) := by
  simp_rw [← eLpNorm_rpow_eq_lintegral (zero_lt_one.trans_le Fact.out).ne' hp]
  exact (ENNReal.continuous_rpow_const).comp (continuous_eLpNorm_edist x)

/-- **Uniform integrability of moments along a `W_p`-convergent family.** For a finite exponent
`1 ≤ p < ∞`, along a family converging in the `p`-Wasserstein distance the `p`-moments about any
basepoint have uniformly small tails: for every `ε > 0` there is a radius `R` such that eventually
the part of the `p`-moment coming from distance at least `R` is at most `ε`. -/
theorem exists_setLIntegral_edist_rpow_le (hp : p ≠ ∞) {γ : Type*} {L : Filter γ}
    {μs : γ → WassersteinSpace p X} {μ : WassersteinSpace p X} (h : Tendsto μs L (𝓝 μ)) (x : X)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μs i : ProbabilityMeasure X) : Measure X) ≤ ε := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set g : X → ℝ≥0 := fun y ↦ nndist x y ^ p.toReal
  have hg : Continuous g :=
    (NNReal.continuous_rpow_const hq.le).comp (continuous_const.nndist continuous_id)
  have hcoe (y : X) : (g y : ℝ≥0∞) = edist x y ^ p.toReal := by
    rw [ENNReal.coe_rpow_of_nonneg _ hq.le, edist_nndist]
  have hweak : Tendsto (fun i ↦ (μs i : ProbabilityMeasure X)) L
      (𝓝 (μ : ProbabilityMeasure X)) := (continuous_toProbabilityMeasure.tendsto μ).comp h
  have hfin : ∫⁻ y, g y ∂((μ : ProbabilityMeasure X) : Measure X) ≠ ∞ := by
    simp_rw [hcoe, ← eLpNorm_rpow_eq_lintegral hp0 hp]
    exact ENNReal.rpow_ne_top_of_nonneg hq.le
      ((hasFiniteMoment μ).memLp measurable_edist_right.aestronglyMeasurable).eLpNorm_ne_top
  have hlim : Tendsto (fun i ↦ ∫⁻ y, g y ∂((μs i : ProbabilityMeasure X) : Measure X)) L
      (𝓝 (∫⁻ y, g y ∂((μ : ProbabilityMeasure X) : Measure X))) := by
    simp_rw [hcoe]
    exact ((continuous_lintegral_edist_rpow hp x).tendsto μ).comp h
  obtain ⟨R, hR⟩ := exists_setLIntegral_le_of_tendsto_lintegral hg hweak hfin hlim hε
  refine ⟨R ^ p.toReal⁻¹, hR.mono fun i hi ↦ ?_⟩
  have hset : {y | R ^ p.toReal⁻¹ ≤ nndist x y} = {y | R ≤ g y} := by
    ext y
    exact NNReal.rpow_inv_le_iff hq
  simpa only [hset, hcoe] using hi

end WassersteinSpace

end TauCeti
