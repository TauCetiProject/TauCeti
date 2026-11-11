/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Covering
public import TauCeti.MeasureTheory.Measure.FiniteMeasure.LowerDensity

/-!
# Lower density of the limit defect measure at the limit zero set

Consider solutions of the Seiberg–Witten equations on a symplectic four-manifold `X` at
parameters `rᵢ → ∞`, with normalized spinors `χᵢ = αᵢ u₀ + βᵢ`, zero sets `Zᵢ = αᵢ⁻¹(0)` and
defect measures `μᵢ = (rᵢ / 4) |1 - |χᵢ|²| dvol`, whose total masses are bounded independently of
`i`. Along a subsequence the zero sets converge in the Hausdorff distance to a closed set `Z` (see
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Limit`) and the defect measures converge weakly to a
finite measure `ν`.

At every zero `x` of `αᵢ`, the defect energy `E(σ) = μᵢ (closedBall x σ)` satisfies Taubes's
differential inequality `E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ rᵢ^(-1/2)) E'(σ) + K σ⁴` for almost
every `σ ∈ (c₀ rᵢ^(-1/2), σ₀)` and the smallest-scale bound `E(c₀ rᵢ^(-1/2)) ≥ c₁ / rᵢ`, with
constants independent of `i`. Integrating the inequality gives `μᵢ (closedBall x ρ) ≥ c ρ ²` for
`c₀ rᵢ^(-1/2) ≤ ρ ≤ ρ₀`
(`TauCeti.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le`), and since the smallest
scale `c₀ rᵢ^(-1/2)` tends to zero this bound passes to the limit
(`MeasureTheory.FiniteMeasure.le_measure_closedBall_of_tendsto`). The result
(`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_tendsto`) is the
support-point lower density of the limit measure:

`ν (closedBall x ρ) ≥ c ρ ²`  for every `x ∈ Z` and `0 < ρ ≤ ρ₀`,

with `c` and `ρ₀` depending only on the constants of the differential inequality. By the density
comparison for Hausdorff measure, `(c / 4) μH[2] Z ≤ ν U` for every open `U ⊇ Z`. Taking `U` to be
the whole space, the limit zero set has two-dimensional Hausdorff measure at most `4 ν(X) / c`,
which is finite.

The statements are for an arbitrary metric space and an arbitrary nontrivial filter, so they apply
to the manifold with a distance inducing its topology, along any subsequence. The differential
inequality and the smallest-scale bound are hypotheses.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Filter Metric MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal

namespace TauCeti.SeibergWitten

variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {l : Filter ι}

/-- **Lower density of the limit defect measure.** Fix `C, C₁, K ≥ 0` and `c₀, c₁, σ₀ > 0`.
There are constants `c > 0` and `ρ₀ > 0` with the following property. Let `r i → ∞` along a
nontrivial filter, let finite measures `μ i` converge weakly to `ν`, and let closed sets `Z i`
converge to `Z₀` in the Hausdorff distance. Suppose that eventually, at every point `x ∈ Z i`,
the function `E(σ) = μ i (closedBall x σ)` satisfies Taubes's differential inequality
`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ (r i)^(-1/2)) E'(σ) + K σ⁴` at almost every
`σ ∈ (c₀ (r i)^(-1/2), σ₀)`, and `E(c₀ (r i)^(-1/2)) ≥ c₁ / r i`. Then
`ν (closedBall x ρ) ≥ c ρ ^ 2` for every `x ∈ Z₀` and every radius `0 < ρ ≤ ρ₀`, and
`(c / 4) μH[2] Z₀ ≤ ν U` for every open set `U` containing `Z₀`. -/
theorem exists_forall_ofReal_mul_sq_le_measure_closedBall_of_tendsto [l.NeBot]
    {C C₁ K c₀ c₁ σ₀ : ℝ} (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hσ₀ : 0 < σ₀) :
    ∃ c > 0, ∃ ρ₀ > 0, ∀ (r : ι → ℝ) (μ : ι → FiniteMeasure X) (ν : FiniteMeasure X)
      (Z : ι → Closeds X) (Z₀ : Closeds X), Tendsto r l atTop → Tendsto μ l (𝓝 ν) →
      Tendsto Z l (𝓝 Z₀) →
      (∀ᶠ i in l, ∀ x ∈ Z i,
        (∀ᵐ σ, σ ∈ Ioo (c₀ / √(r i)) σ₀ →
          ((μ i : Measure X) (closedBall x σ)).toReal ≤
            σ / 2 * (1 + C * σ) * (1 + C₁ / √(r i)) *
              deriv (fun σ ↦ ((μ i : Measure X) (closedBall x σ)).toReal) σ + K * σ ^ 4) ∧
        c₁ / r i ≤ ((μ i : Measure X) (closedBall x (c₀ / √(r i)))).toReal) →
      (∀ x ∈ Z₀, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
        ENNReal.ofReal (c * ρ ^ 2) ≤ (ν : Measure X) (closedBall x ρ)) ∧
      ∀ U, IsOpen U → (Z₀ : Set X) ⊆ U →
        ENNReal.ofReal (c / 4) * μH[2] (Z₀ : Set X) ≤ (ν : Measure X) U := by
  obtain ⟨c, hc, ρ₀, hρ₀, hdens⟩ :=
    exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le (X := X) hC hC₁ hK hc₀ hc₁ hσ₀
  refine ⟨c, hc, ρ₀, hρ₀, fun r μ ν Z Z₀ hr hμ hZ hmono ↦ ?_⟩
  -- The smallest admissible radius `c₀ / √(r i)` tends to zero.
  have hh : Tendsto (fun i ↦ c₀ / √(r i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hr)
  have hdens' : ∀ᶠ i in l, ∀ y ∈ Z i, ∀ ρ, c₀ / √(r i) ≤ ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ 2) ≤ (μ i : Measure X) (closedBall y ρ) := by
    filter_upwards [hmono, hr.eventually_ge_atTop 1] with i hi hri y hy
    exact hdens (r i) hri (μ i) y (measure_ne_top _ _) (hi y hy).1 (hi y hy).2
  refine ⟨fun x hx ρ hρ hρρ₀ ↦
    FiniteMeasure.le_measure_closedBall_of_tendsto hμ hZ hh hdens' hx hρ hρρ₀,
    fun U hU hZU ↦ ?_⟩
  have h4 : c / 4 = c / 2 ^ 2 := by norm_num
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  simpa only [h4, h2] using
    FiniteMeasure.mul_hausdorffMeasure_le_measure_of_tendsto hμ hZ hh hρ₀ hdens' hU hZU

end TauCeti.SeibergWitten
