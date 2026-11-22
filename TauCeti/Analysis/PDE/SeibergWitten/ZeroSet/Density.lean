/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Covering
public import TauCeti.MeasureTheory.Measure.FiniteMeasure.LowerDensity
public import TauCeti.MeasureTheory.Measure.Vague.LowerDensity
import TauCeti.MeasureTheory.Covering.HausdorffDensity

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

On a noncompact manifold, or on the total space of a normal bundle after rescaling, the defect
measures are only locally finite, with masses bounded on compact sets, and the constants of the
differential inequality are only locally uniform. A subsequence of such measures converges
vaguely, against continuous compactly supported functions, to a locally finite measure `ν`
(`TauCeti.exists_subseq_tendsto_integral_of_iSup_measure_ne_top`). Let `Z₀` be a set of limits of
zeros: every point of `Z₀` is a limit of points of `Zᵢ`. If near each point the differential
inequality and the smallest-scale bound hold at the zeros of `αᵢ` with constants depending on the
point, then near each point the limit measure has a lower density bound at the points of `Z₀`
with uniform constants, and `Z₀` has locally finite two-dimensional Hausdorff measure
(`exists_forall_ofReal_mul_sq_le_measure_closedBall_of_tendsto_integral_compactlySupported`).

The statements are for an arbitrary metric space, proper in the locally finite case, and an
arbitrary nontrivial filter, so they apply to the manifold with a distance inducing its topology,
along any subsequence. The differential inequality and the smallest-scale bound are hypotheses.

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

open scoped CompactlySupported in
/-- **Lower density of a vague limit of defect measures.** Let `X` be a proper metric space, let
`r i → ∞` along a nontrivial filter, let locally finite measures `μ i` converge vaguely to `ν`,
and let every point of `Z₀` be a limit of points of `Z i`. Suppose that every point has a
neighbourhood `U` and constants `C, C₁, K ≥ 0` and `c₀, c₁, σ₀ > 0` such that eventually, at
every point `y ∈ Z i ∩ U`, the function `E(σ) = μ i (closedBall y σ)` satisfies Taubes's
differential inequality `E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ (r i)^(-1/2)) E'(σ) + K σ⁴` at almost
every `σ ∈ (c₀ (r i)^(-1/2), σ₀)`, and `E(c₀ (r i)^(-1/2)) ≥ c₁ / r i`. Then every point has a
neighbourhood `V` and constants `c, ρ₀ > 0` with `ν (closedBall y ρ) ≥ c ρ ^ 2` for every
`y ∈ Z₀ ∩ V` and every radius `0 < ρ ≤ ρ₀`, and `Z₀` has locally finite two-dimensional
Hausdorff measure. -/
theorem exists_forall_ofReal_mul_sq_le_measure_closedBall_of_tendsto_integral_compactlySupported
    [ProperSpace X] [l.NeBot] {r : ι → ℝ} (hr : Tendsto r l atTop) {μ : ι → Measure X}
    [∀ i, IsLocallyFiniteMeasure (μ i)] {ν : Measure X} [IsLocallyFiniteMeasure ν]
    (hμ : ∀ f : C_c(X, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)))
    {Z : ι → Set X} {Z₀ : Set X} (hZ : ∀ x ∈ Z₀, ∀ ε > 0, ∀ᶠ i in l, ∃ y ∈ Z i, dist y x < ε)
    (hmono : ∀ x, ∃ U ∈ 𝓝 x, ∃ C C₁ K c₀ c₁ σ₀ : ℝ, 0 ≤ C ∧ 0 ≤ C₁ ∧ 0 ≤ K ∧ 0 < c₀ ∧ 0 < c₁ ∧
      0 < σ₀ ∧ ∀ᶠ i in l, ∀ y ∈ Z i ∩ U,
        (∀ᵐ σ, σ ∈ Ioo (c₀ / √(r i)) σ₀ →
          (μ i (closedBall y σ)).toReal ≤ σ / 2 * (1 + C * σ) * (1 + C₁ / √(r i)) *
            deriv (fun σ ↦ (μ i (closedBall y σ)).toReal) σ + K * σ ^ 4) ∧
        c₁ / r i ≤ (μ i (closedBall y (c₀ / √(r i)))).toReal) :
    (∀ x, ∃ V ∈ 𝓝 x, ∃ c > 0, ∃ ρ₀ > 0, ∀ y ∈ Z₀ ∩ V, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ 2) ≤ ν (closedBall y ρ)) ∧
      IsLocallyFiniteMeasure (μH[2].restrict Z₀) := by
  have hdens : ∀ x, ∃ V ∈ 𝓝 x, ∃ c > 0, ∃ ρ₀ > 0, ∀ y ∈ Z₀ ∩ V, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ 2) ≤ ν (closedBall y ρ) := by
    intro x
    obtain ⟨U, hU, C, C₁, K, c₀, c₁, σ₀, hC, hC₁, hK, hc₀, hc₁, hσ₀, hev⟩ := hmono x
    obtain ⟨c, hc, ρ₀, hρ₀, hball⟩ :=
      exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le (X := X) hC hC₁ hK hc₀ hc₁ hσ₀
    -- The smallest admissible radius `c₀ / √(r i)` tends to zero.
    have hh : Tendsto (fun i ↦ c₀ / √(r i)) l (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hr)
    have hev' : ∀ᶠ i in l, ∀ y ∈ Z i ∩ U, ∀ ρ, c₀ / √(r i) ≤ ρ → ρ ≤ ρ₀ →
        ENNReal.ofReal (c * ρ ^ 2) ≤ μ i (closedBall y ρ) := by
      filter_upwards [hev, hr.eventually_ge_atTop 1] with i hi hri y hy
      exact hball (r i) hri (μ i) y measure_closedBall_lt_top.ne (hi y hy).1 (hi y hy).2
    refine ⟨interior U, interior_mem_nhds.2 hU, c, hc, ρ₀, hρ₀, fun y hy ρ hρ hρρ₀ ↦ ?_⟩
    exact Measure.le_measure_closedBall_of_tendsto_integral_compactlySupported hμ (hZ y hy.1) hh
      (mem_interior_iff_mem_nhds.1 hy.2) hev' hρ hρρ₀
  exact ⟨hdens, Measure.isLocallyFiniteMeasure_restrict_hausdorffMeasure_of_ofReal_mul_pow_le ν
    hdens⟩

end TauCeti.SeibergWitten
