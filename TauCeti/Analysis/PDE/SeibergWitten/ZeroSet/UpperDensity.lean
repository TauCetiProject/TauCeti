/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.MeasureTheory.Measure.FiniteMeasure.UpperDensity
import TauCeti.Analysis.Calculus.PowerGrowth

/-!
# The quadratic upper bound for the defect energy at large parameter

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ = α u₀ + β`, and its defect measure is
`μ = (r / 4) |1 - |χ|²| dvol`, whose total mass is bounded independently of `r`. Taubes's
monotonicity estimate says that, at every centre `x`, the defect energy
`E(σ) = μ (closedBall x σ)` of the balls about `x` satisfies the differential inequality

`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) E'(σ) + K σ⁴`

at almost every `σ ∈ (c₀ r^(-1/2), σ₀)`, with constants independent of `r`, of the solution and
of `x`. Integrating it from `σ` up to the fixed radius `σ₀`, where `E(σ₀)` is bounded by the
total mass `M`, gives the **quadratic upper bound**

`μ (closedBall x σ) ≤ C' σ ²`  for `c₀ r^(-1/2) ≤ σ ≤ σ₀`,

with `C'` depending only on `C, C₁, K, c₀, σ₀` and `M`
(`TauCeti.exists_forall_measure_closedBall_le_of_ae_le`). The real-variable integration step is
`TauCeti.le_mul_sq_of_le_mul_deriv_add`. Unlike the quadratic lower bound
(`TauCeti.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le`), which needs the centre to
be a zero of `α`, this bound holds at every centre.

For solutions at parameters `rᵢ → ∞` whose defect measures converge weakly to a finite measure
`ν`, the smallest scale `c₀ rᵢ^(-1/2)` tends to zero and the bound passes to the limit
(`TauCeti.SeibergWitten.exists_forall_measure_closedBall_le_of_tendsto`):
`ν (closedBall x ρ) ≤ C' ρ ²` for `0 ≤ ρ < σ₀`, at every point `x` where the hypotheses hold. In
particular `ν` has no atoms there, and `ν A ≤ C' μH[2] A` for every set `A` of such points. With
the lower density bound at the limit zero set
(`TauCeti.SeibergWitten.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_tendsto`), the limit
defect measure is comparable with the two-dimensional Hausdorff measure of the limit zero set.

The statements are for an arbitrary metric space and an arbitrary nontrivial filter, so they apply
to the manifold with a distance inducing its topology, along any subsequence. The differential
inequality and the mass bound are hypotheses.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace TauCeti

variable [PseudoMetricSpace X]

/-- **Quadratic upper bound from the monotonicity inequality.** Fix `C, C₁, K, M ≥ 0` and
`c₀, σ₀ > 0`. There is a constant `C' > 0` with the following property. Let `r ≥ 1`, let `μ` be a
measure and `x` a point such that `μ (closedBall x σ₀) ≤ M` and the function
`E(σ) = μ (closedBall x σ)` satisfies Taubes's differential inequality
`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) E'(σ) + K σ⁴` at almost every
`σ ∈ (c₀ r^(-1/2), σ₀)`. Then `μ (closedBall x σ) ≤ C' σ ^ 2` for every radius
`c₀ r^(-1/2) ≤ σ ≤ σ₀`. The constant `C'` depends neither on `r` nor on `μ` and `x`. -/
theorem exists_forall_measure_closedBall_le_of_ae_le {C C₁ K M c₀ σ₀ : ℝ} (hC : 0 ≤ C)
    (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hM : 0 ≤ M) (hc₀ : 0 < c₀) (hσ₀ : 0 < σ₀) :
    ∃ C' > 0, ∀ r, 1 ≤ r → ∀ (μ : Measure X) (x : X),
      μ (closedBall x σ₀) ≤ ENNReal.ofReal M →
      (∀ᵐ σ, σ ∈ Ioo (c₀ / √r) σ₀ →
        (μ (closedBall x σ)).toReal ≤ σ / 2 * (1 + C * σ) * (1 + C₁ / √r) *
          deriv (fun σ ↦ (μ (closedBall x σ)).toReal) σ + K * σ ^ 4) →
      ∀ σ, c₀ / √r ≤ σ → σ ≤ σ₀ → μ (closedBall x σ) ≤ ENNReal.ofReal (C' * σ ^ 2) := by
  -- The integration runs up to `ρ₁ = min σ₀ 1`; above `ρ₁` the mass bound suffices.
  set ρ₁ := min σ₀ 1
  set Λ := Real.exp (2 * C₁ * (1 + |Real.log c₀|)) * ((1 + C * ρ₁) / ρ₁) ^ 2 * (M + K)
  have hΛ : 0 ≤ Λ := by positivity
  refine ⟨Λ + M + 1, by positivity, fun r hr μ x hμM hle σ hσ hσσ₀ ↦ ?_⟩
  have hs : 0 < √r := Real.sqrt_pos.2 (by linarith)
  have hfin : μ (closedBall x σ₀) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμM
  set f : ℝ → ℝ := fun σ ↦ (μ (closedBall x σ)).toReal
  -- `f` is monotone below `σ₀` and bounded there by `M`.
  have hmono : MonotoneOn f (Iic σ₀) := fun _ _ t ht hst ↦ ENNReal.toReal_mono
    (ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall ht)))
    (measure_mono (closedBall_subset_closedBall hst))
  have hfM : ∀ t ≤ σ₀, f t ≤ M := fun t ht ↦
    (hmono ht le_rfl ht).trans (ENNReal.toReal_le_of_le_ofReal hM hμM)
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfin
    (measure_mono (closedBall_subset_closedBall hσσ₀)))]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_or_gt σ ρ₁ with hσρ₁ | hσρ₁
  · -- Apply the real-variable upper bound with `h = r^(-1/2)` on `[σ, ρ₁]`.
    have hρ₁σ₀ : ρ₁ ≤ σ₀ := min_le_left _ _
    have hf' : ∀ᵐ τ, τ ∈ Ioo σ ρ₁ →
        f τ ≤ τ / 2 * (1 + C * τ) * (1 + C₁ / √r) * deriv f τ + K * τ ^ 4 := by
      filter_upwards [hle] with τ hτ hτI
      exact hτ ⟨hσ.trans_lt hτI.1, hτI.2.trans_le hρ₁σ₀⟩
    have key := le_mul_sq_of_le_mul_deriv_add (h := (√r)⁻¹) (K := C₁) hC (by positivity) hK
      hc₀ (inv_pos.2 hs) (inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hr))
      (div_eq_mul_inv _ _).le (by rwa [← div_eq_mul_inv]) hσρ₁ (min_le_right _ _)
      (hmono.mono fun t ht ↦ ht.2.trans hρ₁σ₀) ENNReal.toReal_nonneg (hfM ρ₁ hρ₁σ₀) hf'
    calc f σ ≤ Λ * σ ^ 2 := key
      _ ≤ (Λ + M + 1) * σ ^ 2 := by gcongr; linarith
  · -- Above `ρ₁` the radius is at least `1`, so `f σ ≤ M ≤ M σ ^ 2`.
    have hσ1 : 1 ≤ σ := ((min_lt_iff.1 hσρ₁).resolve_left hσσ₀.not_gt).le
    have hσsq : 1 ≤ σ ^ 2 := one_le_pow₀ hσ1
    calc f σ ≤ M := hfM σ hσσ₀
      _ ≤ M * σ ^ 2 := le_mul_of_one_le_right hM hσsq
      _ ≤ (Λ + M + 1) * σ ^ 2 := by gcongr; linarith

end TauCeti

namespace TauCeti.SeibergWitten

variable [MetricSpace X] [BorelSpace X] {ι : Type*} {l : Filter ι}

/-- **Upper density of the limit defect measure.** Fix `C, C₁, K, M ≥ 0` and `c₀, σ₀ > 0`.
There is a constant `C' > 0` with the following property. Let `r i → ∞` along a nontrivial
filter and let finite measures `μ i` converge weakly to `ν`. Let `A` be a set such that at every
`x ∈ A`, eventually, `μ i (closedBall x σ₀) ≤ M` and the function
`E(σ) = μ i (closedBall x σ)` satisfies Taubes's differential inequality
`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ (r i)^(-1/2)) E'(σ) + K σ⁴` at almost every
`σ ∈ (c₀ (r i)^(-1/2), σ₀)`. Then `ν (closedBall x ρ) ≤ C' ρ ^ 2` for every `x ∈ A` and every
radius `0 ≤ ρ < σ₀`, and `ν A ≤ C' μH[2] A`. -/
theorem exists_forall_measure_closedBall_le_of_tendsto [l.NeBot] {C C₁ K M c₀ σ₀ : ℝ}
    (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hM : 0 ≤ M) (hc₀ : 0 < c₀) (hσ₀ : 0 < σ₀) :
    ∃ C' > 0, ∀ (r : ι → ℝ) (μ : ι → FiniteMeasure X) (ν : FiniteMeasure X) (A : Set X),
      Tendsto r l atTop → Tendsto μ l (𝓝 ν) →
      (∀ x ∈ A, ∀ᶠ i in l, (μ i : Measure X) (closedBall x σ₀) ≤ ENNReal.ofReal M ∧
        ∀ᵐ σ, σ ∈ Ioo (c₀ / √(r i)) σ₀ →
          ((μ i : Measure X) (closedBall x σ)).toReal ≤
            σ / 2 * (1 + C * σ) * (1 + C₁ / √(r i)) *
              deriv (fun σ ↦ ((μ i : Measure X) (closedBall x σ)).toReal) σ + K * σ ^ 4) →
      (∀ x ∈ A, ∀ ρ, 0 ≤ ρ → ρ < σ₀ →
        (ν : Measure X) (closedBall x ρ) ≤ ENNReal.ofReal (C' * ρ ^ 2)) ∧
      (ν : Measure X) A ≤ ENNReal.ofReal C' * μH[2] A := by
  obtain ⟨C', hC', hbound⟩ :=
    exists_forall_measure_closedBall_le_of_ae_le (X := X) hC hC₁ hK hM hc₀ hσ₀
  refine ⟨C', hC', fun r μ ν A hr hμ hA ↦ ?_⟩
  -- The smallest admissible radius `c₀ / √(r i)` tends to zero.
  have hh : Tendsto (fun i ↦ c₀ / √(r i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hr)
  have hdens : ∀ x ∈ A, ∀ᶠ i in l, ∀ ρ, c₀ / √(r i) ≤ ρ → ρ ≤ σ₀ →
      (μ i : Measure X) (closedBall x ρ) ≤ ENNReal.ofReal (C' * ρ ^ 2) := fun x hx ↦ by
    filter_upwards [hA x hx, hr.eventually_ge_atTop 1] with i hi hri
    exact hbound (r i) hri (μ i) x hi.1 hi.2
  exact ⟨fun x hx ρ hρ hρσ₀ ↦
    FiniteMeasure.measure_closedBall_le_of_tendsto hμ hh (hdens x hx) hρ hρσ₀,
    by simpa using FiniteMeasure.measure_le_mul_hausdorffMeasure_of_tendsto hμ hh hC' hσ₀ hdens⟩

end TauCeti.SeibergWitten
