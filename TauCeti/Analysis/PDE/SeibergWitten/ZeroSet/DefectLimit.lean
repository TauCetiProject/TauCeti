/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.DefectEnergy
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Density
public import TauCeti.Topology.Sets.KuratowskiLimit
import TauCeti.MeasureTheory.Measure.Prokhorov
import TauCeti.Topology.MetricSpace.Closeds

/-!
# The limit of the defect measures along a sequence of large-parameter solutions

Consider solutions of the Seiberg–Witten equations at parameters `r k → ∞`, written in a flat
chart `E` of dimension four with an additive Haar measure `μ`. The normalized spinors are
`χ k = α k u₀ + β k`, the zero sets are `Z k = (α k)⁻¹(0)`, and the defect measures are
`μ_k = (r k / 4) |1 - |χ k|²| μ` (`TauCeti.SeibergWitten.defectMeasure`). Suppose that the zero
sets converge to `Z₀` in the sense of Kuratowski, as they do along a subsequence of any sequence
(`TauCeti.exists_strictMono_isKuratowskiLimit`). This file takes the limit of the defect measures
along a further subsequence and proves that it has quadratic lower density at the points of `Z₀`
(`TauCeti.SeibergWitten.`
`exists_strictMono_tendsto_integral_defectMeasure_and_le_measure_closedBall`).

The inputs are those of Taubes's analysis of the zero set:

* **Mass bounds.** The defect measures of every compact set are bounded independently of `k`.
  Then a subsequence converges vaguely, against continuous compactly supported functions, to a
  locally finite measure `ν` (`TauCeti.exists_subseq_tendsto_integral_of_iSup_measure_ne_top`).
  Kuratowski convergence of the zero sets survives the passage to this subsequence
  (`TauCeti.IsKuratowskiLimit.comp`), so `ν` and `Z₀` are limits along the same subsequence.
* **Coarse bounds.** The bounds `|α|² ≤ 1 + C / r`, `|β|² ≤ (C / r) w₊ + C / r²` and
  `|∇_a α|² ≤ C r w₊ + C`, with `w₊ = max (1 - |α|²) 0`, hold with one constant `C`. At a zero of
  `α k` they give the defect energy `E(c / √r) ≥ c₁ / r` of the ball of radius `c / √r`, for every
  small `c` (`TauCeti.SeibergWitten.ofReal_div_le_setLIntegral_of_eq_zero`), and hence for every
  larger radius, since the balls grow.
* **Monotonicity.** Near every point, at the zeros of `α k`, the defect energy `E(σ)` of the balls
  satisfies Taubes's differential inequality
  `E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) E'(σ) + K σ⁴` at almost every
  `σ ∈ (c₀ r^(-1/2), σ₀)`, with constants depending on the point.

Integrating the differential inequality from the smallest scale gives `μ_k (B_ρ(y)) ≥ c ρ²` at the
zeros `y` of `α k`, which passes to the limit at every point of `Z₀`, since each point of a
Kuratowski limit is a limit of zeros (`TauCeti.IsKuratowskiLimit.eventually_exists_dist_lt`).
So near every point `ν (B_ρ(y)) ≥ c ρ²` for `y ∈ Z₀` and `0 < ρ ≤ ρ₀`, with locally uniform
constants, and `Z₀` has locally finite two-dimensional Hausdorff measure
(`TauCeti.SeibergWitten.`
`exists_forall_ofReal_mul_sq_le_measure_closedBall_of_tendsto_integral_compactlySupported`).
The mass bounds and the differential inequality are hypotheses.

## Main results

* `TauCeti.SeibergWitten.`
  `exists_strictMono_tendsto_integral_defectMeasure_and_le_measure_closedBall`: along a
  subsequence the defect measures converge vaguely to a locally finite measure with locally
  uniform quadratic lower density at the Kuratowski limit of the zero sets, which has locally
  finite two-dimensional Hausdorff measure.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Lemma 5.2.
-/

public section

open Filter Metric MeasureTheory Module Set Topology
open scoped ENNReal CompactlySupported

namespace TauCeti.SeibergWitten

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

/-- A radius `c ≤ c₀` with `256 C c² ≤ 1`, at which the coarse bounds control the defect energy at
the smallest scale. -/
private theorem exists_le_and_mul_sq_le_one {C c₀ : ℝ} (hC : 0 ≤ C) (hc₀ : 0 < c₀) :
    ∃ c, 0 < c ∧ c ≤ c₀ ∧ 256 * C * c ^ 2 ≤ 1 := by
  set c := min c₀ (16 * (C + 1))⁻¹
  have h₁ : c * (16 * (C + 1)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans_eq
      (inv_mul_cancel₀ (by positivity))
  refine ⟨c, lt_min hc₀ (by positivity), min_le_left _ _, ?_⟩
  nlinarith [mul_le_mul h₁ h₁ (by positivity) zero_le_one,
    mul_nonneg (sq_nonneg c) (by positivity : (0 : ℝ) ≤ C ^ 2 + C + 1)]

/-- **The limit of the defect measures along a sequence of large-parameter solutions.** Let `E` be
a flat chart of dimension four with an additive Haar measure `μ`, and let `r k → ∞`. Suppose that
the zero sets of `α k` converge to `Z₀` in the sense of Kuratowski, and that:

* the defect measures `μ_k = (r k / 4) |1 - |α k|² - |β k|²| μ` of every compact set are bounded
  independently of `k`;
* eventually, everywhere, `α k` is differentiable and the coarse bounds `|α|² ≤ 1 + C / r`,
  `|β|² ≤ (C / r) w₊ + C / r²` and `|∇_a α|² ≤ C r w₊ + C` hold, with `w₊ = max (1 - |α|²) 0`;
* every point has a neighbourhood `U` and constants `C', C₁, K ≥ 0` and `c₀, σ₀ > 0` such that
  eventually, at every zero `y ∈ U` of `α k`, the defect energy `E(σ) = μ_k (closedBall y σ)`
  satisfies Taubes's differential inequality
  `E(σ) ≤ (σ / 2) (1 + C' σ) (1 + C₁ (r k)^(-1/2)) E'(σ) + K σ⁴` at almost every
  `σ ∈ (c₀ (r k)^(-1/2), σ₀)`.

Then along a subsequence `φ` the defect measures converge vaguely to a locally finite measure `ν`;
every point has a neighbourhood `V` and constants `c, ρ₀ > 0` with `ν (closedBall y ρ) ≥ c ρ ^ 2`
for every `y ∈ Z₀ ∩ V` and every radius `0 < ρ ≤ ρ₀`; and `Z₀` has locally finite
two-dimensional Hausdorff measure. -/
theorem exists_strictMono_tendsto_integral_defectMeasure_and_le_measure_closedBall
    (hE : finrank ℝ E = 4) {μ : Measure E} [μ.IsAddHaarMeasure] {α : ℕ → E → ℂ}
    {b : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ} {β : ℕ → E → F} {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    {Z₀ : Set E} (hZ : IsKuratowskiLimit atTop (fun k ↦ α k ⁻¹' {0}) Z₀)
    (hmass : ∀ K, IsCompact K → ⨆ k, defectMeasure μ (r k) (α k) (β k) K ≠ ∞)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoarse : ∀ᶠ k in atTop, ∀ y, DifferentiableAt ℝ (α k) y ∧ ‖α k y‖ ^ 2 ≤ 1 + C / r k ∧
      ‖β k y‖ ^ 2 ≤ C / r k * max (1 - ‖α k y‖ ^ 2) 0 + C / r k ^ 2 ∧
      ‖covariantDeriv (b k) (α k) y‖ ^ 2 ≤ C * r k * max (1 - ‖α k y‖ ^ 2) 0 + C)
    (hmono : ∀ x, ∃ U ∈ 𝓝 x, ∃ C' C₁ K c₀ σ₀ : ℝ, 0 ≤ C' ∧ 0 ≤ C₁ ∧ 0 ≤ K ∧ 0 < c₀ ∧ 0 < σ₀ ∧
      ∀ᶠ k in atTop, ∀ y ∈ α k ⁻¹' {0} ∩ U, ∀ᵐ σ, σ ∈ Ioo (c₀ / √(r k)) σ₀ →
        (defectMeasure μ (r k) (α k) (β k) (closedBall y σ)).toReal ≤
          σ / 2 * (1 + C' * σ) * (1 + C₁ / √(r k)) *
            deriv (fun σ ↦ (defectMeasure μ (r k) (α k) (β k) (closedBall y σ)).toReal) σ +
              K * σ ^ 4) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : Measure E, IsLocallyFiniteMeasure ν ∧
      (∀ f : C_c(E, ℝ), Tendsto (fun k ↦ ∫ y, f y ∂defectMeasure μ (r (φ k)) (α (φ k)) (β (φ k)))
        atTop (𝓝 (∫ y, f y ∂ν))) ∧
      (∀ x, ∃ V ∈ 𝓝 x, ∃ c > 0, ∃ ρ₀ > 0, ∀ y ∈ Z₀ ∩ V, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
        ENNReal.ofReal (c * ρ ^ 2) ≤ ν (closedBall y ρ)) ∧
      IsLocallyFiniteMeasure (μH[2].restrict Z₀) := by
  set m := fun k ↦ defectMeasure μ (r k) (α k) (β k)
  -- The mass bounds make each defect measure finite on compact sets, so locally finite.
  have hcpt (k : ℕ) : IsFiniteMeasureOnCompacts (m k) :=
    ⟨fun K hK ↦ (le_iSup (fun k ↦ m k K) k).trans_lt (hmass K hK).lt_top⟩
  have hloc (k : ℕ) : IsLocallyFiniteMeasure (m k) := by
    have := hcpt k
    infer_instance
  obtain ⟨ν, φ, hν, hφ, -, hlim⟩ := exists_subseq_tendsto_integral_of_iSup_measure_ne_top m
    (S := range m) (fun K hK ↦ by rw [iSup_range]; exact hmass K hK)
    (Frequently.of_forall mem_range_self)
  have hφt := hφ.tendsto_atTop
  have hloc' (k : ℕ) : IsLocallyFiniteMeasure (m (φ k)) := hloc (φ k)
  refine ⟨φ, hφ, ν, hν, hlim, ?_⟩
  refine exists_forall_ofReal_mul_sq_le_measure_closedBall_of_tendsto_integral_compactlySupported
    (μ := fun k ↦ m (φ k)) (hr.comp hφt) hlim
    (fun x hx _ hε ↦ (hZ.comp hφt).eventually_exists_dist_lt hx hε) fun x ↦ ?_
  obtain ⟨U, hU, C', C₁, K, c₀, σ₀, hC', hC₁, hK, hc₀, hσ₀, hev⟩ := hmono x
  -- The coarse bounds control the defect energy at a radius `c / √r ≤ c₀ / √r`.
  obtain ⟨c, hc, hcc₀, hcC⟩ := exists_le_and_mul_sq_le_one hC hc₀
  have hvol : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  refine ⟨U, hU, C', C₁, K, c₀, c ^ 4 * μ.real (ball 0 1) / 8, σ₀, hC', hC₁, hK, hc₀,
    by positivity, hσ₀, ?_⟩
  filter_upwards [hφt.eventually hev, hφt.eventually hcoarse,
    hφt.eventually (hr.eventually_ge_atTop 1), hφt.eventually (hr.eventually_ge_atTop (8 * C))]
    with k hk hck hr₁ hrC y hy
  refine ⟨hk y hy, ?_⟩
  have hsmall := ofReal_div_le_setLIntegral_of_eq_zero (μ := μ) (b := b (φ k)) (β := β (φ k)) hE
    hC hr₁ hrC hc.le hcC (fun z _ ↦ (hck z).1) (fun z _ ↦ (hck z).2.1) (fun z _ ↦ (hck z).2.2.1)
    (fun z _ ↦ (hck z).2.2.2) hy.1
  rw [← defectMeasure_apply] at hsmall
  -- The ball of radius `c₀ / √r` contains the ball of radius `c / √r`.
  have hball := measure_mono (μ := m (φ k)) (closedBall_subset_closedBall
    (div_le_div_of_nonneg_right hcc₀ (Real.sqrt_nonneg (r (φ k)))) : closedBall y (c / √(r (φ k)))
      ⊆ closedBall y (c₀ / √(r (φ k))))
  exact (ENNReal.ofReal_le_iff_le_toReal measure_closedBall_lt_top.ne).1 (hsmall.trans hball)

end TauCeti.SeibergWitten
