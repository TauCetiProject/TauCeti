/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.MeasureTheory.Measure.QuasiMeasurePreserving
import TauCeti.Topology.Algebra.Order.Field

/-!
# Mean oscillation under changes of variables

Let `Φ : X → Y` be an `L`-Lipschitz map between pseudometric measure spaces, `L > 0`, whose
push-forward of `μ` is dominated by a multiple of `ν`, `Φ_* μ ≤ K ν`, and suppose that the balls
`B(Φ c, L s)` are not much larger than the balls `B(c, s)`: `ν (B(Φ c, L s)) ≤ D μ (B(c, s))`.
This file proves that precomposition with `Φ` controls mean oscillation scale by scale,

`η_{f ∘ Φ}(r) ≤ 2 K D η_f(L r)`

(`LipschitzWith.vmoModulus_comp_le_of_map_le`), and hence `‖f ∘ Φ‖_{BMO} ≤ 2 K D ‖f‖_{BMO}`
(`LipschitzWith.bmoSeminorm_comp_le_of_map_le`), and that `f ∘ Φ` has bounded, respectively
vanishing, mean oscillation when `f` has (`TauCeti.MemBMO.comp_of_map_le`,
`TauCeti.MemVMO.comp_of_map_le`).

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, the ball
condition holds with `D = Lⁿ`, `n = dim E`, for every map, so only the Lipschitz bound and the
bound `Φ_* μ ≤ K μ` on the push-forward remain
(`LipschitzWith.vmoModulus_comp_le_pow_finrank_of_map_le`,
`LipschitzWith.bmoSeminorm_comp_le_pow_finrank_of_map_le`,
`TauCeti.MemBMO.comp_of_map_le_of_addHaar`, `TauCeti.MemVMO.comp_of_map_le_of_addHaar`).
For a diffeomorphism the push-forward bound says that the Jacobian determinant of `Φ` is at least
`1 / K`. Measure-preserving maps have `K = 1`; the shear `(t, y) ↦ (t - γ y, y)` by a Lipschitz
`γ`, which flattens the region above the graph of `γ`, is such a map.

Such changes of variables flatten the boundary of a domain. Flattening also multiplies the
coefficients by derivatives of the chart, which are bounded and uniformly continuous; products of
that kind are treated in `TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Bilinear`. With
both results, a coefficient field of vanishing mean oscillation stays one after flattening, which
is what the `W^{2,p}` and `W^{1,p}` estimates for coefficients of vanishing mean oscillation up to
the boundary require of the transformed equation.

## The argument

On a ball `B = B(c, s)`, with `B' = B(Φ c, L s) ⊇ Φ(B)` and `k` the average of `f` over `B'`, the
mean oscillation of `f ∘ Φ` on `B` is at most the average of `‖f (Φ x) - f (Φ y)‖` over pairs of
points of `B`, hence at most twice the mean deviation `⨍_B ‖f ∘ Φ - k‖`. Pushing the integral
forward along `Φ`,

`∫_B ‖f (Φ x) - k‖ dμ ≤ ∫_{B'} ‖f - k‖ d(Φ_* μ) ≤ K ∫_{B'} ‖f - k‖ dν`,

and `ν B' ≤ D μ B` turns this into `⨍_B ‖f ∘ Φ - k‖ ≤ K D ⨍_{B'} ‖f - k‖`, the mean oscillation of
`f` on a ball of radius `L s`. No integrability of `f` is needed for these estimates.

## References

* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405.
* F. Chiarenza, M. Frasca and P. Longo, *W^{2,p}-solvability of the Dirichlet problem for
  nondivergence elliptic equations with VMO coefficients*, Trans. Amer. Math. Soc. **336** (1993),
  841–853 (flattening the boundary of a domain for coefficients of vanishing mean oscillation).
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

section PseudoMetricSpace

variable {X Y F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [NormedAddCommGroup F] {μ : Measure X}
  {ν : Measure Y} {f : Y → F} {Φ : X → Y} {L K D : ℝ≥0}

/-- **Pushing a ball average forward.** Under the hypotheses of
`LipschitzWith.vmoModulus_comp_le_of_map_le`, the mean deviation of `f ∘ Φ` from a constant `k` on
`B(c, s)` is at most `K D` times that of `f` on `B(Φ c, L s)`. -/
private theorem setLAverage_ball_enorm_comp_sub_le (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν) (hf : StronglyMeasurable f) (k : F) {c : X} {s : ℝ}
    (hD : ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s)) :
    ⨍⁻ x in ball c s, ‖f (Φ x) - k‖ₑ ∂μ ≤
      K * D * ⨍⁻ y in ball (Φ c) (L * s), ‖f y - k‖ₑ ∂ν := by
  set A := ⨍⁻ y in ball (Φ c) (L * s), ‖f y - k‖ₑ ∂ν
  rcases eq_or_ne (μ (ball c s)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ (ball c s)) ⊤ with htop | htop
  · simp [setLAverage_eq, htop]
  have hν : ν (ball (Φ c) (L * s)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top htop) hD
  have hint := hΦ.setLIntegral_ball_comp_le_of_map_le hL hmap (g := fun y => ‖f y - k‖ₑ)
    (hf.sub stronglyMeasurable_const).eNorm c s
  rw [← measure_mul_setLAverage _ hν] at hint
  rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
  calc (μ (ball c s))⁻¹ * ∫⁻ x in ball c s, ‖f (Φ x) - k‖ₑ ∂μ
      ≤ (μ (ball c s))⁻¹ * (K * (ν (ball (Φ c) (L * s)) * A)) := by gcongr
    _ ≤ (μ (ball c s))⁻¹ * (K * (D * μ (ball c s) * A)) := by gcongr
    _ = K * D * A * ((μ (ball c s))⁻¹ * μ (ball c s)) := by ring
    _ = K * D * A := by rw [ENNReal.inv_mul_cancel h0 htop, mul_one]

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- **Mean oscillation under a change of variables.** Let `Φ : X → Y` be `L`-Lipschitz, `L ≠ 0`,
with `Φ_* μ ≤ K ν`, and suppose that `ν (B(Φ c, L s)) ≤ D μ (B(c, s))` for every ball. Then
`η_{f ∘ Φ}(r) ≤ 2 K D η_f(L r)`. -/
theorem _root_.LipschitzWith.vmoModulus_comp_le_of_map_le (hΦ : LipschitzWith L Φ)
    (hL : L ≠ 0) (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s))
    (hf : AEStronglyMeasurable f ν) (r : ℝ) :
    vmoModulus (f ∘ Φ) μ r ≤ 2 * K * D * vmoModulus f ν (L * r) := by
  rw [vmoModulus_congr_ae ((QuasiMeasurePreserving.of_map_le_smul
    hΦ.continuous.measurable.aemeasurable hmap).ae_eq_comp hf.ae_eq_mk),
    vmoModulus_congr_ae hf.ae_eq_mk]
  set g := hf.mk f
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  refine vmoModulus_le fun c s hs => ?_
  rcases le_or_gt s 0 with hs0 | hs0
  · simp [ball_eq_empty.2 hs0]
  set k := ⨍ y in ball (Φ c) (L * s), g y ∂ν
  calc ⨍⁻ x in ball c s, ‖(g ∘ Φ) x - ⨍ z in ball c s, (g ∘ Φ) z ∂μ‖ₑ ∂μ
      ≤ ⨍⁻ x in ball c s, ⨍⁻ y in ball c s, ‖g (Φ x) - g (Φ y)‖ₑ ∂μ ∂μ :=
        setLAverage_enorm_sub_setAverage_le_setLAverage_setLAverage
          (hg.comp_measurable hΦ.continuous.measurable).aestronglyMeasurable
    _ ≤ 2 * ⨍⁻ x in ball c s, ‖g (Φ x) - k‖ₑ ∂μ :=
        setLAverage_setLAverage_enorm_sub_le k
    _ ≤ 2 * (K * D * ⨍⁻ y in ball (Φ c) (L * s), ‖g y - k‖ₑ ∂ν) := by
        gcongr
        exact setLAverage_ball_enorm_comp_sub_le hΦ hL hmap hg k (hD c s hs0)
    _ ≤ 2 * (K * D * vmoModulus g ν (L * r)) := by
        gcongr
        exact setLAverage_enorm_sub_setAverage_le_vmoModulus g ν (Φ c)
          (mul_le_mul_of_nonneg_left hs L.coe_nonneg)
    _ = 2 * K * D * vmoModulus g ν (L * r) := by ring

/-- **The BMO seminorm under a change of variables.** Under the hypotheses of
`LipschitzWith.vmoModulus_comp_le_of_map_le`, `‖f ∘ Φ‖_{BMO} ≤ 2 K D ‖f‖_{BMO}`. -/
theorem _root_.LipschitzWith.bmoSeminorm_comp_le_of_map_le (hΦ : LipschitzWith L Φ)
    (hL : L ≠ 0) (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s))
    (hf : AEStronglyMeasurable f ν) :
    bmoSeminorm (f ∘ Φ) μ ≤ 2 * K * D * bmoSeminorm f ν := by
  rw [← iSup_vmoModulus]
  exact iSup_le fun r => (hΦ.vmoModulus_comp_le_of_map_le hL hmap hD hf r).trans
    (mul_le_mul_right (vmoModulus_le_bmoSeminorm f ν _) _)

/-- **Bounded mean oscillation under a change of variables.** Under the hypotheses of
`LipschitzWith.vmoModulus_comp_le_of_map_le`, `f ∘ Φ` has bounded mean oscillation when `f`
has. -/
theorem MemBMO.comp_of_map_le [SecondCountableTopology Y] (hf : MemBMO f ν)
    (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s)) :
    MemBMO (f ∘ Φ) μ :=
  memBMO_iff.2 ⟨hf.locallyIntegrable.comp_of_map_le hΦ.continuous hmap ENNReal.coe_ne_top,
    (hΦ.bmoSeminorm_comp_le_of_map_le hL hmap hD
      hf.locallyIntegrable.aestronglyMeasurable).trans_lt
        (ENNReal.mul_lt_top (by finiteness) hf.bmoSeminorm_lt_top)⟩

/-- **Vanishing mean oscillation under a change of variables.** Under the hypotheses of
`LipschitzWith.vmoModulus_comp_le_of_map_le`, `f ∘ Φ` has vanishing mean oscillation when `f`
has. -/
theorem MemVMO.comp_of_map_le [SecondCountableTopology Y] (hf : MemVMO f ν)
    (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s)) :
    MemVMO (f ∘ Φ) μ := by
  refine memVMO_iff_tendsto.2 ⟨hf.memBMO.comp_of_map_le hΦ hL hmap hD, ?_⟩
  have hscale : Tendsto (fun r : ℝ => (L : ℝ) * r) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_const_mul_nhdsGT_zero (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hL))
  have hlim := ENNReal.Tendsto.const_mul (hf.tendsto_vmoModulus.comp hscale)
    (Or.inr (show 2 * (K : ℝ≥0∞) * D ≠ ∞ by finiteness))
  rw [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun r => hΦ.vmoModulus_comp_le_of_map_le hL hmap hD
      hf.memBMO.locallyIntegrable.aestronglyMeasurable r

end PseudoMetricSpace

section AddHaar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {Φ : E → E} {L K : ℝ≥0}

/-- For an additive Haar measure, the ball `B(Φ c, L s)` has `Lⁿ` times the measure of `B(c, s)`,
`n = dim E`. -/
private theorem addHaar_ball_mul_le (hL : L ≠ 0) (c : E) (s : ℝ) :
    μ (ball (Φ c) (L * s)) ≤ ((L ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) * μ (ball c s) := by
  rw [μ.addHaar_ball_mul_of_pos _ (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hL)),
    μ.addHaar_ball_center c,
    ENNReal.ofReal_pow L.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

/-- **Mean oscillation under a change of variables of `E`.** For an additive Haar measure on a
finite-dimensional space `E` of dimension `n`, if `Φ : E → E` is `L`-Lipschitz, `L ≠ 0`, with
`Φ_* μ ≤ K μ`, then `η_{f ∘ Φ}(r) ≤ 2 K Lⁿ η_f(L r)`. -/
theorem _root_.LipschitzWith.vmoModulus_comp_le_pow_finrank_of_map_le (hΦ : LipschitzWith L Φ)
    (hL : L ≠ 0) (hmap : μ.map Φ ≤ K • μ) (hf : AEStronglyMeasurable f μ) (r : ℝ) :
    vmoModulus (f ∘ Φ) μ r ≤ 2 * K * L ^ Module.finrank ℝ E * vmoModulus f μ (L * r) := by
  simpa using hΦ.vmoModulus_comp_le_of_map_le hL hmap
    (fun c s _ => addHaar_ball_mul_le hL c s) hf r

/-- **The BMO seminorm under a change of variables of `E`.** For an additive Haar measure on a
finite-dimensional space `E` of dimension `n`, if `Φ : E → E` is `L`-Lipschitz, `L ≠ 0`, with
`Φ_* μ ≤ K μ`, then `‖f ∘ Φ‖_{BMO} ≤ 2 K Lⁿ ‖f‖_{BMO}`. -/
theorem _root_.LipschitzWith.bmoSeminorm_comp_le_pow_finrank_of_map_le (hΦ : LipschitzWith L Φ)
    (hL : L ≠ 0) (hmap : μ.map Φ ≤ K • μ) (hf : AEStronglyMeasurable f μ) :
    bmoSeminorm (f ∘ Φ) μ ≤ 2 * K * L ^ Module.finrank ℝ E * bmoSeminorm f μ := by
  simpa using hΦ.bmoSeminorm_comp_le_of_map_le hL hmap
    (fun c s _ => addHaar_ball_mul_le hL c s) hf

/-- **Bounded mean oscillation under a change of variables of `E`.** For an additive Haar measure
on a finite-dimensional space `E`, if `Φ : E → E` is Lipschitz with `Φ_* μ ≤ K μ`, then `f ∘ Φ` has
bounded mean oscillation when `f` has. -/
theorem MemBMO.comp_of_map_le_of_addHaar (hf : MemBMO f μ) (hΦ : LipschitzWith L Φ)
    (hmap : μ.map Φ ≤ K • μ) : MemBMO (f ∘ Φ) μ :=
  hf.comp_of_map_le (hΦ.weaken (le_max_left L 1)) (by positivity) hmap
    fun c s _ => addHaar_ball_mul_le (by positivity) c s

/-- **Vanishing mean oscillation under a change of variables of `E`.** For an additive Haar measure
on a finite-dimensional space `E`, if `Φ : E → E` is Lipschitz with `Φ_* μ ≤ K μ`, then `f ∘ Φ` has
vanishing mean oscillation when `f` has. In particular this holds for measure-preserving
Lipschitz maps. -/
theorem MemVMO.comp_of_map_le_of_addHaar (hf : MemVMO f μ) (hΦ : LipschitzWith L Φ)
    (hmap : μ.map Φ ≤ K • μ) : MemVMO (f ∘ Φ) μ :=
  hf.comp_of_map_le (hΦ.weaken (le_max_left L 1)) (by positivity) hmap
    fun c s _ => addHaar_ball_mul_le (by positivity) c s

end AddHaar

end TauCeti
