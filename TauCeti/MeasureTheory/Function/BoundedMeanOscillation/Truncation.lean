/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Algebra.Order.Group.MinMax
import TauCeti.Analysis.SpecialFunctions.Log.PosLog

/-!
# BMO and VMO under clipping and truncation

Clipping a real function via `max (-M) (min M (b x))` increases its BMO seminorm and VMO
modulus by at most a factor of two (`TauCeti.bmoSeminorm_max_min_le`,
`TauCeti.vmoModulus_max_min_le`). These estimates use `LipschitzWith.bmoSeminorm_comp_le` and
`LipschitzWith.vmoModulus_comp_le` from `TauCeti.MeasureTheory.Function.BoundedMeanOscillation`.
For nonnegative heights, clipping preserves BMO and VMO for arbitrary measures on
second-countable pseudometric spaces (`TauCeti.MemBMO.max_min`, `TauCeti.MemVMO.max_min`),
without the local-finiteness assumption of the general postcomposition preservation theorems.

For pointwise bounds and agreement, import `TauCeti.Algebra.Order.Group.MinMax`: the clipped
value has norm at most `|M|` (`TauCeti.abs_max_min_le`), and for nonnegative heights at most the
original norm (`TauCeti.abs_max_min_le_abs`). It equals the original value once its absolute
value is at most the height (`TauCeti.max_neg_min_eq_self_of_abs_le`).
`TauCeti.Algebra.Order.Group.MinMax` is re-exported by
`TauCeti.MeasureTheory.Function.LpSeminorm.Clipping`, which also provides essential
boundedness (`MeasureTheory.AEStronglyMeasurable.memLp_top_max_min`) and finite-exponent `Lᵖ`
convergence of scalar products with the clipped multipliers to `b • f` when `b • f` lies in `Lᵖ`
(`TauCeti.tendsto_eLpNorm_max_min_smul_sub`). Together these results permit passage from bounded
multipliers to BMO multipliers in commutator estimates. This is not approximation in the BMO
seminorm, which need not hold.

Truncation from above controls logarithms. If `f ≥ 0` has bounded mean oscillation and its
truncations `min f n` at every level `n ∈ ℕ` have vanishing mean oscillation, then `log (1 + f)` has
vanishing mean oscillation (`TauCeti.memVMO_log_one_add_of_forall_memVMO_min`). The remainder
`log (1 + f) - log (1 + min f n) = log⁺ ((1 + f) / (n + 1))` is an `(n + 1)⁻¹`-Lipschitz function
of `f`, and functions of vanishing mean oscillation are closed in the BMO seminorm
(`TauCeti.memVMO_of_tendsto_bmoSeminorm`).

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.5: approximation of BMO
  multipliers in the Coifman–Rochberg–Weiss commutator theorem.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {b : X → ℝ}

/-- Symmetric clipping at any real height increases the BMO seminorm by at most a factor of
two. No finiteness assumption on the measure is needed. -/
theorem bmoSeminorm_max_min_le (hb : AEStronglyMeasurable b μ) (M : ℝ) :
    bmoSeminorm (fun x ↦ max (-M) (min M (b x))) μ ≤ 2 * bmoSeminorm b μ := by
  have hφ : LipschitzWith 1 (fun t : ℝ ↦ max (-M) (min M t)) :=
    (LipschitzWith.id.const_min M).const_max (-M)
  simpa [Function.comp_def] using hφ.bmoSeminorm_comp_le hb

/-- Symmetric clipping at any real height increases the VMO modulus by at most a factor of
two, uniformly in the radius. -/
theorem vmoModulus_max_min_le (hb : AEStronglyMeasurable b μ) (M r : ℝ) :
    vmoModulus (fun x ↦ max (-M) (min M (b x))) μ r ≤ 2 * vmoModulus b μ r := by
  have hφ : LipschitzWith 1 (fun t : ℝ ↦ max (-M) (min M t)) :=
    (LipschitzWith.id.const_min M).const_max (-M)
  simpa [Function.comp_def] using hφ.vmoModulus_comp_le hb r

/-- Clipping a real BMO function at a nonnegative height preserves BMO, for any measure. -/
theorem MemBMO.max_min [SecondCountableTopology X] (hb : MemBMO b μ) {M : ℝ} (hM : 0 ≤ M) :
    MemBMO (fun x ↦ max (-M) (min M (b x))) μ := by
  have hcont : Continuous (fun t : ℝ ↦ max (-M) (min M t)) := by fun_prop
  apply memBMO_iff.2
  refine ⟨hb.locallyIntegrable.mono
    (hcont.comp_aestronglyMeasurable hb.locallyIntegrable.aestronglyMeasurable)
    (.of_forall fun x ↦ abs_max_min_le_abs hM (b x)), ?_⟩
  exact (bmoSeminorm_max_min_le hb.locallyIntegrable.aestronglyMeasurable M).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hb.bmoSeminorm_lt_top)

/-- Clipping a real VMO function at a nonnegative height preserves VMO, for any measure. -/
theorem MemVMO.max_min [SecondCountableTopology X] (hb : MemVMO b μ) {M : ℝ} (hM : 0 ≤ M) :
    MemVMO (fun x ↦ max (-M) (min M (b x))) μ := by
  apply memVMO_iff_tendsto.2
  refine ⟨hb.memBMO.max_min hM, ?_⟩
  have hlim := ENNReal.Tendsto.const_mul hb.tendsto_vmoModulus
    (Or.inr (show (2 : ℝ≥0∞) ≠ ∞ from by finiteness))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim) (fun _ ↦ zero_le)
  exact fun r ↦ vmoModulus_max_min_le hb.memBMO.locallyIntegrable.aestronglyMeasurable M r

section Log

open Filter
open scoped NNReal Topology

variable [SecondCountableTopology X] [IsLocallyFiniteMeasure μ]

/-- The map `t ↦ log⁺ ((1 + t) / c)` is `c⁻¹`-Lipschitz. -/
private theorem lipschitzWith_posLog_one_add_div {c : ℝ≥0} (hc : c ≠ 0) :
    LipschitzWith c⁻¹ fun t : ℝ => Real.posLog ((1 + t) / c) := by
  have hc' : (0 : ℝ) < c := by positivity
  have h : LipschitzWith c⁻¹ fun t : ℝ => (1 + t) / c :=
    LipschitzWith.of_dist_le_mul fun t s => by
      rw [Real.dist_eq, Real.dist_eq, ← sub_div, add_sub_add_left_eq_sub, abs_div,
        abs_of_pos hc', NNReal.coe_inv, div_eq_inv_mul]
  simpa only [one_mul, Function.comp_def] using Real.lipschitzWith_posLog.comp h

/-- For `t ≥ 0`, cutting `t` off at the level `n` lowers `log (1 + t)` by
`log⁺ ((1 + t) / (n + 1))`. -/
private theorem log_one_add_sub_log_one_add_min {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Real.log (1 + t) - Real.log (1 + min t n) = Real.posLog ((1 + t) / ((n : ℝ≥0) + 1 : ℝ≥0)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  push_cast
  rcases le_total t n with h | h
  · rw [min_eq_left h, sub_self, eq_comm, Real.posLog_eq_zero_iff,
      abs_of_nonneg (by positivity), div_le_one hn]
    linarith
  · rw [min_eq_right h, Real.posLog_eq_log (by
        rw [abs_of_nonneg (by positivity), one_le_div hn]
        linarith),
      Real.log_div (by linarith) hn.ne', add_comm (n : ℝ) 1]

/-- **A logarithm of a function of bounded mean oscillation with vanishing truncations has
vanishing mean oscillation.** Let `f ≥ 0` have bounded mean oscillation, and suppose that its
truncations `min f n` at every level `n ∈ ℕ` have vanishing mean oscillation. Then `log (1 + f)`
has vanishing mean oscillation.

Indeed `log (1 + f)` differs from `log (1 + min f n)`, which has vanishing mean oscillation, by
`log⁺ ((1 + f) / (n + 1))`, a `(n + 1)⁻¹`-Lipschitz function of `f`, whose BMO seminorm is at most
`2 (n + 1)⁻¹ ‖f‖_{BMO}`. -/
theorem memVMO_log_one_add_of_forall_memVMO_min {f : X → ℝ} (hf : MemBMO f μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hmin : ∀ n : ℕ, MemVMO (fun x => min (f x) n) μ) :
    MemVMO (fun x => Real.log (1 + f x)) μ := by
  -- On `[0, ∞)` the logarithm `log (1 + t)` agrees with the `1`-Lipschitz map `log⁺ (1 + t)`.
  have hψ : LipschitzWith 1 fun t : ℝ => Real.posLog (1 + t) := by
    simpa using lipschitzWith_posLog_one_add_div (c := 1) one_ne_zero
  have hψeq {t : ℝ} (ht : 0 ≤ t) : Real.posLog (1 + t) = Real.log (1 + t) :=
    Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hloc : LocallyIntegrable (fun x => Real.log (1 + f x)) μ :=
    ((hf.comp_lipschitz hψ).congr_ae (hf0.mono fun x hx => hψeq hx)).locallyIntegrable
  have hg (n : ℕ) : MemVMO (fun x => Real.log (1 + min (f x) n)) μ :=
    ((hmin n).comp_lipschitz hψ).congr_ae
      (hf0.mono fun x hx => hψeq (le_min hx (Nat.cast_nonneg n)))
  refine memVMO_of_tendsto_bmoSeminorm (l := atTop) hloc hg ?_
  -- The remainder `log⁺ ((1 + f) / (n + 1))` has BMO seminorm at most `2 n⁻¹ ‖f‖_{BMO}`.
  have hle (n : ℕ) : bmoSeminorm ((fun x => Real.log (1 + f x)) -
      fun x => Real.log (1 + min (f x) n)) μ ≤ 2 * (n : ℝ≥0∞)⁻¹ * bmoSeminorm f μ := by
    have hc : (n : ℝ≥0) + 1 ≠ 0 := by positivity
    rw [bmoSeminorm_congr_ae
      (f := (fun x => Real.log (1 + f x)) - fun x => Real.log (1 + min (f x) n))
      (g := (fun t : ℝ => Real.posLog ((1 + t) / ((n : ℝ≥0) + 1 : ℝ≥0))) ∘ f)
      (hf0.mono fun x hx => log_one_add_sub_log_one_add_min hx n)]
    refine ((lipschitzWith_posLog_one_add_div hc).bmoSeminorm_comp_le
      hf.locallyIntegrable.aestronglyMeasurable).trans ?_
    gcongr
    rw [ENNReal.coe_inv hc]
    push_cast
    exact ENNReal.inv_le_inv.2 le_self_add
  have hlim : Tendsto (fun n : ℕ => 2 * (n : ℝ≥0∞)⁻¹ * bmoSeminorm f μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr ENNReal.ofNat_ne_top))
      (Or.inr hf.bmoSeminorm_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle

end Log

end TauCeti
