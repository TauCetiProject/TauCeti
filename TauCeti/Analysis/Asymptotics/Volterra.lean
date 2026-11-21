/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.Filter.AtTopBot.Basic
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.Order.Interval

/-!
# Volterra integral equations with separable kernel bounds

Let `I : Set ℝ` be an order-connected set (in particular, any finite or infinite interval `(a, b)`
with `-∞ ≤ a < b ≤ ∞`), let `K x v` be a kernel continuous on `{(x, v) | x ∈ I ∧ v ∈ I ∧ x ≤ v}`
with a separable bound `‖K x v‖ ≤ P x * Q v`, where `P, Q ≥ 0` are continuous on `I`, and let `J`,
`ψ` be continuous on `I` such that for every `x ∈ I` the tail integrals

* `Φ x = ∫ v in I ∩ Ioi x, Q v * ‖J v‖` and
* `Ψ x = ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖`

converge. Then the Volterra integral equation

  `h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)`

has a unique continuous solution `h` on `I` satisfying `h = O(P)` towards the right endpoint of
`I`, and it obeys the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x ∈ I`.

When `P` is a constant `P₀ ≥ 0` and `‖ψ v‖ ≤ ‖J v‖` on `I` (for instance `ψ = J` when `E = 𝕜`),
the solution obeys the sharper bound `‖h x‖ ≤ exp (P₀ * Φ x) - 1`.

When `I` is open, `K x x = 0`, and `∂K/∂x (x, v) = K' x v` exists for `x < v`, extends
continuously to `x ≤ v`, and satisfies `‖K' x v‖ ≤ P₁ x * Q v` for a continuous `P₁ ≥ 0`, every
such solution is `C¹` on `I` with derivative `h' x = ∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)`,
satisfying `‖h' x‖ ≤ P₁ x * Φ x * exp (Ψ x)` and, in the constant-`P₀` case with `‖ψ‖ ≤ ‖J‖`,
`P₀ * ‖h' x‖ ≤ P₁ x * (exp (P₀ * Φ x) - 1)`.

All of these results also hold for the mirrored left-tail equation
`h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)`, obtained by reflecting `x ↦ -x`.

This formalizes Olver's theorem on Volterra integral equations (Chapter 6, Theorem 10.1), which
underlies the existence, uniqueness, and error-bound theorems for the Liouville–Green
approximation and for linear differential equations at an irregular singularity of rank one
(DLMF §§2.7, 2.8).

The kernel `K` and coefficient `ψ` take values in any normed field `𝕜`, and the forcing `J` and
unknown `h` in any real normed space which is also a normed `𝕜`-space (with completeness assumed
only for existence, and `[NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E]` only for differentiability).

## Main results

Right-tail Volterra equation on an order-connected set `I ⊆ ℝ`:

* `TauCeti.exists_volterra_solution_on`: existence of a continuous solution with the bound
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.exists_volterra_solution`: specialization of existence to the half-line `(a, ∞)`.
* `TauCeti.isBigO_of_norm_le_volterra_bound_on`: any function satisfying the Volterra bound is
  `O(P)` towards the right endpoint of `I`.
* `TauCeti.norm_volterra_solution_le_on`: every continuous solution with `h = O(P)` satisfies
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.volterra_solution_eqOn`, `TauCeti.volterra_solution_eqOn_Ioi`: uniqueness among
  continuous solutions with `h = O(P)`.
* `TauCeti.norm_volterra_solution_le_exp_sub_one_on`: sharper bound
  `‖h x‖ ≤ exp (P₀ * Φ x) - 1` for constant `P₀` and `‖ψ‖ ≤ ‖J‖`.
* `TauCeti.hasDerivAt_volterra_solution_on`, `TauCeti.contDiffOn_volterra_solution_on`:
  `C¹` regularity and derivative integral formula on an open interval `I`.
* `TauCeti.norm_deriv_volterra_solution_le_on`,
  `TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one_on`: general and sharper derivative
  bounds.

Left-tail Volterra equation (`I ∩ Iio x`), proved by reflection `x ↦ -x`:

* `TauCeti.exists_volterra_solution_Iio_on`, `TauCeti.isBigO_of_norm_le_volterra_bound_Iio_on`,
  `TauCeti.norm_volterra_solution_Iio_le_on`, `TauCeti.volterra_solution_Iio_eqOn`,
  `TauCeti.norm_volterra_solution_Iio_le_exp_sub_one_on`,
  `TauCeti.hasDerivAt_volterra_solution_Iio_on`, `TauCeti.contDiffOn_volterra_solution_Iio_on`,
  `TauCeti.norm_deriv_volterra_solution_Iio_le_on`,
  `TauCeti.mul_norm_deriv_volterra_solution_Iio_le_exp_sub_one_on`.

The discrete analogue is `TauCeti.exists_discrete_volterra_solution`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10.
* NIST Digital Library of Mathematical Functions, §2.7(iii), <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Filter Set MeasureTheory Function
open scoped Nat Pointwise Topology

namespace TauCeti

section RightTail

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- The forcing weights `Q v * ‖J v‖` are nonnegative on `I`. -/
private lemma forcing_weight_nonneg (hQ0 : ∀ v ∈ I, 0 ≤ Q v) :
    ∀ v ∈ I, 0 ≤ Q v * ‖J v‖ :=
  fun v hv ↦ mul_nonneg (hQ0 v hv) (norm_nonneg _)

/-- The coefficient weights `P v * Q v * ‖ψ v‖` are nonnegative on `I`. -/
private lemma coeff_weight_nonneg (hP0 : ∀ v ∈ I, 0 ≤ P v) (hQ0 : ∀ v ∈ I, 0 ≤ Q v) :
    ∀ v ∈ I, 0 ≤ P v * Q v * ‖ψ v‖ :=
  fun v hv ↦ mul_nonneg (mul_nonneg (hP0 v hv) (hQ0 v hv)) (norm_nonneg _)

omit [NormedSpace ℝ E] in
/-- The separable bound for `v ↦ K x v • y` on `x ≤ v` in `I`. -/
private lemma norm_kernel_smul_le (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    {x v : ℝ} (hx : x ∈ I) (hv : v ∈ I) (hxv : x ≤ v) (y : E) :
    ‖K x v • y‖ ≤ P x * (Q v * ‖y‖) := by
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hKle x hx v hv hxv) (norm_nonneg _)

omit [NormedSpace ℝ E] in
/-- If `F` is continuous on `I` and `Q * ‖F‖` is integrable on `I ∩ Ioi x`, then so is
`v ↦ K x v • F v`. -/
private lemma integrableOn_kernel_smul_on (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E}
    (hF : ContinuousOn F I) {x : ℝ} (hx : x ∈ I)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    IntegrableOn (fun v ↦ K x v • F v) (I ∩ Ioi x) := by
  have hKx : ContinuousOn (fun v ↦ K x v) (I ∩ Ioi x) :=
    hK.comp (continuous_const.prodMk continuous_id).continuousOn
      fun v hv ↦ ⟨hx, hv.1, hv.2.le⟩
  refine Integrable.mono' (hFint.const_mul (P x))
    ((hKx.smul (hF.mono inter_subset_left)).aestronglyMeasurable
      (hI.measurableSet.inter measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  exact norm_kernel_smul_le hKle hx hv.1 hv.2.le _

omit [NormedSpace ℝ E] in
/-- Extending `v ↦ K x v • F v` by zero from `I ∩ Ioi x` to `I ∩ Ioi c` (`c ≤ x`) preserves
integrability. -/
private lemma integrableOn_indicator_kernel_smul_on (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E}
    (hF : ContinuousOn F I) {c x : ℝ} (hcx : c ≤ x) (hx : x ∈ I)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    IntegrableOn ((Ioi x).indicator (fun v ↦ K x v • F v)) (I ∩ Ioi c) := by
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioi, inter_comm (Ioi x), inter_assoc,
    Ioi_inter_Ioi, sup_eq_right.2 hcx]
  exact integrableOn_kernel_smul_on hI hK hKle hF hx hFint

/-- The separable bound for the integral `∫ v in I ∩ Ioi x, K x v • F v`. -/
private lemma norm_integral_kernel_smul_le_on (hI : I.OrdConnected)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E} {x : ℝ} (hx : x ∈ I)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    ‖∫ v in I ∩ Ioi x, K x v • F v‖ ≤ P x * ∫ v in I ∩ Ioi x, Q v * ‖F v‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hFint.const_mul (P x)) ?_
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  exact norm_kernel_smul_le hKle hx hv.1 hv.2.le _

/-- If `F` is continuous on `I` and `Q * ‖F‖` is integrable on `I ∩ Ioi x` for every `x ∈ I`,
then `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` is continuous on `I`. -/
private lemma continuousOn_integral_kernel_smul_on (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v) (hP : ContinuousOn P I)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) {F : ℝ → E} (hF : ContinuousOn F I)
    (hFint : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x)) :
    ContinuousOn (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) I := by
  intro x₀ hx₀
  obtain ⟨c, hcI, d, _, hcx₀, hx₀d, hcdI, hcdN⟩ := hI.exists_Icc_mem_nhdsWithin hx₀
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hcdI)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ ⟨hcx₀, hx₀d⟩)
  have hSmeas : MeasurableSet (I ∩ Ioi c) := hI.measurableSet.inter measurableSet_Ioi
  have heq : (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v) =ᶠ[𝓝[I] x₀]
      fun x ↦ ∫ v in I ∩ Ioi c, (Ioi x).indicator (fun v ↦ K x v • F v) v := by
    filter_upwards [hcdN] with x hx
    rw [setIntegral_indicator measurableSet_Ioi, inter_assoc, Ioi_inter_Ioi, sup_eq_right.2 hx.1]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ heq ?_
  · refine continuousWithinAt_of_dominated (bound := fun v ↦ M * (Q v * ‖F v‖)) ?_ ?_
      ((hFint c hcI).const_mul M) ?_
    · filter_upwards [hcdN] with x hx
      exact (integrableOn_indicator_kernel_smul_on hI hK hKle hF hx.1 (hcdI hx)
        (hFint x (hcdI hx))).aestronglyMeasurable
    · filter_upwards [hcdN] with x hx
      refine (ae_restrict_iff' hSmeas).2 (ae_of_all _ fun v hv ↦ ?_)
      have hQF : 0 ≤ Q v * ‖F v‖ := mul_nonneg (hQ0 v hv.1) (norm_nonneg _)
      by_cases hxv : x < v
      · rw [indicator_of_mem hxv]
        exact (norm_kernel_smul_le hKle (hcdI hx) hv.1 hxv.le _).trans
          (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hM x hx)) hQF)
      · rw [indicator_of_notMem hxv, norm_zero]
        exact mul_nonneg hM0 hQF
    · filter_upwards [ae_restrict_mem hSmeas, ae_restrict_of_ae (Measure.ae_ne volume x₀)]
        with v hv hvne
      rcases hvne.lt_or_gt with hlt | hgt
      · refine continuousWithinAt_const.congr_of_eventuallyEq ?_
          (indicator_of_notMem (notMem_Ioi.2 hlt.le) _)
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)] with x hx
        exact indicator_of_notMem (notMem_Ioi.2 hx.le) _
      · have hKv : ContinuousWithinAt (fun x ↦ K x v) (I ∩ Iio v) x₀ :=
          ContinuousWithinAt.comp (g := uncurry K) (f := fun x ↦ (x, v))
            (hK (x₀, v) ⟨hx₀, hv.1, hgt.le⟩)
            (continuous_id.prodMk continuous_const).continuousWithinAt
            fun x hx ↦ ⟨hx.1, hv.1, hx.2.le⟩
        have hKvI : ContinuousWithinAt (fun x ↦ K x v) I x₀ :=
          hKv.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hgt)))
        refine (hKvI.smul continuousWithinAt_const).congr_of_eventuallyEq ?_
          (indicator_of_mem (mem_Ioi.2 hgt) _)
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hgt)] with x hx
        exact indicator_of_mem (mem_Ioi.2 hx) _
  · rw [setIntegral_indicator measurableSet_Ioi, inter_assoc, Ioi_inter_Ioi, sup_eq_right.2 hcx₀]

/-- The increments of the Picard iteration for the Volterra equation on `I`: the `0`-th is
`x ↦ ∫ v in I ∩ Ioi x, K x v • J v`, and each further one applies
`F ↦ (x ↦ ∫ v in I ∩ Ioi x, K x v • ψ v • F v)` to the previous one. -/
private noncomputable def picardTermOn (I : Set ℝ) (K : ℝ → ℝ → 𝕜) (J : ℝ → E) (ψ : ℝ → 𝕜) :
    ℕ → ℝ → E
  | 0, x => ∫ v in I ∩ Ioi x, K x v • J v
  | k + 1, x => ∫ v in I ∩ Ioi x, K x v • ψ v • picardTermOn I K J ψ k v

section Iteration

variable (hI : I.OrdConnected)
  (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
  (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I)
  (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
  (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
  (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
  (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))

omit [NormedSpace ℝ E] in
include hI hψ hQ hQ0 hΨ in
/-- If `F` is continuous on `I` with `‖F v‖ ≤ C * P v` on `I ∩ Ioi x`, then `Q * ‖ψ • F‖` is
integrable on `I ∩ Ioi x`. -/
private lemma integrableOn_weight_smul_on {F : ℝ → E} (hF : ContinuousOn F I) {x C : ℝ}
    (hx : x ∈ I) (hFle : ∀ v ∈ I ∩ Ioi x, ‖F v‖ ≤ C * P v) :
    IntegrableOn (fun v ↦ Q v * ‖ψ v • F v‖) (I ∩ Ioi x) := by
  have hcont : ContinuousOn (fun v ↦ Q v * ‖ψ v • F v‖) (I ∩ Ioi x) :=
    (hQ.mul (hψ.smul hF).norm).mono inter_subset_left
  refine Integrable.mono' ((hΨ x hx).const_mul C)
    (hcont.aestronglyMeasurable (hI.measurableSet.inter measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  have hQψ : 0 ≤ Q v * ‖ψ v‖ := mul_nonneg (hQ0 v hv.1) (norm_nonneg _)
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (hQ0 v hv.1)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))), ← mul_assoc]
  calc Q v * ‖ψ v‖ * ‖F v‖ ≤ Q v * ‖ψ v‖ * (C * P v) :=
        mul_le_mul_of_nonneg_left (hFle v hv) hQψ
    _ = C * (P v * Q v * ‖ψ v‖) := by ring

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
include hI hP0 hQ0 hΦ hΨ in
/-- For `x ≤ v` in `I` and `f` monotone and nonnegative on `[0, ∞)`, the bound
`P v * Φ v * f (Ψ v)` at `v` is at most `Φ x * f (Ψ x) * P v`. -/
private lemma mul_tail_le_of_le_on {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0))
    (hf0 : ∀ t, 0 ≤ t → 0 ≤ f t) {x v : ℝ} (hx : x ∈ I) (hv : v ∈ I) (hxv : x ≤ v) :
    P v * (∫ u in I ∩ Ioi v, Q u * ‖J u‖) * f (∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖) ≤
      (∫ u in I ∩ Ioi x, Q u * ‖J u‖) * f (∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖) * P v := by
  have hPv := hP0 v hv
  have hΦx : 0 ≤ ∫ u in I ∩ Ioi x, Q u * ‖J u‖ :=
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
      fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1
  have hΨv : 0 ≤ ∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖ :=
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
      fun u hu ↦ coeff_weight_nonneg (ψ := ψ) hP0 hQ0 u hu.1
  have hΨle := antitoneOn_integral_inter_Ioi hI.measurableSet
    (coeff_weight_nonneg (ψ := ψ) hP0 hQ0) hΨ hx hv hxv
  have hfv := hf0 _ hΨv
  calc _ ≤ P v * (∫ u in I ∩ Ioi x, Q u * ‖J u‖) *
        f (∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖) := by
        gcongr P v * ?_ * ?_
        · exact antitoneOn_integral_inter_Ioi hI.measurableSet
            (forcing_weight_nonneg (J := J) hQ0) hΦ hx hv hxv
        · exact hf hΨv (hΨv.trans hΨle) hΨle
    _ = _ := by ring

include hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ

/-- The Picard increments are continuous on `I`, and the `k`-th is bounded by
`P x * Φ x * (Ψ x ^ k / k!)`. -/
private lemma picardTermOn_spec (k : ℕ) :
    ContinuousOn (picardTermOn I K J ψ k) I ∧ ∀ x ∈ I, ‖picardTermOn I K J ψ k x‖ ≤
      P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        ((∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !) := by
  induction k with
  | zero =>
    refine ⟨continuousOn_integral_kernel_smul_on hI hK hKle hP hQ0 hJ hΦ, fun x hx ↦ ?_⟩
    simpa [picardTermOn] using norm_integral_kernel_smul_le_on hI hKle hx (hΦ x hx)
  | succ k ih =>
    obtain ⟨hcont, hle⟩ := ih
    have hFint : ∀ x ∈ I,
        IntegrableOn (fun v ↦ Q v * ‖ψ v • picardTermOn I K J ψ k v‖) (I ∩ Ioi x) :=
      fun x hx ↦ integrableOn_weight_smul_on hI hψ hQ hQ0 hΨ hcont hx
        (C := (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
          ((∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !)) fun v hv ↦
        (hle v hv.1).trans (mul_tail_le_of_le_on hI hP0 hQ0 hΦ hΨ (f := fun t ↦ t ^ k / k !)
          (fun s (hs : 0 ≤ s) _ _ hst ↦ by dsimp only; gcongr)
          (fun _ _ ↦ by positivity) hx hv.1 hv.2.le)
    refine ⟨continuousOn_integral_kernel_smul_on hI hK hKle hP hQ0 (hψ.smul hcont) hFint,
      fun x hx ↦ ?_⟩
    set Φx := ∫ v in I ∩ Ioi x, Q v * ‖J v‖
    set g : ℝ → ℝ := fun v ↦ P v * Q v * ‖ψ v‖ with hg
    refine (norm_integral_kernel_smul_le_on hI hKle hx (hFint x hx)).trans ?_
    have hint : ∫ v in I ∩ Ioi x, Q v * ‖ψ v • picardTermOn I K J ψ k v‖ ≤
        Φx / k ! * ∫ v in I ∩ Ioi x, g v * (∫ u in I ∩ Ioi v, g u) ^ k := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hFint x hx)
        (((hΨ x hx).mul_pow_integral_inter_Ioi hI.measurableSet k).const_mul _)
        (hI.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_
      have := hP0 v hv.1
      have := hQ0 v hv.1
      have : 0 ≤ ∫ u in I ∩ Ioi v, g u :=
        setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
          fun u hu ↦ coeff_weight_nonneg (ψ := ψ) hP0 hQ0 u hu.1
      have hΦle : ∫ u in I ∩ Ioi v, Q u * ‖J u‖ ≤ Φx :=
        antitoneOn_integral_inter_Ioi hI.measurableSet (forcing_weight_nonneg (J := J) hQ0) hΦ hx
          hv.1 hv.2.le
      rw [norm_smul, ← mul_assoc]
      calc Q v * ‖ψ v‖ * ‖picardTermOn I K J ψ k v‖
          ≤ Q v * ‖ψ v‖ * (P v * Φx * ((∫ u in I ∩ Ioi v, g u) ^ k / k !)) := by
            grw [hle v hv.1, hΦle]
        _ = Φx / k ! * (g v * (∫ u in I ∩ Ioi v, g u) ^ k) := by simp only [hg]; ring
    rw [(hΨ x hx).integral_inter_Ioi_mul_pow_integral_inter_Ioi hI.measurableSet k] at hint
    calc P x * ∫ v in I ∩ Ioi x, Q v * ‖ψ v • picardTermOn I K J ψ k v‖
        ≤ P x * (Φx / k ! * ((∫ u in I ∩ Ioi x, g u) ^ (k + 1) / (k + 1))) :=
          mul_le_mul_of_nonneg_left hint (hP0 x hx)
      _ = P x * Φx * ((∫ u in I ∩ Ioi x, g u) ^ (k + 1) / (k + 1)!) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp

/-- At points `v ≥ x` in `I`, the `k`-th Picard increment is at most
`Φ x * (Ψ x ^ k / k!) * P v`. -/
private lemma norm_picardTermOn_le_of_le (k : ℕ) {x v : ℝ} (hx : x ∈ I) (hv : v ∈ I)
    (hxv : x ≤ v) :
    ‖picardTermOn I K J ψ k v‖ ≤ (∫ u in I ∩ Ioi x, Q u * ‖J u‖) *
      ((∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖) ^ k / k !) * P v :=
  ((picardTermOn_spec hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 v hv).trans
    (mul_tail_le_of_le_on hI hP0 hQ0 hΦ hΨ (f := fun t ↦ t ^ k / k !)
      (fun s (hs : 0 ≤ s) _ _ hst ↦ by dsimp only; gcongr)
      (fun _ _ ↦ by positivity) hx hv hxv)

/-- The sum of the Picard increments is bounded by `P x * Φ x * exp (Ψ x)`. -/
private lemma norm_tsum_picardTermOn_le {x : ℝ} (hx : x ∈ I) :
    ‖∑' k, picardTermOn I K J ψ k x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) :=
  tsum_of_norm_bounded (by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)).mul_left
      (P x * ∫ v in I ∩ Ioi x, Q v * ‖J v‖))
    fun k ↦ (picardTermOn_spec hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 x hx

variable [CompleteSpace E]

/-- The Picard increments are summable at every point of `I`. -/
private lemma summable_picardTermOn {x : ℝ} (hx : x ∈ I) :
    Summable fun k ↦ picardTermOn I K J ψ k x :=
  ((Real.summable_pow_div_factorial (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)).mul_left
    (P x * ∫ v in I ∩ Ioi x, Q v * ‖J v‖)).of_norm_bounded
    fun k ↦ (picardTermOn_spec hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 x hx

/-- The sum of the Picard increments is continuous on `I`. -/
private lemma continuousOn_tsum_picardTermOn :
    ContinuousOn (fun x ↦ ∑' k, picardTermOn I K J ψ k x) I := by
  intro x₀ hx₀
  obtain ⟨c, hcI, d, _, hcx₀, hx₀d, hcdI, hcdN⟩ := hI.exists_Icc_mem_nhdsWithin hx₀
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hcdI)
  refine ((continuousOn_tsum
    (fun k ↦ (picardTermOn_spec hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).1.mono hcdI)
    ((Real.summable_pow_div_factorial (∫ v in I ∩ Ioi c, P v * Q v * ‖ψ v‖)).mul_left
      ((∫ v in I ∩ Ioi c, Q v * ‖J v‖) * M))
    fun k x hx ↦ ?_) x₀ ⟨hcx₀, hx₀d⟩).mono_of_mem_nhdsWithin hcdN
  have : 0 ≤ ∫ u in I ∩ Ioi c, Q u * ‖J u‖ :=
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
      fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1
  have : 0 ≤ ∫ u in I ∩ Ioi c, P u * Q u * ‖ψ u‖ :=
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
      fun u hu ↦ coeff_weight_nonneg (ψ := ψ) hP0 hQ0 u hu.1
  refine (norm_picardTermOn_le_of_le hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hcI (hcdI hx)
    hx.1).trans ?_
  calc _ ≤ (∫ u in I ∩ Ioi c, Q u * ‖J u‖) *
        ((∫ u in I ∩ Ioi c, P u * Q u * ‖ψ u‖) ^ k / k !) * M :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM x hx)) (by positivity)
    _ = _ := by ring

/-- The sum of the Picard increments solves the Volterra equation on `I`. -/
private lemma tsum_picardTermOn_eq {x : ℝ} (hx : x ∈ I) :
    ∑' k, picardTermOn I K J ψ k x = ∫ v in I ∩ Ioi x,
      K x v • (J v + ψ v • ∑' k, picardTermOn I K J ψ k v) := by
  set T := picardTermOn I K J ψ
  set h : ℝ → E := fun x ↦ ∑' k, T k x with h_def
  have hspec := picardTermOn_spec hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hcont : ContinuousOn h I :=
    continuousOn_tsum_picardTermOn hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hψh : IntegrableOn (fun v ↦ Q v * ‖ψ v • h v‖) (I ∩ Ioi x) :=
    integrableOn_weight_smul_on hI hψ hQ hQ0 hΨ hcont hx
      (C := (∫ u in I ∩ Ioi x, Q u * ‖J u‖) * Real.exp (∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖))
      fun v hv ↦
        (norm_tsum_picardTermOn_le hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hv.1).trans
          (mul_tail_le_of_le_on hI hP0 hQ0 hΦ hΨ (Real.exp_monotone.monotoneOn _)
            (fun _ _ ↦ (Real.exp_pos _).le) hx hv.1 hv.2.le)
  have hKJ : IntegrableOn (fun v ↦ K x v • J v) (I ∩ Ioi x) :=
    integrableOn_kernel_smul_on hI hK hKle hJ hx (hΦ x hx)
  have hKψh : IntegrableOn (fun v ↦ K x v • ψ v • h v) (I ∩ Ioi x) :=
    integrableOn_kernel_smul_on hI hK hKle (hψ.smul hcont) hx hψh
  simp only [smul_add]
  rw [integral_add hKJ hKψh]
  set Φx := ∫ u in I ∩ Ioi x, Q u * ‖J u‖
  set Ψx := ∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖
  have hTle : ∀ k, ∀ v ∈ I, x ≤ v → ‖T k v‖ ≤ Φx * (Ψx ^ k / k !) * P v := fun k _ hv hxv ↦
    norm_picardTermOn_le_of_le hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hx hv hxv
  have hFk : ∀ k, IntegrableOn (fun v ↦ K x v • ψ v • T k v) (I ∩ Ioi x) := fun k ↦
    integrableOn_kernel_smul_on hI hK hKle (hψ.smul (hspec k).1) hx
      (integrableOn_weight_smul_on hI hψ hQ hQ0 hΨ (hspec k).1 hx
        fun v hv ↦ hTle k v hv.1 hv.2.le)
  have hsum : Summable fun k ↦ ∫ v in I ∩ Ioi x, ‖K x v • ψ v • T k v‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial Ψx).mul_left (P x * Φx * Ψx))
    refine (setIntegral_mono_on (hFk k).norm
      ((hΨ x hx).const_mul (P x * Φx * (Ψx ^ k / k !)))
      (hI.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_).trans_eq
      (by rw [integral_const_mul]; ring)
    refine (norm_kernel_smul_le hKle hx hv.1 hv.2.le _).trans ?_
    rw [norm_smul]
    have := hP0 x hx
    have := hQ0 v hv.1
    calc P x * (Q v * (‖ψ v‖ * ‖T k v‖))
        ≤ P x * (Q v * (‖ψ v‖ * (Φx * (Ψx ^ k / k !) * P v))) := by grw [hTle k v hv.1 hv.2.le]
      _ = P x * Φx * (Ψx ^ k / k !) * (P v * Q v * ‖ψ v‖) := by ring
  have hser := hasSum_integral_of_summable_integral_norm hFk hsum
  have hinner : ∀ v, ∑' k, K x v • ψ v • T k v = K x v • ψ v • h v := fun v ↦ by
    rw [h_def, tsum_const_smul'', tsum_const_smul'']
  simp only [hinner] at hser
  calc h x = T 0 x + ∑' k, T (k + 1) x := (summable_picardTermOn hI hK hJ hψ hP hQ hP0 hQ0 hKle
        hΦ hΨ hx).tsum_eq_zero_add
    _ = _ := by rw [← hser.tsum_eq]; simp only [T, picardTermOn]

end Iteration

/-- **Volterra integral equations, existence on an interval.** Let `I ⊆ ℝ` be order-connected (for
instance `(a, b)`, `[a, b)`, or `(a, ∞)`), let `K` be continuous on
`{(x, v) | x ∈ I ∧ v ∈ I ∧ x ≤ v}` with `‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are
continuous on `I`, and let `J`, `ψ` be continuous on `I` such that
`Φ x = ∫ v in I ∩ Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖` converge
for every `x ∈ I`. Then the Volterra integral equation
`h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)` has a continuous solution on `I` satisfying
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x ∈ I`. -/
theorem exists_volterra_solution_on [CompleteSpace E] (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I)
    (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) :
    ∃ h : ℝ → E, ContinuousOn h I ∧
      (∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) :=
  ⟨fun x ↦ ∑' k, picardTermOn I K J ψ k x,
    continuousOn_tsum_picardTermOn hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ,
    fun _ hx ↦ tsum_picardTermOn_eq hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hx,
    fun _ hx ↦ norm_tsum_picardTermOn_le hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hx⟩

/-- **Volterra integral equations, existence on `(a, ∞)`.** Specialization of
`TauCeti.exists_volterra_solution_on` to the half-line `Ioi a`. -/
theorem exists_volterra_solution [CompleteSpace E] {a : ℝ}
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hP : ContinuousOn P (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) :
    ∃ h : ℝ → E, ContinuousOn h (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  have hinter : ∀ x ∈ Ioi a, Ioi a ∩ Ioi x = Ioi x := fun _ hx ↦
    inter_eq_right.2 (Ioi_subset_Ioi (le_of_lt hx))
  obtain ⟨h, hcont, heq, hle⟩ := exists_volterra_solution_on ordConnected_Ioi
    (hK.mono fun p hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ hP hQ hP0 hQ0 (fun x hx v _ hxv ↦ hKle x v hx hxv)
    (fun x hx ↦ (hinter x hx).symm ▸ hΦ x hx) (fun x hx ↦ (hinter x hx).symm ▸ hΨ x hx)
  exact ⟨h, hcont, fun x hx ↦ by simpa only [hinter x hx] using heq x hx,
    fun x hx ↦ by simpa only [hinter x hx] using hle x hx⟩

/-! ### Growth, uniqueness, and sharper exponential bounds -/

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- Any function satisfying the Volterra bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` on `I` is `O(P)`
towards the right endpoint of `I`. -/
theorem isBigO_of_norm_le_volterra_bound_on (hI : MeasurableSet I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E}
    (hh : ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)) :
    h =O[map ((↑) : I → ℝ) atTop] P := by
  rcases I.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hbot : map ((↑) : (∅ : Set ℝ) → ℝ) atTop = ⊥ := by
      ext s
      simp [Set.eq_univ_of_forall]
    simp [hbot]
  have : Nonempty I := ⟨⟨x₀, hx₀⟩⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨(∫ v in I ∩ Ioi x₀, Q v * ‖J v‖) * Real.exp (∫ v in I ∩ Ioi x₀, P v * Q v * ‖ψ v‖), ?_⟩
  rw [eventually_map, eventually_atTop]
  refine ⟨⟨x₀, hx₀⟩, fun ⟨v, hv⟩ hxv ↦ ?_⟩
  have hle : x₀ ≤ v := hxv
  have hΦle := antitoneOn_integral_inter_Ioi hI (forcing_weight_nonneg (J := J) hQ0) hΦ hx₀ hv hle
  have hΨle := antitoneOn_integral_inter_Ioi hI (coeff_weight_nonneg (ψ := ψ) hP0 hQ0) hΨ hx₀ hv hle
  have hPv := hP0 v hv
  have hΦx₀ : 0 ≤ ∫ u in I ∩ Ioi x₀, Q u * ‖J u‖ :=
    setIntegral_nonneg (hI.inter measurableSet_Ioi)
      fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1
  calc ‖h v‖ ≤ P v * (∫ u in I ∩ Ioi v, Q u * ‖J u‖) *
        Real.exp (∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖) := hh v hv
    _ ≤ P v * (∫ u in I ∩ Ioi x₀, Q u * ‖J u‖) *
        Real.exp (∫ u in I ∩ Ioi x₀, P u * Q u * ‖ψ u‖) := by gcongr
    _ = (∫ u in I ∩ Ioi x₀, Q u * ‖J u‖) * Real.exp (∫ u in I ∩ Ioi x₀, P u * Q u * ‖ψ u‖) *
        ‖P v‖ := by rw [Real.norm_of_nonneg hPv]; ring

omit [NormedSpace ℝ E] in
/-- If `h` is continuous on `I` and `h = O(P)` towards the right endpoint of `I`, then
`Q * ‖ψ • h‖` is integrable on every right tail `I ∩ Ioi x` (`x ∈ I`). -/
private lemma integrableOn_weight_smul_of_isBigO (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atTop] P)
    {x : ℝ} (hx : x ∈ I) :
    IntegrableOn (fun v ↦ Q v * ‖ψ v • h v‖) (I ∩ Ioi x) := by
  have : Nonempty I := ⟨⟨x, hx⟩⟩
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [eventually_map, eventually_atTop] at hC
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hC
  have htail : IntegrableOn (fun v ↦ Q v * ‖ψ v • h v‖) (I ∩ Ioi x₀) :=
    integrableOn_weight_smul_on hI hψ hQ hQ0 hΨ hh hx₀ (C := C) fun v hv ↦ by
      have := hC ⟨v, hv.1⟩ hv.2.le
      rwa [Real.norm_of_nonneg (hP0 v hv.1)] at this
  rcases le_or_gt x₀ x with hle | _
  · exact htail.mono_set (inter_subset_inter_right I (Ioi_subset_Ioi hle))
  · have hcomp : IntegrableOn (fun v ↦ Q v * ‖ψ v • h v‖) (Icc x x₀) :=
      ((hQ.mul (hψ.smul hh).norm).mono (hI.out hx hx₀)).integrableOn_Icc
    have hsub : I ∩ Ioi x ⊆ Icc x x₀ ∪ (I ∩ Ioi x₀) := fun v hv ↦ by
      rcases le_or_gt v x₀ with h | h
      · exact Or.inl ⟨hv.2.le, h⟩
      · exact Or.inr ⟨hv.1, h⟩
    exact (hcomp.union htail).mono_set hsub

omit [NormedSpace ℝ E] in
/-- If `h` is continuous on `I` and `h = O(P)` towards the right endpoint of `I`, then
`Q * ‖J + ψ • h‖` is integrable on every right tail `I ∩ Ioi x` (`x ∈ I`). -/
private lemma integrableOn_forcing_add_smul_of_isBigO (hI : I.OrdConnected)
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atTop] P)
    {x : ℝ} (hx : x ∈ I) :
    IntegrableOn (fun v ↦ Q v * ‖J v + ψ v • h v‖) (I ∩ Ioi x) := by
  have hψh := integrableOn_weight_smul_of_isBigO hI hψ hQ hP0 hQ0 hΨ hh hO hx
  refine Integrable.mono' ((hΦ x hx).add hψh)
    ((hQ.mul (hJ.add (hψ.smul hh)).norm).mono inter_subset_left |>.aestronglyMeasurable
      (hI.measurableSet.inter measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  have hQv := hQ0 v hv.1
  rw [Real.norm_of_nonneg (by positivity)]
  calc Q v * ‖J v + ψ v • h v‖ ≤ Q v * (‖J v‖ + ‖ψ v • h v‖) := by gcongr; exact norm_add_le _ _
    _ = Q v * ‖J v‖ + Q v * ‖ψ v • h v‖ := by ring

/-- Every continuous solution of the Volterra equation with `h = O(P)` towards the right endpoint
of `I` satisfies `‖h v‖ ≤ C * P v` on `I ∩ Ici x` for every `x ∈ I`. -/
private lemma exists_norm_le_mul_of_isBigO (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atTop] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x : ℝ} (hx : x ∈ I) :
    ∃ C ≥ 0, ∀ v ∈ I, x ≤ v → ‖h v‖ ≤ C * P v := by
  have hψh := integrableOn_weight_smul_of_isBigO hI hψ hQ hP0 hQ0 hΨ hh hO hx
  have hSmeas : MeasurableSet (I ∩ Ioi x) := hI.measurableSet.inter measurableSet_Ioi
  have hC0 : 0 ≤ (∫ u in I ∩ Ioi x, Q u * ‖J u‖) + ∫ u in I ∩ Ioi x, Q u * ‖ψ u • h u‖ :=
    add_nonneg (setIntegral_nonneg hSmeas fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1)
      (setIntegral_nonneg hSmeas fun u hu ↦ mul_nonneg (hQ0 u hu.1) (norm_nonneg _))
  refine ⟨_, hC0, fun v hv hxv ↦ ?_⟩
  have hsub : I ∩ Ioi v ⊆ I ∩ Ioi x := inter_subset_inter_right I (Ioi_subset_Ioi hxv)
  have hdom : IntegrableOn (fun u ↦ P v * (Q u * ‖J u‖ + Q u * ‖ψ u • h u‖)) (I ∩ Ioi v) :=
    ((hΦ v hv).add (hψh.mono_set hsub)).const_mul (P v)
  have hbound : ‖h v‖ ≤ ∫ u in I ∩ Ioi v, P v * (Q u * ‖J u‖ + Q u * ‖ψ u • h u‖) := by
    rw [heq v hv]
    refine norm_integral_le_of_norm_le hdom ?_
    filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with u hu
    refine (norm_kernel_smul_le hKle hv hu.1 hu.2.le _).trans ?_
    have := hP0 v hv
    have := hQ0 u hu.1
    grw [norm_add_le, mul_add]
  have hΦle := setIntegral_mono_set (hΦ x hx)
    ((ae_restrict_iff' hSmeas).2 (ae_of_all _ fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1))
    hsub.eventuallySubset
  have hψhle := setIntegral_mono_set hψh
    ((ae_restrict_iff' hSmeas).2 (ae_of_all _ fun u hu ↦ mul_nonneg (hQ0 u hu.1) (norm_nonneg _)))
    hsub.eventuallySubset
  calc ‖h v‖ ≤ P v * ((∫ u in I ∩ Ioi v, Q u * ‖J u‖) +
        ∫ u in I ∩ Ioi v, Q u * ‖ψ u • h u‖) := by
        rwa [integral_const_mul, integral_add (hΦ v hv) (hψh.mono_set hsub)] at hbound
    _ ≤ P v * ((∫ u in I ∩ Ioi x, Q u * ‖J u‖) + ∫ u in I ∩ Ioi x, Q u * ‖ψ u • h u‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hΦle hψhle) (hP0 v hv)
    _ = _ := by ring

/-- **A priori Volterra bound.** Every continuous solution `h` of the Volterra integral equation
on an order-connected set `I` with `h = O(P)` towards the right endpoint of `I` satisfies
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x ∈ I`. -/
theorem norm_volterra_solution_le_on (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atTop] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  intro x hx
  obtain ⟨C, _, hCle⟩ := exists_norm_le_mul_of_isBigO hI hψ hQ hP0 hQ0 hKle hΦ hΨ hh hO heq hx
  set Φ : ℝ → ℝ := fun v ↦ ∫ u in I ∩ Ioi v, Q u * ‖J u‖
  set g : ℝ → ℝ := fun u ↦ P u * Q u * ‖ψ u‖
  set Ψ : ℝ → ℝ := fun v ↦ ∫ u in I ∩ Ioi v, g u
  have hind : ∀ k : ℕ, ∀ v ∈ I, x ≤ v →
      ‖h v‖ ≤ P v * Φ v * Real.exp (Ψ v) + C * P v * (Ψ v ^ k / k !) := by
    intro k
    induction k with
    | zero =>
      intro v hv hxv
      have hPv := hP0 v hv
      have hΦv : 0 ≤ Φ v := setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
        fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1
      simpa using (hCle v hv hxv).trans (le_add_of_nonneg_left (by positivity))
    | succ k ih =>
      intro v hv hxv
      have hexp : IntegrableOn (fun u ↦ g u * Real.exp (Ψ u)) (I ∩ Ioi v) :=
        (hΨ v hv).mul_exp_integral_inter_Ioi hI.measurableSet
      have hpow : IntegrableOn (fun u ↦ g u * Ψ u ^ k) (I ∩ Ioi v) :=
        (hΨ v hv).mul_pow_integral_inter_Ioi hI.measurableSet k
      have hsum : IntegrableOn (fun u ↦
          Φ v * (g u * Real.exp (Ψ u)) + C * (k ! : ℝ)⁻¹ * (g u * Ψ u ^ k)) (I ∩ Ioi v) :=
        (hexp.const_mul (Φ v)).add (hpow.const_mul _)
      have hdom : IntegrableOn (fun u ↦ P v * (Q u * ‖J u‖ +
          (Φ v * (g u * Real.exp (Ψ u)) + C * (k ! : ℝ)⁻¹ * (g u * Ψ u ^ k)))) (I ∩ Ioi v) :=
        ((hΦ v hv).add hsum).const_mul (P v)
      refine (heq v hv ▸ norm_integral_le_of_norm_le hdom ?_).trans_eq ?_
      · filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with u hu
        refine (norm_kernel_smul_le hKle hv hu.1 hu.2.le _).trans
          (mul_le_mul_of_nonneg_left ?_ (hP0 v hv))
        have hPu := hP0 u hu.1
        have hQu := hQ0 u hu.1
        have hΦle : Φ u ≤ Φ v := antitoneOn_integral_inter_Ioi hI.measurableSet
          (forcing_weight_nonneg (J := J) hQ0) hΦ hv hu.1 hu.2.le
        calc Q u * ‖J u + ψ u • h u‖ ≤ Q u * (‖J u‖ + ‖ψ u‖ * ‖h u‖) := by
              gcongr; exact (norm_add_le _ _).trans (by rw [norm_smul])
          _ = Q u * ‖J u‖ + Q u * ‖ψ u‖ * ‖h u‖ := by ring
          _ ≤ Q u * ‖J u‖ + Q u * ‖ψ u‖ *
              (P u * Φ v * Real.exp (Ψ u) + C * P u * (Ψ u ^ k / k !)) := by
              grw [ih u hu.1 (hxv.trans hu.2.le), hΦle]
          _ = Q u * ‖J u‖ +
              (Φ v * (g u * Real.exp (Ψ u)) + C * (k ! : ℝ)⁻¹ * (g u * Ψ u ^ k)) := by
              simp only [g, div_eq_mul_inv]; ring
      · rw [integral_const_mul, integral_add (hΦ v hv) hsum,
          integral_add (hexp.const_mul (Φ v)) (hpow.const_mul _),
          integral_const_mul, integral_const_mul,
          (hΨ v hv).integral_inter_Ioi_mul_exp_integral_inter_Ioi hI.measurableSet,
          (hΨ v hv).integral_inter_Ioi_mul_pow_integral_inter_Ioi hI.measurableSet k,
          Nat.factorial_succ]
        dsimp only [Φ, Ψ]; push_cast; field_simp; ring
  have hlim : Tendsto (fun k ↦ P x * Φ x * Real.exp (Ψ x) + C * P x * (Ψ x ^ k / k !))
      atTop (𝓝 (P x * Φ x * Real.exp (Ψ x))) := by
    simpa using tendsto_const_nhds.add
      ((Real.summable_pow_div_factorial (Ψ x)).tendsto_atTop_zero.const_mul (C * P x))
  exact ge_of_tendsto' hlim fun k ↦ hind k x hx le_rfl

/-- **Volterra integral equations, uniqueness.** Any two continuous solutions on an order-connected
set `I` that are `O(P)` towards the right endpoint of `I` agree on `I`. -/
theorem volterra_solution_eqOn (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h₁ h₂ : ℝ → E} (hh₁ : ContinuousOn h₁ I) (hh₂ : ContinuousOn h₂ I)
    (hO₁ : h₁ =O[map ((↑) : I → ℝ) atTop] P) (hO₂ : h₂ =O[map ((↑) : I → ℝ) atTop] P)
    (heq₁ : ∀ x ∈ I, h₁ x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h₁ v))
    (heq₂ : ∀ x ∈ I, h₂ x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h₂ v)) :
    EqOn h₁ h₂ I := by
  have hdiff : ∀ x ∈ I, (h₁ - h₂) x =
      ∫ v in I ∩ Ioi x, K x v • ((0 : E) + ψ v • (h₁ - h₂) v) := by
    intro x hx
    have h1 := integrableOn_kernel_smul_on (F := fun v ↦ J v + ψ v • h₁ v) hI hK hKle
      (hJ.add (hψ.smul hh₁)) hx
      (integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh₁ hO₁ hx)
    have h2 := integrableOn_kernel_smul_on (F := fun v ↦ J v + ψ v • h₂ v) hI hK hKle
      (hJ.add (hψ.smul hh₂)) hx
      (integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh₂ hO₂ hx)
    rw [Pi.sub_apply, heq₁ x hx, heq₂ x hx, ← integral_sub h1 h2]
    refine setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi) fun v _ ↦ ?_
    rw [zero_add, ← smul_sub, add_sub_add_left_eq_sub, ← smul_sub, Pi.sub_apply]
  have hbound := norm_volterra_solution_le_on (J := fun _ ↦ (0 : E)) hI hψ hQ hP0 hQ0 hKle
    (fun _ _ ↦ by simp) hΨ (hh₁.sub hh₂) (hO₁.sub hO₂) hdiff
  intro x hx
  have h0 : ‖h₁ x - h₂ x‖ ≤ 0 := by simpa using hbound x hx
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- **Volterra integral equations, uniqueness on `(a, ∞)`.** Specialization of
`TauCeti.volterra_solution_eqOn` to the half-line `Ioi a`, where the right-endpoint filter is
`atTop`. -/
theorem volterra_solution_eqOn_Ioi {a : ℝ}
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h₁ h₂ : ℝ → E} (hh₁ : ContinuousOn h₁ (Ioi a)) (hh₂ : ContinuousOn h₂ (Ioi a))
    (hO₁ : h₁ =O[atTop] P) (hO₂ : h₂ =O[atTop] P)
    (heq₁ : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (heq₂ : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v)) :
    EqOn h₁ h₂ (Ioi a) := by
  have hinter : ∀ x ∈ Ioi a, Ioi a ∩ Ioi x = Ioi x := fun _ hx ↦
    inter_eq_right.2 (Ioi_subset_Ioi (le_of_lt hx))
  have hmap : map ((↑) : Ioi a → ℝ) atTop = atTop := Filter.map_val_Ioi_atTop a
  exact volterra_solution_eqOn ordConnected_Ioi (hK.mono fun p hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ hQ
    hP0 hQ0 (fun x hx v _ hxv ↦ hKle x v hx hxv)
    (fun x hx ↦ (hinter x hx).symm ▸ hΦ x hx) (fun x hx ↦ (hinter x hx).symm ▸ hΨ x hx)
    hh₁ hh₂ (hmap ▸ hO₁) (hmap ▸ hO₂)
    (fun x hx ↦ by simpa only [hinter x hx] using heq₁ x hx)
    (fun x hx ↦ by simpa only [hinter x hx] using heq₂ x hx)

/-- **Sharper Volterra bound for constant `P₀` and `‖ψ‖ ≤ ‖J‖`.** When `‖K x v‖ ≤ P₀ * Q v` with a
constant `P₀ ≥ 0` and `‖ψ v‖ ≤ ‖J v‖` on `I` (for instance `ψ = J` when `E = 𝕜`), every continuous
solution `h` with `h = O(P₀)` towards the right endpoint of `I` satisfies
`‖h x‖ ≤ exp (P₀ * Φ x) - 1` for every `x ∈ I`. -/
theorem norm_volterra_solution_le_exp_sub_one_on {P₀ : ℝ} (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₀ : 0 ≤ P₀) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P₀ * Q v)
    (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atTop] fun _ ↦ P₀)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, ‖h x‖ ≤ Real.exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖J v‖) - 1 := by
  have hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P₀ * Q v * ‖ψ v‖) (I ∩ Ioi x) := fun x hx ↦ by
    refine Integrable.mono' ((hΦ x hx).const_mul P₀)
      (((continuousOn_const.mul hQ).mul hψ.norm).mono inter_subset_left |>.aestronglyMeasurable
        (hI.measurableSet.inter measurableSet_Ioi)) ?_
    filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
    have hQv := hQ0 v hv.1
    rw [Real.norm_of_nonneg (by positivity), mul_assoc]
    gcongr; exact hψJ v hv.1
  intro x hx
  obtain ⟨C, _, hCle⟩ := exists_norm_le_mul_of_isBigO (P := fun _ ↦ P₀) hI hψ hQ
    (fun _ _ ↦ hP₀) hQ0 hKle hΦ hΨ hh hO heq hx
  set g : ℝ → ℝ := fun u ↦ P₀ * (Q u * ‖J u‖)
  set G : ℝ → ℝ := fun v ↦ ∫ u in I ∩ Ioi v, g u
  have hgint : ∀ v ∈ I, IntegrableOn g (I ∩ Ioi v) := fun v hv ↦ (hΦ v hv).const_mul P₀
  have hind : ∀ k : ℕ, ∀ v ∈ I, x ≤ v →
      ‖h v‖ ≤ (Real.exp (G v) - 1) + C * P₀ * (G v ^ k / k !) := by
    intro k
    induction k with
    | zero =>
      intro v hv hxv
      have hGv : 0 ≤ G v := setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
        fun u hu ↦ mul_nonneg hP₀ (forcing_weight_nonneg (J := J) hQ0 u hu.1)
      simpa using (hCle v hv hxv).trans (le_add_of_nonneg_left (sub_nonneg.2 (Real.one_le_exp hGv)))
    | succ k ih =>
      intro v hv hxv
      have hexp : IntegrableOn (fun u ↦ g u * Real.exp (G u)) (I ∩ Ioi v) :=
        (hgint v hv).mul_exp_integral_inter_Ioi hI.measurableSet
      have hpow : IntegrableOn (fun u ↦ g u * G u ^ k) (I ∩ Ioi v) :=
        (hgint v hv).mul_pow_integral_inter_Ioi hI.measurableSet k
      have hdom : IntegrableOn (fun u ↦
          g u * Real.exp (G u) + C * P₀ * (k ! : ℝ)⁻¹ * (g u * G u ^ k)) (I ∩ Ioi v) :=
        hexp.add (hpow.const_mul _)
      refine (heq v hv ▸ norm_integral_le_of_norm_le hdom ?_).trans_eq ?_
      · filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with u hu
        refine (norm_kernel_smul_le (P := fun _ ↦ P₀) hKle hv hu.1 hu.2.le _).trans ?_
        have hQu := hQ0 u hu.1
        calc P₀ * (Q u * ‖J u + ψ u • h u‖)
            ≤ P₀ * (Q u * (‖J u‖ + ‖ψ u‖ * ‖h u‖)) := by
              gcongr; exact (norm_add_le _ _).trans (by rw [norm_smul])
          _ ≤ P₀ * (Q u * (‖J u‖ + ‖J u‖ * ‖h u‖)) := by grw [hψJ u hu.1]
          _ = g u + g u * ‖h u‖ := by simp only [g]; ring
          _ ≤ g u + g u * ((Real.exp (G u) - 1) + C * P₀ * (G u ^ k / k !)) := by
              gcongr; exact ih u hu.1 (hxv.trans hu.2.le)
          _ = g u * Real.exp (G u) + C * P₀ * (k ! : ℝ)⁻¹ * (g u * G u ^ k) := by
              rw [div_eq_mul_inv]; ring
      · rw [integral_add hexp (hpow.const_mul _), integral_const_mul,
          (hgint v hv).integral_inter_Ioi_mul_exp_integral_inter_Ioi hI.measurableSet,
          (hgint v hv).integral_inter_Ioi_mul_pow_integral_inter_Ioi hI.measurableSet k,
          Nat.factorial_succ]
        dsimp only [G]; push_cast; field_simp
  have hlim : Tendsto (fun k ↦ (Real.exp (G x) - 1) + C * P₀ * (G x ^ k / k !))
      atTop (𝓝 (Real.exp (G x) - 1)) := by
    simpa using tendsto_const_nhds.add
      ((Real.summable_pow_div_factorial (G x)).tendsto_atTop_zero.const_mul (C * P₀))
  have hGx : P₀ * ∫ v in I ∩ Ioi x, Q v * ‖J v‖ = G x := (integral_const_mul P₀ _).symm
  rw [hGx]
  exact ge_of_tendsto' hlim fun k ↦ hind k x hx le_rfl

/-! ### Differentiability (`C¹`) and derivative bounds -/

section Differentiability

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Local Lipschitz bound in `x` for the truncated integrand `x ↦ (Ioi x).indicator (K x · • F ·) v`
on an interior interval `(c, d)` when `K v v = 0` and `‖∂K/∂x‖ ≤ M₁ * Q v`. -/
private lemma lipschitzOnWith_indicator_kernel_smul (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    {c d M₁ : ℝ} (hc : c ∈ I) (hd : d ∈ I) (hM₁0 : 0 ≤ M₁)
    (hK'le : ∀ t ∈ Icc c d, ∀ v ∈ I, t ≤ v → ‖K' t v‖ ≤ M₁ * Q v)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) {F : ℝ → E} {v : ℝ} (hv : v ∈ I) :
    LipschitzOnWith (Real.nnabs (M₁ * (Q v * ‖F v‖)))
      (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • F u) v) (Ioo c d) := by
  have hcdI : Icc c d ⊆ I := hI.out hc hd
  have hL0 : 0 ≤ M₁ * (Q v * ‖F v‖) := mul_nonneg hM₁0 (mul_nonneg (hQ0 v hv) (norm_nonneg _))
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  rw [Real.coe_nnabs, abs_of_nonneg hL0]
  wlog hxy : x ≤ y generalizing x y
  · rw [norm_sub_rev, norm_sub_rev x y]
    exact this hy hx (le_of_not_ge hxy)
  rw [Real.norm_of_nonpos (sub_nonpos.2 hxy), neg_sub]
  rcases le_or_gt v x with hvx | hxv
  · rw [indicator_of_notMem (notMem_Ioi.2 hvx),
      indicator_of_notMem (notMem_Ioi.2 (hvx.trans hxy)), sub_self, norm_zero]
    exact mul_nonneg hL0 (sub_nonneg.2 hxy)
  · have htcd : ∀ w ∈ Icc x (min y v), ∀ t ∈ Icc x w, t ∈ Icc c d := fun _ hw _ ht ↦
      ⟨hx.1.le.trans ht.1, ht.2.trans (hw.2.trans ((min_le_left y v).trans hy.2.le))⟩
    have hmvt_on : ∀ w ∈ Icc x (min y v), ‖K w v - K x v‖ ≤ M₁ * Q v * (w - x) := fun w hw ↦
      norm_image_sub_le_of_norm_deriv_right_le_segment
        (hK.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht ↦
          ⟨hcdI (htcd w hw t ht), hv, ht.2.trans (hw.2.trans (min_le_right y v))⟩)
        (fun t ht ↦ (hKderiv t (hcdI (htcd w hw t ⟨ht.1, ht.2.le⟩)) v hv
          (ht.2.trans_le (hw.2.trans (min_le_right y v)))).hasDerivWithinAt)
        (fun t ht ↦ hK'le t (htcd w hw t ⟨ht.1, ht.2.le⟩) v hv
          (ht.2.le.trans (hw.2.trans (min_le_right y v))))
        w ⟨hw.1, le_rfl⟩
    rcases lt_or_ge y v with hyv | hvy
    · rw [indicator_of_mem hxv, indicator_of_mem hyv, ← sub_smul, norm_smul, norm_sub_rev]
      calc ‖K y v - K x v‖ * ‖F v‖ ≤ (M₁ * Q v * (y - x)) * ‖F v‖ :=
            mul_le_mul_of_nonneg_right (hmvt_on y ⟨hxy, le_min le_rfl hyv.le⟩) (norm_nonneg _)
        _ = M₁ * (Q v * ‖F v‖) * (y - x) := by ring
    · rw [indicator_of_mem hxv, indicator_of_notMem (notMem_Ioi.2 hvy), sub_zero, norm_smul]
      have hKxv := hmvt_on v ⟨hxv.le, le_min hvy le_rfl⟩
      rw [hKdiag v hv, zero_sub, norm_neg] at hKxv
      have hMQ : 0 ≤ M₁ * Q v := mul_nonneg hM₁0 (hQ0 v hv)
      calc ‖K x v‖ * ‖F v‖ ≤ (M₁ * Q v * (v - x)) * ‖F v‖ :=
            mul_le_mul_of_nonneg_right hKxv (norm_nonneg _)
        _ ≤ (M₁ * Q v * (y - x)) * ‖F v‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hvy x) hMQ)
              (norm_nonneg _)
        _ = M₁ * (Q v * ‖F v‖) * (y - x) := by ring

/-- Differentiating `x ↦ ∫ v in I ∩ Ioi x, K x v • F v` under the integral sign on an open
order-connected set `I` when `K x x = 0` and `∂K/∂x = K'` satisfies `‖K' x v‖ ≤ P₁ x * Q v`. -/
private lemma hasDerivAt_integral_kernel_smul_on (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K' x v‖ ≤ P₁ x * Q v)
    {F : ℝ → E} (hF : ContinuousOn F I)
    (hFint : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖F v‖) (I ∩ Ioi x))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    HasDerivAt (fun x ↦ ∫ v in I ∩ Ioi x, K x v • F v)
      (∫ v in I ∩ Ioi x₀, K' x₀ v • F v) x₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hIopen x₀ hx₀
  have hcx₀ : x₀ - ε / 2 < x₀ := by linarith
  have hx₀d : x₀ < x₀ + ε / 2 := by linarith
  have hcdI : Icc (x₀ - ε / 2) (x₀ + ε / 2) ⊆ I := fun t ht ↦ hball <| by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hcI : x₀ - ε / 2 ∈ I := hcdI ⟨le_rfl, (hcx₀.trans hx₀d).le⟩
  have hdI : x₀ + ε / 2 ∈ I := hcdI ⟨(hcx₀.trans hx₀d).le, le_rfl⟩
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP₁.mono hcdI)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ x₀ ⟨hcx₀.le, hx₀d.le⟩)
  have hSmeas : MeasurableSet (I ∩ Ioi (x₀ - ε / 2)) := hI.measurableSet.inter measurableSet_Ioi
  have hsub : ∀ x ∈ Ioo (x₀ - ε / 2) (x₀ + ε / 2), (I ∩ Ioi (x₀ - ε / 2)) ∩ Ioi x = I ∩ Ioi x :=
    fun x hx ↦ by rw [inter_assoc, Ioi_inter_Ioi, sup_eq_right.2 hx.1.le]
  have hderiv_ind := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict (I ∩ Ioi (x₀ - ε / 2)))
    (F := fun x v ↦ (Ioi x).indicator (fun u ↦ K x u • F u) v)
    (F' := fun v ↦ (Ioi x₀).indicator (fun u ↦ K' x₀ u • F u) v)
    (bound := fun v ↦ M₁ * (Q v * ‖F v‖)) (s := Ioo (x₀ - ε / 2) (x₀ + ε / 2))
    (Ioo_mem_nhds hcx₀ hx₀d)
    (by
      filter_upwards [Ioo_mem_nhds hcx₀ hx₀d] with x hx
      have hxI : x ∈ I := hcdI ⟨hx.1.le, hx.2.le⟩
      exact (integrableOn_indicator_kernel_smul_on hI hK hKle hF hx.1.le hxI
        (hFint x hxI)).aestronglyMeasurable)
    (integrableOn_indicator_kernel_smul_on hI hK hKle hF hcx₀.le hx₀ (hFint x₀ hx₀))
    (integrableOn_indicator_kernel_smul_on hI hK' hK'le hF hcx₀.le hx₀
      (hFint x₀ hx₀)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hSmeas] with v hv
      exact lipschitzOnWith_indicator_kernel_smul hI hK hKdiag hKderiv hcI hdI hM₁0
        (fun t ht u hu htu ↦ (hK'le t (hcdI ht) u hu htu).trans
          (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hM₁ t ht)) (hQ0 u hu)))
        hQ0 hv.1)
    ((hFint _ hcI).const_mul M₁)
    (by
      filter_upwards [ae_restrict_mem hSmeas, ae_restrict_of_ae (Measure.ae_ne volume x₀)]
        with v hv hvne
      rcases hvne.lt_or_gt with hlt | hgt
      · rw [indicator_of_notMem (notMem_Ioi.2 hlt.le)]
        refine (hasDerivAt_const x₀ (0 : E)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hlt] with x hx
        exact indicator_of_notMem (notMem_Ioi.2 hx.le) _
      · rw [indicator_of_mem hgt]
        refine ((hKderiv x₀ hx₀ v hv.1 hgt).smul_const (F v)).congr_of_eventuallyEq ?_
        filter_upwards [Iio_mem_nhds hgt] with x hx
        exact indicator_of_mem (mem_Ioi.2 hx) _)
  have hres := hderiv_ind.2.congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds hcx₀ hx₀d] with x hx
    rw [setIntegral_indicator measurableSet_Ioi, hsub x hx])
  rwa [setIntegral_indicator measurableSet_Ioi, hsub x₀ ⟨hcx₀, hx₀d⟩] at hres

/-- **Volterra integral equations, derivative formula.** On an open order-connected set `I`, if
`K x x = 0` and `∂K/∂x (x, v) = K' x v` for `x < v` extends continuously to `x ≤ v` with
`‖K' x v‖ ≤ P₁ x * Q v`, then every continuous solution `h` with `h = O(P)` towards the right
endpoint of `I` is differentiable at every `x ∈ I` with derivative
`∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)`. -/
theorem hasDerivAt_volterra_solution_on (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₁ : ContinuousOn P₁ I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atTop] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)) x := by
  intro x hx
  have hd := hasDerivAt_integral_kernel_smul_on hIopen hI hK hKdiag hKderiv hK' hP₁ hQ0 hKle hK'le
    (hJ.add (hψ.smul hh))
    (fun t ht ↦ integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh hO ht) hx
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hIopen.mem_nhds hx] with t ht
  exact heq t ht

/-- **Volterra integral equations, `C¹` regularity.** Under the hypotheses of
`TauCeti.hasDerivAt_volterra_solution_on`, the solution `h` is continuously differentiable
on `I`. -/
theorem contDiffOn_volterra_solution_on (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₁ : ContinuousOn P₁ I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atTop] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)) :
    ContDiffOn ℝ 1 h I := by
  have hderiv := hasDerivAt_volterra_solution_on hIopen hI hK hKdiag hKderiv hK' hJ hψ hQ hP₁
    hP0 hQ0 hKle hK'le hΦ hΨ hh hO heq
  have hcont_deriv : ContinuousOn (derivWithin h I) I :=
    (continuousOn_integral_kernel_smul_on hI hK' hK'le hP₁ hQ0 (hJ.add (hψ.smul hh))
      (fun t ht ↦ integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh hO ht)
      ).congr fun x hx ↦ by rw [derivWithin_of_isOpen hIopen hx, (hderiv x hx).deriv]; rfl
  exact (contDiffOn_one_iff_derivWithin hIopen.uniqueDiffOn).2
    ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt, hcont_deriv⟩

end Differentiability

/-- **Derivative bound for a Volterra solution.** If `h` satisfies the Volterra bound
`‖h v‖ ≤ P v * Φ v * exp (Ψ v)` on `I ∩ Ioi x` and has derivative
`∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)` at `x`, with `‖K' x v‖ ≤ P₁ x * Q v`, then
`‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)`. -/
theorem norm_deriv_volterra_solution_le_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} (hI : I.OrdConnected)
    (hP0 : ∀ v ∈ I, 0 ≤ P v) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    {x : ℝ} (hP₁0 : 0 ≤ P₁ x)
    (hK'le : ∀ v ∈ I, x ≤ v → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : IntegrableOn (fun u ↦ Q u * ‖J u‖) (I ∩ Ioi x))
    (hΨ : IntegrableOn (fun u ↦ P u * Q u * ‖ψ u‖) (I ∩ Ioi x))
    {h : ℝ → E}
    (hhle : ∀ v ∈ I ∩ Ioi x, ‖h v‖ ≤ P v * (∫ u in I ∩ Ioi v, Q u * ‖J u‖) *
      Real.exp (∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖))
    (hderiv : HasDerivAt h (∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)) x) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  set Φx := ∫ v in I ∩ Ioi x, Q v * ‖J v‖
  set g : ℝ → ℝ := fun u ↦ P u * Q u * ‖ψ u‖
  set Ψ : ℝ → ℝ := fun v ↦ ∫ u in I ∩ Ioi v, g u
  have hexp : IntegrableOn (fun v ↦ g v * Real.exp (Ψ v)) (I ∩ Ioi x) :=
    hΨ.mul_exp_integral_inter_Ioi hI.measurableSet
  rw [hderiv.deriv]
  calc ‖∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)‖
      ≤ ∫ v in I ∩ Ioi x, P₁ x * (Q v * ‖J v‖ + Φx * (g v * Real.exp (Ψ v))) := by
        refine norm_integral_le_of_norm_le ((hΦ.add (hexp.const_mul Φx)).const_mul (P₁ x)) ?_
        filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
        have hPv := hP0 v hv.1
        have hQv := hQ0 v hv.1
        have hΦle : ∫ u in I ∩ Ioi v, Q u * ‖J u‖ ≤ Φx :=
          setIntegral_mono_set hΦ ((ae_restrict_iff' (hI.measurableSet.inter measurableSet_Ioi)).2
            (ae_of_all _ fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1))
            (inter_subset_inter_right I (Ioi_subset_Ioi hv.2.le)).eventuallySubset
        rw [norm_smul]
        calc ‖K' x v‖ * ‖J v + ψ v • h v‖
            ≤ (P₁ x * Q v) * (‖J v‖ + ‖ψ v‖ * ‖h v‖) := by
              gcongr
              · exact hK'le v hv.1 hv.2.le
              · exact (norm_add_le _ _).trans (by rw [norm_smul])
          _ = P₁ x * (Q v * ‖J v‖ + Q v * ‖ψ v‖ * ‖h v‖) := by ring
          _ ≤ P₁ x * (Q v * ‖J v‖ + Q v * ‖ψ v‖ * (P v * Φx * Real.exp (Ψ v))) := by
              grw [hhle v hv, hΦle]
          _ = P₁ x * (Q v * ‖J v‖ + Φx * (g v * Real.exp (Ψ v))) := by simp only [g]; ring
    _ = P₁ x * (Φx + Φx * (Real.exp (Ψ x) - 1)) := by
        rw [integral_const_mul, integral_add hΦ (hexp.const_mul Φx),
          integral_const_mul, hΨ.integral_inter_Ioi_mul_exp_integral_inter_Ioi hI.measurableSet]
    _ = P₁ x * Φx * Real.exp (Ψ x) := by ring

/-- **Sharper derivative bound for constant `P₀` and `‖ψ‖ ≤ ‖J‖`.** If `h` satisfies
`‖h v‖ ≤ exp (P₀ * Φ v) - 1` on `I ∩ Ioi x` and has derivative
`∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)` at `x`, with `‖K' x v‖ ≤ P₁ x * Q v` and
`‖ψ v‖ ≤ ‖J v‖`, then `P₀ * ‖deriv h x‖ ≤ P₁ x * (exp (P₀ * Φ x) - 1)`. -/
theorem mul_norm_deriv_volterra_solution_le_exp_sub_one_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} {P₀ : ℝ}
    (hI : I.OrdConnected) (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v) (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖)
    {x : ℝ} (hP₁0 : 0 ≤ P₁ x)
    (hK'le : ∀ v ∈ I, x ≤ v → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : IntegrableOn (fun u ↦ Q u * ‖J u‖) (I ∩ Ioi x))
    {h : ℝ → E}
    (hhle : ∀ v ∈ I ∩ Ioi x, ‖h v‖ ≤ Real.exp (P₀ * ∫ u in I ∩ Ioi v, Q u * ‖J u‖) - 1)
    (hderiv : HasDerivAt h (∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)) x) :
    P₀ * ‖deriv h x‖ ≤ P₁ x * (Real.exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖J v‖) - 1) := by
  set g : ℝ → ℝ := fun u ↦ P₀ * (Q u * ‖J u‖)
  have hgint : IntegrableOn g (I ∩ Ioi x) := hΦ.const_mul P₀
  have hexp_int : IntegrableOn (fun v ↦ g v * Real.exp (∫ u in I ∩ Ioi v, g u)) (I ∩ Ioi x) :=
    hgint.mul_exp_integral_inter_Ioi hI.measurableSet
  rw [hderiv.deriv]
  calc P₀ * ‖∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)‖
      = ‖∫ v in I ∩ Ioi x, P₀ • (K' x v • (J v + ψ v • h v))‖ := by
        rw [integral_smul, norm_smul, Real.norm_of_nonneg hP₀]
    _ ≤ ∫ v in I ∩ Ioi x, P₁ x * (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by
        refine norm_integral_le_of_norm_le (hexp_int.const_mul (P₁ x)) ?_
        filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
        have hQv := hQ0 v hv.1
        have hGeq : ∫ u in I ∩ Ioi v, g u = P₀ * ∫ u in I ∩ Ioi v, Q u * ‖J u‖ :=
          integral_const_mul P₀ _
        rw [norm_smul, Real.norm_of_nonneg hP₀, norm_smul]
        calc P₀ * (‖K' x v‖ * ‖J v + ψ v • h v‖)
            ≤ P₀ * ((P₁ x * Q v) * (‖J v‖ + ‖ψ v‖ * ‖h v‖)) := by
              gcongr
              · exact hK'le v hv.1 hv.2.le
              · exact (norm_add_le _ _).trans (by rw [norm_smul])
          _ ≤ P₀ * ((P₁ x * Q v) * (‖J v‖ + ‖J v‖ *
              (Real.exp (P₀ * ∫ u in I ∩ Ioi v, Q u * ‖J u‖) - 1))) := by
              gcongr
              · exact hψJ v hv.1
              · exact hhle v hv
          _ = P₁ x * (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by
              rw [hGeq]; simp only [g]; ring
    _ = P₁ x * (Real.exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖J v‖) - 1) := by
        rw [integral_const_mul,
          hgint.integral_inter_Ioi_mul_exp_integral_inter_Ioi hI.measurableSet,
          integral_const_mul]

end RightTail

/-! ### Left-tail Volterra integral equations (`I ∩ Iio x`)

Every right-tail theorem above transfers to the mirrored left-tail equation
`h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)` via the reflection `x ↦ -x`. -/

section LeftTail

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

/-- **Left-tail Volterra integral equations, existence on an interval.** Mirrored analogue of
`TauCeti.exists_volterra_solution_on` for `h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)`. -/
theorem exists_volterra_solution_Iio_on [CompleteSpace E] (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I)
    (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x)) :
    ∃ h : ℝ → E, ContinuousOn h I ∧
      (∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨g, hgcont, hgeq, hgle⟩ := exists_volterra_solution_on (I := -I)
    (K := fun x v ↦ K (-x) (-v))
    (hI.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (hK.comp (continuous_neg.prodMap continuous_neg).continuousOn
      fun _ hp ↦ ⟨hp.1, hp.2.1, neg_le_neg hp.2.2⟩)
    (hJ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hψ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hP.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hQ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ (-x) hx))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΨ (-x) hx))
  refine ⟨fun x ↦ g (-x), hgcont.comp continuous_neg.continuousOn fun _ hx ↦ by simpa using hx,
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hx' := hgeq (-x) (by simpa using hx)
    simp only [neg_neg] at hx'
    refine hx'.trans ?_
    simpa only [Function.comp_apply, Set.inter_neg, neg_neg, Set.neg_Ioi] using
      setIntegral_comp_neg (fun v ↦ K x v • (J v + ψ v • g (-v))) (-I ∩ Ioi (-x))
  · simpa only [Function.comp_apply, setIntegral_comp_neg (fun v ↦ Q v * ‖J v‖) (-I ∩ Ioi (-x)),
      setIntegral_comp_neg (fun v ↦ P v * Q v * ‖ψ v‖) (-I ∩ Ioi (-x)),
      Set.inter_neg, neg_neg, Set.neg_Ioi] using hgle (-x) (by simpa using hx)

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- Any function satisfying the left-tail Volterra bound on `I` is `O(P)` towards the left endpoint
of `I`. -/
theorem isBigO_of_norm_le_volterra_bound_Iio_on (hI : MeasurableSet I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E}
    (hh : ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖)) :
    h =O[map ((↑) : I → ℝ) atBot] P := by
  rw [← Asymptotics.isBigO_comp_neg_map_atTop I]
  refine isBigO_of_norm_le_volterra_bound_on hI.neg
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ (-x) hx))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΨ (-x) hx))
    fun x hx ↦ ?_
  simpa only [setIntegral_comp_neg (fun v ↦ Q v * ‖J v‖) (-I ∩ Ioi x),
    setIntegral_comp_neg (fun v ↦ P v * Q v * ‖ψ v‖) (-I ∩ Ioi x),
    Set.inter_neg, neg_neg, Set.neg_Ioi] using hh (-x) hx

/-- **A priori left-tail Volterra bound.** Mirrored analogue of
`TauCeti.norm_volterra_solution_le_on`. -/
theorem norm_volterra_solution_Iio_le_on (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖) := by
  have hbound := norm_volterra_solution_le_on (I := -I) (K := fun x v ↦ K (-x) (-v))
    (hI.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (hψ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hQ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ (-x) hx))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΨ (-x) hx))
    (hh.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (fun x hx ↦ by simpa only [Function.comp_apply, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K (-x) v • (J v + ψ v • h v)) (-I ∩ Ioi x)] using heq (-x) hx)
  intro x hx
  simpa only [Function.comp_apply, setIntegral_comp_neg (fun v ↦ Q v * ‖J v‖) (-I ∩ Ioi (-x)),
    setIntegral_comp_neg (fun v ↦ P v * Q v * ‖ψ v‖) (-I ∩ Ioi (-x)),
    Set.inter_neg, neg_neg, Set.neg_Ioi] using hbound (-x) (by simpa using hx)

/-- **Left-tail Volterra integral equations, uniqueness.** Mirrored analogue of
`TauCeti.volterra_solution_eqOn`. -/
theorem volterra_solution_Iio_eqOn (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h₁ h₂ : ℝ → E} (hh₁ : ContinuousOn h₁ I) (hh₂ : ContinuousOn h₂ I)
    (hO₁ : h₁ =O[map ((↑) : I → ℝ) atBot] P) (hO₂ : h₂ =O[map ((↑) : I → ℝ) atBot] P)
    (heq₁ : ∀ x ∈ I, h₁ x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h₁ v))
    (heq₂ : ∀ x ∈ I, h₂ x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h₂ v)) :
    EqOn h₁ h₂ I := by
  have heq := volterra_solution_eqOn (I := -I) (K := fun x v ↦ K (-x) (-v))
    (hI.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (hK.comp (continuous_neg.prodMap continuous_neg).continuousOn
      fun _ hp ↦ ⟨hp.1, hp.2.1, neg_le_neg hp.2.2⟩)
    (hJ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hψ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hQ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ (-x) hx))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΨ (-x) hx))
    (hh₁.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hh₂.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO₁)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO₂)
    (fun x hx ↦ by simpa only [Function.comp_apply, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K (-x) v • (J v + ψ v • h₁ v)) (-I ∩ Ioi x)] using heq₁ (-x) hx)
    (fun x hx ↦ by simpa only [Function.comp_apply, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K (-x) v • (J v + ψ v • h₂ v)) (-I ∩ Ioi x)] using heq₂ (-x) hx)
  intro x hx
  simpa using heq (Set.neg_mem_neg.2 hx)

/-- **Sharper left-tail Volterra bound for constant `P₀` and `‖ψ‖ ≤ ‖J‖`.** Mirrored analogue of
`TauCeti.norm_volterra_solution_le_exp_sub_one_on`. -/
theorem norm_volterra_solution_Iio_le_exp_sub_one_on {P₀ : ℝ} (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₀ : 0 ≤ P₀) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P₀ * Q v)
    (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] fun _ ↦ P₀)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, ‖h x‖ ≤ Real.exp (P₀ * ∫ v in I ∩ Iio x, Q v * ‖J v‖) - 1 := by
  have hbound := norm_volterra_solution_le_exp_sub_one_on (I := -I) (K := fun x v ↦ K (-x) (-v))
    (hI.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (hψ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hQ.comp continuous_neg.continuousOn fun _ hx ↦ hx) hP₀
    (fun _ hx ↦ hQ0 _ hx) (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun _ hv ↦ hψJ _ hv)
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ (-x) hx))
    (hh.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (fun x hx ↦ by simpa only [Function.comp_apply, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K (-x) v • (J v + ψ v • h v)) (-I ∩ Ioi x)] using heq (-x) hx)
  intro x hx
  simpa only [Function.comp_apply, setIntegral_comp_neg (fun v ↦ Q v * ‖J v‖) (-I ∩ Ioi (-x)),
    Set.inter_neg, neg_neg, Set.neg_Ioi] using hbound (-x) (by simpa using hx)

section LeftDifferentiability

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}

/-- **Left-tail Volterra integral equations, derivative formula.** Mirrored analogue of
`TauCeti.hasDerivAt_volterra_solution_on`. -/
theorem hasDerivAt_volterra_solution_Iio_on (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, v < x → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₁ : ContinuousOn P₁ I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x := by
  have hd := hasDerivAt_volterra_solution_on (I := -I) (K := fun x v ↦ K (-x) (-v))
    (K' := fun x v ↦ -K' (-x) (-v)) (P₁ := fun x ↦ P₁ (-x))
    hIopen.neg (hI.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (hK.comp (continuous_neg.prodMap continuous_neg).continuousOn
      fun _ hp ↦ ⟨hp.1, hp.2.1, neg_le_neg hp.2.2⟩)
    (fun _ hx ↦ hKdiag _ hx)
    (fun x hx v hv hxv ↦ by
      simpa only [Function.comp_def, neg_one_smul] using
        (hKderiv (-x) hx (-v) hv (neg_lt_neg hxv)).scomp x (hasDerivAt_neg x))
    (hK'.neg.comp (continuous_neg.prodMap continuous_neg).continuousOn
      fun _ hp ↦ ⟨hp.1, hp.2.1, neg_le_neg hp.2.2⟩)
    (hJ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hψ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hQ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hP₁.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun _ hx _ hv hxv ↦ by simpa using hK'le _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ (-x) hx))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΨ (-x) hx))
    (hh.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (fun x hx ↦ by simpa only [Function.comp_apply, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K (-x) v • (J v + ψ v • h v)) (-I ∩ Ioi x)] using heq (-x) hx)
  intro x hx
  have h1 := (hd (-x) (by simpa using hx)).scomp x (hasDerivAt_neg x)
  simpa only [Function.comp_def, neg_neg, neg_smul, integral_neg, one_smul, Set.inter_neg,
    Set.neg_Ioi, setIntegral_comp_neg (fun v ↦ K' x v • (J v + ψ v • h v)) (-I ∩ Ioi (-x))] using h1

/-- **Left-tail Volterra integral equations, `C¹` regularity.** Mirrored analogue of
`TauCeti.contDiffOn_volterra_solution_on`. -/
theorem contDiffOn_volterra_solution_Iio_on (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, v < x → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₁ : ContinuousOn P₁ I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ContDiffOn ℝ 1 h I := by
  have hc := contDiffOn_volterra_solution_on (I := -I) (K := fun x v ↦ K (-x) (-v))
    (K' := fun x v ↦ -K' (-x) (-v)) (P₁ := fun x ↦ P₁ (-x))
    hIopen.neg (hI.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (hK.comp (continuous_neg.prodMap continuous_neg).continuousOn
      fun _ hp ↦ ⟨hp.1, hp.2.1, neg_le_neg hp.2.2⟩)
    (fun _ hx ↦ hKdiag _ hx)
    (fun x hx v hv hxv ↦ by
      simpa only [Function.comp_def, neg_one_smul] using
        (hKderiv (-x) hx (-v) hv (neg_lt_neg hxv)).scomp x (hasDerivAt_neg x))
    (hK'.neg.comp (continuous_neg.prodMap continuous_neg).continuousOn
      fun _ hp ↦ ⟨hp.1, hp.2.1, neg_le_neg hp.2.2⟩)
    (hJ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hψ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hQ.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (hP₁.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun _ hx _ hv hxv ↦ by simpa using hK'le _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ (-x) hx))
    (fun x hx ↦ (integrableOn_comp_neg_iff (μ := volume) _ (-I ∩ Ioi x)).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΨ (-x) hx))
    (hh.comp continuous_neg.continuousOn fun _ hx ↦ hx)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (fun x hx ↦ by simpa only [Function.comp_apply, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K (-x) v • (J v + ψ v • h v)) (-I ∩ Ioi x)] using heq (-x) hx)
  exact (hc.comp contDiff_neg.contDiffOn fun _ hx ↦ by simpa using hx).congr fun _ _ ↦ by simp

end LeftDifferentiability

private lemma hasDerivAt_comp_neg_volterra {K' : ℝ → ℝ → 𝕜} {h : ℝ → E} {x : ℝ}
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    HasDerivAt (fun t ↦ h (-t))
      (∫ v in -I ∩ Ioi (-x), (-K' x (-v)) • (J (-v) + ψ (-v) • h (-v))) (-x) := by
  have hd0 : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) (- -x) := by
    simpa only [neg_neg] using hderiv
  simpa only [Function.comp_def, neg_smul, integral_neg, one_smul,
    ← Set.neg_Iio, ← Set.inter_neg, ← setIntegral_comp_neg, neg_neg] using
    hd0.scomp (-x) (hasDerivAt_neg (-x))

/-- **Derivative bound for a left-tail Volterra solution.** Mirrored analogue of
`TauCeti.norm_deriv_volterra_solution_le_on`. -/
theorem norm_deriv_volterra_solution_Iio_le_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} (hI : I.OrdConnected)
    (hP0 : ∀ v ∈ I, 0 ≤ P v) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    {x : ℝ} (hP₁0 : 0 ≤ P₁ x)
    (hK'le : ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : IntegrableOn (fun u ↦ Q u * ‖J u‖) (I ∩ Iio x))
    (hΨ : IntegrableOn (fun u ↦ P u * Q u * ‖ψ u‖) (I ∩ Iio x))
    {h : ℝ → E}
    (hhle : ∀ v ∈ I ∩ Iio x, ‖h v‖ ≤ P v * (∫ u in I ∩ Iio v, Q u * ‖J u‖) *
      Real.exp (∫ u in I ∩ Iio v, P u * Q u * ‖ψ u‖))
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖) := by
  have hd := hasDerivAt_comp_neg_volterra hderiv
  have hle := norm_deriv_volterra_solution_le_on (I := -I) (K' := fun t v ↦ -K' (-t) (-v))
    (P₁ := fun t ↦ P₁ (-t)) (hI.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (fun _ hv ↦ hP0 _ hv) (fun _ hv ↦ hQ0 _ hv) (x := -x) (by simpa using hP₁0)
    (fun v hv hxv ↦ by simpa using hK'le (-v) hv (neg_le.1 hxv))
    ((integrableOn_comp_neg_iff (μ := volume) (fun u ↦ Q u * ‖J u‖) (-I ∩ Ioi (-x))).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ))
    ((integrableOn_comp_neg_iff (μ := volume) (fun u ↦ P u * Q u * ‖ψ u‖) (-I ∩ Ioi (-x))).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΨ))
    (fun v hv ↦ by
      have hv' : -v ∈ I ∩ Iio x := ⟨hv.1, neg_lt.1 hv.2⟩
      simpa only [setIntegral_comp_neg (fun u ↦ Q u * ‖J u‖) (-I ∩ Ioi v),
        setIntegral_comp_neg (fun u ↦ P u * Q u * ‖ψ u‖) (-I ∩ Ioi v),
        Set.inter_neg, neg_neg, Set.neg_Ioi] using hhle (-v) hv')
    (by simpa only [neg_neg] using hd)
  have hdeq : ‖deriv (fun t ↦ h (-t)) (-x)‖ = ‖deriv h x‖ := by
    rw [hd.deriv, hderiv.deriv]
    simp only [neg_smul, integral_neg, norm_neg, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K' x v • (J v + ψ v • h v)) (-I ∩ Ioi (-x))]
  simpa only [hdeq, setIntegral_comp_neg (fun v ↦ Q v * ‖J v‖) (-I ∩ Ioi (-x)),
    setIntegral_comp_neg (fun v ↦ P v * Q v * ‖ψ v‖) (-I ∩ Ioi (-x)),
    Set.inter_neg, neg_neg, Set.neg_Ioi] using hle

/-- **Sharper derivative bound for a left-tail Volterra solution with constant `P₀` and
`‖ψ‖ ≤ ‖J‖`.** Mirrored analogue of
`TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one_on`. -/
theorem mul_norm_deriv_volterra_solution_Iio_le_exp_sub_one_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}
    {P₀ : ℝ} (hI : I.OrdConnected) (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖) {x : ℝ} (hP₁0 : 0 ≤ P₁ x)
    (hK'le : ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : IntegrableOn (fun u ↦ Q u * ‖J u‖) (I ∩ Iio x))
    {h : ℝ → E}
    (hhle : ∀ v ∈ I ∩ Iio x, ‖h v‖ ≤ Real.exp (P₀ * ∫ u in I ∩ Iio v, Q u * ‖J u‖) - 1)
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    P₀ * ‖deriv h x‖ ≤ P₁ x * (Real.exp (P₀ * ∫ v in I ∩ Iio x, Q v * ‖J v‖) - 1) := by
  have hd := hasDerivAt_comp_neg_volterra hderiv
  have hle := mul_norm_deriv_volterra_solution_le_exp_sub_one_on (I := -I)
    (K' := fun t v ↦ -K' (-t) (-v)) (P₁ := fun t ↦ P₁ (-t))
    (hI.preimage_anti fun _ _ h ↦ neg_le_neg h) hP₀
    (fun _ hv ↦ hQ0 _ hv) (fun _ hv ↦ hψJ _ hv) (x := -x) (by simpa using hP₁0)
    (fun v hv hxv ↦ by simpa using hK'le (-v) hv (neg_le.1 hxv))
    ((integrableOn_comp_neg_iff (μ := volume) (fun u ↦ Q u * ‖J u‖) (-I ∩ Ioi (-x))).2
      (by simpa only [Set.inter_neg, neg_neg, Set.neg_Ioi] using hΦ))
    (fun v hv ↦ by
      have hv' : -v ∈ I ∩ Iio x := ⟨hv.1, neg_lt.1 hv.2⟩
      simpa only [setIntegral_comp_neg (fun u ↦ Q u * ‖J u‖) (-I ∩ Ioi v),
        Set.inter_neg, neg_neg, Set.neg_Ioi] using hhle (-v) hv')
    (by simpa only [neg_neg] using hd)
  have hdeq : ‖deriv (fun t ↦ h (-t)) (-x)‖ = ‖deriv h x‖ := by
    rw [hd.deriv, hderiv.deriv]
    simp only [neg_smul, integral_neg, norm_neg, Set.inter_neg, neg_neg, Set.neg_Ioi,
      setIntegral_comp_neg (fun v ↦ K' x v • (J v + ψ v • h v)) (-I ∩ Ioi (-x))]
  simpa only [hdeq, setIntegral_comp_neg (fun v ↦ Q v * ‖J v‖) (-I ∩ Ioi (-x)),
    Set.inter_neg, neg_neg, Set.neg_Ioi] using hle

end LeftTail

/-! ### Degenerate case `K = 0` -/

example {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [CompleteSpace E] {I : Set ℝ} (hI : I.OrdConnected)
    {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) :
    ∃ h : ℝ → E, EqOn h 0 I ∧
      ∀ x ∈ I, (0 : ℝ) ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  have hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖(0 : 𝕜)‖ ≤ P x * Q v := fun x hx v hv _ ↦ by
    simpa using mul_nonneg (hP0 x hx) (hQ0 v hv)
  obtain ⟨h, hcont, heq, hle⟩ := exists_volterra_solution_on (K := fun _ _ ↦ (0 : 𝕜)) hI
    continuousOn_const hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hzero : EqOn h 0 I := volterra_solution_eqOn (K := fun _ _ ↦ (0 : 𝕜)) hI
    continuousOn_const hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hcont continuousOn_const
    (isBigO_of_norm_le_volterra_bound_on hI.measurableSet hP0 hQ0 hΦ hΨ hle)
    (Asymptotics.isBigO_zero P _) heq fun _ _ ↦ by simp
  exact ⟨h, hzero, fun x hx ↦ by simpa [hzero hx] using hle x hx⟩

end TauCeti
