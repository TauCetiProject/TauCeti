/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.ParametricIntegral.MovingEndpoint
import TauCeti.Analysis.SpecialFunctions.Exp.Taylor
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Order.Interval.Set.OrdConnected
import TauCeti.Topology.Algebra.Group.Pointwise
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
Specializing any right-tail theorem to a half-line `Ioi a` is immediate using
`ordConnected_Ioi`, `Ioi_subset_Ioi`, and `Filter.map_val_Ioi_atTop`.

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
* `TauCeti.exists_volterra_solution`: specialization to a half-line `(a, ∞)`
  (Olver, Chapter 6, Theorem 10.1).
* `TauCeti.isBigO_of_norm_le_volterra_bound_on`: any function satisfying the Volterra bound is
  `O(P)` towards the right endpoint of `I`.
* `TauCeti.norm_volterra_solution_le_on`: every continuous solution with `h = O(P)` satisfies
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.volterra_solution_eqOn`: uniqueness among continuous solutions with `h = O(P)`.
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
/-- Triangle inequality for the Volterra forcing integrand `J v + ψ v • h v`. -/
private lemma norm_add_smul_le {h : ℝ → E} (v : ℝ) :
    ‖J v + ψ v • h v‖ ≤ ‖J v‖ + ‖ψ v‖ * ‖h v‖ :=
  (norm_add_le _ _).trans_eq (by rw [norm_smul])

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- The tail integrals `∫ v in I ∩ Ioi x, Q v * ‖J v‖` are nonnegative. -/
private lemma integral_forcing_weight_nonneg (hI : MeasurableSet I)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) (x : ℝ) :
    0 ≤ ∫ v in I ∩ Ioi x, Q v * ‖J v‖ :=
  setIntegral_nonneg (hI.inter measurableSet_Ioi)
    fun v hv ↦ forcing_weight_nonneg (J := J) hQ0 v hv.1

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- The tail integrals `∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖` are nonnegative. -/
private lemma integral_coeff_weight_nonneg (hI : MeasurableSet I)
    (hP0 : ∀ v ∈ I, 0 ≤ P v) (hQ0 : ∀ v ∈ I, 0 ≤ Q v) (x : ℝ) :
    0 ≤ ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖ :=
  setIntegral_nonneg (hI.inter measurableSet_Ioi)
    fun v hv ↦ coeff_weight_nonneg (ψ := ψ) hP0 hQ0 v hv.1

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
    integral_forcing_weight_nonneg hI.measurableSet hQ0 x
  have hΨv : 0 ≤ ∫ u in I ∩ Ioi v, P u * Q u * ‖ψ u‖ :=
    integral_coeff_weight_nonneg hI.measurableSet hP0 hQ0 v
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
    refine ⟨continuousOn_integral_kernel_smul_inter_Ioi hI hK hKle hP hQ0
      (hJ.aestronglyMeasurable hI.measurableSet) hΦ, fun x hx ↦ ?_⟩
    simpa [picardTermOn] using norm_integral_kernel_smul_inter_Ioi_le hI.measurableSet (hKle x hx)
      (hΦ x hx)
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
    refine ⟨continuousOn_integral_kernel_smul_inter_Ioi hI hK hKle hP hQ0
      ((hψ.smul hcont).aestronglyMeasurable hI.measurableSet) hFint, fun x hx ↦ ?_⟩
    set Φx := ∫ v in I ∩ Ioi x, Q v * ‖J v‖
    set g : ℝ → ℝ := fun v ↦ P v * Q v * ‖ψ v‖ with hg
    refine (norm_integral_kernel_smul_inter_Ioi_le hI.measurableSet (hKle x hx)
      (hFint x hx)).trans ?_
    have hint : ∫ v in I ∩ Ioi x, Q v * ‖ψ v • picardTermOn I K J ψ k v‖ ≤
        Φx / k ! * ∫ v in I ∩ Ioi x, g v * (∫ u in I ∩ Ioi v, g u) ^ k := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hFint x hx)
        (((hΨ x hx).mul_pow_integral_inter_Ioi hI.measurableSet k).const_mul _)
        (hI.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_
      have := hP0 v hv.1
      have := hQ0 v hv.1
      have : 0 ≤ ∫ u in I ∩ Ioi v, g u :=
        integral_coeff_weight_nonneg (ψ := ψ) hI.measurableSet hP0 hQ0 v
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
  tsum_of_norm_bounded
    ((Real.hasSum_pow_div_factorial (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)).mul_left
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
  obtain ⟨c, d, hcdI, _, hx₀cd, hcdN⟩ := hI.exists_Icc_mem_nhdsWithin hx₀ hx₀
  obtain ⟨hcx₀, hx₀d⟩ := hx₀cd
  have hcI : c ∈ I := hcdI ⟨le_rfl, hcx₀.trans hx₀d⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hcdI)
  refine ((continuousOn_tsum
    (fun k ↦ (picardTermOn_spec hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).1.mono hcdI)
    ((Real.summable_pow_div_factorial (∫ v in I ∩ Ioi c, P v * Q v * ‖ψ v‖)).mul_left
      ((∫ v in I ∩ Ioi c, Q v * ‖J v‖) * M))
    fun k x hx ↦ ?_) x₀ ⟨hcx₀, hx₀d⟩).mono_of_mem_nhdsWithin hcdN
  have := integral_forcing_weight_nonneg (J := J) hI.measurableSet hQ0 c
  have := integral_coeff_weight_nonneg (ψ := ψ) hI.measurableSet hP0 hQ0 c
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
  -- split the integral into its `J`-part and its `h`-part
  have hψh : IntegrableOn (fun v ↦ Q v * ‖ψ v • h v‖) (I ∩ Ioi x) :=
    integrableOn_weight_smul_on hI hψ hQ hQ0 hΨ hcont hx
      (C := (∫ u in I ∩ Ioi x, Q u * ‖J u‖) * Real.exp (∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖))
      fun v hv ↦
        (norm_tsum_picardTermOn_le hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hv.1).trans
          (mul_tail_le_of_le_on hI hP0 hQ0 hΦ hΨ (Real.exp_monotone.monotoneOn _)
            (fun _ _ ↦ (Real.exp_pos _).le) hx hv.1 hv.2.le)
  have hKJ : IntegrableOn (fun v ↦ K x v • J v) (I ∩ Ioi x) :=
    integrableOn_kernel_smul_inter_Ioi_of_continuousOn hI.measurableSet hK hKle hJ hx (hΦ x hx)
  have hKψh : IntegrableOn (fun v ↦ K x v • ψ v • h v) (I ∩ Ioi x) :=
    integrableOn_kernel_smul_inter_Ioi_of_continuousOn hI.measurableSet hK hKle (hψ.smul hcont) hx
      hψh
  simp only [smul_add]
  rw [integral_add hKJ hKψh]
  -- expand `h v` as the series of increments and interchange the sum and the integral
  set Φx := ∫ u in I ∩ Ioi x, Q u * ‖J u‖
  set Ψx := ∫ u in I ∩ Ioi x, P u * Q u * ‖ψ u‖
  have hTle : ∀ k, ∀ v ∈ I, x ≤ v → ‖T k v‖ ≤ Φx * (Ψx ^ k / k !) * P v := fun k _ hv hxv ↦
    norm_picardTermOn_le_of_le hI hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hx hv hxv
  have hFk : ∀ k, IntegrableOn (fun v ↦ K x v • ψ v • T k v) (I ∩ Ioi x) := fun k ↦
    integrableOn_kernel_smul_inter_Ioi_of_continuousOn hI.measurableSet hK hKle
      (hψ.smul (hspec k).1) hx
      (integrableOn_weight_smul_on hI hψ hQ hQ0 hΨ (hspec k).1 hx
        fun v hv ↦ hTle k v hv.1 hv.2.le)
  have hsum : Summable fun k ↦ ∫ v in I ∩ Ioi x, ‖K x v • ψ v • T k v‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial Ψx).mul_left (P x * Φx * Ψx))
    refine (setIntegral_mono_on (hFk k).norm
      ((hΨ x hx).const_mul (P x * Φx * (Ψx ^ k / k !)))
      (hI.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_).trans_eq
      (by rw [integral_const_mul]; ring)
    refine (norm_kernel_smul_le (hKle x hx) hv.1 hv.2.le _).trans ?_
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

/-- **Volterra integral equations, existence.** Let `K` be continuous on
`{(x, v) | a < x ≤ v}` with `‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are continuous on
`(a, ∞)`, and let `J`, `ψ` be continuous on `(a, ∞)` such that
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for
every `x > a`. Then the Volterra integral equation
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has a solution, continuous on `(a, ∞)`, such
that `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x > a` (the existence part of Olver, Chapter 6,
Theorem 10.1). -/
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
  have hIoi (x : ℝ) (hx : a < x) : Ioi a ∩ Ioi x = Ioi x :=
    inter_eq_right.2 (Ioi_subset_Ioi hx.le)
  obtain ⟨h, hcont, heq, hle⟩ := exists_volterra_solution_on ordConnected_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ hP hQ hP0 hQ0 (fun x hx v _ hxv ↦ hKle x v hx hxv)
    (fun x hx ↦ by simpa only [hIoi x hx] using hΦ x hx)
    (fun x hx ↦ by simpa only [hIoi x hx] using hΨ x hx)
  exact ⟨h, hcont, fun x hx ↦ by simpa only [hIoi x hx] using heq x hx,
    fun x hx ↦ by simpa only [hIoi x hx] using hle x hx⟩


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
    integral_forcing_weight_nonneg hI hQ0 x₀
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
  have hO' : (fun v ↦ Q v * ‖ψ v • h v‖) =O[map ((↑) : I → ℝ) atTop] fun v ↦ P v * Q v * ‖ψ v‖ := by
    rw [Asymptotics.isBigO_iff] at hO ⊢
    obtain ⟨C, hC⟩ := hO
    refine ⟨C, ?_⟩
    rw [eventually_map] at hC ⊢
    filter_upwards [hC] with v hv
    have hQv := hQ0 v v.property
    have hPv := hP0 v v.property
    rw [Real.norm_of_nonneg (mul_nonneg hQv (norm_nonneg _)),
      Real.norm_of_nonneg (mul_nonneg (mul_nonneg hPv hQv) (norm_nonneg _)), norm_smul]
    calc Q v * (‖ψ v‖ * ‖h v‖) ≤ Q v * (‖ψ v‖ * (C * ‖P v‖)) := by gcongr
      _ = C * (P v * Q v * ‖ψ v‖) := by rw [Real.norm_of_nonneg hPv]; ring
  exact (hQ.mul (hψ.smul hh).norm).locallyIntegrableOn hI.measurableSet
    |>.integrableOn_inter_Ioi_of_isBigO hI hO' hΨ hx

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
    add_nonneg (integral_forcing_weight_nonneg hI.measurableSet hQ0 x)
      (setIntegral_nonneg hSmeas fun u hu ↦ mul_nonneg (hQ0 u hu.1) (norm_nonneg _))
  refine ⟨_, hC0, fun v hv hxv ↦ ?_⟩
  have hsub : I ∩ Ioi v ⊆ I ∩ Ioi x := inter_subset_inter_right I (Ioi_subset_Ioi hxv)
  have hdom : IntegrableOn (fun u ↦ P v * (Q u * ‖J u‖ + Q u * ‖ψ u • h u‖)) (I ∩ Ioi v) :=
    ((hΦ v hv).add (hψh.mono_set hsub)).const_mul (P v)
  have hbound : ‖h v‖ ≤ ∫ u in I ∩ Ioi v, P v * (Q u * ‖J u‖ + Q u * ‖ψ u • h u‖) := by
    rw [heq v hv]
    refine norm_integral_le_of_norm_le hdom ?_
    filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with u hu
    refine (norm_kernel_smul_le (hKle v hv) hu.1 hu.2.le _).trans ?_
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

/-- Tail-supersolution comparison: if `‖h‖ ≤ B + R` on `I ∩ Ici x` and every tail bound
`‖h‖ ≤ B + R * f` on `I ∩ Ioi v` feeds back into `‖h v‖ ≤ B v + R v * ∫ u in I ∩ Ioi v, g u * f u`,
then iterating `k` times yields a factorial remainder that vanishes as `k → ∞`, giving
`‖h x‖ ≤ B x`. -/
private lemma norm_le_of_tail_supersolution {E' : Type*} [NormedAddCommGroup E'] {I : Set ℝ}
    (hI : MeasurableSet I) {g B R : ℝ → ℝ} {h : ℝ → E'} {x : ℝ} (hx : x ∈ I)
    (hgint : ∀ v ∈ I, IntegrableOn g (I ∩ Ioi v))
    (h0 : ∀ v ∈ I, x ≤ v → ‖h v‖ ≤ B v + R v)
    (hstep : ∀ v ∈ I, x ≤ v → ∀ (f : ℝ → ℝ),
      (∀ u ∈ I ∩ Ioi v, ‖h u‖ ≤ B u + R u * f u) →
      IntegrableOn (fun u ↦ g u * f u) (I ∩ Ioi v) →
      ‖h v‖ ≤ B v + R v * ∫ u in I ∩ Ioi v, g u * f u) :
    ‖h x‖ ≤ B x := by
  set G : ℝ → ℝ := fun v ↦ ∫ u in I ∩ Ioi v, g u
  have hind : ∀ k : ℕ, ∀ v ∈ I, x ≤ v → ‖h v‖ ≤ B v + R v * (G v ^ k / k.factorial) := by
    intro k
    induction k with
    | zero =>
      intro v hv hxv
      simpa using h0 v hv hxv
    | succ k ih =>
      intro v hv hxv
      have hpow : IntegrableOn (fun u ↦ g u * (G u ^ k / k.factorial)) (I ∩ Ioi v) := by
        dsimp only [G]
        simp_rw [← mul_div_assoc]
        exact ((hgint v hv).mul_pow_integral_inter_Ioi hI k).div_const _
      refine (hstep v hv hxv _ (fun u hu ↦ ih u hu.1 (hxv.trans hu.2.le)) hpow).trans_eq ?_
      simp_rw [← mul_div_assoc]
      rw [integral_div, (hgint v hv).integral_inter_Ioi_mul_pow_integral_inter_Ioi hI k,
        Nat.factorial_succ]
      dsimp only [G]; push_cast; field_simp
  have hlim : Tendsto (fun k ↦ B x + R x * (G x ^ k / k.factorial)) atTop (𝓝 (B x)) := by
    simpa using tendsto_const_nhds.add
      ((Real.summable_pow_div_factorial (G x)).tendsto_atTop_zero.const_mul (R x))
  exact ge_of_tendsto' hlim fun k ↦ hind k x hx le_rfl

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
  refine norm_le_of_tail_supersolution hI.measurableSet
    (B := fun v ↦ P v * Φ v * Real.exp (Ψ v)) (R := fun v ↦ C * P v) hx hΨ
    (fun v hv hxv ↦ by
      have hPv := hP0 v hv
      have hΦv : 0 ≤ Φ v := integral_forcing_weight_nonneg hI.measurableSet hQ0 v
      exact (hCle v hv hxv).trans (le_add_of_nonneg_left (by positivity)))
    (fun v hv _ f hih hfint ↦ ?_)
  have hexp : IntegrableOn (fun u ↦ g u * Real.exp (Ψ u)) (I ∩ Ioi v) :=
    (hΨ v hv).mul_exp_integral_inter_Ioi hI.measurableSet
  have hsum : IntegrableOn (fun u ↦ Φ v * (g u * Real.exp (Ψ u)) + C * (g u * f u))
      (I ∩ Ioi v) :=
    (hexp.const_mul (Φ v)).add (hfint.const_mul C)
  have hdom : IntegrableOn (fun u ↦ P v * (Q u * ‖J u‖ +
      (Φ v * (g u * Real.exp (Ψ u)) + C * (g u * f u)))) (I ∩ Ioi v) :=
    ((hΦ v hv).add hsum).const_mul (P v)
  refine (heq v hv ▸ norm_integral_le_of_norm_le hdom ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with u hu
    refine (norm_kernel_smul_le (hKle v hv) hu.1 hu.2.le _).trans
      (mul_le_mul_of_nonneg_left ?_ (hP0 v hv))
    have hPu := hP0 u hu.1
    have hQu := hQ0 u hu.1
    have hΦle : Φ u ≤ Φ v := antitoneOn_integral_inter_Ioi hI.measurableSet
      (forcing_weight_nonneg (J := J) hQ0) hΦ hv hu.1 hu.2.le
    calc Q u * ‖J u + ψ u • h u‖ ≤ Q u * (‖J u‖ + ‖ψ u‖ * ‖h u‖) := by
          gcongr; exact norm_add_smul_le u
      _ = Q u * ‖J u‖ + Q u * ‖ψ u‖ * ‖h u‖ := by ring
      _ ≤ Q u * ‖J u‖ + Q u * ‖ψ u‖ * (P u * Φ v * Real.exp (Ψ u) + C * P u * f u) := by
          grw [hih u hu, hΦle]
      _ = Q u * ‖J u‖ + (Φ v * (g u * Real.exp (Ψ u)) + C * (g u * f u)) := by
          simp only [g]; ring
  · rw [integral_const_mul, integral_add (hΦ v hv) hsum,
      integral_add (hexp.const_mul (Φ v)) (hfint.const_mul C), integral_const_mul,
      integral_const_mul, (hΨ v hv).integral_inter_Ioi_mul_exp_integral_inter_Ioi hI.measurableSet]
    dsimp only [Φ, Ψ]; ring

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
    have h1 := integrableOn_kernel_smul_inter_Ioi_of_continuousOn (F := fun v ↦ J v + ψ v • h₁ v)
      hI.measurableSet hK hKle (hJ.add (hψ.smul hh₁)) hx
      (integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh₁ hO₁ hx)
    have h2 := integrableOn_kernel_smul_inter_Ioi_of_continuousOn (F := fun v ↦ J v + ψ v • h₂ v)
      hI.measurableSet hK hKle (hJ.add (hψ.smul hh₂)) hx
      (integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh₂ hO₂ hx)
    rw [Pi.sub_apply, heq₁ x hx, heq₂ x hx, ← integral_sub h1 h2]
    refine setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi) fun v _ ↦ ?_
    rw [zero_add, ← smul_sub, add_sub_add_left_eq_sub, ← smul_sub, Pi.sub_apply]
  have hbound := norm_volterra_solution_le_on (J := fun _ ↦ (0 : E)) hI hψ hQ hP0 hQ0 hKle
    (fun _ _ ↦ by simp) hΨ (hh₁.sub hh₂) (hO₁.sub hO₂) hdiff
  intro x hx
  have h0 : ‖h₁ x - h₂ x‖ ≤ 0 := by simpa using hbound x hx
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

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
  rw [show P₀ * ∫ v in I ∩ Ioi x, Q v * ‖J v‖ = G x from (integral_const_mul P₀ _).symm]
  refine norm_le_of_tail_supersolution hI.measurableSet
    (B := fun v ↦ Real.exp (G v) - 1) (R := fun _ ↦ C * P₀) hx hgint
    (fun v hv hxv ↦ by
      have hGv : 0 ≤ G v := setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi)
        fun u hu ↦ mul_nonneg hP₀ (forcing_weight_nonneg (J := J) hQ0 u hu.1)
      exact (hCle v hv hxv).trans (le_add_of_nonneg_left (sub_nonneg.2 (Real.one_le_exp hGv))))
    (fun v hv _ f hih hfint ↦ ?_)
  have hexp : IntegrableOn (fun u ↦ g u * Real.exp (G u)) (I ∩ Ioi v) :=
    (hgint v hv).mul_exp_integral_inter_Ioi hI.measurableSet
  have hdom : IntegrableOn (fun u ↦ g u * Real.exp (G u) + C * P₀ * (g u * f u)) (I ∩ Ioi v) :=
    hexp.add (hfint.const_mul _)
  refine (heq v hv ▸ norm_integral_le_of_norm_le hdom ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with u hu
    refine (norm_kernel_smul_le (P := fun _ ↦ P₀) (hKle v hv) hu.1 hu.2.le _).trans ?_
    have hQu := hQ0 u hu.1
    calc P₀ * (Q u * ‖J u + ψ u • h u‖)
        ≤ P₀ * (Q u * (‖J u‖ + ‖ψ u‖ * ‖h u‖)) := by
          gcongr; exact norm_add_smul_le u
      _ ≤ P₀ * (Q u * (‖J u‖ + ‖J u‖ * ‖h u‖)) := by grw [hψJ u hu.1]
      _ = g u + g u * ‖h u‖ := by simp only [g]; ring
      _ ≤ g u + g u * ((Real.exp (G u) - 1) + C * P₀ * f u) := by gcongr; exact hih u hu
      _ = g u * Real.exp (G u) + C * P₀ * (g u * f u) := by ring
  · rw [integral_add hexp (hfint.const_mul _), integral_const_mul,
      (hgint v hv).integral_inter_Ioi_mul_exp_integral_inter_Ioi hI.measurableSet]

/-! ### Differentiability (`C¹`) and derivative bounds -/

section Differentiability

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}

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
  have hd := hasDerivAt_integral_kernel_smul_inter_Ioi hIopen hK hKdiag hKderiv hx
    (hK'.aestronglyMeasurable_slice_inter_Ioi hIopen.measurableSet hx)
    hP₁ hQ0 hKle hK'le ((hJ.add (hψ.smul hh)).aestronglyMeasurable hIopen.measurableSet)
    (fun t ht ↦ integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh hO ht)
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
    (continuousOn_integral_kernel_smul_inter_Ioi hI hK' hK'le hP₁ hQ0
      ((hJ.add (hψ.smul hh)).aestronglyMeasurable hIopen.measurableSet)
      fun t ht ↦ integrableOn_forcing_add_smul_of_isBigO hI hJ hψ hQ hP0 hQ0 hΦ hΨ hh hO ht
      ).congr fun x hx ↦ by rw [derivWithin_of_isOpen hIopen hx, (hderiv x hx).deriv]; rfl
  exact (contDiffOn_one_iff_derivWithin hIopen.uniqueDiffOn).2
    ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt, hcont_deriv⟩

end Differentiability

/-- **Derivative bound for a Volterra solution.** If `h` satisfies the Volterra bound
`‖h v‖ ≤ P v * Φ v * exp (Ψ v)` on `I ∩ Ioi x` and has derivative
`∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)` at `x`, with `‖K' x v‖ ≤ P₁ x * Q v`, then
`‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)`. -/
theorem norm_deriv_volterra_solution_le_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} (hI : MeasurableSet I)
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
    hΨ.mul_exp_integral_inter_Ioi hI
  rw [hderiv.deriv]
  calc ‖∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)‖
      ≤ ∫ v in I ∩ Ioi x, P₁ x * (Q v * ‖J v‖ + Φx * (g v * Real.exp (Ψ v))) := by
        refine norm_integral_le_of_norm_le ((hΦ.add (hexp.const_mul Φx)).const_mul (P₁ x)) ?_
        filter_upwards [ae_restrict_mem (hI.inter measurableSet_Ioi)] with v hv
        have hPv := hP0 v hv.1
        have hQv := hQ0 v hv.1
        have hΦle : ∫ u in I ∩ Ioi v, Q u * ‖J u‖ ≤ Φx :=
          setIntegral_mono_set hΦ ((ae_restrict_iff' (hI.inter measurableSet_Ioi)).2
            (ae_of_all _ fun u hu ↦ forcing_weight_nonneg (J := J) hQ0 u hu.1))
            (inter_subset_inter_right I (Ioi_subset_Ioi hv.2.le)).eventuallySubset
        rw [norm_smul]
        calc ‖K' x v‖ * ‖J v + ψ v • h v‖
            ≤ (P₁ x * Q v) * (‖J v‖ + ‖ψ v‖ * ‖h v‖) := by
              gcongr
              · exact hK'le v hv.1 hv.2.le
              · exact norm_add_smul_le v
          _ = P₁ x * (Q v * ‖J v‖ + Q v * ‖ψ v‖ * ‖h v‖) := by ring
          _ ≤ P₁ x * (Q v * ‖J v‖ + Q v * ‖ψ v‖ * (P v * Φx * Real.exp (Ψ v))) := by
              grw [hhle v hv, hΦle]
          _ = P₁ x * (Q v * ‖J v‖ + Φx * (g v * Real.exp (Ψ v))) := by simp only [g]; ring
    _ = P₁ x * (Φx + Φx * (Real.exp (Ψ x) - 1)) := by
        rw [integral_const_mul, integral_add hΦ (hexp.const_mul Φx),
          integral_const_mul, hΨ.integral_inter_Ioi_mul_exp_integral_inter_Ioi hI]
    _ = P₁ x * Φx * Real.exp (Ψ x) := by ring

/-- **Sharper derivative bound for constant `P₀` and `‖ψ‖ ≤ ‖J‖`.** If `h` satisfies
`‖h v‖ ≤ exp (P₀ * Φ v) - 1` on `I ∩ Ioi x` and has derivative
`∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)` at `x`, with `‖K' x v‖ ≤ P₁ x * Q v` and
`‖ψ v‖ ≤ ‖J v‖`, then `P₀ * ‖deriv h x‖ ≤ P₁ x * (exp (P₀ * Φ x) - 1)`. -/
theorem mul_norm_deriv_volterra_solution_le_exp_sub_one_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} {P₀ : ℝ}
    (hI : MeasurableSet I) (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v) (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖)
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
    hgint.mul_exp_integral_inter_Ioi hI
  rw [hderiv.deriv]
  calc P₀ * ‖∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)‖
      = ‖∫ v in I ∩ Ioi x, P₀ • (K' x v • (J v + ψ v • h v))‖ := by
        rw [integral_smul, norm_smul, Real.norm_of_nonneg hP₀]
    _ ≤ ∫ v in I ∩ Ioi x, P₁ x * (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by
        refine norm_integral_le_of_norm_le (hexp_int.const_mul (P₁ x)) ?_
        filter_upwards [ae_restrict_mem (hI.inter measurableSet_Ioi)] with v hv
        have hQv := hQ0 v hv.1
        have hGeq : ∫ u in I ∩ Ioi v, g u = P₀ * ∫ u in I ∩ Ioi v, Q u * ‖J u‖ :=
          integral_const_mul P₀ _
        rw [norm_smul, Real.norm_of_nonneg hP₀, norm_smul]
        calc P₀ * (‖K' x v‖ * ‖J v + ψ v • h v‖)
            ≤ P₀ * ((P₁ x * Q v) * (‖J v‖ + ‖ψ v‖ * ‖h v‖)) := by
              gcongr
              · exact hK'le v hv.1 hv.2.le
              · exact norm_add_smul_le v
          _ ≤ P₀ * ((P₁ x * Q v) * (‖J v‖ + ‖J v‖ *
              (Real.exp (P₀ * ∫ u in I ∩ Ioi v, Q u * ‖J u‖) - 1))) := by
              gcongr
              · exact hψJ v hv.1
              · exact hhle v hv
          _ = P₁ x * (g v * Real.exp (∫ u in I ∩ Ioi v, g u)) := by
              rw [hGeq]; simp only [g]; ring
    _ = P₁ x * (Real.exp (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖J v‖) - 1) := by
        rw [integral_const_mul,
          hgint.integral_inter_Ioi_mul_exp_integral_inter_Ioi hI,
          integral_const_mul]

end RightTail

/-! ### Left-tail Volterra integral equations (`I ∩ Iio x`)

Every right-tail theorem above transfers to the mirrored left-tail equation
`h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)` via the reflection `x ↦ -x`. -/

section LeftTail

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

private lemma volterra_eq_comp_neg {h : ℝ → E}
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ -I, h (-x) = ∫ v in -I ∩ Ioi x, K (-x) (-v) • (J (-v) + ψ (-v) • h (-v)) :=
  fun x hx ↦ (heq (-x) hx).trans
    (setIntegral_comp_neg_inter_Ioi (fun v ↦ K (-x) v • (J v + ψ v • h v)) I x).symm

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
    (K := fun x v ↦ K (-x) (-v)) hI.neg hK.uncurry_comp_neg
    hJ.comp_neg hψ.comp_neg hP.comp_neg hQ.comp_neg
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi)
  refine ⟨fun x ↦ g (-x), neg_neg I ▸ hgcont.comp_neg, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hx' := hgeq (-x) (by simpa using hx)
    simp only [neg_neg] at hx'
    exact hx'.trans (by simpa using
      setIntegral_comp_neg_inter_Ioi (fun v ↦ K x v • (J v + ψ v • g (-v))) I (-x))
  · simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x),
      setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I (-x), neg_neg] using
      hgle (-x) (by simpa using hx)

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
  refine isBigO_of_norm_le_volterra_bound_on hI.neg (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi) fun x hx ↦ ?_
  simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I x,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I x] using hh (-x) hx

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
    hI.neg hψ.comp_neg hQ.comp_neg (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi)
    hh.comp_neg ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (volterra_eq_comp_neg heq)
  intro x hx
  simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x),
    setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I (-x), neg_neg] using
    hbound (-x) (by simpa using hx)

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
    hI.neg hK.uncurry_comp_neg hJ.comp_neg hψ.comp_neg hQ.comp_neg
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi)
    hh₁.comp_neg hh₂.comp_neg
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO₁)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO₂)
    (volterra_eq_comp_neg heq₁) (volterra_eq_comp_neg heq₂)
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
    hI.neg hψ.comp_neg hQ.comp_neg hP₀ (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun _ hv ↦ hψJ _ hv) (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    hh.comp_neg ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (volterra_eq_comp_neg heq)
  intro x hx
  simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x), neg_neg] using
    hbound (-x) (by simpa using hx)

section LeftDifferentiability

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}

/-- Shared reflection step proving both `HasDerivAt` and `ContDiffOn ℝ 1` for left-tail Volterra
solutions from the corresponding right-tail theorems on `-I`. -/
private lemma volterra_Iio_hasDerivAt_and_contDiffOn (hIopen : IsOpen I) (hI : I.OrdConnected)
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
    (∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) ∧
      ContDiffOn ℝ 1 h I := by
  have hKderiv' : ∀ x ∈ -I, ∀ v ∈ -I, x < v →
      HasDerivAt (fun t ↦ K (-t) (-v)) (-K' (-x) (-v)) x := fun x hx v hv hxv ↦ by
    simpa only [Function.comp_def, neg_one_smul] using
      (hKderiv (-x) hx (-v) hv (neg_lt_neg hxv)).scomp x (hasDerivAt_neg x)
  have hKle' : ∀ x ∈ -I, ∀ v ∈ -I, x ≤ v → ‖K (-x) (-v)‖ ≤ P (-x) * Q (-v) :=
    fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv)
  have hK'le' : ∀ x ∈ -I, ∀ v ∈ -I, x ≤ v → ‖-K' (-x) (-v)‖ ≤ P₁ (-x) * Q (-v) :=
    fun _ hx _ hv hxv ↦ by simpa using hK'le _ hx _ hv (neg_le_neg hxv)
  have hΦ' : ∀ x ∈ -I, IntegrableOn (fun v ↦ Q (-v) * ‖J (-v)‖) (-I ∩ Ioi x) :=
    fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi
  have hΨ' : ∀ x ∈ -I, IntegrableOn (fun v ↦ P (-v) * Q (-v) * ‖ψ (-v)‖) (-I ∩ Ioi x) :=
    fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi
  have hO' : (fun x ↦ h (-x)) =O[map ((↑) : (-I : Set ℝ) → ℝ) atTop] (fun x ↦ P (-x)) :=
    (Asymptotics.isBigO_comp_neg_map_atTop I).2 hO
  have heq' := volterra_eq_comp_neg heq
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · have hd := hasDerivAt_volterra_solution_on (I := -I) (K := fun x v ↦ K (-x) (-v))
      (K' := fun x v ↦ -K' (-x) (-v)) (P₁ := fun x ↦ P₁ (-x))
      hIopen.neg hI.neg hK.uncurry_comp_neg (fun _ hx ↦ hKdiag _ hx) hKderiv'
      hK'.uncurry_comp_neg.neg hJ.comp_neg hψ.comp_neg hQ.comp_neg hP₁.comp_neg
      (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx) hKle' hK'le' hΦ' hΨ' hh.comp_neg hO' heq'
    have h1 := (hd (-x) (by simpa using hx)).scomp x (hasDerivAt_neg x)
    simpa only [Function.comp_def, neg_neg, neg_smul, integral_neg, one_smul,
      setIntegral_comp_neg_inter_Ioi (fun v ↦ K' x v • (J v + ψ v • h v)) I (-x)] using h1
  · have hg := contDiffOn_volterra_solution_on (I := -I) (K := fun x v ↦ K (-x) (-v))
      (K' := fun x v ↦ -K' (-x) (-v)) (P₁ := fun x ↦ P₁ (-x))
      hIopen.neg hI.neg hK.uncurry_comp_neg (fun _ hx ↦ hKdiag _ hx) hKderiv'
      hK'.uncurry_comp_neg.neg hJ.comp_neg hψ.comp_neg hQ.comp_neg hP₁.comp_neg
      (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx) hKle' hK'le' hΦ' hΨ' hh.comp_neg hO' heq'
    simpa only [Function.comp_def, neg_neg] using
      hg.comp contDiff_neg.contDiffOn fun _ hx ↦ Set.neg_mem_neg.2 hx

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
    ∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x :=
  (volterra_Iio_hasDerivAt_and_contDiffOn hIopen hI hK hKdiag hKderiv hK' hJ hψ hQ hP₁ hP0 hQ0
    hKle hK'le hΦ hΨ hh hO heq).1

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
    ContDiffOn ℝ 1 h I :=
  (volterra_Iio_hasDerivAt_and_contDiffOn hIopen hI hK hKdiag hKderiv hK' hJ hψ hQ hP₁ hP0 hQ0
    hKle hK'le hΦ hΨ hh hO heq).2

end LeftDifferentiability

private lemma hasDerivAt_comp_neg_volterra {K' : ℝ → ℝ → 𝕜} {h : ℝ → E} {x : ℝ}
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    HasDerivAt (fun t ↦ h (-t))
      (∫ v in -I ∩ Ioi (-x), (-K' x (-v)) • (J (-v) + ψ (-v) • h (-v))) (-x) := by
  have hd0 : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) (- -x) := by
    simpa only [neg_neg] using hderiv
  simpa only [Function.comp_def, neg_smul, integral_neg, one_smul,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ K' x v • (J v + ψ v • h v)) I (-x), neg_neg] using
    hd0.scomp (-x) (hasDerivAt_neg (-x))

/-- **Derivative bound for a left-tail Volterra solution.** Mirrored analogue of
`TauCeti.norm_deriv_volterra_solution_le_on`. -/
theorem norm_deriv_volterra_solution_Iio_le_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} (hI : MeasurableSet I)
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
  have hle := norm_deriv_volterra_solution_le_on (I := -I) (K' := fun t v ↦ -K' (-t) (-v))
    (P₁ := fun t ↦ P₁ (-t)) hI.neg (fun _ hv ↦ hP0 _ hv) (fun _ hv ↦ hQ0 _ hv)
    (x := -x) (by simpa using hP₁0) (fun v hv hxv ↦ by simpa using hK'le (-v) hv (neg_le.1 hxv))
    (MeasureTheory.IntegrableOn.comp_neg_inter_Ioi (x := -x) (by simpa using hΦ))
    (MeasureTheory.IntegrableOn.comp_neg_inter_Ioi (x := -x) (by simpa using hΨ))
    (fun v hv ↦ by
      have hv' : -v ∈ I ∩ Iio x := ⟨hv.1, neg_lt.1 hv.2⟩
      simpa only [setIntegral_comp_neg_inter_Ioi (fun u ↦ Q u * ‖J u‖) I v,
        setIntegral_comp_neg_inter_Ioi (fun u ↦ P u * Q u * ‖ψ u‖) I v] using hhle (-v) hv')
    (by simpa only [neg_neg] using hasDerivAt_comp_neg_volterra hderiv)
  simpa only [deriv_comp_neg, neg_neg, norm_neg,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x),
    setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I (-x)] using hle

/-- **Sharper derivative bound for a left-tail Volterra solution with constant `P₀` and
`‖ψ‖ ≤ ‖J‖`.** Mirrored analogue of
`TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one_on`. -/
theorem mul_norm_deriv_volterra_solution_Iio_le_exp_sub_one_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}
    {P₀ : ℝ} (hI : MeasurableSet I) (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖) {x : ℝ} (hP₁0 : 0 ≤ P₁ x)
    (hK'le : ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : IntegrableOn (fun u ↦ Q u * ‖J u‖) (I ∩ Iio x))
    {h : ℝ → E}
    (hhle : ∀ v ∈ I ∩ Iio x, ‖h v‖ ≤ Real.exp (P₀ * ∫ u in I ∩ Iio v, Q u * ‖J u‖) - 1)
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    P₀ * ‖deriv h x‖ ≤ P₁ x * (Real.exp (P₀ * ∫ v in I ∩ Iio x, Q v * ‖J v‖) - 1) := by
  have hle := mul_norm_deriv_volterra_solution_le_exp_sub_one_on (I := -I)
    (K' := fun t v ↦ -K' (-t) (-v)) (P₁ := fun t ↦ P₁ (-t)) hI.neg hP₀
    (fun _ hv ↦ hQ0 _ hv) (fun _ hv ↦ hψJ _ hv) (x := -x) (by simpa using hP₁0)
    (fun v hv hxv ↦ by simpa using hK'le (-v) hv (neg_le.1 hxv))
    (MeasureTheory.IntegrableOn.comp_neg_inter_Ioi (x := -x) (by simpa using hΦ))
    (fun v hv ↦ by
      have hv' : -v ∈ I ∩ Iio x := ⟨hv.1, neg_lt.1 hv.2⟩
      simpa only [setIntegral_comp_neg_inter_Ioi (fun u ↦ Q u * ‖J u‖) I v] using hhle (-v) hv')
    (by simpa only [neg_neg] using hasDerivAt_comp_neg_volterra hderiv)
  simpa only [deriv_comp_neg, neg_neg, norm_neg,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x)] using hle

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
