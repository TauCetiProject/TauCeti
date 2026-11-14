/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Bochner.Cumulative

/-!
# Volterra integral equations with separable kernel bounds

Let `I ⊆ ℝ` be an open set — for example any open interval `Ioo a b`, ray `Ioi a` or `Iio b`, or
`univ = ℝ`. Consider the upper-tail Volterra integral equation

  `h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)`   for `x ∈ I`,

where the kernel `K : ℝ → ℝ → 𝕜` and the coefficient `ψ : ℝ → 𝕜` take values in a normed ring `𝕜`
(such as `ℂ`, `ℝ`, or a Banach algebra of matrices or bounded operators), and the forcing `J` and
unknown `h` take values in a Banach space `E` carrying a bounded `𝕜`-module action. Suppose that
`K` is continuous on `{p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2}` with `‖K x v‖ ≤ P x * Q v` for `x < v`
in `I`, where `P, Q ≥ 0`, and that the tail integrals

* `Φ x = ∫ v in I ∩ Ioi x, Q v * ‖J v‖` and
* `Ψ x = ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖`

are finite for every `x ∈ I`. Note that `Φ x` and `Ψ x` may diverge as `x` approaches a lower
endpoint of `I`, and neither `K` nor its bound needs to be defined on the measure-zero diagonal
`{x = v}` for existence, uniqueness, or norm bounds.

Following Olver (Chapter 6, §10), the Picard increments `volterraPicardTerm` satisfy
`‖T_k x‖ ≤ P x * Φ x * (Ψ x) ^ k / k!` by the Fubini tail-power identity
`MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`, without assuming continuity of `Q`.
Summing over `k` produces a continuous solution on `I` bounded by `P x * Φ x * exp (Ψ x)`, unique
among measurable solutions satisfying `h = O(P)` on `I ∩ Ici x` for every `x ∈ I`.

When `P` is a constant `P₀ ≥ 0` and `‖J v‖ ≤ M * ‖ψ v‖` (in particular when `E = 𝕜`, `J = ψ`, and
`M = 1`), the Picard increments telescope one step earlier, giving the sharper bound
`‖h x‖ ≤ M * (exp (P₀ * Φ_ψ x) - 1)`, where `Φ_ψ x = ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖`. Evaluating at
the constant kernel `K x v = P₀` shows that this bound is attained with equality.

Differentiation under the integral sign, derivative error bounds, and `C¹` regularity of solutions
are developed in `TauCeti.Analysis.ODE.Volterra.Deriv`. Together these two files supply the
existence, uniqueness, regularity, and error-bound engine behind the Liouville–Green approximation
and the asymptotic theory of linear differential equations at irregular singularities and large
parameters.

## Main declarations

* `TauCeti.integrableOn_kernel_smul_Ioi_of_le`, `TauCeti.integrableOn_kernel_smul_Ioi`,
  `TauCeti.continuousOn_integral_kernel_smul_Ioi_of_le`,
  `TauCeti.continuousOn_integral_kernel_smul_Ioi`: integrability and continuity of parametric
  upper-tail kernel integrals `x ↦ ∫ v in I ∩ Ioi x, K x v • g v`.
* `TauCeti.volterraPicardTerm`, `TauCeti.continuousOn_volterraPicardTerm`,
  `TauCeti.norm_volterraPicardTerm_le`: the Picard increments on `I` and their factorial estimate
  `P x * Φ x * (Ψ x) ^ k / k!`.
* `TauCeti.exists_volterra_solution_on`, `TauCeti.exists_volterra_solution`,
  `TauCeti.exists_volterra_solution_Ioo`: existence of a continuous solution with
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` on open sets `I`, rays `(a, ∞)`, and bounded `(a, b)`.
* `TauCeti.volterra_solution_unique_on`, `TauCeti.volterra_solution_unique`,
  `TauCeti.volterra_solution_unique_Ioo`: uniqueness among measurable solutions that are `O(P)` on
  each right subinterval `I ∩ Ici x`.
* `TauCeti.norm_volterra_solution_le_on`, `TauCeti.norm_volterra_solution_le`: every such `O(P)`
  solution satisfies the `P Φ exp Ψ` bound.
* `TauCeti.norm_volterra_solution_le_mul_exp_sub_one_on`,
  `TauCeti.norm_volterra_solution_le_exp_sub_one_on`,
  `TauCeti.norm_volterra_solution_le_exp_sub_one`: the sharper `exp (P₀ * Φ_ψ) - 1` bounds for
  constant `P = P₀`, and `TauCeti.volterra_const_kernel_solution_eq_exp_sub_one_on` /
  `TauCeti.volterra_const_kernel_solution_eq_exp_sub_one` witnessing their sharpness.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10, Theorems 10.1 and 10.2.
* NIST Digital Library of Mathematical Functions, §§2.7–2.8, <https://dlmf.nist.gov/2.7> and
  <https://dlmf.nist.gov/2.8>.
-/

public section

noncomputable section

open Filter MeasureTheory Set Asymptotics
open scoped Nat Topology

namespace TauCeti

/-! ### Open intervals and upper-tail parametric kernel integrals -/

/-- Every point `x₀` of an open set `I ⊆ ℝ` lies strictly inside a compact interval
`[c₁, c₂] ⊆ I`. -/
private lemma exists_Icc_subset_of_isOpen {I : Set ℝ} (hI : IsOpen I) {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ c₁ c₂, c₁ ∈ I ∧ c₂ ∈ I ∧ c₁ < x₀ ∧ x₀ < c₂ ∧ Icc c₁ c₂ ⊆ I := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hI x₀ hx₀
  have hsub : Icc (x₀ - ε / 2) (x₀ + ε / 2) ⊆ I := fun u hu => by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  exact ⟨x₀ - ε / 2, x₀ + ε / 2, hsub ⟨le_rfl, by linarith⟩, hsub ⟨by linarith, le_rfl⟩,
    by linarith, by linarith, hsub⟩

section KernelIntegral

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {P Q : ℝ → ℝ}

omit [NormedSpace ℝ E] in
/-- Separable kernel estimate on `x < v`: `‖K x v • y‖ ≤ P x * (Q v * ‖y‖)`. -/
private lemma norm_kernel_smul_le_of_lt (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    {x v : ℝ} (hx : x ∈ I) (hv : v ∈ I) (hxv : x < v) (y : E) :
    ‖K x v • y‖ ≤ P x * (Q v * ‖y‖) := by
  refine (norm_smul_le _ _).trans ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hKle x hx v hv hxv) (norm_nonneg _)

omit [NormedRing 𝕜] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma integrable_indicator_Ioi_restrict {c₁ u : ℝ} {f : ℝ → E}
    (hf : IntegrableOn f (I ∩ Ioi u)) :
    Integrable ((Ioi u).indicator f) (volume.restrict (I ∩ Ioi c₁)) := by
  rw [integrable_indicator_iff measurableSet_Ioi]
  have hsub : Ioi u ∩ (I ∩ Ioi c₁) ⊆ I ∩ Ioi u := fun v hv => ⟨hv.2.1, hv.1⟩
  have hint := hf.mono_set hsub
  rwa [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi]

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma inter_Ioi_inter_Ioi_of_lt {c₁ x : ℝ} (hcx : c₁ < x) :
    (I ∩ Ioi c₁) ∩ Ioi x = I ∩ Ioi x := by
  rw [inter_assoc, Ioi_inter_Ioi, sup_eq_right.mpr hcx.le]

omit [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma integral_indicator_Ioi_restrict {c₁ u : ℝ} (hcu : c₁ < u) (f : ℝ → E) :
    ∫ v, (Ioi u).indicator f v ∂(volume.restrict (I ∩ Ioi c₁)) = ∫ v in I ∩ Ioi u, f v := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_comm (Ioi u), inter_Ioi_inter_Ioi_of_lt hcu]

omit [NormedSpace ℝ E] in
/-- If `K` is continuous on `{p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2}` with `‖K x v‖ ≤ P x * Q v` and
`Q v * ‖g v‖` is majorized on `I ∩ Ioi x` by an integrable function `B`, then `v ↦ K x v • g v`
is integrable on `I ∩ Ioi x` (without requiring measurability of `Q`). -/
theorem integrableOn_kernel_smul_Ioi_of_le (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    {g : ℝ → E} (hg : AEStronglyMeasurable g (volume.restrict I))
    {B : ℝ → ℝ} {x : ℝ} (hx : x ∈ I)
    (hB_le : ∀ v ∈ I, x < v → Q v * ‖g v‖ ≤ B v)
    (hB_int : IntegrableOn B (I ∩ Ioi x)) :
    IntegrableOn (fun v => K x v • g v) (I ∩ Ioi x) := by
  have hKslice : ContinuousOn (fun v => K x v) (I ∩ Ioi x) :=
    hK.comp (continuous_const.prodMk continuous_id).continuousOn fun v hv => ⟨hx, hv.1, hv.2⟩
  have hmeas : AEStronglyMeasurable (fun v => K x v • g v) (volume.restrict (I ∩ Ioi x)) :=
    (hKslice.aestronglyMeasurable (hI.measurableSet.inter measurableSet_Ioi)).smul
      (hg.mono_set inter_subset_left)
  refine (hB_int.const_mul (max (P x) 0)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  calc ‖K x v • g v‖ ≤ P x * (Q v * ‖g v‖) := norm_kernel_smul_le_of_lt hKle hx hv.1 hv.2 (g v)
    _ ≤ max (P x) 0 * (Q v * ‖g v‖) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (hQ0 v hv.1) (norm_nonneg _))
    _ ≤ max (P x) 0 * B v := mul_le_mul_of_nonneg_left (hB_le v hv.1 hv.2) (le_max_right _ _)

omit [NormedSpace ℝ E] in
/-- If `K` is continuous on `{p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2}` with `‖K x v‖ ≤ P x * Q v` and
`Q * ‖g‖` is integrable on `I ∩ Ioi x`, then `v ↦ K x v • g v` is integrable on `I ∩ Ioi x`. -/
theorem integrableOn_kernel_smul_Ioi (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    {g : ℝ → E} (hg : AEStronglyMeasurable g (volume.restrict I))
    {x : ℝ} (hx : x ∈ I) (hg_int : IntegrableOn (fun v => Q v * ‖g v‖) (I ∩ Ioi x)) :
    IntegrableOn (fun v => K x v • g v) (I ∩ Ioi x) := by
  have hKslice : ContinuousOn (fun v => K x v) (I ∩ Ioi x) :=
    hK.comp (continuous_const.prodMk continuous_id).continuousOn
      fun v hv => ⟨hx, hv.1, hv.2⟩
  have hmeas : AEStronglyMeasurable (fun v => K x v • g v) (volume.restrict (I ∩ Ioi x)) :=
    (hKslice.aestronglyMeasurable (hI.measurableSet.inter measurableSet_Ioi)).smul
      (hg.mono_set inter_subset_left)
  refine (hg_int.const_mul (P x)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  exact norm_kernel_smul_le_of_lt hKle hx hv.1 hv.2 (g v)

/-- **Continuity of upper-tail kernel integrals under an integrable majorant.** If `K` is
continuous on `{p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2}` with `‖K x v‖ ≤ P x * Q v` for continuous `P`
and nonnegative `Q`, and `Q v * ‖g v‖ ≤ B v` on `I` with `B` integrable on `I ∩ Ioi x` for every
`x ∈ I`, then `x ↦ ∫ v in I ∩ Ioi x, K x v • g v` is continuous on `I`. -/
theorem continuousOn_integral_kernel_smul_Ioi_of_le (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hP : ContinuousOn P I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    {g : ℝ → E} (hg : AEStronglyMeasurable g (volume.restrict I))
    {B : ℝ → ℝ} (hB_le : ∀ v ∈ I, Q v * ‖g v‖ ≤ B v)
    (hB_int : ∀ x ∈ I, IntegrableOn B (I ∩ Ioi x)) :
    ContinuousOn (fun x => ∫ v in I ∩ Ioi x, K x v • g v) I := by
  intro x₀ hx₀
  obtain ⟨c₁, c₂, hc₁, _, hc₁x₀, hx₀c₂, hIcc⟩ := exists_Icc_subset_of_isOpen hI hx₀
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hIcc)
  set M' : ℝ := max M 0
  set ν : Measure ℝ := volume.restrict (I ∩ Ioi c₁)
  have hImeas : MeasurableSet (I ∩ Ioi c₁) := hI.measurableSet.inter measurableSet_Ioi
  have heq : (fun x => ∫ v in I ∩ Ioi x, K x v • g v) =ᶠ[𝓝 x₀]
      (fun x => ∫ v, (Ioi x).indicator (fun v => K x v • g v) v ∂ν) := by
    filter_upwards [Ioo_mem_nhds hc₁x₀ hx₀c₂] with x hx
    exact (integral_indicator_Ioi_restrict hx.1 _).symm
  refine ContinuousAt.continuousWithinAt <|
    (continuousAt_of_dominated (bound := fun v => M' * B v) ?_ ?_
      ((hB_int c₁ hc₁).const_mul M') ?_).congr heq.symm
  · filter_upwards [Ioo_mem_nhds hc₁x₀ hx₀c₂] with x hx
    have hxI : x ∈ I := hIcc (Ioo_subset_Icc_self hx)
    exact (integrable_indicator_Ioi_restrict (integrableOn_kernel_smul_Ioi_of_le hI hK hQ0 hKle hg
      hxI (fun v hv _ => hB_le v hv) (hB_int x hxI))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds hc₁x₀ hx₀c₂] with x hx
    have hxIcc : x ∈ Icc c₁ c₂ := Ioo_subset_Icc_self hx
    have hPx : P x ≤ M' := (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM x hxIcc).trans
      (le_max_left _ _))
    filter_upwards [ae_restrict_mem hImeas] with v hv
    by_cases hxv : x < v
    · rw [indicator_of_mem hxv]
      exact (norm_kernel_smul_le_of_lt hKle (hIcc hxIcc) hv.1 hxv _).trans <|
        (mul_le_mul_of_nonneg_right hPx (mul_nonneg (hQ0 v hv.1) (norm_nonneg _))).trans
          (mul_le_mul_of_nonneg_left (hB_le v hv.1) (le_max_right _ _))
    · rw [indicator_of_notMem hxv, norm_zero]
      exact mul_nonneg (le_max_right _ _) ((mul_nonneg (hQ0 v hv.1) (norm_nonneg _)).trans
        (hB_le v hv.1))
  · have hne : ∀ᵐ v ∂ν, v ≠ x₀ := by
      simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using measure_singleton (μ := ν) x₀
    filter_upwards [ae_restrict_mem hImeas, hne] with v hv hvne
    rcases lt_or_gt_of_ne hvne with hvx₀ | hx₀v
    · refine (continuousAt_const (y := (0 : E))).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hvx₀] with x hx
      exact indicator_of_notMem (show v ∉ Ioi x from not_lt.mpr (mem_Ioi.mp hx).le) _
    · have hS : {x : ℝ | x ∈ I ∧ x < v} ∈ 𝓝 x₀ :=
        Filter.inter_mem (hI.mem_nhds hx₀) (Iio_mem_nhds hx₀v)
      have hKv : ContinuousOn (fun x => K x v) {x : ℝ | x ∈ I ∧ x < v} :=
        hK.comp (continuous_id.prodMk continuous_const).continuousOn fun x hx => ⟨hx.1, hv.1, hx.2⟩
      refine ((hKv.continuousAt hS).smul (continuousAt_const (y := g v))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hx₀v] with x hx
      exact indicator_of_mem (show v ∈ Ioi x from hx) _

/-- **Continuity of upper-tail kernel integrals.** If `K` is continuous on
`{p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2}` with `‖K x v‖ ≤ P x * Q v` for continuous `P` and
nonnegative `Q`, and `Q * ‖g‖` is integrable on `I ∩ Ioi x` for every `x ∈ I`, then
`x ↦ ∫ v in I ∩ Ioi x, K x v • g v` is continuous on `I`. -/
theorem continuousOn_integral_kernel_smul_Ioi (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hP : ContinuousOn P I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    {g : ℝ → E} (hg : AEStronglyMeasurable g (volume.restrict I))
    (hg_int : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖g v‖) (I ∩ Ioi x)) :
    ContinuousOn (fun x => ∫ v in I ∩ Ioi x, K x v • g v) I :=
  continuousOn_integral_kernel_smul_Ioi_of_le hI hK hP hQ0 hKle hg (fun _ _ => le_rfl) hg_int

end KernelIntegral

/-! ### Picard iteration and general open-interval Volterra equations -/

section OpenInterval

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

/-- The increments of the Picard iteration for the upper-tail Volterra integral equation on `I`:
the `0`-th increment is `∫ v in I ∩ Ioi x, K x v • J v`, and each subsequent increment applies
`u ↦ ∫ v in I ∩ Ioi x, K x v • ψ v • u v`. -/
def volterraPicardTerm (I : Set ℝ) (K : ℝ → ℝ → 𝕜) (J : ℝ → E) (ψ : ℝ → 𝕜) : ℕ → ℝ → E
  | 0, x => ∫ v in I ∩ Ioi x, K x v • J v
  | k + 1, x => ∫ v in I ∩ Ioi x, K x v • ψ v • volterraPicardTerm I K J ψ k v

omit [IsBoundedSMul 𝕜 E] in
/-- The `0`-th Picard increment is the inhomogeneous term `∫ v in I ∩ Ioi x, K x v • J v`. -/
@[simp]
theorem volterraPicardTerm_zero (I : Set ℝ) (K : ℝ → ℝ → 𝕜) (J : ℝ → E) (ψ : ℝ → 𝕜) (x : ℝ) :
    volterraPicardTerm I K J ψ 0 x = ∫ v in I ∩ Ioi x, K x v • J v := (rfl)

omit [IsBoundedSMul 𝕜 E] in
/-- Recurrence step for `volterraPicardTerm` at `k + 1`. -/
@[simp]
theorem volterraPicardTerm_succ (I : Set ℝ) (K : ℝ → ℝ → 𝕜) (J : ℝ → E) (ψ : ℝ → 𝕜)
    (k : ℕ) (x : ℝ) :
    volterraPicardTerm I K J ψ (k + 1) x =
      ∫ v in I ∩ Ioi x, K x v • ψ v • volterraPicardTerm I K J ψ k v := (rfl)

omit [IsBoundedSMul 𝕜 E] in
/-- Every Picard increment vanishes when the Volterra kernel is identically zero. -/
@[simp]
theorem volterraPicardTerm_zero_kernel (I : Set ℝ) (J : ℝ → E) (ψ : ℝ → 𝕜) (k : ℕ) (x : ℝ) :
    volterraPicardTerm I (0 : ℝ → ℝ → 𝕜) J ψ k x = 0 := by
  cases k <;> simp [volterraPicardTerm]

omit [NormedSpace ℝ E] in
private lemma forcing_weight_nonneg_on {J : ℝ → E} (hQ0 : ∀ v ∈ I, 0 ≤ Q v) :
    ∀ v ∈ I, 0 ≤ Q v * ‖J v‖ :=
  fun v hv => mul_nonneg (hQ0 v hv) (norm_nonneg _)

omit [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma coeff_weight_nonneg_on {ψ : ℝ → 𝕜} (hP0 : ∀ x ∈ I, 0 ≤ P x)
    (hQ0 : ∀ v ∈ I, 0 ≤ Q v) : ∀ v ∈ I, 0 ≤ P v * Q v * ‖ψ v‖ :=
  fun v hv => mul_nonneg (mul_nonneg (hP0 v hv) (hQ0 v hv)) (norm_nonneg _)

/-- Monotonicity of a nonnegative upper-tail integral on an open set `I`. -/
private lemma tail_integral_antitone_on (hI : IsOpen I) {w : ℝ → ℝ} (hw0 : ∀ v ∈ I, 0 ≤ w v)
    (hw_int : ∀ x ∈ I, IntegrableOn w (I ∩ Ioi x)) {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ I) (hle : x₁ ≤ x₂) :
    ∫ v in I ∩ Ioi x₂, w v ≤ ∫ v in I ∩ Ioi x₁, w v := by
  refine setIntegral_mono_set (hw_int x₁ hx₁) ?_
    (ae_of_all _ (inter_subset_inter_right _ (Ioi_subset_Ioi hle)))
  filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
  exact hw0 v hv.1

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma restrict_Ioi_eq (I : Set ℝ) (x : ℝ) :
    (volume.restrict I).restrict (Ioi x) = volume.restrict (I ∩ Ioi x) := by
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_comm]

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma integrableOn_mul_pow_tail_on {w : ℝ → ℝ} {x : ℝ}
    (hw : IntegrableOn w (I ∩ Ioi x)) (k : ℕ) :
    IntegrableOn (fun s => w s * (∫ u in I ∩ Ioi s, w u) ^ k) (I ∩ Ioi x) := by
  have hw' : IntegrableOn w (Ioi x) (volume.restrict I) := by
    rwa [IntegrableOn, restrict_Ioi_eq]
  have hint := hw'.integrableOn_mul_pow_integral_Ioi k
  simpa only [IntegrableOn, restrict_Ioi_eq] using hint

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma integral_mul_pow_tail_on {w : ℝ → ℝ} {x : ℝ}
    (hw : IntegrableOn w (I ∩ Ioi x)) (k : ℕ) :
    ∫ s in I ∩ Ioi x, w s * (∫ u in I ∩ Ioi s, w u) ^ k =
      (∫ s in I ∩ Ioi x, w s) ^ (k + 1) / (k + 1) := by
  have hw' : IntegrableOn w (Ioi x) (volume.restrict I) := by
    rwa [IntegrableOn, restrict_Ioi_eq]
  simpa only [restrict_Ioi_eq] using hw'.integral_Ioi_mul_pow_integral_Ioi k

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma integrableOn_sum_mul_pow_tail_on {w : ℝ → ℝ} {x : ℝ}
    (hw : IntegrableOn w (I ∩ Ioi x)) (a : ℕ → ℝ) (m : ℕ) :
    IntegrableOn
      (fun v => ∑ k ∈ Finset.range m, a k * (w v * (∫ u in I ∩ Ioi v, w u) ^ k)) (I ∩ Ioi x) :=
  integrable_finsetSum _ fun k _ => (integrableOn_mul_pow_tail_on hw k).const_mul (a k)

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma integral_sum_mul_pow_tail_on {w : ℝ → ℝ} {x : ℝ}
    (hw : IntegrableOn w (I ∩ Ioi x)) (a : ℕ → ℝ) (m : ℕ) :
    ∫ v in I ∩ Ioi x, (∑ k ∈ Finset.range m, a k * (w v * (∫ u in I ∩ Ioi v, w u) ^ k)) =
      ∑ k ∈ Finset.range m, a k * ((∫ v in I ∩ Ioi x, w v) ^ (k + 1) / (k + 1)) := by
  rw [integral_finsetSum _ fun k _ => (integrableOn_mul_pow_tail_on hw k).const_mul (a k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_mul_pow_tail_on hw k]

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
private lemma mul_integral_mul_exp_tail_on {w : ℝ → ℝ} {x : ℝ}
    (hw : IntegrableOn w (I ∩ Ioi x)) (c : ℝ) :
    c * ∫ s in I ∩ Ioi x, w s * Real.exp (c * ∫ u in I ∩ Ioi s, w u) =
      Real.exp (c * ∫ s in I ∩ Ioi x, w s) - 1 := by
  have hw' : IntegrableOn w (Ioi x) (volume.restrict I) := by
    rwa [IntegrableOn, restrict_Ioi_eq]
  simpa only [restrict_Ioi_eq] using hw'.mul_integral_Ioi_mul_exp_integral_Ioi c

omit [NormedSpace ℝ E] in
/-- One-step factorial estimate for `v ↦ ‖K x v • ψ v • u v‖` on `I ∩ Ioi x`. -/
private lemma integrableOn_and_integral_norm_kernel_smul_smul_le (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {u : ℝ → E} (hu : AEStronglyMeasurable u (volume.restrict I))
    {c : ℝ} {k : ℕ} {x : ℝ} (hx : x ∈ I)
    (hu_le : ∀ v ∈ I, x < v →
      ‖u v‖ ≤ c * P v * (∫ t in I ∩ Ioi v, P t * Q t * ‖ψ t‖) ^ k / k !) :
    IntegrableOn (fun v => K x v • ψ v • u v) (I ∩ Ioi x) ∧
      ∫ v in I ∩ Ioi x, ‖K x v • ψ v • u v‖ ≤
        c * P x * (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ (k + 1) / (k + 1)! := by
  set w : ℝ → ℝ := fun v => P v * Q v * ‖ψ v‖
  set Ψ : ℝ → ℝ := fun v => ∫ t in I ∩ Ioi v, w t
  have hQu_le : ∀ v ∈ I, x < v → Q v * ‖ψ v • u v‖ ≤ c / k ! * (w v * Ψ v ^ k) := by
    intro v hvI hxv
    calc Q v * ‖ψ v • u v‖ ≤ Q v * (‖ψ v‖ * ‖u v‖) :=
          mul_le_mul_of_nonneg_left (norm_smul_le _ _) (hQ0 v hvI)
      _ ≤ Q v * (‖ψ v‖ * (c * P v * Ψ v ^ k / k !)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hu_le v hvI hxv) (norm_nonneg _)) (hQ0 v hvI)
      _ = c / k ! * (w v * Ψ v ^ k) := by simp only [w]; ring
  have hB_int : IntegrableOn (fun v => c / k ! * (w v * Ψ v ^ k)) (I ∩ Ioi x) :=
    (integrableOn_mul_pow_tail_on (hΨ x hx) k).const_mul (c / k !)
  have hint := integrableOn_kernel_smul_Ioi_of_le hI hK hQ0 hKle (hψ.smul hu) hx hQu_le hB_int
  refine ⟨hint, ?_⟩
  have hpt : ∀ᵐ v ∂(volume.restrict (I ∩ Ioi x)),
      ‖K x v • ψ v • u v‖ ≤ P x * (c / k !) * (w v * Ψ v ^ k) := by
    filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
    calc ‖K x v • ψ v • u v‖ ≤ P x * (Q v * ‖ψ v • u v‖) :=
          norm_kernel_smul_le_of_lt hKle hx hv.1 hv.2 _
      _ ≤ P x * (c / k ! * (w v * Ψ v ^ k)) :=
          mul_le_mul_of_nonneg_left (hQu_le v hv.1 hv.2) (hP0 x hx)
      _ = P x * (c / k !) * (w v * Ψ v ^ k) := (mul_assoc _ _ _).symm
  calc ∫ v in I ∩ Ioi x, ‖K x v • ψ v • u v‖
      ≤ ∫ v in I ∩ Ioi x, P x * (c / k !) * (w v * Ψ v ^ k) :=
        integral_mono_ae hint.norm
          ((integrableOn_mul_pow_tail_on (hΨ x hx) k).const_mul _) hpt
    _ = P x * (c / k !) * ∫ v in I ∩ Ioi x, w v * Ψ v ^ k := integral_const_mul _ _
    _ = P x * (c / k !) * (Ψ x ^ (k + 1) / (k + 1)) := by
        rw [integral_mul_pow_tail_on (hΨ x hx) k]
    _ = c * P x * Ψ x ^ (k + 1) / (k + 1)! := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, ← div_div]
        ring

/-- Continuity of the `(k + 1)`-st Picard increment given continuity and factorial bound for `k`. -/
private lemma continuousOn_volterraPicardTerm_succ_of_ih (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP : ContinuousOn P I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {k : ℕ} (hk_cont : ContinuousOn (volterraPicardTerm I K J ψ k) I)
    (hk_le : ∀ x ∈ I, ‖volterraPicardTerm I K J ψ k x‖ ≤
      P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !) :
    ContinuousOn (volterraPicardTerm I K J ψ (k + 1)) I := by
  intro x₀ hx₀
  set w : ℝ → ℝ := fun v => P v * Q v * ‖ψ v‖
  set Φ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, Q v * ‖J v‖
  set Ψ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, w v
  have hΨ_nonneg : ∀ v ∈ I, 0 ≤ Ψ v := fun v _ =>
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi) fun t ht =>
      coeff_weight_nonneg_on hP0 hQ0 t ht.1
  obtain ⟨c₁, _, hc₁, _, hc₁x₀, _, _⟩ := exists_Icc_subset_of_isOpen hI hx₀
  set I₁ : Set ℝ := I ∩ Ioi c₁
  have hI₁ : IsOpen I₁ := hI.inter isOpen_Ioi
  have hB_le : ∀ v ∈ I₁, Q v * ‖ψ v • volterraPicardTerm I K J ψ k v‖ ≤
      Φ c₁ / k ! * (w v * Ψ v ^ k) := fun v hv => by
    have hΦ_le : Φ v ≤ Φ c₁ :=
      tail_integral_antitone_on hI (forcing_weight_nonneg_on hQ0) hΦ hc₁ hv.2.le
    calc Q v * ‖ψ v • volterraPicardTerm I K J ψ k v‖
        ≤ Q v * (‖ψ v‖ * (P v * Φ v * Ψ v ^ k / k !)) :=
          mul_le_mul_of_nonneg_left
            ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hk_le v hv.1) (norm_nonneg _)))
            (hQ0 v hv.1)
      _ ≤ Q v * (‖ψ v‖ * (P v * Φ c₁ * Ψ v ^ k / k !)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΦ_le (hP0 v hv.1))
                (pow_nonneg (hΨ_nonneg v hv.1) k))
              (Nat.cast_nonneg _)) (norm_nonneg _)) (hQ0 v hv.1)
      _ = Φ c₁ / k ! * (w v * Ψ v ^ k) := by simp only [w]; ring
  have hcont_I₁ : ContinuousOn
      (fun x => ∫ v in I₁ ∩ Ioi x, K x v • ψ v • volterraPicardTerm I K J ψ k v) I₁ :=
    continuousOn_integral_kernel_smul_Ioi_of_le hI₁
      (hK.mono fun p hp => ⟨hp.1.1, hp.2.1.1, hp.2.2⟩)
      (hP.mono inter_subset_left) (fun v hv => hQ0 v hv.1)
      (fun x hx v hv hxv => hKle x hx.1 v hv.1 hxv)
      ((hψ.smul (hk_cont.aestronglyMeasurable hI.measurableSet)).mono_set inter_subset_left)
      hB_le fun x hx => by
        rw [inter_Ioi_inter_Ioi_of_lt hx.2]
        exact (integrableOn_mul_pow_tail_on (hΨ x hx.1) k).const_mul (Φ c₁ / k !)
  exact ((hcont_I₁.congr fun x hx => by
    simp only [I₁, volterraPicardTerm_succ, inter_Ioi_inter_Ioi_of_lt hx.2]).continuousAt
      (hI₁.mem_nhds ⟨hx₀, hc₁x₀⟩)).continuousWithinAt

/-- Inductive proof that every Picard increment is continuous on `I` and satisfies the factorial
bound `P x * Φ x * Ψ x ^ k / k!`. -/
private lemma volterraPicardTerm_cont_and_le (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP : ContinuousOn P I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) (k : ℕ) :
    ContinuousOn (volterraPicardTerm I K J ψ k) I ∧
      ∀ x ∈ I, ‖volterraPicardTerm I K J ψ k x‖ ≤
        P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
          (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k ! := by
  induction k with
  | zero =>
    refine ⟨continuousOn_integral_kernel_smul_Ioi hI hK hP hQ0 hKle hJ hΦ, fun x hx => ?_⟩
    simp only [volterraPicardTerm_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
      div_one]
    have hint := integrableOn_kernel_smul_Ioi hI hK hKle hJ hx (hΦ x hx)
    refine norm_integral_le_integral_norm _ |>.trans ?_
    rw [← integral_const_mul]
    refine integral_mono_ae hint.norm ((hΦ x hx).const_mul (P x)) ?_
    filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
    exact norm_kernel_smul_le_of_lt hKle hx hv.1 hv.2 (J v)
  | succ k ih =>
    refine ⟨continuousOn_volterraPicardTerm_succ_of_ih hI hK hψ hP hP0 hQ0 hKle hΦ hΨ ih.1 ih.2,
      fun x hx => ?_⟩
    set Φ : ℝ → ℝ := fun u => ∫ v in I ∩ Ioi u, Q v * ‖J v‖
    set Ψ : ℝ → ℝ := fun u => ∫ v in I ∩ Ioi u, P v * Q v * ‖ψ v‖
    have hΨ0 : ∀ v ∈ I, 0 ≤ Ψ v := fun v _ =>
      setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi) fun t ht =>
        coeff_weight_nonneg_on hP0 hQ0 t ht.1
    have hrec := (integrableOn_and_integral_norm_kernel_smul_smul_le hI hK hψ hP0 hQ0 hKle hΨ
      (ih.1.aestronglyMeasurable hI.measurableSet) (c := Φ x) hx fun v hv hxv => by
        refine (ih.2 v hv).trans ?_
        have hΦ_le : Φ v ≤ Φ x :=
          tail_integral_antitone_on hI (forcing_weight_nonneg_on hQ0) hΦ hx hxv.le
        rw [mul_comm (Φ x) (P v)]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΦ_le (hP0 v hv))
            (pow_nonneg (hΨ0 v hv) k))
          (Nat.cast_nonneg _)).2
    exact (norm_integral_le_integral_norm _).trans (by simpa only [mul_comm (Φ x) (P x)] using hrec)

/-- Every Picard increment `volterraPicardTerm I K J ψ k` is continuous on `I`. -/
theorem continuousOn_volterraPicardTerm (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP : ContinuousOn P I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) (k : ℕ) :
    ContinuousOn (volterraPicardTerm I K J ψ k) I :=
  (volterraPicardTerm_cont_and_le hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ k).1

/-- Factorial bound on the `k`-th Picard increment:
`‖volterraPicardTerm I K J ψ k x‖ ≤ P x * Φ x * Ψ x ^ k / k!`. -/
theorem norm_volterraPicardTerm_le (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP : ContinuousOn P I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    (k : ℕ) {x : ℝ} (hx : x ∈ I) :
    ‖volterraPicardTerm I K J ψ k x‖ ≤
      P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k ! :=
  (volterraPicardTerm_cont_and_le hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ k).2 x hx

omit [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
/-- Any function satisfying the Volterra error bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` on `I`
automatically satisfies the uniqueness growth condition `h =O[𝓟 (I ∩ Ici x)] P` for every
`x ∈ I`. -/
theorem isBigO_of_norm_le_volterra_bound_on (hI : IsOpen I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E}
    (hh_le : ∀ x ∈ I, ‖h x‖ ≤
      P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖))
    {x : ℝ} (hx : x ∈ I) :
    h =O[𝓟 (I ∩ Ici x)] P := by
  set Φx : ℝ := ∫ v in I ∩ Ioi x, Q v * ‖J v‖
  set Ψx : ℝ := ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖
  refine IsBigO.of_bound (Φx * Real.exp Ψx) ?_
  rw [eventually_principal]
  rintro v ⟨hvI, hxv⟩
  have hΦ_le : ∫ t in I ∩ Ioi v, Q t * ‖J t‖ ≤ Φx :=
    tail_integral_antitone_on hI (forcing_weight_nonneg_on hQ0) hΦ hx hxv
  have hΨ_le : ∫ t in I ∩ Ioi v, P t * Q t * ‖ψ t‖ ≤ Ψx :=
    tail_integral_antitone_on hI (coeff_weight_nonneg_on hP0 hQ0) hΨ hx hxv
  have hΦ0 : 0 ≤ ∫ t in I ∩ Ioi v, Q t * ‖J t‖ :=
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi) fun t ht =>
      forcing_weight_nonneg_on hQ0 t ht.1
  calc ‖h v‖ ≤ P v * (∫ t in I ∩ Ioi v, Q t * ‖J t‖) *
        Real.exp (∫ t in I ∩ Ioi v, P t * Q t * ‖ψ t‖) := hh_le v hvI
    _ ≤ P v * Φx * Real.exp Ψx := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hΦ_le (hP0 v hvI))
          (Real.exp_le_exp.mpr hΨ_le) (Real.exp_nonneg _)
          (mul_nonneg (hP0 v hvI) (hΦ0.trans hΦ_le))
    _ = Φx * Real.exp Ψx * ‖P v‖ := by
        rw [Real.norm_of_nonneg (hP0 v hvI)]
        ring

omit [NormedSpace ℝ E] in
/-- If `h` is measurable on `I` and `h =O[𝓟 (I ∩ Ici x)] P`, then the full Volterra integrand
`v ↦ K x v • (J v + ψ v • h v)` is integrable on `I ∩ Ioi x`. -/
theorem integrableOn_volterra_of_isBigO_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    {x : ℝ} (hx : x ∈ I) (hhO : h =O[𝓟 (I ∩ Ici x)] P) :
    IntegrableOn (fun v => K x v • (J v + ψ v • h v)) (I ∩ Ioi x) := by
  obtain ⟨c, hc⟩ := hhO.bound
  rw [eventually_principal] at hc
  set C : ℝ := max c 0
  refine integrableOn_kernel_smul_Ioi_of_le hI hK hQ0 hKle (hJ.add (hψ.smul hh)) hx
    (B := fun v => Q v * ‖J v‖ + C * (P v * Q v * ‖ψ v‖)) (fun v hv hxv => ?_)
    ((hΦ x hx).add ((hΨ x hx).const_mul C))
  have hhv : ‖h v‖ ≤ C * P v :=
    (hc v ⟨hv, hxv.le⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      |>.trans_eq (by rw [Real.norm_of_nonneg (hP0 v hv)])
  calc Q v * ‖J v + ψ v • h v‖
      ≤ Q v * (‖J v‖ + ‖ψ v‖ * ‖h v‖) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
          (add_le_add_right (norm_smul_le _ _) _)) (hQ0 v hv)
    _ ≤ Q v * (‖J v‖ + ‖ψ v‖ * (C * P v)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_mul_of_nonneg_left hhv (norm_nonneg _)) _) (hQ0 v hv)
    _ = Q v * ‖J v‖ + C * (P v * Q v * ‖ψ v‖) := by ring

omit [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] in
/-- Helper identity `∑' k, a * (b ^ k / k!) = a * Real.exp b`. -/
private lemma tsum_mul_pow_div_factorial (a b : ℝ) :
    (∑' k : ℕ, a * b ^ k / k !) = a * Real.exp b := by
  have heq : (fun k : ℕ => a * b ^ k / k !) = fun k : ℕ => a * (b ^ k / k !) :=
    funext fun _ => mul_div_assoc _ _ _
  rw [heq, tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Locally uniform Weierstrass M-test continuity of the Picard series on `I`. -/
private lemma continuousOn_tsum_volterraPicardTerm [CompleteSpace E] (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP : ContinuousOn P I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) :
    ContinuousOn (fun x => ∑' k, volterraPicardTerm I K J ψ k x) I := by
  intro x₀ hx₀
  set Φ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, Q v * ‖J v‖
  set Ψ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖
  have hΦ0 : ∀ x ∈ I, 0 ≤ Φ x := fun x _ =>
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi) fun v hv =>
      forcing_weight_nonneg_on hQ0 v hv.1
  have hΨ0 : ∀ x ∈ I, 0 ≤ Ψ x := fun x _ =>
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi) fun v hv =>
      coeff_weight_nonneg_on hP0 hQ0 v hv.1
  obtain ⟨c₁, c₂, hc₁, _, hc₁x₀, hx₀c₂, hIcc⟩ := exists_Icc_subset_of_isOpen hI hx₀
  obtain ⟨MP, hMP⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hIcc)
  set MP' : ℝ := max MP 0
  have hmaj_sum : Summable (fun k : ℕ => MP' * Φ c₁ * Ψ c₁ ^ k / k !) := by
    simpa only [mul_div_assoc] using (Real.summable_pow_div_factorial (Ψ c₁)).mul_left (MP' * Φ c₁)
  have hcont_Ioo : ContinuousOn (fun x => ∑' k, volterraPicardTerm I K J ψ k x) (Ioo c₁ c₂) :=
    continuousOn_tsum
      (fun k => (continuousOn_volterraPicardTerm hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ k).mono
        (Ioo_subset_Icc_self.trans hIcc))
      hmaj_sum fun k x hx => by
        have hxIcc := Ioo_subset_Icc_self hx
        have hxI := hIcc hxIcc
        have hPx : P x ≤ MP' := (le_abs_self _).trans
          ((Real.norm_eq_abs _ ▸ hMP x hxIcc).trans (le_max_left _ _))
        have hΦx := tail_integral_antitone_on hI (forcing_weight_nonneg_on hQ0) hΦ hc₁ hx.1.le
        have hΨx := tail_integral_antitone_on hI (coeff_weight_nonneg_on hP0 hQ0) hΨ hc₁ hx.1.le
        refine (norm_volterraPicardTerm_le hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ k hxI).trans
          (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
        exact mul_le_mul (mul_le_mul hPx hΦx (hΦ0 x hxI) (le_max_right _ _))
          (pow_le_pow_left₀ (hΨ0 x hxI) hΨx k) (pow_nonneg (hΨ0 x hxI) k)
          (mul_nonneg (le_max_right _ _) (hΦ0 c₁ hc₁))
  exact (hcont_Ioo.continuousAt (Ioo_mem_nhds hc₁x₀ hx₀c₂)).continuousWithinAt

omit [NormedSpace ℝ E] in
private lemma integrableOn_kernel_smul_smul_of_isBigO_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    {x : ℝ} (hx : x ∈ I) (hhO : h =O[𝓟 (I ∩ Ici x)] P) :
    IntegrableOn (fun v => K x v • ψ v • h v) (I ∩ Ioi x) :=
  ((integrableOn_volterra_of_isBigO_on hI hK hJ hψ hP0 hQ0 hKle hΦ hΨ hh hx hhO).sub
    (integrableOn_kernel_smul_Ioi hI hK hKle hJ hx (hΦ x hx))).congr_fun
    (fun _ _ => by simp only [Pi.sub_apply, smul_add, add_sub_cancel_left])
    (hI.measurableSet.inter measurableSet_Ioi)

private lemma tsum_succ_volterraPicardTerm_eq_integral (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP : ContinuousOn P I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    (hT_sum : ∀ v ∈ I, Summable (fun k => volterraPicardTerm I K J ψ k v))
    {x : ℝ} (hx : x ∈ I) :
    (∑' k, volterraPicardTerm I K J ψ (k + 1) x) =
      ∫ v in I ∩ Ioi x, K x v • ψ v • (∑' k, volterraPicardTerm I K J ψ k v) := by
  set T : ℕ → ℝ → E := volterraPicardTerm I K J ψ
  set Φx : ℝ := ∫ v in I ∩ Ioi x, Q v * ‖J v‖
  set Ψ : ℝ → ℝ := fun u => ∫ v in I ∩ Ioi u, P v * Q v * ‖ψ v‖
  have hΨ0 : ∀ v ∈ I, 0 ≤ Ψ v := fun v _ =>
    setIntegral_nonneg (hI.measurableSet.inter measurableSet_Ioi) fun t ht =>
      coeff_weight_nonneg_on hP0 hQ0 t ht.1
  have hstep : ∀ k, IntegrableOn (fun v => K x v • ψ v • T k v) (I ∩ Ioi x) ∧
      ∫ v in I ∩ Ioi x, ‖K x v • ψ v • T k v‖ ≤
        P x * Φx * Ψ x ^ (k + 1) / (k + 1)! := fun k => by
    have hr := integrableOn_and_integral_norm_kernel_smul_smul_le hI hK hψ hP0 hQ0 hKle hΨ
      ((continuousOn_volterraPicardTerm hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ k).aestronglyMeasurable
        hI.measurableSet) (c := Φx) hx fun v hv hxv => by
        refine (norm_volterraPicardTerm_le hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ k hv).trans ?_
        have hΦ_le := tail_integral_antitone_on hI (forcing_weight_nonneg_on hQ0) hΦ hx hxv.le
        rw [mul_comm Φx (P v)]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΦ_le (hP0 v hv))
            (pow_nonneg (hΨ0 v hv) k))
          (Nat.cast_nonneg _)
    exact ⟨hr.1, by simpa only [mul_comm Φx (P x)] using hr.2⟩
  have hmaj : Summable (fun k : ℕ => P x * Φx * Ψ x ^ k / k !) := by
    simpa only [mul_div_assoc] using (Real.summable_pow_div_factorial (Ψ x)).mul_left (P x * Φx)
  have hswap := integral_tsum_of_summable_integral_norm (fun k => (hstep k).1) <|
    .of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun k => (hstep k).2)
      ((summable_nat_add_iff 1).mpr hmaj)
  dsimp only [T] at hswap ⊢
  rw [tsum_congr fun k => volterraPicardTerm_succ I K J ψ k x, hswap]
  exact setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi) fun v hv => by
    rw [((hT_sum v hv.1).const_smul (ψ v)).tsum_const_smul (K x v),
      (hT_sum v hv.1).tsum_const_smul (ψ v)]

/-- **Existence and error bound for Volterra integral equations on open intervals (Olver,
Theorem 10.1).** On any open set `I ⊆ ℝ`, under the separable kernel bound `‖K x v‖ ≤ P x * Q v`
with continuous `P ≥ 0` and finite upper-tail integrals `Φ x` and `Ψ x`, the Picard series defines
a continuous solution `h` of `h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)` satisfying
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for all `x ∈ I`. -/
theorem exists_volterra_solution_on [CompleteSpace E] (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP : ContinuousOn P I) (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) :
    ∃ h : ℝ → E,
      ContinuousOn h I ∧
      (∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)) ∧
      (∀ x ∈ I, ‖h x‖ ≤
        P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
          Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖)) := by
  set T : ℕ → ℝ → E := volterraPicardTerm I K J ψ
  set Φ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, Q v * ‖J v‖
  set Ψ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖
  set h : ℝ → E := fun x => ∑' k, T k x
  have hT_le : ∀ k, ∀ x ∈ I, ‖T k x‖ ≤ P x * Φ x * Ψ x ^ k / k ! :=
    fun k _ hx => norm_volterraPicardTerm_le hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ k hx
  have hmaj_sum : ∀ a b : ℝ, Summable (fun k : ℕ => a * b ^ k / k !) := fun a b => by
    simpa only [mul_div_assoc] using (Real.summable_pow_div_factorial b).mul_left a
  have hT_norm_sum : ∀ x ∈ I, Summable (fun k => ‖T k x‖) := fun x hx =>
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hT_le k x hx) (hmaj_sum (P x * Φ x) (Ψ x))
  have hT_sum : ∀ x ∈ I, Summable (fun k => T k x) := fun x hx => (hT_norm_sum x hx).of_norm
  have hh_cont : ContinuousOn h I :=
    continuousOn_tsum_volterraPicardTerm hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ
  have hh_le : ∀ x ∈ I, ‖h x‖ ≤ P x * Φ x * Real.exp (Ψ x) := fun x hx => by
    refine (norm_tsum_le_tsum_norm (hT_norm_sum x hx)).trans ?_
    rw [← tsum_mul_pow_div_factorial]
    exact (hT_norm_sum x hx).tsum_le_tsum (fun k => hT_le k x hx) (hmaj_sum _ _)
  refine ⟨h, hh_cont, fun x hx => ?_, hh_le⟩
  have hint_J := integrableOn_kernel_smul_Ioi hI hK hKle hJ hx (hΦ x hx)
  have hint_h := integrableOn_kernel_smul_smul_of_isBigO_on hI hK hJ hψ hP0 hQ0 hKle hΦ hΨ
    (hh_cont.aestronglyMeasurable hI.measurableSet) hx
    (isBigO_of_norm_le_volterra_bound_on hI hP0 hQ0 hΦ hΨ hh_le hx)
  calc h x = T 0 x + ∑' k, T (k + 1) x := (hT_sum x hx).tsum_eq_zero_add
    _ = (∫ v in I ∩ Ioi x, K x v • J v) + ∫ v in I ∩ Ioi x, K x v • ψ v • h v := by
        dsimp only [T, h]
        rw [volterraPicardTerm_zero,
          tsum_succ_volterraPicardTerm_eq_integral hI hK hJ hψ hP hP0 hQ0 hKle hΦ hΨ hT_sum hx]
    _ = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v) := by
        rw [← integral_add hint_J hint_h]
        exact setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi)
          fun v _ => (smul_add _ _ _).symm

private lemma norm_integral_kernel_smul_le_of_le (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) (hx₀x : x₀ ≤ x) :
    ‖∫ v in I ∩ Ioi x, K x v • J v‖ ≤ P x * ∫ v in I ∩ Ioi x₀, Q v * ‖J v‖ := by
  have hint_J := integrableOn_kernel_smul_Ioi hI hK hKle hJ hx (hΦ x hx)
  refine (norm_integral_le_integral_norm _).trans <|
    (integral_mono_ae hint_J.norm ((hΦ x hx).const_mul (P x)) ?_).trans ?_
  · filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
    exact norm_kernel_smul_le_of_lt hKle hx hv.1 hv.2 (J v)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (tail_integral_antitone_on hI (forcing_weight_nonneg_on hQ0) hΦ hx₀ hx₀x) (hP0 x hx)

/-- Finite-step Grönwall-by-iteration bound on `I ∩ Ici x₀` for any `O(P)` Volterra solution. -/
private lemma norm_volterra_iter_le_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] P)
    {x₀ C : ℝ} (hx₀ : x₀ ∈ I) (hC : ∀ v ∈ I, x₀ ≤ v → ‖h v‖ ≤ C * P v) (n : ℕ) :
    ∀ x ∈ I, x₀ ≤ x →
      ‖h x‖ ≤ P x * (∫ v in I ∩ Ioi x₀, Q v * ‖J v‖) *
          (∑ k ∈ Finset.range n, (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !) +
        C * P x * (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) ^ n / n ! := by
  set Φ₀ : ℝ := ∫ v in I ∩ Ioi x₀, Q v * ‖J v‖
  set w : ℝ → ℝ := fun v => P v * Q v * ‖ψ v‖
  set Ψ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, w v
  induction n with
  | zero =>
    intro x hx hx₀x
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one, div_one] using hC x hx hx₀x
  | succ n ih =>
    intro x hx hx₀x
    have hint_J := integrableOn_kernel_smul_Ioi hI hK hKle hJ hx (hΦ x hx)
    have hint_h := integrableOn_kernel_smul_smul_of_isBigO_on hI hK hJ hψ hP0 hQ0 hKle hΦ hΨ hh hx
      (hhO x hx)
    set g : ℝ → ℝ := fun v =>
      (∑ k ∈ Finset.range n, P x * Φ₀ / k ! * (w v * Ψ v ^ k)) + C * P x / n ! * (w v * Ψ v ^ n)
    have hg_int : IntegrableOn g (I ∩ Ioi x) :=
      (integrableOn_sum_mul_pow_tail_on (hΨ x hx) (fun k => P x * Φ₀ / k !) n).add
        ((integrableOn_mul_pow_tail_on (hΨ x hx) n).const_mul _)
    have hpt : ∀ᵐ v ∂(volume.restrict (I ∩ Ioi x)), ‖K x v • ψ v • h v‖ ≤ g v := by
      filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
      calc ‖K x v • ψ v • h v‖
          ≤ P x * (Q v * (‖ψ v‖ * (P v * Φ₀ * (∑ k ∈ Finset.range n, Ψ v ^ k / k !) +
              C * P v * Ψ v ^ n / n !))) :=
            (norm_kernel_smul_le_of_lt hKle hx hv.1 hv.2 _).trans <|
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
                  (ih v hv.1 (hx₀x.trans hv.2.le)) (norm_nonneg _)))
                (hQ0 v hv.1)) (hP0 x hx)
        _ = g v := by
            simp only [g, w, mul_add, Finset.mul_sum]
            exact congrArg₂ _ (Finset.sum_congr rfl fun _ _ => by ring) (by ring)
    have hg_val : ∫ v in I ∩ Ioi x, g v =
        P x * Φ₀ * (∑ k ∈ Finset.range n, Ψ x ^ (k + 1) / (k + 1)!) +
          C * P x * Ψ x ^ (n + 1) / (n + 1)! := by
      simp only [g]
      rw [integral_add (integrableOn_sum_mul_pow_tail_on (hΨ x hx) _ n)
          ((integrableOn_mul_pow_tail_on (hΨ x hx) n).const_mul _),
        integral_sum_mul_pow_tail_on (hΨ x hx) _ n, integral_const_mul,
        integral_mul_pow_tail_on (hΨ x hx) n, Finset.mul_sum]
      refine congrArg₂ _ (Finset.sum_congr rfl fun k _ => ?_) ?_ <;>
        (rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, ← div_div]; ring)
    have hsplit : h x = (∫ v in I ∩ Ioi x, K x v • J v) + ∫ v in I ∩ Ioi x, K x v • ψ v • h v := by
      rw [hh_eq x hx, ← integral_add hint_J hint_h]
      exact setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi) fun v _ =>
        smul_add _ _ _
    calc ‖h x‖ ≤ ‖∫ v in I ∩ Ioi x, K x v • J v‖ + ‖∫ v in I ∩ Ioi x, K x v • ψ v • h v‖ :=
          hsplit ▸ norm_add_le _ _
      _ ≤ P x * Φ₀ + ∫ v in I ∩ Ioi x, g v :=
          add_le_add (norm_integral_kernel_smul_le_of_le hI hK hJ hP0 hQ0 hKle hΦ hx₀ hx hx₀x)
            ((norm_integral_le_integral_norm _).trans (integral_mono_ae hint_h.norm hg_int hpt))
      _ = P x * Φ₀ * (∑ k ∈ Finset.range (n + 1), Ψ x ^ k / k !) +
            C * P x * Ψ x ^ (n + 1) / (n + 1)! := by
          rw [hg_val, Finset.sum_range_succ']
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]; ring

/-- **A priori error bound for any `O(P)` Volterra solution.** Every measurable solution `h` of
`h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)` on `I` satisfying
`∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] P` satisfies `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` on `I`, without
requiring `ContinuousOn P I` or `CompleteSpace E`. -/
theorem norm_volterra_solution_le_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] P)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ‖h x₀‖ ≤
      P x₀ * (∫ v in I ∩ Ioi x₀, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x₀, P v * Q v * ‖ψ v‖) := by
  set Φ₀ : ℝ := ∫ v in I ∩ Ioi x₀, Q v * ‖J v‖
  set Ψ₀ : ℝ := ∫ v in I ∩ Ioi x₀, P v * Q v * ‖ψ v‖
  obtain ⟨c, hc⟩ := (hhO x₀ hx₀).bound
  rw [eventually_principal] at hc
  set C : ℝ := max c 0
  have hC : ∀ v ∈ I, x₀ ≤ v → ‖h v‖ ≤ C * P v := fun v hv hxv =>
    (hc v ⟨hv, hxv⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      |>.trans_eq (by rw [Real.norm_of_nonneg (hP0 v hv)])
  have hexp_sum : HasSum (fun k : ℕ => Ψ₀ ^ k / k !) (Real.exp Ψ₀) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (Real.summable_pow_div_factorial Ψ₀).hasSum
  have htend : Tendsto
      (fun n : ℕ => P x₀ * Φ₀ * (∑ k ∈ Finset.range n, Ψ₀ ^ k / k !) +
        C * P x₀ * Ψ₀ ^ n / n !)
      atTop (𝓝 (P x₀ * Φ₀ * Real.exp Ψ₀ + C * P x₀ * 0)) := by
    refine Tendsto.add (hexp_sum.tendsto_sum_nat.const_mul (P x₀ * Φ₀)) ?_
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial Ψ₀).tendsto_atTop_zero.const_mul (C * P x₀)
  rw [mul_zero, add_zero] at htend
  exact ge_of_tendsto htend (Eventually.of_forall fun n =>
    norm_volterra_iter_le_on hI hK hJ hψ hP0 hQ0 hKle hΦ hΨ hh hh_eq hhO hx₀ hC n x₀ hx₀ le_rfl)

/-- **Uniqueness of `O(P)` Volterra solutions on open intervals (Olver, Theorem 10.1).** Any two
measurable solutions of `h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)` on `I` satisfying
`∀ x ∈ I, hᵢ =O[𝓟 (I ∩ Ici x)] P` coincide everywhere on `I`. -/
theorem volterra_solution_unique_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h₁ h₂ : ℝ → E}
    (hh₁ : AEStronglyMeasurable h₁ (volume.restrict I))
    (hh₂ : AEStronglyMeasurable h₂ (volume.restrict I))
    (hh₁_eq : ∀ x ∈ I, h₁ x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h₁ v))
    (hh₂_eq : ∀ x ∈ I, h₂ x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h₂ v))
    (hh₁O : ∀ x ∈ I, h₁ =O[𝓟 (I ∩ Ici x)] P)
    (hh₂O : ∀ x ∈ I, h₂ =O[𝓟 (I ∩ Ici x)] P) :
    EqOn h₁ h₂ I := by
  intro x₀ hx₀
  have hd_eq : ∀ x ∈ I, (h₁ - h₂) x =
      ∫ v in I ∩ Ioi x, K x v • ((0 : ℝ → E) v + ψ v • (h₁ - h₂) v) := by
    intro x hx
    have hi₁ := integrableOn_volterra_of_isBigO_on hI hK hJ hψ hP0 hQ0 hKle hΦ hΨ hh₁ hx (hh₁O x hx)
    have hi₂ := integrableOn_volterra_of_isBigO_on hI hK hJ hψ hP0 hQ0 hKle hΦ hΨ hh₂ hx (hh₂O x hx)
    simp only [Pi.sub_apply, Pi.zero_apply, zero_add]
    rw [hh₁_eq x hx, hh₂_eq x hx, ← integral_sub hi₁ hi₂]
    exact setIntegral_congr_fun (hI.measurableSet.inter measurableSet_Ioi) fun v _ => by
      rw [← smul_sub, add_sub_add_left_eq_sub, ← smul_sub]
  have hd_le := norm_volterra_solution_le_on hI hK aestronglyMeasurable_zero hψ hP0 hQ0 hKle
    (fun _ _ => by simp) hΨ (hh₁.sub hh₂) hd_eq (fun x hx => (hh₁O x hx).sub (hh₂O x hx)) hx₀
  simp only [Pi.sub_apply, Pi.zero_apply, norm_zero, mul_zero, integral_zero, zero_mul] at hd_le
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hd_le)

omit [IsBoundedSMul 𝕜 E] in
/-- When the kernel is identically zero, every solution of the Volterra integral equation on `I`
vanishes on `I`. -/
theorem eqOn_zero_of_volterra_zero_kernel {h : ℝ → E}
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, (0 : 𝕜) • (J v + ψ v • h v)) :
    EqOn h 0 I := fun x hx => by
  simpa using hh_eq x hx

end OpenInterval


/-! ### Sharper `exp (P₀ * Φ) - 1` bounds when `P` is constant (Olver, Theorem 10.2) -/

section NormBound

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {Q : ℝ → ℝ}

omit [NormedSpace ℝ E] in
private lemma mul_norm_rhs_le_of_le_mul_norm {M C : ℝ} {v : ℝ} (hQv : 0 ≤ Q v)
    (hJψ : ‖J v‖ ≤ M * ‖ψ v‖) {h : ℝ → E} (hhv : ‖h v‖ ≤ C) :
    Q v * ‖J v + ψ v • h v‖ ≤ (|M| + max C 0) * (Q v * ‖ψ v‖) := by
  have hhv' : ‖h v‖ ≤ max C 0 := hhv.trans (le_max_left _ _)
  calc Q v * ‖J v + ψ v • h v‖
      ≤ Q v * (|M| * ‖ψ v‖ + ‖ψ v‖ * max C 0) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
          (hJψ.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)))
          ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hhv' (norm_nonneg _))))) hQv
    _ = (|M| + max C 0) * (Q v * ‖ψ v‖) := by ring

/-- Finite-step iteration bound for constant `P = P₀` and `‖J v‖ ≤ M * ‖ψ v‖`. -/
private lemma norm_volterra_const_iter_le_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    {P₀ M : ℝ} (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hJψ : ∀ v ∈ I, ‖J v‖ ≤ M * ‖ψ v‖)
    (hΦψ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    {x₀ C : ℝ} (hC : ∀ v ∈ I, x₀ ≤ v → ‖h v‖ ≤ C) (n : ℕ) :
    ∀ x ∈ I, x₀ ≤ x →
      ‖h x‖ ≤
        M * (∑ k ∈ Finset.range n, (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖) ^ (k + 1) / (k + 1)!) +
          C * (P₀ * ∫ v in I ∩ Ioi x, Q v * ‖ψ v‖) ^ n / n ! := by
  set w : ℝ → ℝ := fun v => Q v * ‖ψ v‖
  set Φ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, w v
  induction n with
  | zero =>
    intro x hx hx₀x
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one, div_one] using hC x hx hx₀x
  | succ n ih =>
    intro x hx hx₀x
    have hint := integrableOn_kernel_smul_Ioi_of_le hI hK hQ0 hKle (hJ.add (hψ.smul hh)) hx
      (fun v hv hxv =>
        mul_norm_rhs_le_of_le_mul_norm (hQ0 v hv) (hJψ v hv) (hC v hv (hx₀x.trans hxv.le)))
      ((hΦψ x hx).const_mul _)
    set a : ℕ → ℝ := fun k => M * P₀ ^ (k + 1) / (k !)
    set g : ℝ → ℝ := fun v =>
      (∑ k ∈ Finset.range (n + 1), a k * (w v * Φ v ^ k)) + C * P₀ ^ (n + 1) / n ! * (w v * Φ v ^ n)
    have hg_int : IntegrableOn g (I ∩ Ioi x) :=
      (integrableOn_sum_mul_pow_tail_on (hΦψ x hx) a (n + 1)).add
        ((integrableOn_mul_pow_tail_on (hΦψ x hx) n).const_mul _)
    have hpt : ∀ᵐ v ∂(volume.restrict (I ∩ Ioi x)), ‖K x v • (J v + ψ v • h v)‖ ≤ g v := by
      filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
      have hsum_shift : M + M * (∑ k ∈ Finset.range n, (P₀ * Φ v) ^ (k + 1) / (k + 1)!) =
          M * (∑ k ∈ Finset.range (n + 1), (P₀ * Φ v) ^ k / k !) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]; ring
      calc ‖K x v • (J v + ψ v • h v)‖
          ≤ P₀ * (Q v * (M * ‖ψ v‖ + ‖ψ v‖ *
              (M * (∑ k ∈ Finset.range n, (P₀ * Φ v) ^ (k + 1) / (k + 1)!) +
                C * (P₀ * Φ v) ^ n / n !))) :=
            (norm_kernel_smul_le_of_lt hKle hx hv.1 hv.2 _).trans <|
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                ((norm_add_le _ _).trans (add_le_add (hJψ v hv.1)
                  ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
                    (ih v hv.1 (hx₀x.trans hv.2.le)) (norm_nonneg _)))))
                (hQ0 v hv.1)) hP₀
        _ = g v := by
            have hlhs : P₀ * (Q v * (M * ‖ψ v‖ + ‖ψ v‖ *
                (M * (∑ k ∈ Finset.range n, (P₀ * Φ v) ^ (k + 1) / (k + 1)!) +
                  C * (P₀ * Φ v) ^ n / n !))) =
                P₀ * w v * (M + M * (∑ k ∈ Finset.range n, (P₀ * Φ v) ^ (k + 1) / (k + 1)!) +
                  C * (P₀ * Φ v) ^ n / n !) := by simp only [w]; ring
            rw [hlhs, hsum_shift]
            simp only [g, a, mul_add, Finset.mul_sum, mul_pow]
            exact congrArg₂ _ (Finset.sum_congr rfl fun _ _ => by ring) (by ring)
    rw [hh_eq x hx]
    refine (norm_integral_le_integral_norm _).trans
      ((integral_mono_ae hint.norm hg_int hpt).trans (le_of_eq ?_))
    simp only [g]
    rw [integral_add (integrableOn_sum_mul_pow_tail_on (hΦψ x hx) a (n + 1))
        ((integrableOn_mul_pow_tail_on (hΦψ x hx) n).const_mul _),
      integral_sum_mul_pow_tail_on (hΦψ x hx) a (n + 1), integral_const_mul,
      integral_mul_pow_tail_on (hΦψ x hx) n, Finset.mul_sum]
    refine congrArg₂ _ (Finset.sum_congr rfl fun k _ => ?_) ?_ <;>
      (simp only [a, mul_pow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, ← div_div]; ring)

/-- **Sharper `exp (P₀ * Φ_ψ) - 1` bound for constant `P = P₀` (Olver, Theorem 10.2).** When
`‖K x v‖ ≤ P₀ * Q v` with `0 ≤ P₀` and `‖J v‖ ≤ M * ‖ψ v‖`, every measurable solution `h` that is
bounded on `I ∩ Ici x` for each `x ∈ I` satisfies
`‖h x₀‖ ≤ M * (exp (P₀ * ∫ v in I ∩ Ioi x₀, Q v * ‖ψ v‖) - 1)`. -/
theorem norm_volterra_solution_le_mul_exp_sub_one_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    {P₀ M : ℝ} (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hJψ : ∀ v ∈ I, ‖J v‖ ≤ M * ‖ψ v‖)
    (hΦψ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] (fun _ => (1 : ℝ)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ‖h x₀‖ ≤ M * (Real.exp (P₀ * ∫ v in I ∩ Ioi x₀, Q v * ‖ψ v‖) - 1) := by
  set u₀ : ℝ := P₀ * ∫ v in I ∩ Ioi x₀, Q v * ‖ψ v‖
  obtain ⟨c, hc⟩ := (hhO x₀ hx₀).bound
  rw [eventually_principal] at hc
  have hC : ∀ v ∈ I, x₀ ≤ v → ‖h v‖ ≤ c := fun v hv hxv => by simpa using hc v ⟨hv, hxv⟩
  have hexp_sum : HasSum (fun k : ℕ => u₀ ^ k / k !) (Real.exp u₀) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (Real.summable_pow_div_factorial u₀).hasSum
  have hshift_tend : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, u₀ ^ (k + 1) / (k + 1)!)
      atTop (𝓝 (Real.exp u₀ - 1)) := by
    have hsub := (hexp_sum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub_const 1
    refine hsub.congr fun n => ?_
    simp only [Function.comp_apply, Finset.sum_range_succ', pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, add_sub_cancel_right]
  have htend : Tendsto
      (fun n : ℕ => M * (∑ k ∈ Finset.range n, u₀ ^ (k + 1) / (k + 1)!) + c * u₀ ^ n / n !)
      atTop (𝓝 (M * (Real.exp u₀ - 1) + c * 0)) := by
    refine Tendsto.add (hshift_tend.const_mul M) ?_
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial u₀).tendsto_atTop_zero.const_mul c
  rw [mul_zero, add_zero] at htend
  exact ge_of_tendsto htend (Eventually.of_forall fun n =>
    norm_volterra_const_iter_le_on hI hK hJ hψ hP₀ hQ0 hKle hJψ hΦψ hh hh_eq hC n x₀ hx₀ le_rfl)

/-- Scalar/algebra specialization (`J = ψ`, `M = 1`) of
`norm_volterra_solution_le_mul_exp_sub_one_on`: `‖h x₀‖ ≤ exp (P₀ * Φ_ψ x₀) - 1`. -/
theorem norm_volterra_solution_le_exp_sub_one_on {𝕜 : Type*} [NormedRing 𝕜] [NormedSpace ℝ 𝕜]
    {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {ψ : ℝ → 𝕜} {Q : ℝ → ℝ} (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    {P₀ : ℝ} (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hΦψ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → 𝕜} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v * (ψ v + ψ v * h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] (fun _ => (1 : ℝ)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ‖h x₀‖ ≤ Real.exp (P₀ * ∫ v in I ∩ Ioi x₀, Q v * ‖ψ v‖) - 1 := by
  simpa only [one_mul] using norm_volterra_solution_le_mul_exp_sub_one_on (E := 𝕜) hI hK hψ hψ hP₀
    hQ0 hKle (M := 1) (fun v _ => by rw [one_mul]) hΦψ hh hh_eq hhO hx₀

end NormBound


/-! ### Specializations to rays `(a, ∞)` and bounded intervals `(a, b)`, and sharpness -/

section Specializations

private lemma Ioi_inter_Ioi_of_le {a x : ℝ} (hax : a ≤ x) : Ioi a ∩ Ioi x = Ioi x := by
  rw [Ioi_inter_Ioi, sup_eq_right.mpr hax]

private lemma Ioi_inter_Ici_of_lt {a x : ℝ} (hax : a < x) : Ioi a ∩ Ici x = Ici x :=
  inter_eq_right.mpr fun _ hv => hax.trans_le hv

private lemma Ioo_inter_Ioi_of_mem {a b x : ℝ} (hx : x ∈ Ioo a b) : Ioo a b ∩ Ioi x = Ioo x b := by
  rw [Ioo_inter_Ioi, max_eq_right hx.1.le]

private lemma Ioo_inter_Ici_of_mem {a b x : ℝ} (hx : x ∈ Ioo a b) : Ioo a b ∩ Ici x = Ico x b := by
  ext v
  simp only [mem_inter_iff, mem_Ioo, mem_Ici, mem_Ico]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hx.1.trans_le h.1, h.2⟩, h.1⟩⟩

/-- On `(a, ∞)`, an asymptotic bound `h =O[atTop] P` together with continuity of `h` and strict
positivity and continuity of `P` implies `h =O[𝓟 (Ici x)] P` for every `x > a`. -/
theorem isBigO_Ici_of_continuousOn_of_isBigO_atTop {E : Type*} [NormedAddCommGroup E]
    {a : ℝ} {h : ℝ → E} {P : ℝ → ℝ}
    (hh : ContinuousOn h (Ioi a)) (hP : ContinuousOn P (Ioi a))
    (hP_pos : ∀ x > a, 0 < P x) (hhO : h =O[atTop] P) {x : ℝ} (hx : a < x) :
    h =O[𝓟 (Ici x)] P := by
  obtain ⟨c, hc⟩ := hhO.bound
  obtain ⟨R, hR⟩ := eventually_atTop.mp hc
  set R' : ℝ := max x R
  have hsub : Icc x R' ⊆ Ioi a := fun v hv => hx.trans_le hv.1
  have hquot : ContinuousOn (fun v => ‖h v‖ / P v) (Icc x R') :=
    (hh.norm.mono hsub).div (hP.mono hsub) fun v hv => (hP_pos v (hsub hv)).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hquot
  set C : ℝ := max M (max c 0)
  refine IsBigO.of_bound C ?_
  rw [eventually_principal]
  intro v hv
  rcases le_or_gt v R' with hvR | hvR
  · have hPv : 0 < P v := hP_pos v (hx.trans_le hv)
    have hdiv : ‖h v‖ / P v ≤ C :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM v ⟨hv, hvR⟩).trans (le_max_left _ _))
    rw [Real.norm_of_nonneg hPv.le, ← div_le_iff₀ hPv]
    exact hdiv
  · exact (hR v ((le_max_right x R).trans hvR.le)).trans
      (mul_le_mul_of_nonneg_right ((le_max_left c 0).trans (le_max_right M _)) (norm_nonneg _))

section RayNorm

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {a : ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

/-- **Existence and error bound for Volterra integral equations on `(a, ∞)` (Olver,
Theorem 10.1).** Under the separable kernel bound `‖K x v‖ ≤ P x * Q v` with continuous `P ≥ 0`
and finite tail integrals `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` for `x > a`, there exists a continuous solution `h` on
`Ioi a` satisfying `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`. -/
theorem exists_volterra_solution [CompleteSpace E]
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP : ContinuousOn P (Ioi a)) (hP0 : ∀ x > a, 0 ≤ P x) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x > a, IntegrableOn (fun v => Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x > a, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioi x)) :
    ∃ h : ℝ → E,
      ContinuousOn h (Ioi a) ∧
      (∀ x > a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧
      (∀ x > a, ‖h x‖ ≤
        P x * (∫ v in Ioi x, Q v * ‖J v‖) *
          Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)) := by
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ := exists_volterra_solution_on isOpen_Ioi
    (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hJ hψ hP hP0 hQ0
    (fun x hx v _ hxv => hKle x hx v hxv)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦ x hx)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΨ x hx)
  refine ⟨h, hh_cont, fun x hx => ?_, fun x hx => ?_⟩
  · simpa only [Ioi_inter_Ioi_of_le hx.le] using hh_eq x hx
  · simpa only [Ioi_inter_Ioi_of_le hx.le] using hh_le x hx

/-- A priori `P Φ exp Ψ` bound on `(a, ∞)` for any measurable Volterra solution satisfying
`∀ x > a, h =O[𝓟 (Ici x)] P`. -/
theorem norm_volterra_solution_le
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP0 : ∀ x > a, 0 ≤ P x) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x > a, IntegrableOn (fun v => Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x > a, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict (Ioi a)))
    (hh_eq : ∀ x > a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x > a, h =O[𝓟 (Ici x)] P) {x₀ : ℝ} (hx₀ : a < x₀) :
    ‖h x₀‖ ≤
      P x₀ * (∫ v in Ioi x₀, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioi x₀, P v * Q v * ‖ψ v‖) := by
  simpa only [Ioi_inter_Ioi_of_le hx₀.le] using norm_volterra_solution_le_on isOpen_Ioi
    (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hJ hψ hP0 hQ0
    (fun x hx v _ hxv => hKle x hx v hxv)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦ x hx)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΨ x hx) hh
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh_eq x hx)
    (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hhO x hx) hx₀

/-- **Uniqueness of `O(P)` Volterra solutions on `(a, ∞)` (Olver, Theorem 10.1).** -/
theorem volterra_solution_unique
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP0 : ∀ x > a, 0 ≤ P x) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x > a, IntegrableOn (fun v => Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x > a, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioi x))
    {h₁ h₂ : ℝ → E}
    (hh₁ : AEStronglyMeasurable h₁ (volume.restrict (Ioi a)))
    (hh₂ : AEStronglyMeasurable h₂ (volume.restrict (Ioi a)))
    (hh₁_eq : ∀ x > a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (hh₂_eq : ∀ x > a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (hh₁O : ∀ x > a, h₁ =O[𝓟 (Ici x)] P)
    (hh₂O : ∀ x > a, h₂ =O[𝓟 (Ici x)] P) :
    EqOn h₁ h₂ (Ioi a) :=
  volterra_solution_unique_on isOpen_Ioi (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hJ hψ hP0
    hQ0 (fun x hx v _ hxv => hKle x hx v hxv)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦ x hx)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΨ x hx) hh₁ hh₂
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh₁_eq x hx)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh₂_eq x hx)
    (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hh₁O x hx)
    (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hh₂O x hx)

/-- **Sharper `exp (P₀ * Φ_ψ) - 1` bound on `(a, ∞)` (Olver, Theorem 10.2).** -/
theorem norm_volterra_solution_le_exp_sub_one {𝕜 : Type*} [NormedRing 𝕜] [NormedSpace ℝ 𝕜]
    {a P₀ : ℝ} {K : ℝ → ℝ → 𝕜} {ψ : ℝ → 𝕜} {Q : ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hΦψ : ∀ x > a, IntegrableOn (fun v => Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → 𝕜} (hh : AEStronglyMeasurable h (volume.restrict (Ioi a)))
    (hh_eq : ∀ x > a, h x = ∫ v in Ioi x, K x v * (ψ v + ψ v * h v))
    (hhO : ∀ x > a, h =O[𝓟 (Ici x)] (fun _ => (1 : ℝ))) {x₀ : ℝ} (hx₀ : a < x₀) :
    ‖h x₀‖ ≤ Real.exp (P₀ * ∫ v in Ioi x₀, Q v * ‖ψ v‖) - 1 := by
  simpa only [Ioi_inter_Ioi_of_le hx₀.le] using
    norm_volterra_solution_le_exp_sub_one_on isOpen_Ioi
      (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hψ hP₀ hQ0
      (fun x hx v _ hxv => hKle x hx v hxv)
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦψ x hx) hh
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh_eq x hx)
      (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hhO x hx) hx₀

/-- **Existence and error bound on a bounded open interval `(a, b)`.** -/
theorem exists_volterra_solution_Ioo [CompleteSpace E] {b : ℝ}
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioo a b)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioo a b)))
    (hP : ContinuousOn P (Ioo a b)) (hP0 : ∀ x ∈ Ioo a b, 0 ≤ P x)
    (hQ0 : ∀ v ∈ Ioo a b, 0 ≤ Q v)
    (hKle : ∀ x ∈ Ioo a b, ∀ v ∈ Ioo a b, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioo a b, IntegrableOn (fun v => Q v * ‖J v‖) (Ioo x b))
    (hΨ : ∀ x ∈ Ioo a b, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioo x b)) :
    ∃ h : ℝ → E,
      ContinuousOn h (Ioo a b) ∧
      (∀ x ∈ Ioo a b, h x = ∫ v in Ioo x b, K x v • (J v + ψ v • h v)) ∧
      (∀ x ∈ Ioo a b, ‖h x‖ ≤
        P x * (∫ v in Ioo x b, Q v * ‖J v‖) *
          Real.exp (∫ v in Ioo x b, P v * Q v * ‖ψ v‖)) := by
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ := exists_volterra_solution_on isOpen_Ioo
    (hK.mono fun p hp => ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hJ hψ hP hP0 hQ0 hKle
    (fun x hx => by rw [Ioo_inter_Ioi_of_mem hx]; exact hΦ x hx)
    (fun x hx => by rw [Ioo_inter_Ioi_of_mem hx]; exact hΨ x hx)
  refine ⟨h, hh_cont, fun x hx => ?_, fun x hx => ?_⟩
  · simpa only [Ioo_inter_Ioi_of_mem hx] using hh_eq x hx
  · simpa only [Ioo_inter_Ioi_of_mem hx] using hh_le x hx

/-- **Uniqueness of `O(P)` Volterra solutions on `(a, b)`.** -/
theorem volterra_solution_unique_Ioo {b : ℝ}
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioo a b)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioo a b)))
    (hP0 : ∀ x ∈ Ioo a b, 0 ≤ P x) (hQ0 : ∀ v ∈ Ioo a b, 0 ≤ Q v)
    (hKle : ∀ x ∈ Ioo a b, ∀ v ∈ Ioo a b, x < v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioo a b, IntegrableOn (fun v => Q v * ‖J v‖) (Ioo x b))
    (hΨ : ∀ x ∈ Ioo a b, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioo x b))
    {h₁ h₂ : ℝ → E}
    (hh₁ : AEStronglyMeasurable h₁ (volume.restrict (Ioo a b)))
    (hh₂ : AEStronglyMeasurable h₂ (volume.restrict (Ioo a b)))
    (hh₁_eq : ∀ x ∈ Ioo a b, h₁ x = ∫ v in Ioo x b, K x v • (J v + ψ v • h₁ v))
    (hh₂_eq : ∀ x ∈ Ioo a b, h₂ x = ∫ v in Ioo x b, K x v • (J v + ψ v • h₂ v))
    (hh₁O : ∀ x ∈ Ioo a b, h₁ =O[𝓟 (Ico x b)] P)
    (hh₂O : ∀ x ∈ Ioo a b, h₂ =O[𝓟 (Ico x b)] P) :
    EqOn h₁ h₂ (Ioo a b) :=
  volterra_solution_unique_on isOpen_Ioo (hK.mono fun p hp => ⟨hp.1.1, hp.2.2, hp.2.1.2⟩) hJ hψ
    hP0 hQ0 hKle
    (fun x hx => by rw [Ioo_inter_Ioi_of_mem hx]; exact hΦ x hx)
    (fun x hx => by rw [Ioo_inter_Ioi_of_mem hx]; exact hΨ x hx) hh₁ hh₂
    (fun x hx => by rw [Ioo_inter_Ioi_of_mem hx]; exact hh₁_eq x hx)
    (fun x hx => by rw [Ioo_inter_Ioi_of_mem hx]; exact hh₂_eq x hx)
    (fun x hx => by rw [Ioo_inter_Ici_of_mem hx]; exact hh₁O x hx)
    (fun x hx => by rw [Ioo_inter_Ici_of_mem hx]; exact hh₂O x hx)

end RayNorm


/-- **Sharpness of the `exp (P₀ * Φ_ψ) - 1` bound.** For the constant kernel `K x v = P₀` and any
real-valued `ψ` integrable on upper tails `I ∩ Ioi x`, the function
`h x = exp (P₀ * ∫ v in I ∩ Ioi x, ψ v) - 1` is an exact solution of the Volterra equation
`h x = ∫ v in I ∩ Ioi x, P₀ * (ψ v + ψ v * h v)` on `I`. In particular, when `0 ≤ P₀` and
`0 ≤ ψ` on `I`, `h` attains `norm_volterra_solution_le_exp_sub_one_on` (with `Q = 1`) with
equality. -/
theorem volterra_const_kernel_solution_eq_exp_sub_one_on {I : Set ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ x ∈ I, IntegrableOn ψ (I ∩ Ioi x)) (P₀ : ℝ) {x : ℝ} (hx : x ∈ I) :
    Real.exp (P₀ * ∫ v in I ∩ Ioi x, ψ v) - 1 =
      ∫ v in I ∩ Ioi x,
        P₀ * (ψ v + ψ v * (Real.exp (P₀ * ∫ u in I ∩ Ioi v, ψ u) - 1)) := by
  have heq : (fun v => P₀ * (ψ v + ψ v * (Real.exp (P₀ * ∫ u in I ∩ Ioi v, ψ u) - 1))) =
      fun v => P₀ * (ψ v * Real.exp (P₀ * ∫ u in I ∩ Ioi v, ψ u)) := by
    ext v; ring
  rw [heq, integral_const_mul, mul_integral_mul_exp_tail_on (hψ x hx) P₀]

/-- Ray `(a, ∞)` specialization of `volterra_const_kernel_solution_eq_exp_sub_one_on`: for constant
kernel `K x v = P₀`, `h x = exp (P₀ * ∫ v in Ioi x, ψ v) - 1` solves
`h x = ∫ v in Ioi x, P₀ * (ψ v + ψ v * h v)` for all `x > a`. -/
theorem volterra_const_kernel_solution_eq_exp_sub_one {a : ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ x > a, IntegrableOn ψ (Ioi x)) (P₀ : ℝ) {x : ℝ} (hx : a < x) :
    Real.exp (P₀ * ∫ v in Ioi x, ψ v) - 1 =
      ∫ v in Ioi x,
        P₀ * (ψ v + ψ v * (Real.exp (P₀ * ∫ u in Ioi v, ψ u) - 1)) := by
  have heq : (fun v => P₀ * (ψ v + ψ v * (Real.exp (P₀ * ∫ u in Ioi v, ψ u) - 1))) =
      fun v => P₀ * (ψ v * Real.exp (P₀ * ∫ u in Ioi v, ψ u)) := by
    ext v; ring
  rw [heq, integral_const_mul, (hψ x hx).mul_integral_Ioi_mul_exp_integral_Ioi P₀]

end Specializations

end TauCeti
