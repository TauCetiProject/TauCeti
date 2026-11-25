/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.ODE.Gronwall.Tail
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Volterra integral equations with separable kernel bounds

Let `K x v` be a kernel, continuous on `{(x, v) | a < x ≤ v}`, with a separable bound
`‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are continuous on `(a, ∞)`, and let `J`, `ψ` be
continuous on `(a, ∞)` such that, for every `x > a`, the integrals

* `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
* `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`

converge. Then the Volterra integral equation

  `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)`

has a solution `h`, continuous on `(a, ∞)`, with `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every
`x > a`.

This is Olver's theorem on Volterra integral equations (Chapter 6, Theorem 10.1) on the half-line
`(a, ∞)`; the finite right endpoint of that theorem is not treated here. The solution is unique
among continuous solutions that are `O(P)` at infinity. If `K` vanishes on the diagonal and has
a partial derivative `K₁` in its first variable, continuous with `‖K₁ x v‖ ≤ P₁ x * Q v` for a
continuous `P₁ ≥ 0`, then the solution is `C¹` with `‖h' x‖ ≤ P₁ x * Φ x * exp (Ψ x)`. If `P` is
a constant `P₀` and `‖J‖ ≤ ‖ψ‖`, every continuous solution bounded at infinity satisfies
`‖h x‖ ≤ exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1`, which sharpens the bound
`P x * Φ x * exp (Ψ x)` when `J = ψ`. The error bounds also hold, at a point `x > a`, for every
solution on the ray `[x, ∞)` that is `O(P)` (respectively bounded) there, with no continuity,
measurability or completeness. The existence and error-bound theorems for
the Liouville–Green approximation and for the solutions of linear differential equations at an
irregular singularity of rank one (DLMF §§2.7, 2.8) reduce to equations of this form.

The kernel `K` and the coefficient `ψ` take values in any normed field `𝕜`, and the forcing `J`
and the unknown `h` in any real Banach space which is also a normed `𝕜`-space; for `𝕜 = E = ℂ`
the scalar multiplications are products of complex numbers. The differentiability results ask
in addition that `𝕜` be a normed `ℝ`-algebra compatible with `E`, as `ℝ` and `ℂ` are.

## Main results

* `TauCeti.exists_volterra_solution`: existence of a continuous solution with the bound
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.volterra_solution_unique`: two continuous solutions that are `O(P)` at infinity agree
  on `(a, ∞)`; consequently every such solution satisfies the bound
  (`TauCeti.norm_volterra_solution_le`).
* `TauCeti.existsUnique_volterra_solution`: on `(a, ∞)` there is exactly one continuous solution
  that is `O(P)` at infinity.
* `TauCeti.norm_volterra_solution_le_exp_sub_one`: the bound
  `‖h x‖ ≤ exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1` for a constant `P = P₀`, `‖J‖ ≤ ‖ψ‖` and
  `h` bounded at infinity, which sharpens the general bound when `J = ψ`.
* `TauCeti.exists_volterra_solution_exp_sub_one`: existence of a continuous solution with the
  sharper bound, for `‖K x v‖ ≤ Q v` and `‖J‖ ≤ ‖ψ‖`.
* `TauCeti.norm_volterra_solution_le_of_isBigO_principal_Ici` and
  `TauCeti.norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici`: the two bounds at `x`
  for every solution on `[x, ∞)` that is `O(P)` (respectively bounded) on `[x, ∞)`.
* `TauCeti.volterra_solution_unique_of_integrableOn` and
  `TauCeti.volterra_solution_unique_of_aestronglyMeasurable`: uniqueness among solutions that are
  `O(P)` on `[x, ∞)` for every `x > a` and whose integrands are integrable, respectively which are
  almost everywhere strongly measurable for measurable data
  (via `TauCeti.integrableOn_volterra_of_isBigO`).
* `TauCeti.hasDerivAt_volterra_solution`, `TauCeti.contDiffOn_volterra_solution` and
  `TauCeti.norm_deriv_volterra_solution_le`: the derivative
  `h' x = ∫ v in Ioi x, K₁ x v • (J v + ψ v • h v)`, the `C¹` regularity of `h`, and the bound
  `‖h' x‖ ≤ P₁ x * Φ x * exp (Ψ x)`.

A solution is constructed as the sum of the Picard increments (the Liouville–Neumann series).
The `k`-th increment is bounded by
`P x * Φ x * Ψ x ^ k / k!`, by the identity `∫ v in Ioi x, g v * Ψ v ^ k = Ψ x ^ (k + 1) / (k + 1)`
for `Ψ` the tail integral of `g` (`MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`).
The bounds for an arbitrary solution on a ray come from Grönwall's inequality on a ray,
`TauCeti.le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi`, which iterates the same identity;
uniqueness follows by applying the bound with zero forcing to the difference of two solutions.
The derivative of
`x ↦ ∫ v in Ioi x, K x v • F v` is computed by writing its increments as iterated integrals and
exchanging the order of integration. The derivative bound rests on
`∫ v in Ioi x, g v * exp (Ψ v) = exp (Ψ x) - 1`
(`MeasureTheory.IntegrableOn.integral_Ioi_mul_exp_integral_Ioi`).
The discrete analogue is `TauCeti.existsUnique_discrete_volterra_solution`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10.
* NIST Digital Library of Mathematical Functions, §2.7(iii), <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Asymptotics Filter Set MeasureTheory Function
open scoped Nat Topology

namespace TauCeti

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {a : ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- The forcing weights `Q v * ‖J v‖` are nonnegative on `(x, ∞)` for every `x ≥ a`. -/
private lemma forcing_weight_nonneg (hQ0 : ∀ v ∈ Ioi a, 0 ≤ Q v) {x : ℝ} (hx : a ≤ x) :
    ∀ v ∈ Ioi x, 0 ≤ Q v * ‖J v‖ :=
  fun v hv ↦ mul_nonneg (hQ0 v (hx.trans_lt hv)) (norm_nonneg _)

/-- The coefficient weights `P v * Q v * ‖ψ v‖` are nonnegative on `(x, ∞)` for every `x ≥ a`. -/
private lemma coeff_weight_nonneg (hP0 : ∀ v ∈ Ioi a, 0 ≤ P v) (hQ0 : ∀ v ∈ Ioi a, 0 ≤ Q v)
    {x : ℝ} (hx : a ≤ x) : ∀ v ∈ Ioi x, 0 ≤ P v * Q v * ‖ψ v‖ :=
  fun v hv ↦ mul_nonneg (mul_nonneg (hP0 v (hx.trans_lt hv)) (hQ0 v (hx.trans_lt hv)))
    (norm_nonneg _)

omit [NormedSpace ℝ E] in
/-- The separable bound for `v ↦ K x v • y` on `[x, ∞)`. -/
private lemma norm_kernel_smul_le (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    {x v : ℝ} (hx : a < x) (hv : x ≤ v) (y : E) : ‖K x v • y‖ ≤ P x * (Q v * ‖y‖) := by
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hKle x v hx hv) (norm_nonneg _)

omit [NormedSpace ℝ E] in
/-- If `K x` and `F` are almost everywhere strongly measurable on `(x, ∞)`, and `‖F‖ ≤ B` there
with `Q * B` integrable on `(x, ∞)`, then `v ↦ K x v • F v` is integrable on `(x, ∞)`. -/
private lemma integrableOn_kernel_smul_of_le
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E} {B : ℝ → ℝ} {x : ℝ}
    (hx : a < x) (hKm : AEStronglyMeasurable (K x) (volume.restrict (Ioi x)))
    (hFm : AEStronglyMeasurable F (volume.restrict (Ioi x))) (hFB : ∀ v ∈ Ioi x, ‖F v‖ ≤ B v)
    (hB : IntegrableOn (fun v ↦ Q v * B v) (Ioi x)) :
    IntegrableOn (fun v ↦ K x v • F v) (Ioi x) := by
  refine Integrable.mono' (hB.const_mul (P x)) (hKm.smul hFm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
  refine (norm_kernel_smul_le hKle hx hv.le _).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (hFB v hv) ((norm_nonneg _).trans (hKle x v hx hv.le))

omit [NormedSpace ℝ E] in
/-- If `F` is continuous on `(a, ∞)` and `Q * ‖F‖` is integrable on `(x, ∞)`, then so is
`v ↦ K x v • F v`. -/
private lemma integrableOn_kernel_smul
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E}
    (hF : ContinuousOn F (Ioi a)) {x : ℝ} (hx : a < x)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (Ioi x)) :
    IntegrableOn (fun v ↦ K x v • F v) (Ioi x) :=
  integrableOn_kernel_smul_of_le hKle hx
    ((hK.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hv ↦
      ⟨hx, le_of_lt hv⟩).aestronglyMeasurable measurableSet_Ioi)
    ((hF.mono (Ioi_subset_Ioi hx.le)).aestronglyMeasurable measurableSet_Ioi)
    (fun _ _ ↦ le_rfl) hFint

/-- The separable bound for the integral `∫ v in Ioi x, K x v • F v`. -/
private lemma norm_integral_kernel_smul_le
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E} {x : ℝ} (hx : a < x)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (Ioi x)) :
    ‖∫ v in Ioi x, K x v • F v‖ ≤ P x * ∫ v in Ioi x, Q v * ‖F v‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hFint.const_mul (P x)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact norm_kernel_smul_le hKle hx (le_of_lt hv) _

/-- If `F` is continuous on `(a, ∞)` and `Q * ‖F‖` is integrable on every `(x, ∞)` with `x > a`,
then `x ↦ ∫ v in Ioi x, K x v • F v` is continuous on `(a, ∞)`. -/
private lemma continuousOn_integral_kernel_smul
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) (hP : ContinuousOn P (Ioi a))
    (hQ0 : ∀ v ∈ Ioi a, 0 ≤ Q v) {F : ℝ → E} (hF : ContinuousOn F (Ioi a))
    (hFint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖F v‖) (Ioi x)) :
    ContinuousOn (fun x ↦ ∫ v in Ioi x, K x v • F v) (Ioi a) := by
  intro x₀ (hx₀ : a < x₀)
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨c, hac, hcx⟩ := exists_between hx₀
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hP.mono ((Icc_subset_Ioi_iff (hcx.trans (lt_add_one x₀)).le).2 hac))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ ⟨hcx.le, by linarith⟩)
  -- extend the integrands by zero to the fixed ray `(c, ∞)`
  have heq : (fun x ↦ ∫ v in Ioi c, (Ioi x).indicator (fun v ↦ K x v • F v) v) =ᶠ[𝓝 x₀]
      fun x ↦ ∫ v in Ioi x, K x v • F v := by
    filter_upwards [Ioi_mem_nhds hcx] with x hx
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.2 hx.le]
  refine ContinuousAt.congr ?_ heq
  refine continuousAt_of_dominated (bound := fun v ↦ M * (Q v * ‖F v‖)) ?_ ?_
    ((hFint c hac).const_mul M) ?_
  · filter_upwards [Ioi_mem_nhds hcx] with x hx
    exact ((integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_kernel_smul hK hKle hF
      (hac.trans hx) (hFint x (hac.trans hx)))).integrableOn.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds hcx (lt_add_one x₀)] with x hx
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun v (hv : c < v) ↦ ?_)
    have hQF : 0 ≤ Q v * ‖F v‖ := mul_nonneg (hQ0 v (hac.trans hv)) (norm_nonneg _)
    by_cases hxv : x < v
    · rw [indicator_of_mem hxv]
      refine (norm_kernel_smul_le hKle (hac.trans hx.1) hxv.le _).trans ?_
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hM x ⟨hx.1.le, hx.2.le⟩)) hQF
    · rw [indicator_of_notMem hxv, norm_zero]
      exact mul_nonneg hM0 hQF
  · filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume x₀)] with v hv
    rcases hv.lt_or_gt with hlt | hgt
    · refine (continuousAt_const (y := (0 : E))).congr ?_
      filter_upwards [Ioi_mem_nhds hlt] with x hx
      rw [indicator_of_notMem (notMem_Ioi.2 hx.le)]
    · have hmem : {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2} ∈ 𝓝 (x₀, v) :=
        mem_of_superset (((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst continuous_snd)).mem_nhds ⟨hx₀, hgt⟩)
          fun p hp ↦ ⟨hp.1, hp.2.le⟩
      have hKv : ContinuousAt (fun x ↦ K x v) x₀ :=
        (hK.continuousAt hmem).comp (f := fun x ↦ (x, v)) (by fun_prop)
      refine (hKv.fun_smul (continuousAt_const (y := F v))).congr ?_
      filter_upwards [gt_mem_nhds hgt] with x hx
      rw [indicator_of_mem (mem_Ioi.2 hx)]

/-- The increments of the Picard iteration for the Volterra equation: the `0`-th is
`x ↦ ∫ v in Ioi x, K x v • J v`, and each further one applies
`F ↦ (x ↦ ∫ v in Ioi x, K x v • ψ v • F v)` to the previous one. -/
private noncomputable def picardTerm (K : ℝ → ℝ → 𝕜) (J : ℝ → E) (ψ : ℝ → 𝕜) : ℕ → ℝ → E
  | 0, x => ∫ v in Ioi x, K x v • J v
  | k + 1, x => ∫ v in Ioi x, K x v • ψ v • picardTerm K J ψ k v

section Iteration

variable (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
  (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
  (hP : ContinuousOn P (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
  (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
  (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
  (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
  (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))

omit [NormedSpace ℝ E] in
include hψ hQ hQ0 hΨ in
/-- If `F` is continuous on `(a, ∞)` with `‖F v‖ ≤ C * P v` for `v > x`, then
`Q * ‖ψ • F‖` is integrable on `(x, ∞)`. -/
private lemma integrableOn_weight_smul {F : ℝ → E} (hF : ContinuousOn F (Ioi a)) {x C : ℝ}
    (hx : a < x) (hFle : ∀ v ∈ Ioi x, ‖F v‖ ≤ C * P v) :
    IntegrableOn (fun v ↦ Q v * ‖ψ v • F v‖) (Ioi x) := by
  have hcont : ContinuousOn (fun v ↦ Q v * ‖ψ v • F v‖) (Ioi x) :=
    (hQ.mul (hψ.smul hF).norm).mono (Ioi_subset_Ioi hx.le)
  refine Integrable.mono' ((hΨ x hx).const_mul C)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
  have hQψ : 0 ≤ Q v * ‖ψ v‖ := mul_nonneg (hQ0 v (hx.trans hv)) (norm_nonneg _)
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (hQ0 v (hx.trans hv))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))), ← mul_assoc]
  calc Q v * ‖ψ v‖ * ‖F v‖ ≤ Q v * ‖ψ v‖ * (C * P v) :=
        mul_le_mul_of_nonneg_left (hFle v hv) hQψ
    _ = C * (P v * Q v * ‖ψ v‖) := by ring

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
include hP0 hQ0 hΦ hΨ in
/-- For `a < x ≤ v` and `f` monotone and nonnegative on `[0, ∞)`, the bound
`P v * Φ v * f (Ψ v)` at `v` is at most `Φ x * f (Ψ x) * P v`, where `Φ` and `Ψ` are the forcing
and coefficient tail integrals. -/
private lemma mul_tail_le_of_le {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0))
    (hf0 : ∀ t, 0 ≤ t → 0 ≤ f t) {x v : ℝ} (hx : a < x) (hv : x ≤ v) :
    P v * (∫ u in Ioi v, Q u * ‖J u‖) * f (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ≤
      (∫ u in Ioi x, Q u * ‖J u‖) * f (∫ u in Ioi x, P u * Q u * ‖ψ u‖) * P v := by
  have hva : a < v := hx.trans_le hv
  have hPv := hP0 v hva
  have hΦx := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (forcing_weight_nonneg (J := J) hQ0 hx.le)
  have hΨv := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (coeff_weight_nonneg (ψ := ψ) hP0 hQ0 hva.le)
  have hΨle := antitoneOn_integral_Ioi (coeff_weight_nonneg hP0 hQ0 le_rfl) hΨ hx hva hv
  have hfv := hf0 _ hΨv
  calc _ ≤ P v * (∫ u in Ioi x, Q u * ‖J u‖) * f (∫ u in Ioi x, P u * Q u * ‖ψ u‖) := by
        gcongr P v * ?_ * ?_
        · exact antitoneOn_integral_Ioi (forcing_weight_nonneg hQ0 le_rfl) hΦ hx hva hv
        · exact hf hΨv (hΨv.trans hΨle) hΨle
    _ = _ := by ring

omit [NormedSpace ℝ E] in
include hQ0 hΨ in
/-- If `‖F v‖ ≤ C * P v * f (Ψ v)` for `v > x`, where `f` is continuous and
`Ψ v = ∫ u in Ioi v, P u * Q u * ‖ψ u‖` is the coefficient tail integral, then the weighted
integral `∫ v in Ioi x, Q v * ‖ψ v • F v‖` is at most `C * ∫ v in Ioi x, g v * f (Ψ v)` for the
coefficient weight `g v = P v * Q v * ‖ψ v‖`. -/
private lemma integral_weight_smul_le_comp {F : ℝ → E} {f : ℝ → ℝ} (hf : Continuous f)
    {x C : ℝ} (hx : a < x) (hFint : IntegrableOn (fun v ↦ Q v * ‖ψ v • F v‖) (Ioi x))
    (hFle : ∀ v ∈ Ioi x, ‖F v‖ ≤ C * P v * f (∫ u in Ioi v, P u * Q u * ‖ψ u‖)) :
    ∫ v in Ioi x, Q v * ‖ψ v • F v‖ ≤
      C * ∫ v in Ioi x, P v * Q v * ‖ψ v‖ * f (∫ u in Ioi v, P u * Q u * ‖ψ u‖) := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on hFint (((hΨ x hx).mul_comp_integral_Ioi hf.continuousOn).const_mul _)
    measurableSet_Ioi fun v (hv : x < v) ↦ ?_
  have hQψ : 0 ≤ Q v * ‖ψ v‖ := mul_nonneg (hQ0 v (hx.trans hv)) (norm_nonneg _)
  rw [norm_smul, ← mul_assoc]
  calc Q v * ‖ψ v‖ * ‖F v‖
      ≤ Q v * ‖ψ v‖ * (C * P v * f (∫ u in Ioi v, P u * Q u * ‖ψ u‖)) := by grw [hFle v hv]
    _ = _ := by ring

omit [NormedSpace ℝ E] in
include hQ0 hΨ in
/-- If `‖F v‖ ≤ C * P v * Ψ v ^ k / k!` for `v > x`, where `Ψ v = ∫ u in Ioi v, P u * Q u * ‖ψ u‖`
is the coefficient tail integral, then the weighted integral
`∫ v in Ioi x, Q v * ‖ψ v • F v‖` is at most `C * Ψ x ^ (k + 1) / (k + 1)!`. -/
private lemma integral_weight_smul_le {F : ℝ → E} {x C : ℝ} (k : ℕ) (hx : a < x)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖ψ v • F v‖) (Ioi x))
    (hFle : ∀ v ∈ Ioi x, ‖F v‖ ≤ C * P v * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k / k !) :
    ∫ v in Ioi x, Q v * ‖ψ v • F v‖ ≤
      C * (∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)! := by
  calc ∫ v in Ioi x, Q v * ‖ψ v • F v‖
      ≤ C / k ! * ∫ v in Ioi x, P v * Q v * ‖ψ v‖ * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k :=
        integral_weight_smul_le_comp hQ0 hΨ (continuous_pow k) hx hFint
          fun v hv ↦ (hFle v hv).trans_eq (by ring)
    _ = C * (∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)! := by
        rw [(hΨ x hx).integral_Ioi_mul_pow_integral_Ioi k, Nat.factorial_succ]
        push_cast
        field_simp

include hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ

/-- The Picard increments are continuous on `(a, ∞)`, and the `k`-th is bounded by
`P x * Φ x * (Ψ x ^ k / k!)`. -/
private lemma picardTerm_spec (k : ℕ) :
    ContinuousOn (picardTerm K J ψ k) (Ioi a) ∧ ∀ x ∈ Ioi a, ‖picardTerm K J ψ k x‖ ≤
      P x * (∫ v in Ioi x, Q v * ‖J v‖) *
        ((∫ v in Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !) := by
  induction k with
  | zero =>
    refine ⟨continuousOn_integral_kernel_smul hK hKle hP hQ0 hJ hΦ, fun x hx ↦ ?_⟩
    simpa [picardTerm] using norm_integral_kernel_smul_le hKle hx (hΦ x hx)
  | succ k ih =>
    obtain ⟨hcont, hle⟩ := ih
    -- the weighted integrands of the next step are integrable on every ray
    have hFint : ∀ x ∈ Ioi a,
        IntegrableOn (fun v ↦ Q v * ‖ψ v • picardTerm K J ψ k v‖) (Ioi x) := fun x hx ↦
      integrableOn_weight_smul hψ hQ hQ0 hΨ hcont hx (C := (∫ v in Ioi x, Q v * ‖J v‖) *
        ((∫ v in Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !)) fun v (hv : x < v) ↦
        (hle v (hx.trans hv)).trans (mul_tail_le_of_le hP0 hQ0 hΦ hΨ (f := fun t ↦ t ^ k / k !)
          (fun s (hs : 0 ≤ s) _ _ hst ↦ by dsimp only; gcongr) (fun _ _ ↦ by positivity) hx hv.le)
    refine ⟨continuousOn_integral_kernel_smul hK hKle hP hQ0 (hψ.smul hcont) hFint,
      fun x hx ↦ ?_⟩
    set Φx := ∫ v in Ioi x, Q v * ‖J v‖
    -- bound the weighted integral through `∫ g * Ψ ^ k = Ψ x ^ (k + 1) / (k + 1)`
    have hint := integral_weight_smul_le hQ0 hΨ (C := Φx) k hx (hFint x hx) fun v (hv : x < v) ↦ by
      have hva : a < v := hx.trans hv
      have hΦle : ∫ u in Ioi v, Q u * ‖J u‖ ≤ Φx :=
        antitoneOn_integral_Ioi (forcing_weight_nonneg hQ0 le_rfl) hΦ hx hva hv.le
      have hΨv := setIntegral_nonneg (μ := volume) measurableSet_Ioi
        (coeff_weight_nonneg (ψ := ψ) hP0 hQ0 hva.le)
      calc ‖picardTerm K J ψ k v‖
          ≤ P v * (∫ u in Ioi v, Q u * ‖J u‖) * ((∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k / k !) :=
            hle v hva
        _ ≤ P v * Φx * ((∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k / k !) := by
            have := hP0 v hva
            grw [hΦle]
        _ = _ := by ring
    refine (norm_integral_kernel_smul_le hKle hx (hFint x hx)).trans ?_
    calc P x * ∫ v in Ioi x, Q v * ‖ψ v • picardTerm K J ψ k v‖
        ≤ P x * (Φx * (∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)!) :=
          mul_le_mul_of_nonneg_left hint (hP0 x hx)
      _ = P x * Φx * ((∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)!) := by ring

/-- At points `v ≥ x`, the `k`-th Picard increment is at most
`Φ x * (Ψ x ^ k / k!) * P v`, with the tail integrals `Φ` and `Ψ` taken at `x`. -/
private lemma norm_picardTerm_le_of_le (k : ℕ) {x v : ℝ} (hx : a < x) (hv : x ≤ v) :
    ‖picardTerm K J ψ k v‖ ≤ (∫ u in Ioi x, Q u * ‖J u‖) *
      ((∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ k / k !) * P v :=
  ((picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 v (hx.trans_le hv)).trans
    (mul_tail_le_of_le hP0 hQ0 hΦ hΨ (f := fun t ↦ t ^ k / k !)
      (fun s (hs : 0 ≤ s) _ _ hst ↦ by dsimp only; gcongr) (fun _ _ ↦ by positivity) hx hv)

/-- The weighted integrands `Q * ‖ψ • T k‖` of the Picard increments `T k` are integrable on every
ray `(x, ∞)` with `x > a`. -/
private lemma integrableOn_weight_smul_picardTerm (k : ℕ) {x : ℝ} (hx : a < x) :
    IntegrableOn (fun v ↦ Q v * ‖ψ v • picardTerm K J ψ k v‖) (Ioi x) :=
  integrableOn_weight_smul hψ hQ hQ0 hΨ (picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).1 hx
    fun v (hv : x < v) ↦ norm_picardTerm_le_of_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hx hv.le

/-- The sum of the Picard increments is bounded by `P x * Φ x * exp (Ψ x)`. -/
private lemma norm_tsum_picardTerm_le {x : ℝ} (hx : a < x) :
    ‖∑' k, picardTerm K J ψ k x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) :=
  tsum_of_norm_bounded (by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)).mul_left
      (P x * ∫ v in Ioi x, Q v * ‖J v‖))
    fun k ↦ (picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 x hx

variable [CompleteSpace E]

/-- The Picard increments are summable at every point of `(a, ∞)`. -/
private lemma summable_picardTerm {x : ℝ} (hx : a < x) :
    Summable fun k ↦ picardTerm K J ψ k x :=
  ((Real.summable_pow_div_factorial (∫ v in Ioi x, P v * Q v * ‖ψ v‖)).mul_left
    (P x * ∫ v in Ioi x, Q v * ‖J v‖)).of_norm_bounded
    fun k ↦ (picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 x hx

/-- The sum of the Picard increments is continuous on `(a, ∞)`: near each `x₀ > a` the series
converges uniformly, being dominated by an exponential series. -/
private lemma continuousOn_tsum_picardTerm :
    ContinuousOn (fun x ↦ ∑' k, picardTerm K J ψ k x) (Ioi a) := by
  intro x₀ (hx₀ : a < x₀)
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨c, hac, hcx⟩ := exists_between hx₀
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hP.mono ((Icc_subset_Ioi_iff (hcx.trans (lt_add_one x₀)).le).2 hac))
  refine (continuousOn_tsum
    (fun k ↦ (picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).1.mono
      fun x (hx : x ∈ Icc c (x₀ + 1)) ↦ hac.trans_le hx.1)
    ((Real.summable_pow_div_factorial (∫ v in Ioi c, P v * Q v * ‖ψ v‖)).mul_left
      ((∫ v in Ioi c, Q v * ‖J v‖) * M))
    fun k x (hx : x ∈ Icc c (x₀ + 1)) ↦ ?_).continuousAt (Icc_mem_nhds hcx (lt_add_one x₀))
  have := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (forcing_weight_nonneg (J := J) hQ0 hac.le)
  have := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (coeff_weight_nonneg (ψ := ψ) hP0 hQ0 hac.le)
  refine (norm_picardTerm_le_of_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hac hx.1).trans ?_
  calc _ ≤ (∫ u in Ioi c, Q u * ‖J u‖) * ((∫ u in Ioi c, P u * Q u * ‖ψ u‖) ^ k / k !) * M :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM x hx)) (by positivity)
    _ = _ := by ring

/-- The sum of the Picard increments solves the Volterra equation. -/
private lemma tsum_picardTerm_eq {x : ℝ} (hx : a < x) :
    ∑' k, picardTerm K J ψ k x = ∫ v in Ioi x,
      K x v • (J v + ψ v • ∑' k, picardTerm K J ψ k v) := by
  set T := picardTerm K J ψ
  set h : ℝ → E := fun x ↦ ∑' k, T k x with h_def
  have hspec := picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hcont : ContinuousOn h (Ioi a) :=
    continuousOn_tsum_picardTerm hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  -- split the integral into its `J`-part and its `h`-part
  have hψh : IntegrableOn (fun v ↦ Q v * ‖ψ v • h v‖) (Ioi x) :=
    integrableOn_weight_smul hψ hQ hQ0 hΨ hcont hx
      (C := (∫ u in Ioi x, Q u * ‖J u‖) * Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖))
      fun v (hv : x < v) ↦
        (norm_tsum_picardTerm_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ (hx.trans hv)).trans
          (mul_tail_le_of_le hP0 hQ0 hΦ hΨ (Real.exp_monotone.monotoneOn _)
            (fun _ _ ↦ (Real.exp_pos _).le) hx hv.le)
  have hKJ : IntegrableOn (fun v ↦ K x v • J v) (Ioi x) :=
    integrableOn_kernel_smul hK hKle hJ hx (hΦ x hx)
  have hKψh : IntegrableOn (fun v ↦ K x v • ψ v • h v) (Ioi x) :=
    integrableOn_kernel_smul hK hKle (hψ.smul hcont) hx hψh
  simp only [smul_add]
  rw [integral_add hKJ hKψh]
  -- expand `h v` as the series of increments and interchange the sum and the integral
  set Φx := ∫ u in Ioi x, Q u * ‖J u‖
  set Ψx := ∫ u in Ioi x, P u * Q u * ‖ψ u‖
  have hTle : ∀ k, ∀ v, x ≤ v → ‖T k v‖ ≤ Φx * (Ψx ^ k / k !) * P v := fun k _ hv ↦
    norm_picardTerm_le_of_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hx hv
  have hFk : ∀ k, IntegrableOn (fun v ↦ K x v • ψ v • T k v) (Ioi x) := fun k ↦
    integrableOn_kernel_smul hK hKle (hψ.smul (hspec k).1) hx
      (integrableOn_weight_smul_picardTerm hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k hx)
  have hsum : Summable fun k ↦ ∫ v in Ioi x, ‖K x v • ψ v • T k v‖ := by
    refine Summable.of_nonneg_of_le (fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) ((Real.summable_pow_div_factorial Ψx).mul_left (P x * Φx * Ψx))
    refine (setIntegral_mono_on (hFk k).norm
      ((hΨ x hx).const_mul (P x * Φx * (Ψx ^ k / k !))) measurableSet_Ioi
      fun v (hv : x < v) ↦ ?_).trans_eq (by rw [integral_const_mul]; ring)
    refine (norm_kernel_smul_le hKle hx hv.le _).trans ?_
    rw [norm_smul]
    have := hP0 x hx
    have := hQ0 v (hx.trans hv)
    calc P x * (Q v * (‖ψ v‖ * ‖T k v‖))
        ≤ P x * (Q v * (‖ψ v‖ * (Φx * (Ψx ^ k / k !) * P v))) := by grw [hTle k v hv.le]
      _ = P x * Φx * (Ψx ^ k / k !) * (P v * Q v * ‖ψ v‖) := by ring
  have hser := hasSum_integral_of_summable_integral_norm hFk hsum
  have hinner : ∀ v, ∑' k, K x v • ψ v • T k v = K x v • ψ v • h v := fun v ↦ by
    rw [h_def, tsum_const_smul'', tsum_const_smul'']
  simp only [hinner] at hser
  calc h x = T 0 x + ∑' k, T (k + 1) x := (summable_picardTerm hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
        hx).tsum_eq_zero_add
    _ = _ := by rw [← hser.tsum_eq]; simp only [T, picardTerm]

end Iteration

/-- **Volterra integral equations, existence.** Let `K` be continuous on
`{(x, v) | a < x ≤ v}` with `‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are continuous on
`(a, ∞)`, and let `J`, `ψ` be continuous on `(a, ∞)` such that
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for
every `x > a`. Then the Volterra integral equation
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has a solution, continuous on `(a, ∞)`, such
that `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x > a` (the existence part of Olver, Chapter 6,
Theorem 10.1). -/
theorem exists_volterra_solution [CompleteSpace E]
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
        Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) :=
  ⟨fun x ↦ ∑' k, picardTerm K J ψ k x,
    continuousOn_tsum_picardTerm hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ,
    fun _ hx ↦ tsum_picardTerm_eq hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hx,
    fun _ hx ↦ norm_tsum_picardTerm_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hx⟩

/-! ### Solutions on a ray

The bounds in this section concern a solution of the equation on a ray `[x, ∞)` only, which is
`O(P)` on that ray. They need no continuity, measurability or completeness: the error bound
comes from Grönwall's inequality on a ray,
`TauCeti.le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi`. -/

section Ray

omit [NormedSpace ℝ E] in
/-- If `K x`, `J`, `ψ` and `h` are almost everywhere strongly measurable on `(x, ∞)` (with respect
to the restriction of the Lebesgue measure), for some `x > a` at which `Φ x` and `Ψ x` converge,
and `h` is `O(P)` on `[x, ∞)`, then the integrand `v ↦ K x v • (J v + ψ v • h v)` of the Volterra
equation is integrable on `(x, ∞)`. -/
theorem integrableOn_volterra_of_isBigO (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {x : ℝ} (hx : a < x)
    (hKm : AEStronglyMeasurable (K x) (volume.restrict (Ioi x)))
    (hJm : AEStronglyMeasurable J (volume.restrict (Ioi x)))
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi x)))
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi x))) (hh : h =O[𝓟 (Ici x)] P) :
    IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (Ioi x) := by
  obtain ⟨C, hC⟩ := (isBigO_principal_iff_of_nonneg fun v (hv : x ≤ v) ↦
    hP0 v (hx.trans_le hv)).1 hh
  refine integrableOn_kernel_smul_of_le (B := fun v ↦ ‖J v‖ + ‖ψ v‖ * (C * P v)) hKle hx hKm
    (hJm.add (hψm.smul hm))
    (fun v (hv : x < v) ↦ (norm_add_le _ _).trans (by rw [norm_smul]; gcongr; exact hC v hv.le))
    ?_
  refine (hΦ.add (hΨ.const_mul C)).congr_fun (fun v _ ↦ ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

/-- **Volterra integral equations, bound on a ray.** Let `‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`,
where `P ≥ 0` on `(a, ∞)`, and let `x > a` be such that `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge. Then every solution of the Volterra equation
`h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v)` on `[x, ∞)` that is `O(P)` on `[x, ∞)` satisfies
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)` (the error bound of Olver, Chapter 6, Theorem 10.1). -/
theorem norm_volterra_solution_le_of_isBigO_principal_Ici (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {x : ℝ} (hx : a < x) {h : ℝ → E}
    (h_eq : ∀ y ∈ Ici x, h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v))
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) (h_isBigO : h =O[𝓟 (Ici x)] P) :
    ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  rcases (hP0 x hx).eq_or_lt with hPx | hPx
  · -- if `P x = 0`, then `K x v = 0` for every `v ≥ x`, so `h x = 0`
    rw [← hPx, zero_mul, zero_mul, h_eq x self_mem_Ici]
    refine (norm_integral_le_of_norm_le (g := fun _ ↦ (0 : ℝ)) (integrable_zero _ _ _)
      ?_).trans_eq (by simp)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right ((hKle x v hx hv.le).trans_eq (by rw [← hPx, zero_mul]))
      (norm_nonneg _)).trans_eq (zero_mul _)
  -- otherwise `Q ≥ 0` on `[x, ∞)`, and Grönwall's inequality applies to `‖h‖`
  have hQ0 : ∀ v ∈ Ici x, 0 ≤ Q v := fun v (hv : x ≤ v) ↦
    nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (hKle x v hx hv)) hPx
  obtain ⟨C, hC⟩ := (isBigO_principal_iff_of_nonneg fun v (hv : x ≤ v) ↦
    hP0 v (hx.trans_le hv)).1 h_isBigO
  have hΨ' : IntegrableOn (fun v ↦ P v * (Q v * ‖ψ v‖)) (Ioi x) := by
    simpa only [mul_assoc] using hΨ
  simpa only [mul_assoc] using le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi
    (u := fun y ↦ ‖h y‖)
    (A := ∫ v in Ioi x, Q v * ‖J v‖) hΨ' hC fun y (hy : x ≤ y) b hb hgb ↦ by
    have hya := hx.trans_le hy
    have hJy := hΦ.mono_set (Ioi_subset_Ioi hy)
    rw [h_eq y hy]
    calc ‖∫ v in Ioi y, K y v • (J v + ψ v • h v)‖
        ≤ ∫ v in Ioi y, P y * (Q v * ‖J v‖ + Q v * ‖ψ v‖ * b v) := by
          refine norm_integral_le_of_norm_le ((hJy.add hgb).const_mul (P y)) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : y < v)
          have hQv := hQ0 v (hy.trans hv.le)
          refine (norm_kernel_smul_le hKle hya hv.le _).trans ?_
          gcongr P y * ?_
          · exact hP0 y hya
          calc Q v * ‖J v + ψ v • h v‖ ≤ Q v * (‖J v‖ + ‖ψ v‖ * b v) := by
                gcongr
                exact (norm_add_le _ _).trans (by rw [norm_smul]; gcongr; exact hb v hv)
            _ = _ := by ring
      _ = P y * ((∫ v in Ioi y, Q v * ‖J v‖) + ∫ v in Ioi y, Q v * ‖ψ v‖ * b v) := by
          rw [integral_const_mul, integral_add hJy hgb]
      _ ≤ P y * ((∫ v in Ioi x, Q v * ‖J v‖) + ∫ v in Ioi y, Q v * ‖ψ v‖ * b v) := by
          refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (hP0 y hya)
          exact setIntegral_mono_set hΦ ((ae_restrict_iff' measurableSet_Ioi).2
            (ae_of_all _ fun v (hv : x < v) ↦ mul_nonneg (hQ0 v hv.le) (norm_nonneg _)))
            (Ioi_subset_Ioi hy).eventuallySubset

/-- **Volterra integral equations, uniqueness among solutions with integrable integrands.** Let
`‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`, where `P ≥ 0` on `(a, ∞)`, and let
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for every `x > a`. Then two solutions `h₁`, `h₂`
of the Volterra equation `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` on `(a, ∞)` whose
integrands are integrable on `(x, ∞)`, and which are `O(P)` on `[x, ∞)`, for every `x > a`, agree
on `(a, ∞)`. -/
theorem volterra_solution_unique_of_integrableOn (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h₁ h₂ : ℝ → E}
    (h₁_int : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ K x v • (J v + ψ v • h₁ v)) (Ioi x))
    (h₂_int : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ K x v • (J v + ψ v • h₂ v)) (Ioi x))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_isBigO : ∀ x ∈ Ioi a, h₁ =O[𝓟 (Ici x)] P)
    (h₂_isBigO : ∀ x ∈ Ioi a, h₂ =O[𝓟 (Ici x)] P) :
    EqOn h₁ h₂ (Ioi a) := by
  intro x₀ (hx₀ : a < x₀)
  -- the difference solves the homogeneous equation
  have hd : ∀ y ∈ Ici x₀, (h₁ - h₂) y =
      ∫ v in Ioi y, K y v • ((0 : ℝ → E) v + ψ v • (h₁ - h₂) v) := fun y (hy : x₀ ≤ y) ↦ by
    have hya := hx₀.trans_le hy
    rw [Pi.sub_apply, h₁_eq y hya, h₂_eq y hya, ← integral_sub (h₁_int y hya) (h₂_int y hya)]
    refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
    simp only [Pi.sub_apply, Pi.zero_apply, zero_add, smul_sub, smul_add]
    abel
  -- so the bound with zero forcing gives `‖h₁ x₀ - h₂ x₀‖ ≤ 0`
  have hle := norm_volterra_solution_le_of_isBigO_principal_Ici hP0 hKle hx₀ hd (by simp)
    (hΨ x₀ hx₀) ((h₁_isBigO x₀ hx₀).sub (h₂_isBigO x₀ hx₀))
  simp only [Pi.zero_apply, norm_zero, mul_zero, integral_zero, zero_mul] at hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- **Volterra integral equations, uniqueness among measurable solutions.** Let
`‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`, where `P ≥ 0` on `(a, ∞)`, let `K x` be almost everywhere
strongly measurable on `(x, ∞)` for every `x > a` and `J`, `ψ` almost everywhere strongly
measurable on `(a, ∞)`, and let `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for every `x > a`. Then two solutions of the
Volterra equation `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that are almost everywhere
strongly measurable on `(a, ∞)` and `O(P)` on `[x, ∞)` for every
`x > a` agree on `(a, ∞)`. This is the uniqueness part of Olver, Chapter 6, Theorem 10.1, for
measurable rather than continuous data; compare `volterra_solution_unique`. -/
theorem volterra_solution_unique_of_aestronglyMeasurable (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hKm : ∀ x ∈ Ioi a, AEStronglyMeasurable (K x) (volume.restrict (Ioi x)))
    (hJm : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h₁ h₂ : ℝ → E}
    (h₁_meas : AEStronglyMeasurable h₁ (volume.restrict (Ioi a)))
    (h₂_meas : AEStronglyMeasurable h₂ (volume.restrict (Ioi a)))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_isBigO : ∀ x ∈ Ioi a, h₁ =O[𝓟 (Ici x)] P)
    (h₂_isBigO : ∀ x ∈ Ioi a, h₂ =O[𝓟 (Ici x)] P) :
    EqOn h₁ h₂ (Ioi a) := by
  have hint {h : ℝ → E} (hm : AEStronglyMeasurable h (volume.restrict (Ioi a)))
      (hh : ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] P) (x : ℝ) (hx : x ∈ Ioi a) :
      IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (Ioi x) :=
    have hsub : Ioi x ⊆ Ioi a := Ioi_subset_Ioi (le_of_lt hx)
    integrableOn_volterra_of_isBigO hP0 hKle hx (hKm x hx) (hJm.mono_set hsub)
      (hψm.mono_set hsub) (hΦ x hx) (hΨ x hx) (hm.mono_set hsub) (hh x hx)
  exact volterra_solution_unique_of_integrableOn hP0 hKle hΨ (hint h₁_meas h₁_isBigO)
    (hint h₂_meas h₂_isBigO) h₁_eq h₂_eq h₁_isBigO h₂_isBigO

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` of
`exists_volterra_solution` on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`, is `O(P)` on `[x, ∞)` for every `x > a`. -/
theorem isBigO_principal_Ici_of_norm_le_volterra_bound (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)) :
    ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] P := fun x (hx : a < x) ↦
  (isBigO_principal_iff_of_nonneg fun v (hv : x ≤ v) ↦ hP0 v (hx.trans_le hv)).2
    ⟨_, fun v (hv : x ≤ v) ↦ (hh v (hx.trans_le hv)).trans (mul_tail_le_of_le hP0 hQ0 hΦ hΨ
      (Real.exp_monotone.monotoneOn _) (fun _ _ ↦ (Real.exp_pos _).le) hx hv)⟩

end Ray

section Uniqueness

omit [NormedSpace ℝ E] in
/-- If `F` is continuous on `(a, ∞)` and `O(P)` at infinity, then `Q * ‖ψ • F‖` is integrable on
`(x, ∞)` for every `x > a`. -/
private lemma integrableOn_weight_smul_of_isBigO (hψ : ContinuousOn ψ (Ioi a))
    (hQ : ContinuousOn Q (Ioi a)) (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {F : ℝ → E}
    (hF : ContinuousOn F (Ioi a)) (hFP : F =O[atTop] P) {x : ℝ} (hx : a < x) :
    IntegrableOn (fun v ↦ Q v * ‖ψ v • F v‖) (Ioi x) := by
  obtain ⟨C, hC⟩ := hFP.bound
  obtain ⟨N, hN⟩ := eventually_atTop.1 hC
  have hxM : x ≤ max N x := le_max_right _ _
  -- on the compact piece `[x, max N x]` use continuity, beyond it the bound `‖F v‖ ≤ C * P v`
  rw [← Ioc_union_Ioi_eq_Ioi hxM]
  refine IntegrableOn.union ?_ (integrableOn_weight_smul hψ hQ hQ0 hΨ hF (hx.trans_le hxM)
    (C := C) fun v (hv : max N x < v) ↦ ?_)
  · exact ((hQ.mul (hψ.smul hF).norm).mono
      ((Icc_subset_Ioi_iff hxM).2 hx)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · have := hN v ((le_max_left _ _).trans hv.le)
    rwa [Real.norm_of_nonneg (hP0 v ((hx.trans_le hxM).trans hv))] at this

omit [NormedSpace ℝ E] in
/-- If `F` is continuous on `(a, ∞)` and `O(P)` at infinity, then the weight
`Q * ‖J + ψ • F‖` of the Volterra integrand is integrable on `(x, ∞)` for every `x > a`. -/
private lemma integrableOn_weight_add_of_isBigO (hJ : ContinuousOn J (Ioi a))
    (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a)) (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {F : ℝ → E}
    (hF : ContinuousOn F (Ioi a)) (hFP : F =O[atTop] P) {x : ℝ} (hx : a < x) :
    IntegrableOn (fun v ↦ Q v * ‖J v + ψ v • F v‖) (Ioi x) := by
  refine Integrable.mono'
    ((hΦ x hx).add (integrableOn_weight_smul_of_isBigO hψ hQ hP0 hQ0 hΨ hF hFP hx))
    (((hQ.mul (hJ.add (hψ.smul hF)).norm).mono (Ioi_subset_Ioi hx.le)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
  have hQv := hQ0 v (hx.trans hv)
  rw [Real.norm_of_nonneg (mul_nonneg hQv (norm_nonneg _)), Pi.add_apply, ← mul_add]
  grw [norm_add_le]

/-- **Volterra integral equations, uniqueness.** Under the hypotheses of
`exists_volterra_solution`, two solutions of `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that
are continuous on `(a, ∞)` and `O(P)` at infinity coincide on `(a, ∞)`. -/
theorem volterra_solution_unique (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h₁ h₂ : ℝ → E}
    (h₁_cont : ContinuousOn h₁ (Ioi a)) (h₂_cont : ContinuousOn h₂ (Ioi a))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_isBigO : h₁ =O[atTop] P) (h₂_isBigO : h₂ =O[atTop] P) : EqOn h₁ h₂ (Ioi a) := by
  have hdint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v • (h₁ v - h₂ v)‖) (Ioi x) :=
    fun x hx ↦ integrableOn_weight_smul_of_isBigO hψ hQ hP0 hQ0 hΨ (h₁_cont.sub h₂_cont)
      (h₁_isBigO.sub h₂_isBigO) hx
  -- the difference solves the homogeneous equation
  have hd : ∀ x ∈ Ioi a, h₁ x - h₂ x = ∫ v in Ioi x, K x v • ψ v • (h₁ v - h₂ v) := by
    intro x hx
    have hint {h : ℝ → E} (hc : ContinuousOn h (Ioi a)) (hO : h =O[atTop] P) :
        IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (Ioi x) :=
      integrableOn_kernel_smul hK hKle (hJ.add (hψ.smul hc)) hx
        (integrableOn_weight_add_of_isBigO hJ hψ hQ hP0 hQ0 hΦ hΨ hc hO hx)
    rw [h₁_eq x hx, h₂_eq x hx,
      ← integral_sub (hint h₁_cont h₁_isBigO) (hint h₂_cont h₂_isBigO)]
    simp only [← smul_sub, add_sub_add_left_eq_sub]
  intro x₀ (hx₀ : a < x₀)
  -- by the equation, `‖h₁ v - h₂ v‖ ≤ C * P v` beyond `x₀`, so the difference is `O(P)` there
  have hO : (fun v ↦ h₁ v - h₂ v) =O[𝓟 (Ici x₀)] P := by
    refine (isBigO_principal_iff_of_nonneg fun v (hv : x₀ ≤ v) ↦ hP0 v (hx₀.trans_le hv)).2
      ⟨∫ v in Ioi x₀, Q v * ‖ψ v • (h₁ v - h₂ v)‖, fun v (hv : x₀ ≤ v) ↦ ?_⟩
    have hva : a < v := hx₀.trans_le hv
    change ‖h₁ v - h₂ v‖ ≤ _
    rw [hd v hva]
    refine (norm_integral_kernel_smul_le hKle hva (hdint v hva)).trans
      ((mul_le_mul_of_nonneg_left (setIntegral_mono_set (hdint x₀ hx₀) ?_
        (Ioi_subset_Ioi hv).eventuallySubset) (hP0 v hva)).trans_eq (mul_comm _ _))
    exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : x₀ < u) ↦
      mul_nonneg (hQ0 u (hx₀.trans hu)) (norm_nonneg _))
  -- so the bound with zero forcing gives `‖h₁ x₀ - h₂ x₀‖ ≤ 0`
  have hle := norm_volterra_solution_le_of_isBigO_principal_Ici (J := 0) hP0 hKle hx₀
    (fun y (hy : x₀ ≤ y) ↦ (hd y (hx₀.trans_le hy)).trans
      (by simp only [Pi.zero_apply, zero_add]))
    (by simp) (hΨ x₀ hx₀) hO
  simp only [Pi.zero_apply, norm_zero, mul_zero, integral_zero, zero_mul] at hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` of `exists_volterra_solution`
on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`,
is `O(P)` at infinity. -/
theorem isBigO_of_norm_le_volterra_bound (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x) (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)) :
    h =O[atTop] P :=
  (isBigO_principal_Ici_of_norm_le_volterra_bound hP0 hQ0 hΦ hΨ hh (a + 1)
    (lt_add_one a)).mono (le_principal_iff.2 (Ici_mem_atTop _))

/-- **Volterra integral equations, bound.** Under the hypotheses of `exists_volterra_solution`,
every solution of `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)`
and `O(P)` at infinity satisfies `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x > a`, where
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`. -/
theorem norm_volterra_solution_le [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hP : ContinuousOn P (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) * Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨h₀, h₀_cont, h₀_eq, h₀_le⟩ :=
    exists_volterra_solution hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  rw [volterra_solution_unique hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ h_cont h₀_cont h_eq h₀_eq h_isBigO
    (isBigO_of_norm_le_volterra_bound hP0 hQ0 hΦ hΨ h₀_le) hx]
  exact h₀_le x hx

/-- **Volterra integral equations, existence and uniqueness.** Under the hypotheses of
`exists_volterra_solution`, the equation `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has, on
`(a, ∞)`, exactly one solution that is continuous there and `O(P)` at infinity: the restrictions
to `(a, ∞)` of all such solutions `h : ℝ → E` coincide. Values outside `(a, ∞)` are not
constrained by the equation, so uniqueness is stated for the restriction. -/
theorem existsUnique_volterra_solution [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hP : ContinuousOn P (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) :
    ∃! g : Ioi a → E, ∃ h : ℝ → E, (Ioi a).domRestrict h = g ∧ ContinuousOn h (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧ h =O[atTop] P := by
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ :=
    exists_volterra_solution hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hh_isBigO := isBigO_of_norm_le_volterra_bound hP0 hQ0 hΦ hΨ hh_le
  refine ⟨(Ioi a).domRestrict h, ⟨h, rfl, hh_cont, hh_eq, hh_isBigO⟩, ?_⟩
  rintro _ ⟨h', rfl, hh'_cont, hh'_eq, hh'_isBigO⟩
  funext x
  exact volterra_solution_unique hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh'_cont hh_cont hh'_eq hh_eq
    hh'_isBigO hh_isBigO x.property

end Uniqueness

/-! ### The sharper bound when the forcing is dominated by the coefficient -/

/-- **Volterra integral equations, sharper bound on a ray.** Let `‖K x v‖ ≤ Q v` for
`a < x ≤ v` and `‖J v‖ ≤ ‖ψ v‖` for `v > a`, and let `x > a` be such that
`Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖` converges. Then every solution of the Volterra equation
`h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v)` on `[x, ∞)` that is bounded on `[x, ∞)`
satisfies `‖h x‖ ≤ exp (Φ x) - 1`.

This is Olver's sharper bound `|h(x)| ≤ e^{P₀ Φ(x)} - 1` for a constant `P = P₀` and `J = ψ`
(Chapter 6, Theorem 10.1), with the constant `P₀` absorbed into `Q`; the form with `P₀` for
continuous solutions on `(a, ∞)` is `norm_volterra_solution_le_exp_sub_one`. When
`‖J v‖ = ‖ψ v‖`, for example when `J = ψ`, it improves on the bound `Φ x * exp (Φ x)` that
`norm_volterra_solution_le_of_isBigO_principal_Ici` gives with `P = 1`, since `e^t - 1 ≤ t e^t`
for `t ≥ 0`. For a forcing `J` with `‖J v‖ < ‖ψ v‖` the comparison is with that bound after
replacing `‖J‖` by `‖ψ‖`, which only enlarges it; the general bound itself can then be smaller,
for example `0` when `J = 0`. -/
theorem norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖) {x : ℝ}
    (hx : a < x) {h : ℝ → E}
    (h_eq : ∀ y ∈ Ici x, h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v))
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x))
    (h_isBigO : h =O[𝓟 (Ici x)] fun _ ↦ (1 : ℝ)) :
    ‖h x‖ ≤ Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  obtain ⟨C, hC⟩ := isBigO_principal.1 h_isBigO
  -- Grönwall's inequality applies to `1 + ‖h‖`, with `P = 1`
  have hle := le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi (u := fun y ↦ 1 + ‖h y‖)
    (P := fun _ ↦ 1)
    (g := fun v ↦ Q v * ‖ψ v‖) (A := 1) (C := 1 + C) (by simpa only [one_mul] using hΦ)
    (fun y hy ↦ by have := hC y hy; rw [norm_one, mul_one] at this; linarith)
    fun y (hy : x ≤ y) b hb hgb ↦ by
    have hya := hx.trans_le hy
    rw [one_mul, h_eq y hy]
    gcongr
    refine norm_integral_le_of_norm_le hgb ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : y < v)
    have hKv := hKle y v hya hv.le
    have hQv : 0 ≤ Q v := (norm_nonneg _).trans hKv
    have hF : ‖J v + ψ v • h v‖ ≤ ‖ψ v‖ * (1 + ‖h v‖) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, mul_add, mul_one]
      gcongr
      exact hJψ v (hya.trans hv)
    rw [norm_smul, mul_assoc]
    exact mul_le_mul hKv (hF.trans (by gcongr; exact hb v hv)) (norm_nonneg _) hQv
  simp only [one_mul] at hle
  linarith

/-- **Volterra integral equations, sharper bound.** If the kernel bound is
`‖K x v‖ ≤ P₀ * Q v` with a constant `P₀`, and the forcing is dominated by the coefficient,
`‖J v‖ ≤ ‖ψ v‖` (for instance `J = ψ` when `E = 𝕜`), then every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and bounded at
infinity satisfies `‖h x‖ ≤ exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1` for every `x > a`.
For `J = ψ` this sharpens the bound of `norm_volterra_solution_le`, which then reads
`‖h x‖ ≤ P₀ Φ x * exp (P₀ Φ x)` with `Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖`. -/
theorem norm_volterra_solution_le_exp_sub_one {P₀ : ℝ}
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P₀ * Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hψint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] fun _ ↦ (1 : ℝ)) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  -- `h` is bounded on `[x, ∞)`, and the bound on a ray applies with the weight `P₀ * Q`
  have hb : h =O[𝓟 (Ici x)] fun _ ↦ (1 : ℝ) :=
    h_isBigO.isBigO_principal_Ici_of_continuousOn (h_cont.mono (Ici_subset_Ioi.2 hx))
      continuousOn_const fun _ _ ↦ by simp
  have hint : IntegrableOn (fun v ↦ P₀ * Q v * ‖ψ v‖) (Ioi x) := by
    have := (hψint x hx).const_mul P₀
    simp only [← mul_assoc] at this
    exact this
  have hle := norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici
    (Q := fun v ↦ P₀ * Q v) hKle hJψ hx (fun y hy ↦ h_eq y (lt_of_lt_of_le hx hy)) hint hb
  simp_rw [mul_assoc] at hle
  rwa [integral_const_mul] at hle

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ exp (Φ x) - 1` of
`norm_volterra_solution_le_exp_sub_one` on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖`
with `Q ≥ 0`, is bounded on `[x, ∞)` for every `x > a`. -/
theorem isBigO_one_of_norm_le_exp_sub_one (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1) :
    ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] fun _ ↦ (1 : ℝ) := fun x (hx : a < x) ↦
  isBigO_principal.2 ⟨Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1, fun v (hv : x ≤ v) ↦ by
    rw [norm_one, mul_one]
    refine (hh v (hx.trans_le hv)).trans ?_
    gcongr Real.exp ?_ - 1
    exact antitoneOn_integral_Ioi (fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _)) hΦ hx
      (hx.trans_le hv) hv⟩

/-- **Volterra integral equations, existence with the sharper bound.** Let `K` be continuous on
`{(x, v) | a < x ≤ v}` with `‖K x v‖ ≤ Q v` there, where `Q` is continuous on `(a, ∞)`, and let
`J`, `ψ` be continuous on `(a, ∞)` with `‖J v‖ ≤ ‖ψ v‖` there and
`Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖` convergent for every `x > a`. Then the Volterra equation
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has a solution, continuous on `(a, ∞)`, such that
`‖h x‖ ≤ exp (Φ x) - 1` for every `x > a`. -/
theorem exists_volterra_solution_exp_sub_one [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x)) :
    ∃ h : ℝ → E, ContinuousOn h (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioi a, ‖h x‖ ≤ Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  have hQ0 : ∀ v ∈ Ioi a, 0 ≤ Q v := fun v (hv : a < v) ↦
    (norm_nonneg _).trans (hKle v v hv le_rfl)
  -- the general theory applies with `P = 1`
  have hP0 : ∀ x ∈ Ioi a, (0 : ℝ) ≤ (fun _ : ℝ ↦ (1 : ℝ)) x := fun _ _ ↦ zero_le_one
  have hKle' : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ (fun _ : ℝ ↦ (1 : ℝ)) x * Q v :=
    fun x v hx hv ↦ (hKle x v hx hv).trans_eq (one_mul _).symm
  have hΦJ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x) := fun x (hx : a < x) ↦ by
    refine (hΦ x hx).mono' (((hQ.mul hJ.norm).mono (Ioi_subset_Ioi hx.le)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
    have hQv := hQ0 v (hx.trans hv)
    rw [Real.norm_of_nonneg (mul_nonneg hQv (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hJψ v (hx.trans hv)) hQv
  have hΨ : ∀ x ∈ Ioi a,
      IntegrableOn (fun v ↦ (fun _ : ℝ ↦ (1 : ℝ)) v * Q v * ‖ψ v‖) (Ioi x) := fun x hx ↦ by
    simpa only [one_mul] using hΦ x hx
  obtain ⟨h, h_cont, h_eq, h_le⟩ :=
    exists_volterra_solution hK hJ hψ continuousOn_const hQ hP0 hQ0 hKle' hΦJ hΨ (E := E)
  exact ⟨h, h_cont, h_eq, fun x hx ↦
    norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici hKle hJψ hx
    (fun y hy ↦ h_eq y (lt_of_lt_of_le hx hy)) (hΦ x hx)
    (isBigO_principal_Ici_of_norm_le_volterra_bound hP0 hQ0 hΦJ hΨ h_le x hx)⟩

section Derivative

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}

omit [NormedSpace ℝ E] [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] in
/-- For `a < c ≤ y`, the function `(s, v) ↦ K₁ s v • F v`, cut off to `a < s ≤ v`, is integrable
on `(c, y] × (c, ∞)`: there it is dominated by `M * (Q v * ‖F v‖)`, with `M` a bound for `P₁`
on `[c, y]`. -/
private lemma integrable_indicator_kernel_smul_prod
    (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x) {F : ℝ → E} (hF : ContinuousOn F (Ioi a))
    (hFint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖F v‖) (Ioi x)) {c y : ℝ} (hc : a < c)
    (hcy : c ≤ y) :
    Integrable ({p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2}.indicator fun p ↦ K₁ p.1 p.2 • F p.2)
      ((volume.restrict (Ioc c y)).prod (volume.restrict (Ioi c))) := by
  have hS : MeasurableSet {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  have hG : ContinuousOn (fun p : ℝ × ℝ ↦ K₁ p.1 p.2 • F p.2) {p | a < p.1 ∧ p.1 ≤ p.2} :=
    hK₁.smul (hF.comp continuous_snd.continuousOn fun p hp ↦ hp.1.trans_le hp.2)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hP₁.mono ((Icc_subset_Ioi_iff hcy).2 hc))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c ⟨le_rfl, hcy⟩)
  refine Integrable.mono' (((continuousOn_const (c := M)).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self).mul_prod (hFint c hc))
    ((aestronglyMeasurable_indicator_iff hS).2 (hG.aestronglyMeasurable hS)) ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
  obtain ⟨⟨hp₁, hp₁'⟩, hp₂⟩ := hp
  have hQF : 0 ≤ Q p.2 * ‖F p.2‖ := mul_nonneg (hQ0 _ (hc.trans hp₂)) (norm_nonneg _)
  by_cases hpS : p ∈ {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2}
  · rw [indicator_of_mem hpS, norm_smul]
    calc ‖K₁ p.1 p.2‖ * ‖F p.2‖ ≤ P₁ p.1 * Q p.2 * ‖F p.2‖ :=
          mul_le_mul_of_nonneg_right (hK₁le _ _ hpS.1 hpS.2) (norm_nonneg _)
      _ ≤ M * (Q p.2 * ‖F p.2‖) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right
            ((Real.le_norm_self _).trans (hM p.1 ⟨hp₁.le, hp₁'⟩)) hQF
  · rw [indicator_of_notMem hpS, norm_zero]
    exact mul_nonneg hM0 hQF

/-- Let `K` vanish on the diagonal, with partial derivative `K₁` in its first variable. For
`a < c ≤ y` and `v > c`, integrating `K₁ s v • F v` over `c < s ≤ min y v` gives
`K y v • F v - K c v • F v` when `v > y`, and `-K c v • F v` when `v ≤ y`. -/
private lemma integral_Ioc_indicator_kernel_smul [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2}) (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
    (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x) {F : ℝ → E}
    {c y v : ℝ} (hc : a < c) (hcy : c ≤ y) (hv : c < v) :
    ∫ s in Ioc c y,
        {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2}.indicator (fun p ↦ K₁ p.1 p.2 • F p.2) (s, v) =
      (Ioi y).indicator (fun v ↦ K y v • F v) v - K c v • F v := by
  have hm : c ≤ y ⊓ v := le_inf hcy hv.le
  have hmv : y ⊓ v ≤ v := inf_le_right
  have hmem (s : ℝ) (hs : s ∈ Icc c (y ⊓ v)) : (s, v) ∈ {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2} :=
    ⟨hc.trans_le hs.1, hs.2.trans hmv⟩
  have hFTC : ∫ s in c..y ⊓ v, K₁ s v • F v = K (y ⊓ v) v • F v - K c v • F v :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun s ↦ K s v • F v) hm
      ((hK.comp ((continuous_id.prodMk continuous_const).continuousOn (s := Icc c (y ⊓ v)))
        hmem).smul continuousOn_const)
      (fun s hs ↦ (hKderiv s v (hc.trans hs.1) (hs.2.trans_le hmv)).smul_const (F v))
      (ContinuousOn.intervalIntegrable_of_Icc hm ((hK₁.comp
        ((continuous_id.prodMk continuous_const).continuousOn (s := Icc c (y ⊓ v)))
        hmem).smul continuousOn_const))
  calc _ = ∫ s in Ioc c y, (Iic v).indicator (fun s ↦ K₁ s v • F v) s := by
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
        simp only [indicator_apply, mem_ofPred_eq, mem_Iic, hc.trans hs.1, true_and]
    _ = K (y ⊓ v) v • F v - K c v • F v := by
        rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
          ← intervalIntegral.integral_of_le hm, hFTC]
    _ = _ := by
        rcases le_or_gt v y with hvy | hyv
        · rw [inf_of_le_right hvy, hKdiag v (hc.trans hv), zero_smul,
            indicator_of_notMem (not_lt.2 hvy)]
        · rw [inf_of_le_left hyv.le, indicator_of_mem hyv]

/-- Let `K` vanish on the diagonal, with partial derivative `K₁` in its first variable. For
`a < c ≤ y`, the difference of `x ↦ ∫ v in Ioi x, K x v • F v` between `y` and `c` is the integral
over `(c, y]` of `s ↦ ∫ v in Ioi s, K₁ s v • F v`. -/
private lemma integral_Ioc_integral_kernel_smul [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
    (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x) {F : ℝ → E} (hF : ContinuousOn F (Ioi a))
    (hFint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖F v‖) (Ioi x)) {c y : ℝ} (hc : a < c)
    (hcy : c ≤ y) :
    ∫ s in Ioc c y, ∫ v in Ioi s, K₁ s v • F v =
      (∫ v in Ioi y, K y v • F v) - ∫ v in Ioi c, K c v • F v := by
  -- write both sides as iterated integrals over `(c, y] × (c, ∞)` and swap the order
  calc ∫ s in Ioc c y, ∫ v in Ioi s, K₁ s v • F v
      = ∫ s in Ioc c y, ∫ v in Ioi c,
          {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2}.indicator (fun p ↦ K₁ p.1 p.2 • F p.2) (s, v) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
        have hcs : c < s := hs.1
        have hind (v : ℝ) : {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2}.indicator
            (fun p ↦ K₁ p.1 p.2 • F p.2) (s, v) = (Ici s).indicator (fun v ↦ K₁ s v • F v) v := by
          simp only [indicator_apply, mem_ofPred_eq, mem_Ici, hc.trans hcs, true_and]
        simp only [hind]
        rw [setIntegral_indicator measurableSet_Ici, inter_eq_right.2 (Ici_subset_Ioi.2 hcs),
          integral_Ici_eq_integral_Ioi]
    _ = ∫ v in Ioi c, ∫ s in Ioc c y,
          {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2}.indicator (fun p ↦ K₁ p.1 p.2 • F p.2) (s, v) :=
        integral_integral_swap
          (integrable_indicator_kernel_smul_prod hK₁ hP₁ hK₁le hQ0 hF hFint hc hcy)
    _ = ∫ v in Ioi c, ((Ioi y).indicator (fun v ↦ K y v • F v) v - K c v • F v) :=
        setIntegral_congr_fun measurableSet_Ioi fun v (hv : c < v) ↦
          integral_Ioc_indicator_kernel_smul hK hKdiag hK₁ hKderiv hc hcy hv
    _ = _ := by
        rw [integral_sub (((integrableOn_kernel_smul hK hKle hF (hc.trans_le hcy)
            (hFint y (hc.trans_le hcy))).integrable_indicator measurableSet_Ioi).integrableOn)
          (integrableOn_kernel_smul hK hKle hF hc (hFint c hc)),
          setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.2 hcy]

/-- Let `K` vanish on the diagonal, with partial derivative `K₁` in its first variable bounded by
`P₁ x * Q v`. Then `x ↦ ∫ v in Ioi x, K x v • F v` has derivative `∫ v in Ioi x, K₁ x v • F v`
at every `x > a`. -/
private lemma hasDerivAt_integral_kernel_smul [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
    (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x) {F : ℝ → E} (hF : ContinuousOn F (Ioi a))
    (hFint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖F v‖) (Ioi x)) {x : ℝ} (hx : a < x) :
    HasDerivAt (fun y ↦ ∫ v in Ioi y, K y v • F v) (∫ v in Ioi x, K₁ x v • F v) x := by
  obtain ⟨c, hac, hcx⟩ := exists_between hx
  have hH : ContinuousOn (fun s ↦ ∫ v in Ioi s, K₁ s v • F v) (Ioi a) :=
    continuousOn_integral_kernel_smul hK₁ hK₁le hP₁ hQ0 hF hFint
  refine ((intervalIntegral.integral_hasDerivAt_right
    ((hH.mono ((Icc_subset_Ioi_iff hcx.le).2 hac)).intervalIntegrable_of_Icc hcx.le)
    (hH.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hH.continuousAt (Ioi_mem_nhds hx))).const_add
    (∫ v in Ioi c, K c v • F v)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hcx] with y (hy : c < y)
  rw [intervalIntegral.integral_of_le hy.le, integral_Ioc_integral_kernel_smul hK hKle hKdiag hK₁
    hKderiv hP₁ hK₁le hQ0 hF hFint hac hy.le]
  abel

/-- **Volterra integral equations, derivative.** Under the hypotheses of
`exists_volterra_solution`, let `K` vanish on the diagonal and have a partial derivative `K₁` in
its first variable for `a < x < v`, continuous on `{(x, v) | a < x ≤ v}` with
`‖K₁ x v‖ ≤ P₁ x * Q v` there, where `P₁` is continuous on `(a, ∞)`. Then every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and `O(P)` at
infinity has derivative `∫ v in Ioi x, K₁ x v • (J v + ψ v • h v)` at every `x > a`. -/
theorem hasDerivAt_volterra_solution [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0) (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {h : ℝ → E} (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) {x : ℝ} (hx : x ∈ Ioi a) :
    HasDerivAt h (∫ v in Ioi x, K₁ x v • (J v + ψ v • h v)) x := by
  refine (hasDerivAt_integral_kernel_smul (F := fun v ↦ J v + ψ v • h v) hK hKle hKdiag hK₁
    hKderiv hP₁ hK₁le hQ0 (hJ.add (hψ.smul h_cont)) (fun y hy ↦
      integrableOn_weight_add_of_isBigO hJ hψ hQ hP0 hQ0 hΦ hΨ h_cont h_isBigO hy)
      hx).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy using h_eq y hy

/-- **Volterra integral equations, regularity.** Under the hypotheses of
`hasDerivAt_volterra_solution`, every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and `O(P)` at
infinity is continuously differentiable on `(a, ∞)`. -/
theorem contDiffOn_volterra_solution [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0) (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {h : ℝ → E} (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) : ContDiffOn ℝ 1 h (Ioi a) := by
  have hd {x : ℝ} (hx : x ∈ Ioi a) := hasDerivAt_volterra_solution hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ
    hKdiag hK₁ hKderiv hP₁ hK₁le h_cont h_eq h_isBigO hx
  rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi,
    contDiffOn_zero]
  refine ⟨fun x hx ↦ (hd hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  exact (continuousOn_integral_kernel_smul (F := fun v ↦ J v + ψ v • h v) hK₁ hK₁le hP₁ hQ0
    (hJ.add (hψ.smul h_cont))
    fun y hy ↦ integrableOn_weight_add_of_isBigO hJ hψ hQ hP0 hQ0 hΦ hΨ h_cont h_isBigO
      hy).congr fun x hx ↦ (hd hx).deriv

/-- **Volterra integral equations, derivative bound.** Under the hypotheses of
`hasDerivAt_volterra_solution`, and with `P₁ ≥ 0`, every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and `O(P)` at
infinity satisfies `‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)` for every `x > a`, where
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`. -/
theorem norm_deriv_volterra_solution_le [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hP : ContinuousOn P (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0) (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hP₁0 : ∀ x ∈ Ioi a, 0 ≤ P₁ x)
    (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {h : ℝ → E} (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖deriv h x‖ ≤
      P₁ x * (∫ v in Ioi x, Q v * ‖J v‖) * Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  have hx' : a < x := hx
  have hFint := integrableOn_weight_add_of_isBigO hJ hψ hQ hP0 hQ0 hΦ hΨ h_cont h_isBigO hx'
  have hψh := integrableOn_weight_smul_of_isBigO hψ hQ hP0 hQ0 hΨ h_cont h_isBigO hx'
  rw [(hasDerivAt_volterra_solution hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hKdiag hK₁ hKderiv hP₁ hK₁le
    h_cont h_eq h_isBigO hx).deriv, mul_assoc]
  refine (norm_integral_kernel_smul_le hK₁le hx' hFint).trans
    (mul_le_mul_of_nonneg_left ?_ (hP₁0 x hx))
  set Φx := ∫ v in Ioi x, Q v * ‖J v‖
  -- split off the forcing term, then bound `‖h v‖` by `P v * Φ x * exp (Ψ v)`
  have hsplit : ∫ v in Ioi x, Q v * ‖J v + ψ v • h v‖ ≤
      Φx + ∫ v in Ioi x, Q v * ‖ψ v • h v‖ := by
    rw [← integral_add (hΦ x hx) hψh]
    refine setIntegral_mono_on hFint ((hΦ x hx).add hψh) measurableSet_Ioi fun v (hv : x < v) ↦ ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (hQ0 v (hx'.trans hv))
  have hexp : ∫ v in Ioi x, Q v * ‖ψ v • h v‖ ≤
      Φx * (Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖) - 1) := by
    rw [← (hΨ x hx).integral_Ioi_mul_exp_integral_Ioi]
    refine integral_weight_smul_le_comp hQ0 hΨ Real.continuous_exp hx' hψh fun v (hv : x < v) ↦ ?_
    have hva : a < v := hx'.trans hv
    have hΦle : ∫ u in Ioi v, Q u * ‖J u‖ ≤ Φx :=
      antitoneOn_integral_Ioi (forcing_weight_nonneg hQ0 le_rfl) hΦ hx' hva hv.le
    have := hP0 v hva
    calc ‖h v‖
        ≤ P v * (∫ u in Ioi v, Q u * ‖J u‖) * Real.exp (∫ u in Ioi v, P u * Q u * ‖ψ u‖) :=
          norm_volterra_solution_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ h_cont h_eq h_isBigO hva
      _ ≤ P v * Φx * Real.exp (∫ u in Ioi v, P u * Q u * ‖ψ u‖) := by grw [hΦle]
      _ = Φx * P v * Real.exp (∫ u in Ioi v, P u * Q u * ‖ψ u‖) := by ring
  calc _ ≤ Φx + Φx * (Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖) - 1) :=
        by linarith
    _ = Φx * Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖) := by ring

end Derivative

end TauCeti
