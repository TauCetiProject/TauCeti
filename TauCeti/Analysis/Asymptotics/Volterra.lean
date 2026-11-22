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
import Mathlib.Topology.Algebra.Order.Floor
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
`P x * Φ x * exp (Ψ x)` when `J = ψ`. The existence and error-bound theorems for
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
* `TauCeti.norm_volterra_solution_le_exp_sub_one`: the bound
  `‖h x‖ ≤ exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1` for a constant `P = P₀`, `‖J‖ ≤ ‖ψ‖` and
  `h` bounded at infinity, which sharpens the general bound when `J = ψ`.
* `TauCeti.hasDerivAt_volterra_solution`, `TauCeti.contDiffOn_volterra_solution` and
  `TauCeti.norm_deriv_volterra_solution_le`: the derivative
  `h' x = ∫ v in Ioi x, K₁ x v • (J v + ψ v • h v)`, the `C¹` regularity of `h`, and the bound
  `‖h' x‖ ≤ P₁ x * Φ x * exp (Ψ x)`.

A solution is constructed as the sum of the Picard increments (the Liouville–Neumann series).
The `k`-th increment is bounded by
`P x * Φ x * Ψ x ^ k / k!`, by the identity `∫ v in Ioi x, g v * Ψ v ^ k = Ψ x ^ (k + 1) / (k + 1)`
for `Ψ` the tail integral of `g` (`MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`).
The same estimate, iterated, shows that the difference of two `O(P)` solutions is at most
`C * P x * Ψ x ^ k / k!` for every `k`, hence zero. The derivative of
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
/-- If `F` is continuous on `(a, ∞)` and `Q * ‖F‖` is integrable on `(x, ∞)`, then so is
`v ↦ K x v • F v`. -/
private lemma integrableOn_kernel_smul
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E}
    (hF : ContinuousOn F (Ioi a)) {x : ℝ} (hx : a < x)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖F v‖) (Ioi x)) :
    IntegrableOn (fun v ↦ K x v • F v) (Ioi x) := by
  have hKx : ContinuousOn (fun v ↦ K x v) (Ioi x) :=
    hK.comp (continuous_const.prodMk continuous_id).continuousOn fun v hv ↦ ⟨hx, le_of_lt hv⟩
  refine Integrable.mono' (hFint.const_mul (P x))
    ((hKx.smul (hF.mono (Ioi_subset_Ioi hx.le))).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact norm_kernel_smul_le hKle hx (le_of_lt hv) _

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
/-- If `‖F v‖ ≤ C * P v * Ψ v ^ k / k!` for `v > x`, where `Ψ v = ∫ u in Ioi v, P u * Q u * ‖ψ u‖`
is the coefficient tail integral, then the weighted integral
`∫ v in Ioi x, Q v * ‖ψ v • F v‖` is at most `C * Ψ x ^ (k + 1) / (k + 1)!`. -/
private lemma integral_weight_smul_le {F : ℝ → E} {x C : ℝ} (k : ℕ) (hx : a < x)
    (hFint : IntegrableOn (fun v ↦ Q v * ‖ψ v • F v‖) (Ioi x))
    (hFle : ∀ v ∈ Ioi x, ‖F v‖ ≤ C * P v * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k / k !) :
    ∫ v in Ioi x, Q v * ‖ψ v • F v‖ ≤
      C * (∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)! := by
  calc ∫ v in Ioi x, Q v * ‖ψ v • F v‖
      ≤ ∫ v in Ioi x, C / k ! *
          (P v * Q v * ‖ψ v‖ * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k) := by
        refine setIntegral_mono_on hFint (((hΨ x hx).mul_pow_integral_Ioi k).const_mul _)
          measurableSet_Ioi fun v (hv : x < v) ↦ ?_
        have hQψ : 0 ≤ Q v * ‖ψ v‖ := mul_nonneg (hQ0 v (hx.trans hv)) (norm_nonneg _)
        rw [norm_smul, ← mul_assoc]
        calc Q v * ‖ψ v‖ * ‖F v‖
            ≤ Q v * ‖ψ v‖ * (C * P v * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k / k !) := by
              grw [hFle v hv]
          _ = _ := by ring
    _ = C * (∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)! := by
        rw [integral_const_mul, (hΨ x hx).integral_Ioi_mul_pow_integral_Ioi k,
          Nat.factorial_succ]
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
  set C := ∫ v in Ioi x₀, Q v * ‖ψ v • (h₁ v - h₂ v)‖
  -- beyond `x₀`, the iterated estimates give `‖h₁ v - h₂ v‖ ≤ C * P v * Ψ v ^ k / k!`
  have hiter : ∀ k : ℕ, ∀ v, x₀ ≤ v →
      ‖h₁ v - h₂ v‖ ≤ C * P v * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ k / k ! := by
    intro k
    induction k with
    | zero =>
      intro v hv
      have hva : a < v := hx₀.trans_le hv
      suffices ‖h₁ v - h₂ v‖ ≤ P v * C by simpa [mul_comm C] using this
      rw [hd v hva]
      refine (norm_integral_kernel_smul_le hKle hva (hdint v hva)).trans
        (mul_le_mul_of_nonneg_left (setIntegral_mono_set (hdint x₀ hx₀) ?_
          (Ioi_subset_Ioi hv).eventuallySubset) (hP0 v hva))
      exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : x₀ < u) ↦
        mul_nonneg (hQ0 u (hx₀.trans hu)) (norm_nonneg _))
    | succ k ih =>
      intro v hv
      have hva : a < v := hx₀.trans_le hv
      rw [hd v hva]
      refine (norm_integral_kernel_smul_le hKle hva (hdint v hva)).trans ?_
      calc P v * ∫ u in Ioi v, Q u * ‖ψ u • (h₁ u - h₂ u)‖
          ≤ P v * (C * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)!) :=
            mul_le_mul_of_nonneg_left (integral_weight_smul_le hQ0 hΨ k hva (hdint v hva)
              fun u (hu : v < u) ↦ ih u (hv.trans hu.le)) (hP0 v hva)
        _ = C * P v * (∫ u in Ioi v, P u * Q u * ‖ψ u‖) ^ (k + 1) / (k + 1)! := by ring
  have hlim : Tendsto (fun k : ℕ ↦
      C * P x₀ * ((∫ u in Ioi x₀, P u * Q u * ‖ψ u‖) ^ k / k !)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (FloorSemiring.tendsto_pow_div_factorial_atTop
      (∫ u in Ioi x₀, P u * Q u * ‖ψ u‖)).const_mul (C * P x₀)
  refine sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim fun k ↦ ?_))
  rw [← mul_div_assoc]
  exact hiter k x₀ le_rfl

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` of `exists_volterra_solution`
on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`,
is `O(P)` at infinity. -/
theorem isBigO_of_norm_le_volterra_bound (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x) (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)) :
    h =O[atTop] P := by
  refine IsBigO.of_bound ((∫ v in Ioi (a + 1), Q v * ‖J v‖) *
    Real.exp (∫ v in Ioi (a + 1), P v * Q v * ‖ψ v‖)) ?_
  filter_upwards [eventually_ge_atTop (a + 1)] with x hx
  have hxa : a < x := (lt_add_one a).trans_le hx
  rw [Real.norm_of_nonneg (hP0 x hxa)]
  exact (hh x hxa).trans (mul_tail_le_of_le hP0 hQ0 hΦ hΨ (Real.exp_monotone.monotoneOn _)
    (fun _ _ ↦ (Real.exp_pos _).le) (lt_add_one a) hx)

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

end Uniqueness

section ConstantBound

variable {P₀ : ℝ}

/-- When `P` is a constant `P₀ > 0` and `‖J‖ ≤ ‖ψ‖`, the `k`-th Picard increment is at most
`Ψ x ^ (k + 1) / (k + 1)!`, where `Ψ x = ∫ v in Ioi x, P₀ * Q v * ‖ψ v‖`. -/
private lemma norm_picardTerm_le_pow_succ
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP₀ : 0 < P₀) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P₀ * Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P₀ * Q v * ‖ψ v‖) (Ioi x)) (k : ℕ) {x : ℝ}
    (hx : a < x) :
    ‖picardTerm K J ψ k x‖ ≤ (∫ v in Ioi x, P₀ * Q v * ‖ψ v‖) ^ (k + 1) / (k + 1)! := by
  induction k generalizing x with
  | zero =>
    suffices ‖picardTerm K J ψ 0 x‖ ≤ ∫ v in Ioi x, P₀ * Q v * ‖ψ v‖ by simpa using this
    rw [picardTerm]
    refine (norm_integral_kernel_smul_le (P := fun _ ↦ P₀) hKle hx (hΦ x hx)).trans ?_
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((hΦ x hx).const_mul P₀) (hΨ x hx) measurableSet_Ioi
      fun v (hv : x < v) ↦ ?_
    have := hQ0 v (hx.trans hv)
    rw [mul_assoc]
    grw [hJψ v (hx.trans hv)]
  | succ k ih =>
    have hFint := integrableOn_weight_smul_picardTerm (P := fun _ ↦ P₀) hK hJ hψ
      continuousOn_const hQ (fun _ _ ↦ hP₀.le) hQ0 hKle hΦ hΨ k hx
    -- the weighted-integral estimate with `P = P₀` and `C = P₀⁻¹`
    have hint := integral_weight_smul_le (P := fun _ ↦ P₀) hQ0 hΨ (C := P₀⁻¹) (k + 1) hx hFint
      fun v (hv : x < v) ↦ (ih (hx.trans hv)).trans_eq (by field_simp)
    rw [picardTerm]
    refine (norm_integral_kernel_smul_le (P := fun _ ↦ P₀) hKle hx hFint).trans
      ((mul_le_mul_of_nonneg_left hint hP₀.le).trans_eq ?_)
    field_simp

/-- **Volterra integral equations, sharper bound.** If the kernel bound is
`‖K x v‖ ≤ P₀ * Q v` with a constant `P₀ ≥ 0`, and the forcing is dominated by the coefficient,
`‖J v‖ ≤ ‖ψ v‖` (for instance `J = ψ` when `E = 𝕜`), then every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and bounded at
infinity satisfies `‖h x‖ ≤ exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1` for every `x > a`.
For `J = ψ` this sharpens the bound of `norm_volterra_solution_le`, which then reads
`‖h x‖ ≤ P₀ Φ x * exp (P₀ Φ x)` with `Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖`. -/
theorem norm_volterra_solution_le_exp_sub_one [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP₀ : 0 ≤ P₀) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P₀ * Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hψint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] fun _ ↦ (1 : ℝ)) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  rcases hP₀.eq_or_lt with rfl | hP₀pos
  · -- for `P₀ = 0` the kernel vanishes, and so does `h`
    have hzero : h x = 0 := by
      rw [h_eq x hx, ← integral_zero ℝ E]
      refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : x < v) ↦ ?_
      have hK0 : ‖K x v‖ ≤ 0 := by simpa using hKle x v hx hv.le
      rw [norm_le_zero_iff.1 hK0, zero_smul]
    simp [hzero]
  have hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x) := fun x hx ↦ by
    refine Integrable.mono' (hψint x hx) (((hQ.mul hJ.norm).mono
      (Ioi_subset_Ioi (le_of_lt hx))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
    have hQv := hQ0 v (hx.trans hv)
    rw [Real.norm_of_nonneg (mul_nonneg hQv (norm_nonneg _))]
    grw [hJψ v (hx.trans hv)]
  have hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P₀ * Q v * ‖ψ v‖) (Ioi x) := fun x hx ↦ by
    have := (hψint x hx).const_mul P₀
    simp only [← mul_assoc] at this
    exact this
  have hP : ContinuousOn (fun _ : ℝ ↦ P₀) (Ioi a) := continuousOn_const
  have hP0 : ∀ x ∈ Ioi a, 0 ≤ (fun _ : ℝ ↦ P₀) x := fun _ _ ↦ hP₀
  -- `h` is the sum of the Picard increments
  rw [volterra_solution_unique (P := fun _ ↦ P₀) hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ h_cont
    (continuousOn_tsum_picardTerm hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ) h_eq
    (fun y hy ↦ tsum_picardTerm_eq hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hy)
    (h_isBigO.trans (isBigO_const_const _ hP₀pos.ne' _))
    (isBigO_of_norm_le_volterra_bound hP0 hQ0 hΦ hΨ fun y hy ↦
      norm_tsum_picardTerm_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hy) hx]
  -- and the increments are dominated by the terms of the series of `exp Ψ - 1`
  have hΨx : ∫ v in Ioi x, P₀ * Q v * ‖ψ v‖ = P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖ := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have he := NormedSpace.expSeries_div_hasSum_exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖)
  rw [← Real.exp_eq_exp_ℝ] at he
  have he' := (hasSum_nat_add_iff' 1).2 he
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at he'
  refine tsum_of_norm_bounded he' fun k ↦ ?_
  rw [← hΨx]
  exact norm_picardTerm_le_pow_succ hK hJ hψ hQ hP₀pos hQ0 hKle hJψ hΦ hΨ k hx

end ConstantBound

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
    rw [← (hΨ x hx).integral_Ioi_mul_exp_integral_Ioi, ← integral_const_mul]
    refine setIntegral_mono_on hψh ((hΨ x hx).mul_exp_integral_Ioi.const_mul _) measurableSet_Ioi
      fun v (hv : x < v) ↦ ?_
    have hva : a < v := hx'.trans hv
    have hhv := norm_volterra_solution_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ h_cont h_eq h_isBigO
      hva
    have hΦle : ∫ u in Ioi v, Q u * ‖J u‖ ≤ Φx :=
      antitoneOn_integral_Ioi (forcing_weight_nonneg hQ0 le_rfl) hΦ hx' hva hv.le
    rw [norm_smul, ← mul_assoc]
    calc Q v * ‖ψ v‖ * ‖h v‖
        ≤ Q v * ‖ψ v‖ * (P v * Φx * Real.exp (∫ u in Ioi v, P u * Q u * ‖ψ u‖)) := by
          have := hP0 v hva
          have := hQ0 v hva
          grw [hhv, hΦle]
      _ = Φx * (P v * Q v * ‖ψ v‖ * Real.exp (∫ u in Ioi v, P u * Q u * ‖ψ u‖)) := by ring
  calc _ ≤ Φx + Φx * (Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖) - 1) :=
        by linarith
    _ = Φx * Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖) := by ring

end Derivative

end TauCeti
