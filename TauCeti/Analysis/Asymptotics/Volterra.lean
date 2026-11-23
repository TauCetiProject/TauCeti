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
`x > a`. On `(a, ∞)` it is the only solution that is almost everywhere strongly measurable on
`(a, ∞)` and `O(P)` on `[x, ∞)` for every `x > a`, and every solution that is `O(P)` on `[x, ∞)`
satisfies the same bound at `x`. In the case `P = 1`, that is when `‖K x v‖ ≤ Q v` and
`Ψ x = Φ₁ x = ∫ v in Ioi x, Q v * ‖ψ v‖`, if moreover `‖J v‖ ≤ ‖ψ v‖`, then every solution that
is bounded on `[x, ∞)` satisfies the sharper bound `‖h x‖ ≤ exp (Φ₁ x) - 1`.

These are the existence, uniqueness and error-bound parts of Olver's theorem on Volterra
integral equations (Chapter 6, Theorem 10.1), on the half-line `(a, ∞)`; the differentiability
and finite-endpoint parts of that theorem are not treated here. The existence and error-bound
theorems for the Liouville–Green approximation and for the solutions of linear differential
equations at an irregular singularity of rank one (DLMF §§2.7, 2.8) reduce to equations of this
form.

The kernel `K` and the coefficient `ψ` take values in any normed field `𝕜`, and the forcing `J`
and the unknown `h` in any real Banach space which is also a normed `𝕜`-space; for `𝕜 = E = ℂ`
the scalar multiplications are products of complex numbers.

## Main results

* `TauCeti.exists_volterra_solution`: existence of a continuous solution with the bound
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.volterra_solution_unique`: two solutions that are almost everywhere strongly
  measurable on `(a, ∞)` and `O(P)` on `[x, ∞)` for every `x > a` agree on `(a, ∞)`.
* `TauCeti.norm_volterra_solution_le`: every solution that is `O(P)` on `[x, ∞)`, for some
  `x > a` at which `Φ x` and `Ψ x` converge, satisfies `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.isBigO_of_norm_le_volterra_bound`: conversely, every function satisfying this bound
  is `O(P)` on `[x, ∞)` for every `x > a`.
* `TauCeti.integrableOn_volterra_of_isBigO`: for a measurable function that is `O(P)` on
  `[x, ∞)`, the integrand of the equation at `x` is integrable on `(x, ∞)`.
* `TauCeti.norm_volterra_solution_le_exp_sub_one`: when `‖K x v‖ ≤ Q v` and `‖J v‖ ≤ ‖ψ v‖`,
  every solution that is bounded on `[x, ∞)`, for some `x > a` at which `Φ₁ x` converges,
  satisfies the sharper bound `‖h x‖ ≤ exp (Φ₁ x) - 1`.
* `TauCeti.isBigO_one_of_norm_le_exp_sub_one`: every function satisfying the sharper bound on
  `(a, ∞)` is bounded on `[x, ∞)` for every `x > a`.
* `TauCeti.exists_volterra_solution_exp_sub_one`: under the same conditions, with `Φ₁`
  convergent on `(a, ∞)`, existence of a continuous solution with the sharper bound.

A solution is constructed as the sum of the Picard increments (the Liouville–Neumann series).
The `k`-th increment is bounded by
`P x * Φ x * Ψ x ^ k / k!`, by the identity `∫ v in Ioi x, g v * Ψ v ^ k = Ψ x ^ (k + 1) / (k + 1)`
for `Ψ` the tail integral of `g` (`MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`).
The bounds for an arbitrary solution come from Grönwall's inequality on a ray, proved by
iterating with the same identity. The discrete analogue is
`TauCeti.exists_discrete_volterra_solution`.

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
    set g : ℝ → ℝ := fun v ↦ P v * Q v * ‖ψ v‖ with hg
    refine (norm_integral_kernel_smul_le hKle hx (hFint x hx)).trans ?_
    -- bound the weighted integral through `∫ g * Ψ ^ k = Ψ x ^ (k + 1) / (k + 1)`
    have hint : ∫ v in Ioi x, Q v * ‖ψ v • picardTerm K J ψ k v‖ ≤
        Φx / k ! * ∫ v in Ioi x, g v * (∫ u in Ioi v, g u) ^ k := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hFint x hx)
        (((hΨ x hx).mul_pow_integral_Ioi k).const_mul _) measurableSet_Ioi
        fun v (hv : x < v) ↦ ?_
      have hva : a < v := hx.trans hv
      have := hP0 v hva
      have := hQ0 v hva
      have := setIntegral_nonneg (μ := volume) measurableSet_Ioi
        (coeff_weight_nonneg (ψ := ψ) hP0 hQ0 hva.le)
      have hΦle : ∫ u in Ioi v, Q u * ‖J u‖ ≤ Φx :=
        antitoneOn_integral_Ioi (forcing_weight_nonneg hQ0 le_rfl) hΦ hx hva hv.le
      rw [norm_smul, ← mul_assoc]
      calc Q v * ‖ψ v‖ * ‖picardTerm K J ψ k v‖
          ≤ Q v * ‖ψ v‖ * (P v * Φx * ((∫ u in Ioi v, g u) ^ k / k !)) := by
            grw [hle v hva, hΦle]
        _ = Φx / k ! * (g v * (∫ u in Ioi v, g u) ^ k) := by simp only [hg]; ring
    rw [(hΨ x hx).integral_Ioi_mul_pow_integral_Ioi k] at hint
    calc P x * ∫ v in Ioi x, Q v * ‖ψ v • picardTerm K J ψ k v‖
        ≤ P x * (Φx / k ! * ((∫ u in Ioi x, g u) ^ (k + 1) / (k + 1))) :=
          mul_le_mul_of_nonneg_left hint (hP0 x hx)
      _ = P x * Φx * ((∫ u in Ioi x, g u) ^ (k + 1) / (k + 1)!) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp

/-- At points `v ≥ x`, the `k`-th Picard increment is at most
`Φ x * (Ψ x ^ k / k!) * P v`, with the tail integrals `Φ` and `Ψ` taken at `x`. -/
private lemma norm_picardTerm_le_of_le (k : ℕ) {x v : ℝ} (hx : a < x) (hv : x ≤ v) :
    ‖picardTerm K J ψ k v‖ ≤ (∫ u in Ioi x, Q u * ‖J u‖) *
      ((∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ k / k !) * P v :=
  ((picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 v (hx.trans_le hv)).trans
    (mul_tail_le_of_le hP0 hQ0 hΦ hΨ (f := fun t ↦ t ^ k / k !)
      (fun s (hs : 0 ≤ s) _ _ hst ↦ by dsimp only; gcongr) (fun _ _ ↦ by positivity) hx hv)

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
      (integrableOn_weight_smul hψ hQ hQ0 hΨ (hspec k).1 hx fun v (hv : x < v) ↦ hTle k v hv.le)
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
Theorem 10.1). By `volterra_solution_unique`, on `(a, ∞)` it is the only solution that is
almost everywhere strongly measurable on `(a, ∞)` and `O(P)` on `[x, ∞)` for every `x > a`. -/
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

/-! ### Uniqueness and the bounds satisfied by every solution -/

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function that is `O(P)` on `[x, ∞)`, with `P ≥ 0` there, is bounded on `[x, ∞)` by a
multiple of `P`. -/
private lemma exists_bound_of_isBigO (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) {h : ℝ → E} {x : ℝ}
    (hx : a < x) (hh : h =O[𝓟 (Ici x)] P) : ∃ C, ∀ v ∈ Ici x, ‖h v‖ ≤ C * P v := by
  obtain ⟨C, hC⟩ := isBigO_principal.1 hh
  refine ⟨C, fun v hv ↦ ?_⟩
  rw [← Real.norm_of_nonneg (hP0 v (hx.trans_le hv))]
  exact hC v hv

omit [NormedSpace ℝ E] in
/-- If `h` is almost everywhere strongly measurable and `O(P)` on `[x, ∞)` for some `x > a` at
which `Φ x` and `Ψ x` converge, then the integrand `v ↦ K x v • (J v + ψ v • h v)` of the
Volterra equation is integrable on `(x, ∞)`. -/
theorem integrableOn_volterra_of_isBigO
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {x : ℝ} (hx : a < x)
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi x))) (hh : h =O[𝓟 (Ici x)] P) :
    IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (Ioi x) := by
  obtain ⟨C, hC⟩ := exists_bound_of_isBigO hP0 hx hh
  have hsub : Ioi x ⊆ Ioi a := Ioi_subset_Ioi hx.le
  have hKx : ContinuousOn (fun v ↦ K x v) (Ioi x) :=
    hK.comp (continuous_const.prodMk continuous_id).continuousOn fun v hv ↦ ⟨hx, le_of_lt hv⟩
  refine Integrable.mono' ((hΦ.add (hΨ.const_mul C)).const_mul (P x))
    ((hKx.aestronglyMeasurable measurableSet_Ioi).smul
      (((hJ.mono hsub).aestronglyMeasurable measurableSet_Ioi).add
        (((hψ.mono hsub).aestronglyMeasurable measurableSet_Ioi).smul hm))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
  have hF : ‖J v + ψ v • h v‖ ≤ ‖J v‖ + ‖ψ v‖ * (C * P v) :=
    (norm_add_le _ _).trans (by rw [norm_smul]; gcongr; exact hC v hv.le)
  rw [norm_smul]
  calc ‖K x v‖ * ‖J v + ψ v • h v‖ ≤ P x * Q v * (‖J v‖ + ‖ψ v‖ * (C * P v)) :=
        mul_le_mul (hKle x v hx hv.le) hF (norm_nonneg _)
          ((norm_nonneg _).trans (hKle x v hx hv.le))
    _ = P x * (Q v * ‖J v‖ + C * (P v * Q v * ‖ψ v‖)) := by ring

/-- **Grönwall's inequality on a ray.** Let `u ≤ C * P` on `[x, ∞)`, and suppose that for every
`y ≥ x` and every majorant `b` of `u` on `(y, ∞)` with `g * b` integrable there,
`u y ≤ P y * (A + ∫ v in Ioi y, g v * b v)`. Then
`u x ≤ P x * A * exp (∫ v in Ioi x, P v * g v)`. The `k`-th iterate of the inequality gives
`u y ≤ P y * (A * ∑ j < k, Ψ y ^ j / j! + C * (Ψ y ^ k / k!))` for `Ψ` the tail integral of
`P * g`. -/
private lemma le_mul_exp_of_le_tail_integral {u P g : ℝ → ℝ} {x A C : ℝ}
    (hg : IntegrableOn (fun v ↦ P v * g v) (Ioi x)) (hC : ∀ y ∈ Ici x, u y ≤ C * P y)
    (hu : ∀ y ∈ Ici x, ∀ b : ℝ → ℝ, (∀ v ∈ Ioi y, u v ≤ b v) →
      IntegrableOn (fun v ↦ g v * b v) (Ioi y) → u y ≤ P y * (A + ∫ v in Ioi y, g v * b v)) :
    u x ≤ P x * A * Real.exp (∫ v in Ioi x, P v * g v) := by
  set Ψ : ℝ → ℝ := fun y ↦ ∫ v in Ioi y, P v * g v with hΨ_def
  set B : ℕ → ℝ → ℝ := fun k y ↦
    A * ∑ j ∈ Finset.range k, Ψ y ^ j / j ! + C * (Ψ y ^ k / k !) with hB
  have hiter : ∀ k : ℕ, ∀ y ∈ Ici x, u y ≤ P y * B k y := by
    intro k
    induction k with
    | zero => intro y hy; simpa [hB, mul_comm] using hC y hy
    | succ k ih =>
      intro y (hy : x ≤ y)
      have hgy := hg.mono_set (Ioi_subset_Ioi hy)
      -- each term `g * P * Ψ ^ j / j!` integrates to `Ψ y ^ (j + 1) / (j + 1)!`
      have hfun (j : ℕ) : (fun v ↦ g v * (P v * (Ψ v ^ j / j !))) =
          fun v ↦ P v * g v * (∫ u in Ioi v, P u * g u) ^ j / j ! := by
        ext v; simp only [hΨ_def]; ring
      have hint (j : ℕ) : IntegrableOn (fun v ↦ g v * (P v * (Ψ v ^ j / j !))) (Ioi y) := by
        rw [hfun]; exact (hgy.mul_pow_integral_Ioi j).div_const _
      have heq (j : ℕ) :
          ∫ v in Ioi y, g v * (P v * (Ψ v ^ j / j !)) = Ψ y ^ (j + 1) / (j + 1)! := by
        rw [hfun, integral_div, hgy.integral_Ioi_mul_pow_integral_Ioi j, Nat.factorial_succ]
        push_cast
        field_simp
        rfl
      have hsplit : (fun v ↦ g v * (P v * B k v)) = fun v ↦
          A * ∑ j ∈ Finset.range k, g v * (P v * (Ψ v ^ j / j !)) +
            C * (g v * (P v * (Ψ v ^ k / k !))) := by
        ext v; simp only [hB, ← Finset.mul_sum]; ring
      have hbint : IntegrableOn (fun v ↦ g v * (P v * B k v)) (Ioi y) := by
        rw [hsplit]
        exact ((integrable_finsetSum _ fun j _ ↦ hint j).const_mul A).add ((hint k).const_mul C)
      refine (hu y hy _ (fun v hv ↦ ih v (hy.trans hv.le)) hbint).trans_eq ?_
      rw [hsplit, integral_add ((integrable_finsetSum _ fun j _ ↦ hint j).const_mul A)
        ((hint k).const_mul C), integral_const_mul, integral_const_mul,
        integral_finsetSum _ fun j _ ↦ hint j]
      simp only [heq, hB, Finset.sum_range_succ' _ k, pow_zero, Nat.factorial_zero, Nat.cast_one,
        div_one]
      ring
  -- let `k → ∞`
  have hlim : Tendsto (fun k ↦ P x * B k x) atTop (𝓝 (P x * A * Real.exp (Ψ x))) := by
    have hexp := (NormedSpace.expSeries_div_hasSum_exp (Ψ x)).tendsto_sum_nat
    rw [← Real.exp_eq_exp_ℝ] at hexp
    simpa [hB, mul_assoc] using ((hexp.const_mul A).add
      ((FloorSemiring.tendsto_pow_div_factorial_atTop (Ψ x)).const_mul C)).const_mul (P x)
  exact ge_of_tendsto' hlim fun k ↦ hiter k x self_mem_Ici

/-- **Volterra integral equations, bound.** Let `‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`, where
`P ≥ 0` on `(a, ∞)`, and let `x > a` be such that `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge. Then every solution of the Volterra equation
`h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v)` on `(a, ∞)` that is `O(P)` on `[x, ∞)` satisfies
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)` (the error bound of Olver, Chapter 6, Theorem 10.1). -/
theorem norm_volterra_solution_le (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {h : ℝ → E}
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) {x : ℝ} (hx : a < x)
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) (h_isBigO : h =O[𝓟 (Ici x)] P) :
    ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  rcases (hP0 x hx).eq_or_lt with hPx | hPx
  · -- if `P x = 0`, then `K x v = 0` for every `v ≥ x`, so `h x = 0`
    rw [← hPx, zero_mul, zero_mul, h_eq x hx]
    refine (norm_integral_le_of_norm_le (g := fun _ ↦ (0 : ℝ)) (integrable_zero _ _ _)
      ?_).trans_eq (by simp)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right ((hKle x v hx hv.le).trans_eq (by rw [← hPx, zero_mul]))
      (norm_nonneg _)).trans_eq (zero_mul _)
  -- otherwise `Q ≥ 0` on `[x, ∞)`, and Grönwall's inequality applies to `‖h‖`
  have hQ0 : ∀ v ∈ Ici x, 0 ≤ Q v := fun v (hv : x ≤ v) ↦
    nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (hKle x v hx hv)) hPx
  obtain ⟨C, hC⟩ := exists_bound_of_isBigO hP0 hx h_isBigO
  have hΨ' : IntegrableOn (fun v ↦ P v * (Q v * ‖ψ v‖)) (Ioi x) := by
    simpa only [mul_assoc] using hΨ
  simpa only [mul_assoc] using le_mul_exp_of_le_tail_integral (u := fun y ↦ ‖h y‖)
    (A := ∫ v in Ioi x, Q v * ‖J v‖) hΨ' hC fun y (hy : x ≤ y) b hb hgb ↦ by
    have hya := hx.trans_le hy
    have hJy := hΦ.mono_set (Ioi_subset_Ioi hy)
    rw [h_eq y hya]
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

/-- **Volterra integral equations, uniqueness.** Let `K` be continuous on
`{(x, v) | a < x ≤ v}` with `‖K x v‖ ≤ P x * Q v` there, where `P ≥ 0` on `(a, ∞)`, and let `J`,
`ψ` be continuous on `(a, ∞)` such that `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for every `x > a`. Then two solutions of the
Volterra equation `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that are almost everywhere
strongly measurable on `(a, ∞)` and `O(P)` on `[x, ∞)` for every `x > a` agree on `(a, ∞)` (the
uniqueness part of Olver, Chapter 6, Theorem 10.1). -/
theorem volterra_solution_unique
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h₁ h₂ : ℝ → E}
    (h₁_meas : AEStronglyMeasurable h₁ (volume.restrict (Ioi a)))
    (h₂_meas : AEStronglyMeasurable h₂ (volume.restrict (Ioi a)))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_isBigO : ∀ x ∈ Ioi a, h₁ =O[𝓟 (Ici x)] P)
    (h₂_isBigO : ∀ x ∈ Ioi a, h₂ =O[𝓟 (Ici x)] P) :
    EqOn h₁ h₂ (Ioi a) := by
  intro x₀ (hx₀ : a < x₀)
  have hint {h : ℝ → E} (hm : AEStronglyMeasurable h (volume.restrict (Ioi a)))
      (hh : ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] P) {x : ℝ} (hx : a < x) :
      IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (Ioi x) :=
    integrableOn_volterra_of_isBigO hK hJ hψ hP0 hKle hx (hΦ x hx) (hΨ x hx)
      (hm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hx.le) le_rfl)) (hh x hx)
  -- the difference solves the homogeneous equation
  have hd : ∀ x ∈ Ioi a, (h₁ - h₂) x =
      ∫ v in Ioi x, K x v • ((0 : ℝ → E) v + ψ v • (h₁ - h₂) v) := fun x hx ↦ by
    rw [Pi.sub_apply, h₁_eq x hx, h₂_eq x hx,
      ← integral_sub (hint h₁_meas h₁_isBigO hx) (hint h₂_meas h₂_isBigO hx)]
    refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
    simp only [Pi.sub_apply, Pi.zero_apply, zero_add, smul_sub, smul_add]
    abel
  -- so the bound with zero forcing gives `‖h₁ x₀ - h₂ x₀‖ ≤ 0`
  have hle := norm_volterra_solution_le hP0 hKle hd hx₀ (by simp) (hΨ x₀ hx₀)
    ((h₁_isBigO x₀ hx₀).sub (h₂_isBigO x₀ hx₀))
  simp only [Pi.zero_apply, norm_zero, mul_zero, integral_zero, zero_mul] at hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` of
`exists_volterra_solution` on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`, is `O(P)` on `[x, ∞)` for every `x > a`. -/
theorem isBigO_of_norm_le_volterra_bound (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)) :
    ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] P := fun x (hx : a < x) ↦
  isBigO_principal.2 ⟨_, fun v (hv : x ≤ v) ↦ by
    rw [Real.norm_of_nonneg (hP0 v (hx.trans_le hv))]
    exact (hh v (hx.trans_le hv)).trans (mul_tail_le_of_le hP0 hQ0 hΦ hΨ
      (Real.exp_monotone.monotoneOn _) (fun _ _ ↦ (Real.exp_pos _).le) hx hv)⟩

/-! ### The sharper bound when the forcing is dominated by the coefficient -/

/-- **Volterra integral equations, sharper bound.** Let `‖K x v‖ ≤ Q v` for `a < x ≤ v` and
`‖J v‖ ≤ ‖ψ v‖` for `v > a`, and let `x > a` be such that `Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖`
converges. Then every solution of the Volterra equation
`h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v)` on `(a, ∞)` that is bounded on `[x, ∞)`
satisfies `‖h x‖ ≤ exp (Φ x) - 1`.

This is Olver's sharper bound `|h(x)| ≤ e^{P₀ Φ(x)} - 1` for a constant `P = P₀` and `J = ψ`
(Chapter 6, Theorem 10.1), with the constant `P₀` absorbed into `Q`. It improves on the bound
`P₀ Φ e^{P₀ Φ}` of `norm_volterra_solution_le`, since `e^t - 1 ≤ t e^t` for `t ≥ 0`. -/
theorem norm_volterra_solution_le_exp_sub_one
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    {h : ℝ → E} (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) {x : ℝ}
    (hx : a < x) (hΦ : IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x))
    (h_isBigO : h =O[𝓟 (Ici x)] fun _ ↦ (1 : ℝ)) :
    ‖h x‖ ≤ Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  obtain ⟨C, hC⟩ := isBigO_principal.1 h_isBigO
  -- Grönwall's inequality applies to `1 + ‖h‖`, with `P = 1`
  have hle := le_mul_exp_of_le_tail_integral (u := fun y ↦ 1 + ‖h y‖) (P := fun _ ↦ 1)
    (g := fun v ↦ Q v * ‖ψ v‖) (A := 1) (C := 1 + C) (by simpa only [one_mul] using hΦ)
    (fun y hy ↦ by have := hC y hy; rw [norm_one, mul_one] at this; linarith)
    fun y (hy : x ≤ y) b hb hgb ↦ by
    have hya := hx.trans_le hy
    rw [one_mul, h_eq y hya]
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
  exact ⟨h, h_cont, h_eq, fun x hx ↦ norm_volterra_solution_le_exp_sub_one hKle hJψ h_eq hx
    (hΦ x hx) (isBigO_of_norm_le_volterra_bound hP0 hQ0 hΦJ hΨ h_le x hx)⟩

end TauCeti
