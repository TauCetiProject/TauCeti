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

This is Olver's theorem on Volterra integral equations (Chapter 6, Theorem 10.1), on the
half-line `(a, ∞)`. The existence and error-bound theorems for the Liouville–Green
approximation and for the solutions of linear differential equations at an irregular singularity
of rank one (DLMF §§2.7, 2.8) reduce to equations of this form.

The kernel `K` and the coefficient `ψ` take values in any normed field `𝕜`, and the forcing `J`
and the unknown `h` in any real Banach space which is also a normed `𝕜`-space; for `𝕜 = E = ℂ`
the scalar multiplications are products of complex numbers.

## Main results

* `TauCeti.exists_volterra_solution`: existence of a continuous solution with the bound
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.

The solution is the sum of the Picard iterates. The `k`-th increment is bounded by
`P x * Φ x * Ψ x ^ k / k!`, by the identity `∫ v in Ioi x, g v * Ψ v ^ k = Ψ x ^ (k + 1) / (k + 1)`
for `Ψ` the tail integral of `g` (`MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`).
The discrete analogue is `TauCeti.exists_discrete_volterra_solution`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10.
* NIST Digital Library of Mathematical Functions, §2.7(iii), <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Filter Set MeasureTheory Function
open scoped Nat Topology

namespace TauCeti

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {a : ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

/-- A tail integral `∫ v in Ioi y, f v` of a function nonnegative on `(a, ∞)` decreases as `y`
increases beyond `a`. -/
private lemma integral_Ioi_le_integral_Ioi {f : ℝ → ℝ} (hf0 : ∀ v ∈ Ioi a, 0 ≤ f v) {x y : ℝ}
    (hx : a < x) (hxy : x ≤ y) (hint : IntegrableOn f (Ioi x)) :
    ∫ v in Ioi y, f v ≤ ∫ v in Ioi x, f v :=
  setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).2
    (ae_of_all _ fun v hv ↦ hf0 v (hx.trans hv))) (Ioi_subset_Ioi hxy).eventuallySubset

/-- A tail integral `∫ v in Ioi x, f v` of a function nonnegative on `(a, ∞)` is nonnegative. -/
private lemma integral_Ioi_nonneg {f : ℝ → ℝ} (hf0 : ∀ v ∈ Ioi a, 0 ≤ f v) {x : ℝ}
    (hx : a < x) : 0 ≤ ∫ v in Ioi x, f v :=
  setIntegral_nonneg measurableSet_Ioi fun v hv ↦ hf0 v (hx.trans hv)

/-- The bound `p * s' * (t' ^ k / k!)` of a Picard increment at a point `v ≥ x`, whose tail
integrals `s' ≤ s` and `t' ≤ t` are those at `x`, is at most `s * (t ^ k / k!) * p`. -/
private lemma mul_pow_div_factorial_le {p s s' t t' : ℝ} (k : ℕ) (hp : 0 ≤ p) (hs' : 0 ≤ s')
    (ht' : 0 ≤ t') (hs : s' ≤ s) (ht : t' ≤ t) :
    p * s' * (t' ^ k / k !) ≤ s * (t ^ k / k !) * p :=
  calc p * s' * (t' ^ k / k !) ≤ p * s * (t ^ k / k !) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs hp)
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ ht' ht k) (by positivity))
          (by positivity) (mul_nonneg hp (hs'.trans hs))
    _ = s * (t ^ k / k !) * p := by ring

/-- The bound `p * s' * exp t'` of a solution at a point `v ≥ x`, whose tail integrals
`s' ≤ s` and `t' ≤ t` are those at `x`, is at most `s * exp t * p`. -/
private lemma mul_exp_le {p s s' t t' : ℝ} (hp : 0 ≤ p) (hs' : 0 ≤ s') (hs : s' ≤ s)
    (ht : t' ≤ t) : p * s' * Real.exp t' ≤ s * Real.exp t * p :=
  calc p * s' * Real.exp t' ≤ p * s * Real.exp t :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs hp) (Real.exp_le_exp.2 ht) (by positivity)
          (mul_nonneg hp (hs'.trans hs))
    _ = s * Real.exp t * p := by ring

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
  set c := (a + x₀) / 2
  have hac : a < c := by simp only [c]; linarith
  have hcx : c < x₀ := by simp only [c]; linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hP.mono fun x (hx : x ∈ Icc c (x₀ + 1)) ↦ hac.trans_le hx.1)
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
      refine (show ContinuousAt (fun x ↦ K x v • F v) x₀ from
        hKv.smul continuousAt_const).congr ?_
      filter_upwards [Iio_mem_nhds hgt] with x hx
      rw [indicator_of_mem (show v ∈ Ioi x from hx)]

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

include hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ

/-- The Picard increments are continuous on `(a, ∞)`, and the `k`-th is bounded by
`P x * Φ x * (Ψ x ^ k / k!)`. -/
private lemma picardTerm_spec (k : ℕ) :
    ContinuousOn (picardTerm K J ψ k) (Ioi a) ∧ ∀ x ∈ Ioi a, ‖picardTerm K J ψ k x‖ ≤
      P x * (∫ v in Ioi x, Q v * ‖J v‖) *
        ((∫ v in Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !) := by
  have hg0 : ∀ v ∈ Ioi a, 0 ≤ P v * Q v * ‖ψ v‖ := fun v hv ↦
    mul_nonneg (mul_nonneg (hP0 v hv) (hQ0 v hv)) (norm_nonneg _)
  have hJ0 : ∀ v ∈ Ioi a, 0 ≤ Q v * ‖J v‖ := fun v hv ↦ mul_nonneg (hQ0 v hv) (norm_nonneg _)
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
        ((∫ v in Ioi x, P v * Q v * ‖ψ v‖) ^ k / k !)) fun v (hv : x < v) ↦ by
          have hva : a < v := hx.trans hv
          exact (hle v hva).trans (mul_pow_div_factorial_le k (hP0 v hva)
            (integral_Ioi_nonneg hJ0 hva) (integral_Ioi_nonneg hg0 hva)
            (integral_Ioi_le_integral_Ioi hJ0 hx hv.le (hΦ x hx))
            (integral_Ioi_le_integral_Ioi hg0 hx hv.le (hΨ x hx)))
    refine ⟨continuousOn_integral_kernel_smul hK hKle hP hQ0 (hψ.smul hcont) hFint,
      fun x hx ↦ ?_⟩
    set Φx := ∫ v in Ioi x, Q v * ‖J v‖
    set g : ℝ → ℝ := fun v ↦ P v * Q v * ‖ψ v‖ with hg
    have hgc : ContinuousOn g (Ioi x) :=
      ((hP.mul hQ).mul hψ.norm).mono (Ioi_subset_Ioi hx.le)
    refine (norm_integral_kernel_smul_le hKle hx (hFint x hx)).trans ?_
    -- bound the weighted integral through `∫ g * Ψ ^ k = Ψ x ^ (k + 1) / (k + 1)`
    have hint : ∫ v in Ioi x, Q v * ‖ψ v • picardTerm K J ψ k v‖ ≤
        Φx / k ! * ∫ v in Ioi x, g v * (∫ u in Ioi v, g u) ^ k := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hFint x hx)
        (((hΨ x hx).integrableOn_mul_pow_integral_Ioi hgc k).const_mul _) measurableSet_Ioi
        fun v (hv : x < v) ↦ ?_
      have hva : a < v := hx.trans hv
      rw [norm_smul, ← mul_assoc]
      calc Q v * ‖ψ v‖ * ‖picardTerm K J ψ k v‖
          ≤ Q v * ‖ψ v‖ * (P v * Φx * ((∫ u in Ioi v, g u) ^ k / k !)) := by
            refine mul_le_mul_of_nonneg_left ((hle v hva).trans ?_)
              (mul_nonneg (hQ0 v hva) (norm_nonneg _))
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (integral_Ioi_le_integral_Ioi hJ0 hx hv.le (hΦ x hx)) (hP0 v hva))
              (by have := integral_Ioi_nonneg hg0 hva; positivity)
        _ = Φx / k ! * (g v * (∫ u in Ioi v, g u) ^ k) := by simp only [hg]; ring
    rw [(hΨ x hx).integral_Ioi_mul_pow_integral_Ioi hgc k] at hint
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
      ((∫ u in Ioi x, P u * Q u * ‖ψ u‖) ^ k / k !) * P v := by
  have hva : a < v := hx.trans_le hv
  have hg0 : ∀ u ∈ Ioi a, 0 ≤ P u * Q u * ‖ψ u‖ := fun u hu ↦
    mul_nonneg (mul_nonneg (hP0 u hu) (hQ0 u hu)) (norm_nonneg _)
  have hJ0 : ∀ u ∈ Ioi a, 0 ≤ Q u * ‖J u‖ := fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _)
  have hΦv : ∫ u in Ioi v, Q u * ‖J u‖ ≤ ∫ u in Ioi x, Q u * ‖J u‖ :=
    integral_Ioi_le_integral_Ioi hJ0 hx hv (hΦ x hx)
  have hΨv : ∫ u in Ioi v, P u * Q u * ‖ψ u‖ ≤ ∫ u in Ioi x, P u * Q u * ‖ψ u‖ :=
    integral_Ioi_le_integral_Ioi hg0 hx hv (hΨ x hx)
  exact ((picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).2 v hva).trans
    (mul_pow_div_factorial_le k (hP0 v hva) (integral_Ioi_nonneg hJ0 hva)
      (integral_Ioi_nonneg hg0 hva) hΦv hΨv)

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
  set c := (a + x₀) / 2
  have hac : a < c := by simp only [c]; linarith
  have hcx : c < x₀ := by simp only [c]; linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hP.mono fun x (hx : x ∈ Icc c (x₀ + 1)) ↦ hac.trans_le hx.1)
  refine (continuousOn_tsum
    (fun k ↦ (picardTerm_spec hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ k).1.mono
      fun x (hx : x ∈ Icc c (x₀ + 1)) ↦ hac.trans_le hx.1)
    ((Real.summable_pow_div_factorial (∫ v in Ioi c, P v * Q v * ‖ψ v‖)).mul_left
      ((∫ v in Ioi c, Q v * ‖J v‖) * M))
    fun k x (hx : x ∈ Icc c (x₀ + 1)) ↦ ?_).continuousAt (Icc_mem_nhds hcx (lt_add_one x₀))
  have hΦc : 0 ≤ ∫ u in Ioi c, Q u * ‖J u‖ :=
    integral_Ioi_nonneg (fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _)) hac
  have hΨc : 0 ≤ ∫ u in Ioi c, P u * Q u * ‖ψ u‖ := integral_Ioi_nonneg
    (fun u hu ↦ mul_nonneg (mul_nonneg (hP0 u hu) (hQ0 u hu)) (norm_nonneg _)) hac
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
      fun v (hv : x < v) ↦ by
        have hva : a < v := hx.trans hv
        exact (norm_tsum_picardTerm_le hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ hva).trans
          (mul_exp_le (hP0 v hva)
            (integral_Ioi_nonneg (fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _)) hva)
            (integral_Ioi_le_integral_Ioi (fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _))
              hx hv.le (hΦ x hx))
            (integral_Ioi_le_integral_Ioi (fun u hu ↦
              mul_nonneg (mul_nonneg (hP0 u hu) (hQ0 u hu)) (norm_nonneg _)) hx hv.le (hΨ x hx)))
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
    calc P x * (Q v * (‖ψ v‖ * ‖T k v‖))
        ≤ P x * (Q v * (‖ψ v‖ * (Φx * (Ψx ^ k / k !) * P v))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hTle k v hv.le) (norm_nonneg _)) (hQ0 v (hx.trans hv))) (hP0 x hx)
      _ = P x * Φx * (Ψx ^ k / k !) * (P v * Q v * ‖ψ v‖) := by ring
  have hser := hasSum_integral_of_summable_integral_norm hFk hsum
  have hinner : ∀ v, ∑' k, K x v • ψ v • T k v = K x v • ψ v • h v := fun v ↦ by
    rw [h_def, tsum_const_smul'', tsum_const_smul'']
  simp only [hinner] at hser
  calc h x = T 0 x + ∑' k, T (k + 1) x := (summable_picardTerm hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
        hx).tsum_eq_zero_add
    _ = _ := by rw [← hser.tsum_eq]; rfl

end Iteration

/-- **Volterra integral equations, existence.** Let `K` be continuous on
`{(x, v) | a < x ≤ v}` with `‖K x v‖ ≤ P x * Q v` there, where `P, Q ≥ 0` are continuous on
`(a, ∞)`, and let `J`, `ψ` be continuous on `(a, ∞)` such that
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for
every `x > a`. Then the Volterra integral equation
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has a solution, continuous on `(a, ∞)`, such
that `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x > a` (Olver, Chapter 6, Theorem 10.1). -/
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

end TauCeti
