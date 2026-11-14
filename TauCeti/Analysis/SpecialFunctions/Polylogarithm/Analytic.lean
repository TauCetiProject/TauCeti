/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Nonpositive
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Holomorphy, differential recursion, and conjugation of principal polylogarithms

On the principal domain `Ω = {z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ ∖ [1, ∞)`, the principal
polylogarithm `TauCeti.Polylog.polylog` is complex analytic in every integer weight `n`, satisfies
the Euler differential recursion `z * deriv (polylog (n + 1)) z = polylog n z`, and rebuilds each
weight from the previous one by the radial integral `polylog (n + 1) z = ∫ t in 0..1, polylog n
(t * z) / t`.

For weights `k + 2 ≥ 2`, complex differentiability on `Ω` is established by differentiating the
logarithmic radial integral under the integral sign on compact closed balls inside `Ω`, using the
uniform lower bound on `‖1 - t z‖` from `TauCeti.Polylog.exists_le_norm_one_sub_ofReal_mul` to
dominate the differentiated integrand `(-log t) ^ k / (1 - t z)` by a multiple of `|log t| ^ k`.
Complex differentiability on the open domain `Ω` gives holomorphy (`AnalyticOnNhd`), and the
identity principle on the star-convex domain `Ω` extends the Euler differential recursion from the
open unit disc (`TauCeti.Polylog.mul_deriv_polylog_add_one_of_norm_lt_one`) to all of `Ω`.
Applying the fundamental theorem of calculus to the smooth path `t ↦ polylog (n + 1) (t * z)` on
`[0, 1]` then yields the recursive radial integral in every integer weight `n`.

Finally, `polylog n` commutes with complex conjugation on `Ω` (and on all of `ℂ`, including the
totalised pole at `1`, in nonpositive weights), so `polylog n x` is real for every real `x < 1`,
whereas on the branch cut `(1, ∞)` the lower-boundary convention breaks conjugation symmetry.

## Main declarations

* `TauCeti.Polylog.hasDerivAt_polylog_one` and `TauCeti.Polylog.hasDerivAt_polylog_nat_add_two`:
  explicit complex derivatives in weights `1` and `k + 2` on `Ω`.
* `TauCeti.Polylog.differentiableOn_polylog`, `TauCeti.Polylog.analyticOnNhd_polylog`, and
  `TauCeti.Polylog.analyticAt_polylog`: complex differentiability and analyticity on `Ω` in every
  integer weight.
* `TauCeti.Polylog.mul_deriv_polylog_add_one`, `TauCeti.Polylog.mul_deriv_polylog`,
  `TauCeti.Polylog.hasDerivAt_polylog_add_one`, and `TauCeti.Polylog.deriv_polylog_add_one`:
  the Euler differential recursion on `Ω` and its quotient form away from `0`.
* `TauCeti.Polylog.intervalIntegrable_polylog_div` and
  `TauCeti.Polylog.polylog_add_one_eq_integral`: the recursive radial integral on `Ω` in every
  integer weight.
* `TauCeti.Polylog.polylog_neg_nat_conj`, `TauCeti.Polylog.polylog_conj`, and
  `TauCeti.Polylog.im_polylog_ofReal`: Schwarz conjugation symmetry and reality on `(-∞, 1)`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §§1.1–1.3, (1)–(3), pp. 50–51.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, introduction, p. 5.
-/

public section

open Filter MeasureTheory Polynomial Set Topology

namespace TauCeti.Polylog

private lemma isOpen_principalDomain : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

private lemma zero_mem_principalDomain : (0 : ℂ) ∈ {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
  simp [Complex.one_mem_slitPlane]

private lemma one_sub_ofReal_mul_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - (t : ℂ) * z ∈ Complex.slitPlane := by
  have hz' : 1 + -z ∈ Complex.slitPlane := by simpa [sub_eq_add_neg] using hz
  have hmem := Complex.starConvex_one_slitPlane.add_smul_mem hz' ht0 ht1
  rwa [Complex.real_smul, mul_neg, ← sub_eq_add_neg] at hmem

private lemma starConvex_zero_principalDomain :
    StarConvex ℝ (0 : ℂ) {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
  intro z hz a b ha hb hab
  simp only [smul_zero, zero_add, mem_ofPred_eq, Complex.real_smul]
  exact one_sub_ofReal_mul_mem_slitPlane hz hb (by linarith)

private lemma isPreconnected_principalDomain :
    IsPreconnected {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  ((starConvex_zero_principalDomain.isPathConnected
    zero_mem_principalDomain).isConnected).isPreconnected

private lemma ne_one_of_one_sub_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z ≠ 1 := by
  rintro rfl
  simp at hz

/-- On the principal domain `1 - z ∈ Complex.slitPlane`, `polylog 1 z = -Complex.log (1 - z)` has
complex derivative `(1 - z)⁻¹`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) ((1 - z)⁻¹) z := by
  have hsub : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hlog := ((Complex.hasDerivAt_log hz).comp z hsub).neg
  refine (hlog.congr_of_eventuallyEq (Eventually.of_forall polylog_one)).congr_deriv ?_
  ring

/-- Value of `deriv (polylog 1)` on the principal domain, including at `z = 0`. -/
theorem deriv_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog 1) z = (1 - z)⁻¹ :=
  (hasDerivAt_polylog_one hz).deriv

private lemma intervalIntegrable_and_hasDerivAt_radialIntegral (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) volume 0 1 ∧
    HasDerivAt
      (fun w : ℂ ↦ ∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ))
      (∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_principalDomain z hz
  set r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have hKΩ : Metric.closedBall z r ⊆ {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨δ, hδ, hδK⟩ := exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z r) hKΩ
  let F : ℂ → ℝ → ℂ := fun w t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * w)) / (t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun w t ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * w)
  let bound : ℝ → ℝ := fun t ↦ δ⁻¹ * |Real.log t| ^ k
  refine intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound)
    (Metric.closedBall_mem_nhds z hr)
    (Eventually.of_forall fun w ↦ (by fun_prop : Measurable (F w)).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z)
    (by fun_prop : Measurable (F' z)).aestronglyMeasurable
    ?_ ?_ ?_
  · refine ae_of_all _ fun t ht w hw ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hlow : δ ≤ ‖1 - (t : ℂ) * w‖ := hδK w hw t (Ioc_subset_Icc_self ht)
    dsimp only [F', bound]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, div_eq_inv_mul]
    gcongr
  · have hbound_eq : bound = fun t : ℝ ↦ δ⁻¹ * ‖Real.log t ^ k‖ := by
      ext t
      dsimp only [bound]
      rw [Real.norm_eq_abs, abs_pow]
    rw [hbound_eq]
    exact (TauCeti.intervalIntegrable_log_pow k).norm.const_mul δ⁻¹
  · refine ae_of_all _ fun t ht w hw ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hslit : 1 - (t : ℂ) * w ∈ Complex.slitPlane :=
      one_sub_ofReal_mul_mem_slitPlane (hKΩ hw) ht.1.le ht.2
    have hinner : HasDerivAt (fun u : ℂ ↦ 1 - (t : ℂ) * u) (-(t : ℂ)) w := by
      simpa using ((hasDerivAt_id w).const_mul (t : ℂ)).const_sub (1 : ℂ)
    have hlog := (((Complex.hasDerivAt_log hslit).comp w hinner).neg.const_mul
      (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ)
    have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
    have hdenom_ne : 1 - (t : ℂ) * w ≠ 0 := Complex.slitPlane_ne_zero hslit
    refine hlog.congr_deriv ?_
    dsimp only [F']
    field_simp [ht_ne, hdenom_ne]

/-- For `z` in the principal domain `1 - z ∈ Complex.slitPlane`, the differentiated radial kernel
`t ↦ (-log t) ^ k / (1 - t z)` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_deriv_radialIntegrand (k : ℕ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) volume 0 1 :=
  (intervalIntegrable_and_hasDerivAt_radialIntegral k hz).1

/-- Differentiating the defining radial integral under the integral sign gives the complex
derivative of `polylog (k + 2)` on the principal domain `1 - z ∈ Complex.slitPlane`. -/
theorem hasDerivAt_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((Nat.factorial k : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z)) z := by
  have hd := (intervalIntegrable_and_hasDerivAt_radialIntegral k hz).2.const_mul
    (Nat.factorial k : ℂ)⁻¹
  exact hd.congr_of_eventuallyEq (Eventually.of_forall (polylog_nat_add_two k))

/-- Every integer-weight polylogarithm is complex differentiable at each point of the principal
domain `1 - z ∈ Complex.slitPlane`. -/
theorem differentiableAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (polylog n) z := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · exact (hasDerivAt_polylog_zero_weight (ne_one_of_one_sub_mem_slitPlane hz)).differentiableAt
    · exact (hasDerivAt_polylog_one hz).differentiableAt
    · exact (hasDerivAt_polylog_nat_add_two k hz).differentiableAt
  | negSucc r =>
    exact (analyticAt_polylog_neg_nat (r + 1)
      (ne_one_of_one_sub_mem_slitPlane hz)).differentiableAt

/-- Every integer-weight polylogarithm is complex differentiable on the principal domain
`{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableOn_polylog (n : ℤ) :
    DifferentiableOn ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  fun _ hz ↦ (differentiableAt_polylog n hz).differentiableWithinAt

/-- Every integer-weight polylogarithm is holomorphic (`AnalyticOnNhd`) on the principal domain
`ℂ ∖ [1, ∞) = {z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  (differentiableOn_polylog n).analyticOnNhd isOpen_principalDomain

/-- Pointwise form of `analyticOnNhd_polylog`: `polylog n` is complex analytic at every point with
`1 - z ∈ Complex.slitPlane`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z :=
  analyticOnNhd_polylog n z hz

/-- Euler differential recursion on the principal domain: for every integer weight `n` and every
`z` with `1 - z ∈ Complex.slitPlane`, `z * deriv (polylog (n + 1)) z = polylog n z` (including at
`z = 0`, where both sides vanish). -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  have hlhs : AnalyticOnNhd ℂ (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w)
      {w : ℂ | 1 - w ∈ Complex.slitPlane} :=
    fun w hw ↦ analyticAt_id.mul (analyticAt_polylog (n + 1) hw).deriv
  have hev : (fun w : ℂ ↦ w * deriv (polylog (n + 1)) w) =ᶠ[𝓝 (0 : ℂ)] polylog n := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
    exact mul_deriv_polylog_add_one_of_norm_lt_one n (by simpa using hw)
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_polylog n)
    isPreconnected_principalDomain zero_mem_principalDomain hev hz

/-- Shifted-index form of the Euler differential recursion on the principal domain:
`z * deriv (polylog n) z = polylog (n - 1) z` for every `n : ℤ` and `1 - z ∈ Complex.slitPlane`. -/
theorem mul_deriv_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog n) z = polylog (n - 1) z := by
  simpa [sub_add_cancel] using mul_deriv_polylog_add_one (n - 1) hz

/-- Away from `0` in the principal domain, `deriv (polylog (n + 1)) z = polylog n z / z`. -/
theorem deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog (n + 1)) z = polylog n z / z := by
  rw [eq_div_iff hz0, mul_comm]
  exact mul_deriv_polylog_add_one n hz

/-- Away from `0` in the principal domain, `polylog (n + 1)` has complex derivative
`polylog n z / z`. -/
theorem hasDerivAt_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    (hz0 : z ≠ 0) :
    HasDerivAt (polylog (n + 1)) (polylog n z / z) z :=
  deriv_polylog_add_one n hz hz0 ▸ (differentiableAt_polylog (n + 1) hz).hasDerivAt

/-- Away from `0` in the principal domain, `deriv (polylog n) z = polylog (n - 1) z / z`. -/
theorem deriv_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    deriv (polylog n) z = polylog (n - 1) z / z := by
  simpa [sub_add_cancel] using deriv_polylog_add_one (n - 1) hz hz0

/-- Away from `0` in the principal domain, `polylog n` has complex derivative
`polylog (n - 1) z / z`. -/
theorem hasDerivAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) (hz0 : z ≠ 0) :
    HasDerivAt (polylog n) (polylog (n - 1) z / z) z :=
  deriv_polylog n hz hz0 ▸ (differentiableAt_polylog n hz).hasDerivAt

private lemma continuousOn_mul_deriv_polylog_add_one (n : ℤ) {z : ℂ}
    (hz : 1 - z ∈ Complex.slitPlane) :
    ContinuousOn (fun t : ℝ ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z)) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one]
  intro t ht
  have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
    one_sub_ofReal_mul_mem_slitPlane hz ht.1 ht.2
  have hcont_inner : ContinuousAt (fun s : ℝ ↦ (s : ℂ) * z) t :=
    Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  have hcont_deriv : ContinuousAt (fun s : ℝ ↦ deriv (polylog (n + 1)) ((s : ℂ) * z)) t :=
    ContinuousAt.comp (g := deriv (polylog (n + 1))) (f := fun s : ℝ ↦ (s : ℂ) * z)
      (analyticAt_polylog (n + 1) htz).deriv.continuousAt hcont_inner
  exact (continuousAt_const.mul hcont_deriv).continuousWithinAt

/-- For every integer weight `n` and `z` in the principal domain `1 - z ∈ Complex.slitPlane`, the
recursive radial integrand `t ↦ polylog n (t * z) / t` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_polylog_div (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ ↦ polylog n ((t : ℂ) * z) / (t : ℂ)) volume 0 1 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z)) volume 0 1 :=
    (continuousOn_mul_deriv_polylog_add_one n hz).intervalIntegrable
  refine hbase.congr fun t ht ↦ ?_
  rw [uIoc_of_le zero_le_one] at ht
  have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
    one_sub_ofReal_mul_mem_slitPlane hz ht.1.le ht.2
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
  rw [← mul_deriv_polylog_add_one n htz]
  field_simp [ht_ne]

/-- Recursive radial-integral representation on the principal domain: for every integer weight `n`
and every `z` with `1 - z ∈ Complex.slitPlane`,
`polylog (n + 1) z = ∫ t in 0..1, polylog n (t * z) / t`. -/
theorem polylog_add_one_eq_integral (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog (n + 1) z = ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) := by
  let g : ℝ → ℂ := polylog (n + 1) ∘ fun t : ℝ ↦ (t : ℂ) * z
  let g' : ℝ → ℂ := fun t ↦ z * deriv (polylog (n + 1)) ((t : ℂ) * z)
  have hg_deriv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      one_sub_ofReal_mul_mem_slitPlane hz ht.1 ht.2
    have hinner : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * z) z t :=
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).congr_deriv (one_mul z)
    exact (HasDerivAt.scomp (𝕜 := ℝ) (𝕜' := ℂ) (F := ℂ) t
      (differentiableAt_polylog (n + 1) htz).hasDerivAt hinner).congr_deriv (smul_eq_mul _ _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv
    (continuousOn_mul_deriv_polylog_add_one n hz).intervalIntegrable
  have hcongr : ∫ t : ℝ in 0..1, polylog n ((t : ℂ) * z) / (t : ℂ) = ∫ t : ℝ in 0..1, g' t := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      one_sub_ofReal_mul_mem_slitPlane hz ht.1.le ht.2
    have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
    dsimp only [g']
    rw [← mul_deriv_polylog_add_one n htz]
    field_simp [ht_ne]
  rw [hcongr, hftc]
  simp [g]

/-- Nonpositive-weight polylogarithms commute with complex conjugation everywhere on `ℂ`,
including at the totalised pole `z = 1` where both sides vanish, because they are rational
functions with integer coefficients. -/
theorem polylog_neg_nat_conj (r : ℕ) (z : ℂ) :
    polylog (-(r : ℤ)) (starRingEnd ℂ z) = starRingEnd ℂ (polylog (-(r : ℤ)) z) := by
  rw [polylog_neg_nat_eq_div, polylog_neg_nat_eq_div]
  have haeval : starRingEnd ℂ (aeval z (eulerianPolynomial r)) =
      aeval (starRingEnd ℂ z) (eulerianPolynomial r) := by
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂,
      Subsingleton.elim ((starRingEnd ℂ).comp (algebraMap ℤ ℂ)) (algebraMap ℤ ℂ)]
  rw [map_div₀, map_mul, map_pow, map_sub, map_one, haeval]

/-- Schwarz reflection for principal polylogarithms: on the conjugation-invariant principal domain
`1 - z ∈ Complex.slitPlane`, `polylog n` commutes with complex conjugation in every integer
weight `n`. -/
theorem polylog_conj (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog n (starRingEnd ℂ z) = starRingEnd ℂ (polylog n z) := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · exact polylog_neg_nat_conj 0 z
    · change polylog 1 (starRingEnd ℂ z) = starRingEnd ℂ (polylog 1 z)
      rw [polylog_one, polylog_one, map_neg, ← Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hz),
        map_sub, map_one]
    · change polylog (k + 2 : ℕ) (starRingEnd ℂ z) = starRingEnd ℂ (polylog (k + 2 : ℕ) z)
      have hcomm := Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm
        (a := (0 : ℝ)) (b := 1) (μ := volume)
        (f := fun t : ℝ ↦
          ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ))
      simp only [LinearIsometryEquiv.coe_toLinearIsometry, Complex.conjLIE_apply] at hcomm
      rw [polylog_nat_add_two, polylog_nat_add_two, map_mul, map_inv₀, map_natCast, ← hcomm]
      congr 1
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le zero_le_one] at ht
      have htz : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
        one_sub_ofReal_mul_mem_slitPlane hz ht.1 ht.2
      simp only [map_div₀, map_mul, map_pow, map_neg,
        Complex.conj_ofReal, ← Complex.log_conj _ (Complex.slitPlane_arg_ne_pi htz),
        map_sub, map_one]
  | negSucc r =>
    exact polylog_neg_nat_conj (r + 1) z

/-- For every real argument `x < 1` and every integer weight `n`, `polylog n x` has zero imaginary
part. -/
theorem im_polylog_ofReal (n : ℤ) {x : ℝ} (hx : x < 1) :
    (polylog n x).im = 0 := by
  have hxΩ : 1 - (x : ℂ) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_mem_slitPlane.2 (sub_pos.2 hx)
  exact Complex.conj_eq_iff_im.1 ((polylog_conj n hxΩ).symm.trans (by rw [Complex.conj_ofReal]))

/-- For every real argument `x < 1` and every integer weight `n`, `polylog n x` equals its real
part coerced back to `ℂ`. -/
theorem ofReal_re_polylog_ofReal (n : ℤ) {x : ℝ} (hx : x < 1) :
    ((polylog n x).re : ℂ) = polylog n x :=
  Complex.ext (by simp) (by simp [im_polylog_ofReal n hx])

/-- At `z = -1`, every integer-weight polylogarithm is real. -/
theorem im_polylog_neg_one (n : ℤ) : (polylog n (-1)).im = 0 := by
  simpa using im_polylog_ofReal n (x := -1) (by norm_num)

/-- On the branch cut `(1, ∞)`, conjugation compatibility fails in positive weight because
`polylog` selects the lower boundary value: at `z = 3`, `polylog 1 (conj 3) = -log 2 - π i` whereas
`conj (polylog 1 3) = -log 2 + π i`. -/
theorem polylog_one_conj_three_ne :
    polylog 1 (starRingEnd ℂ 3) ≠ starRingEnd ℂ (polylog 1 3) := by
  rw [map_ofNat (starRingEnd ℂ) 3]
  intro h
  have him : (polylog 1 3).im = 0 := Complex.conj_eq_iff_im.1 h.symm
  rw [polylog_one_three] at him
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, neg_zero, zero_sub, neg_eq_zero] at him
  exact Real.pi_ne_zero him

end TauCeti.Polylog
