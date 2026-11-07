/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Integral.RieszPotential
import TauCeti.MeasureTheory.Integral.SchurTest
import TauCeti.MeasureTheory.Measure.MeasurableHull

/-!
# The Poincaré–Wirtinger inequality for `C¹` functions on a convex domain

Let `Ω` be a bounded convex open subset of a finite-dimensional real normed space `E` of
dimension `n`, let `μ` be an additive Haar measure, and let `S ⊆ Ω` have positive measure. For a
`C¹` function `u` on `Ω` and `1 ≤ p < ∞`, this file proves

`‖u - ⨍ y in S, u y ∂μ‖_{Lᵖ(Ω)} ≤ C * ‖Du‖_{Lᵖ(Ω)}`, where
`C = μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)`.

The constant depends only on the dimension, through the Haar measure of the unit ball, on the
diameter of `Ω` and on the measure of `S`, as it must: rescaling `Ω` by `t` multiplies it by
`t`. The mean may be taken over any subset of positive measure, not only over `Ω` itself.

The proof bounds the deviation `u x - ⨍ S u` pointwise by the Riesz potential
`∫_Ω ‖Du y‖ ‖x - y‖ ^ (1 - n) dy` (`TauCeti.enorm_sub_setAverage_le_of_convex`), and bounds that
potential in `Lᵖ(Ω)` by Schur's test (`TauCeti.lintegral_rpow_lintegral_mul_le`): since `Ω` lies
in the closed ball of radius `diam Ω` about each of its points, the integral of the kernel
`‖x - y‖ ^ (1 - n)` over `Ω` in either variable is at most `n μ(B(0, 1)) diam Ω`. The constant is
not sharp; Gilbarg–Trudinger obtain `(μ(B(0, 1)) / μ(S)) ^ (1 - 1/n) (diam Ω) ^ n` from a finer
bound on the Riesz potential.

Integrating the pointwise estimate over a subset `A ⊆ Ω` instead, the integral of the kernel
over `A` is at most its integral over a ball of the same measure as `A`
(`TauCeti.setLIntegral_enorm_sub_rpow_le`), which gives a factor `μ(A) ^ (1/n)`. The resulting
bound on `∫_A ‖u - ⨍ S u‖` is a weak-type `L^{n/(n-1)}` Poincaré inequality, implied by the
strong `L^{n/(n-1)}` Sobolev–Poincaré inequality through Hölder's inequality, and it is invariant
under rescaling `Ω`.

## Main declarations

* `TauCeti.lintegral_enorm_sub_setAverage_rpow_le_of_convex`: the inequality in `∫⁻` form.
* `TauCeti.eLpNorm_sub_setAverage_le_of_convex`: the inequality between `Lᵖ` seminorms.
* `TauCeti.setIntegral_norm_sub_setAverage_sq_le_of_convex`: the case `p = 2` for Bochner
  integrals of squared norms, for maps that are `C¹` on the whole space.
* `TauCeti.setIntegral_norm_sq_le_of_convex`: the consequence
  `∫_Ω ‖u‖² ≤ (2 + 4 μ(Ω)/μ(S)) C² ∫_Ω ‖Du‖² + (4 μ(Ω)/μ(S)) ∫_S ‖u‖²`, which bounds `u` on `Ω`
  by its derivative and its size on the subset `S`.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_of_convex`: the `L¹`
  deviation on a subset `A ⊆ Ω` is at most `μ(B(0, 1)) ^ (1 - 1/n) * (diam Ω) ^ n / μ(S)` times
  `μ(A) ^ (1/n) ‖Du‖_{L¹(Ω)}`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16 and equation (7.45).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω S : Set E}

/-- **The Poincaré–Wirtinger inequality on a convex domain**, in `∫⁻` form. If `u` is `C¹` on a
bounded convex open set `Ω` and `S ⊆ Ω` has positive measure, then for `1 ≤ p` the `p`-th power
of the deviation of `u` from its mean over `S` has integral over `Ω` at most `C ^ p` times the
integral of `‖Du‖ ^ p` over `Ω`, where `C = μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` and `n` is
the dimension of the space. -/
theorem lintegral_enorm_sub_setAverage_rpow_le_of_convex (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) {p : ℝ}
    (hp : 1 ≤ p) :
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal ((μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) ^ p) *
        ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ ^ p ∂μ := by
  set n := finrank ℝ E
  set d := diam Ω
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hS_top : μ S ≠ ∞ := ((measure_mono hS).trans_lt hb.measure_lt_top).ne
  -- The Riesz kernel and its potential of the norm of the derivative.
  set k : E → E → ℝ≥0∞ := fun x y => ‖x - y‖ₑ ^ (1 - (n : ℝ))
  set V : E → ℝ≥0∞ := fun x => ∫⁻ y in Ω, k x y * ‖fderiv ℝ u y‖ₑ ∂μ
  -- The pointwise potential estimate, with its constant `c`.
  set c : ℝ≥0∞ := ENNReal.ofReal (d ^ n / n) / μ S
  have hpoint : ∀ x ∈ Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤ c * V x := fun x hx => by
    simpa only [V, k, mul_comm (‖fderiv ℝ u _‖ₑ)] using
      enorm_sub_setAverage_le_of_convex hΩ hΩc hb hu hx hS hS₀
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero the left-hand side vanishes.
    rw [setLIntegral_congr_fun hΩ.measurableSet fun x hx => by
      rw [enorm_sub_setAverage_eq_zero_of_subsingleton x hS₀ hS_top,
        ENNReal.zero_rpow_of_pos (zero_lt_one.trans_le hp)], lintegral_zero]
    exact bot_le
  have hn : 0 < (n : ℝ) := Nat.cast_pos.2 finrank_pos
  have hd : 0 ≤ d := diam_nonneg
  -- Schur's test for the kernel `k` on `Ω`: both of its marginal integrals are at most `K`.
  set K : ℝ := n * μ.real (ball 0 1) * d
  have hK : 0 ≤ K := by positivity
  have hmarg : ∀ x ∈ Ω, ∫⁻ y in Ω, k x y ∂μ ≤ ENNReal.ofReal K := fun x hx =>
    lintegral_enorm_sub_rpow_le_of_mem hb hx
  have hcont := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hschur : ∫⁻ x in Ω, V x ^ p ∂μ ≤
      ENNReal.ofReal K ^ (p - 1) * ENNReal.ofReal K * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ ^ p ∂μ :=
    lintegral_rpow_lintegral_mul_le (by fun_prop)
      (hcont.enorm.aemeasurable hΩ.measurableSet) hp
      ((ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ hmarg))
      ((ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun y hy => by
        simpa only [k, enorm_sub_rev y] using hmarg y hy))
  -- Assemble the constant.
  have hcK : c * ENNReal.ofReal K =
      ENNReal.ofReal (μ.real (ball 0 1) * d ^ (n + 1) / μ.real S) := by
    rw [show K = n * (μ.real (ball 0 1) * d) by ring,
      ENNReal.ofReal_pow_div_natCast_div_mul_ofReal_natCast_mul finrank_pos hd hS₀ hS_top]
    congr 1
    simp only [Measure.real]
    ring
  have hKp : ENNReal.ofReal K ^ (p - 1) * ENNReal.ofReal K = ENNReal.ofReal K ^ p := by
    rw [ENNReal.ofReal_rpow_of_nonneg hK (by linarith), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hK hp0, ← Real.rpow_add_one' hK (by linarith), sub_add_cancel]
  calc
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ^ p ∂μ ≤ ∫⁻ x in Ω, c ^ p * V x ^ p ∂μ :=
      setLIntegral_mono' hΩ.measurableSet fun x hx => by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0]
        exact ENNReal.rpow_le_rpow (hpoint x hx) hp0
    _ = c ^ p * ∫⁻ x in Ω, V x ^ p ∂μ := lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hp0 (ENNReal.div_ne_top ENNReal.ofReal_ne_top hS₀))
    _ ≤ c ^ p * (ENNReal.ofReal K ^ p * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) := by
      rw [← hKp]
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hp0, hcK,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0]

/-- **The Poincaré–Wirtinger inequality on a convex domain, localized to a subset.** If `u` is
`C¹` on a bounded convex open set `Ω` and `S ⊆ Ω` has positive measure, then for every `A ⊆ Ω` the
integral over `A` of the deviation of `u` from its mean over `S` is at most
`μ(B(0, 1)) ^ (1 - 1/n) * (diam Ω) ^ n / μ(S) * μ(A) ^ (1/n)` times the integral of `‖Du‖` over
`Ω`, where `n` is the dimension of the space. The factor `μ(A) ^ (1/n)` makes this a weak-type
`L^{n/(n-1)}` Poincaré inequality. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_of_convex (hΩ : IsOpen Ω)
    (hΩc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) {A : Set E} (hA : A ⊆ Ω) :
    ∫⁻ x in A, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) * diam Ω ^ finrank ℝ E /
        μ.real S) * μ A ^ (finrank ℝ E : ℝ)⁻¹ * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ ∂μ := by
  set n := finrank ℝ E
  set d := diam Ω
  have hS_top : μ S ≠ ∞ := ((measure_mono hS).trans_lt hb.measure_lt_top).ne
  -- It suffices to treat a measurable set `A' ⊇ A` in `Ω` of the same measure.
  obtain ⟨A', hAA', hA'Ω, hA'm, hμA'⟩ := exists_measurableSet_subset_measure_eq (μ := μ)
    hΩ.measurableSet hA
  refine (lintegral_mono_set hAA').trans ?_
  rw [← hμA']
  -- The Riesz kernel and the pointwise potential estimate, with its constant `c`.
  set k : E → E → ℝ≥0∞ := fun x y => ‖x - y‖ₑ ^ (1 - (n : ℝ))
  set c : ℝ≥0∞ := ENNReal.ofReal (d ^ n / n) / μ S with hc_def
  have hpoint : ∀ x ∈ Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      c * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ * k x y ∂μ := fun x hx =>
    enorm_sub_setAverage_le_of_convex hΩ hΩc hb hu hx hS hS₀
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero the left-hand side vanishes.
    have hzero : ∀ x ∈ A', ‖u x - ⨍ y in S, u y ∂μ‖ₑ = 0 := fun x hx =>
      enorm_sub_setAverage_eq_zero_of_subsingleton x hS₀ hS_top
    rw [setLIntegral_congr_fun hA'm hzero, lintegral_zero]
    exact bot_le
  -- The kernel bound `∫_{A'} ‖x - y‖ ^ (1 - n) dx ≤ n ω ^ (1 - 1/n) μ(A') ^ (1/n)`.
  set K : ℝ := n * μ.real (ball 0 1) ^ (1 - (n : ℝ)⁻¹)
  have hkA (y : E) : ∫⁻ x in A', k x y ∂μ ≤ ENNReal.ofReal K * μ A' ^ (n : ℝ)⁻¹ := by
    simpa only [k, enorm_sub_rev y] using setLIntegral_enorm_sub_rpow_le_finrank hA'm y
  have hmeas : AEMeasurable (Function.uncurry fun x y => ‖fderiv ℝ u y‖ₑ * k x y)
      ((μ.restrict A').prod (μ.restrict Ω)) :=
    ((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).enorm.aemeasurable
      hΩ.measurableSet).comp_snd.mul (by fun_prop)
  have hc : c * ENNReal.ofReal K =
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (n : ℝ)⁻¹) * d ^ n / μ.real S) :=
    ENNReal.ofReal_pow_div_natCast_div_mul_ofReal_natCast_mul finrank_pos diam_nonneg hS₀ hS_top
  calc ∫⁻ x in A', ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ
      ≤ ∫⁻ x in A', c * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ * k x y ∂μ ∂μ :=
        setLIntegral_mono' hA'm fun x hx => hpoint x (hA'Ω hx)
    _ = c * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ * ∫⁻ x in A', k x y ∂μ ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.div_ne_top ENNReal.ofReal_ne_top hS₀),
          lintegral_lintegral_swap hmeas]
        congr 1
        exact lintegral_congr fun y => lintegral_const_mul _ (by fun_prop)
    _ ≤ c * ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ * (ENNReal.ofReal K * μ A' ^ (n : ℝ)⁻¹) ∂μ := by
        gcongr with y
        exact hkA y
    _ = _ := by
        have hA'fin : μ A' ≠ ∞ :=
          ne_top_of_le_ne_top hb.measure_lt_top.ne (measure_mono hA'Ω)
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) hA'fin)), ← hc]
        ring

/-- **The Poincaré–Wirtinger inequality on a convex domain.** If `u` is `C¹` on a bounded convex
open set `Ω` and `S ⊆ Ω` has positive measure, then for `1 ≤ p < ∞` the `Lᵖ(Ω)` seminorm of the
deviation of `u` from its mean over `S` is at most `μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` times
the `Lᵖ(Ω)` seminorm of the derivative of `u`, where `n` is the dimension of the space. -/
theorem eLpNorm_sub_setAverage_le_of_convex (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => u x - ⨍ y in S, u y ∂μ) p (μ.restrict Ω) ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) *
        eLpNorm (fderiv ℝ u) p (μ.restrict Ω) :=
  eLpNorm_le_eLpNorm_of_lintegral_rpow_le (by positivity) (zero_lt_one.trans_le hp).ne' hp'
    ((hu.continuousOn.aestronglyMeasurable hΩ.measurableSet).sub aestronglyMeasurable_const)
    (lintegral_enorm_sub_setAverage_rpow_le_of_convex hΩ hΩc hb hu hS hS₀
      (by simpa using ENNReal.toReal_mono hp' hp))

/-- **The Poincaré–Wirtinger inequality on a convex domain**, for `p = 2` and Bochner integrals.
If `u` is `C¹`, `Ω` is a bounded convex open set and `S ⊆ Ω` has positive measure, the integral
over `Ω` of the squared deviation of `u` from its mean over `S` is at most `C ^ 2` times the
integral of `‖Du‖ ^ 2` over `Ω`, where `C = μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)`. -/
theorem setIntegral_norm_sub_setAverage_sq_le_of_convex (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiff ℝ 1 u) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) :
    ∫ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ ^ 2 ∂μ ≤
      (μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) ^ 2 *
        ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2 ∂μ := by
  have h := lintegral_enorm_sub_setAverage_rpow_le_of_convex (μ := μ) hΩ hΩc hb hu.contDiffOn
    hS hS₀ one_le_two
  have hpowF (v : F) : ENNReal.ofReal (‖v‖ ^ 2) = ‖v‖ₑ ^ 2 := by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hpowL (L : E →L[ℝ] F) : ENNReal.ofReal (‖L‖ ^ 2) = ‖L‖ₑ ^ 2 := by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  -- Continuous functions are integrable on the compact closure of `Ω`.
  have hi₁ : IntegrableOn (fun x ↦ ‖u x - ⨍ y in S, u y ∂μ‖ ^ 2) Ω μ :=
    ((Continuous.continuousOn (by fun_prop)).integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  have hi₂ : IntegrableOn (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) Ω μ :=
    ((((hu.continuous_fderiv one_ne_zero).norm.pow 2).continuousOn).integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hi₁ (ae_of_all _ fun _ ↦ by positivity),
    ofReal_integral_eq_lintegral_ofReal hi₂ (ae_of_all _ fun _ ↦ by positivity)]
  simp only [hpowF, hpowL]
  simpa only [Real.rpow_two, ENNReal.rpow_two] using h


/-- **The Poincaré inequality on a convex domain, relative to a subset.** If `u` is `C¹`, `Ω` is a
bounded convex open set and `S ⊆ Ω` is measurable with positive measure, then `∫_Ω ‖u‖²` is at
most `(2 + 4 μ(Ω) / μ(S)) C ^ 2 ∫_Ω ‖Du‖² + (4 μ(Ω) / μ(S)) ∫_S ‖u‖²`, where
`C = μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` is the Poincaré–Wirtinger constant. -/
theorem setIntegral_norm_sq_le_of_convex (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiff ℝ 1 u) (hSm : MeasurableSet S) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) :
    ∫ x in Ω, ‖u x‖ ^ 2 ∂μ ≤
      (2 + 4 * μ.real Ω / μ.real S) *
          (μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) ^ 2 *
          ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2 ∂μ +
        4 * μ.real Ω / μ.real S * ∫ x in S, ‖u x‖ ^ 2 ∂μ := by
  set m := ⨍ y in S, u y ∂μ
  set C := μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S
  have hΩfin : μ Ω ≠ ∞ := hb.measure_lt_top.ne
  have hs : 0 < μ.real S :=
    ENNReal.toReal_pos hS₀ ((measure_mono hS).trans_lt hb.measure_lt_top).ne
  have hV : 0 ≤ μ.real Ω := measureReal_nonneg
  have hcpt := hb.isCompact_closure
  have hdev : IntegrableOn (fun x ↦ ‖u x - m‖ ^ 2) Ω μ :=
    ((Continuous.continuousOn (by fun_prop)).integrableOn_compact hcpt).mono_set subset_closure
  have hsq : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) Ω μ :=
    ((Continuous.continuousOn (by fun_prop)).integrableOn_compact hcpt).mono_set subset_closure
  have hX := setIntegral_norm_sub_setAverage_sq_le_of_convex (μ := μ) hΩ hΩc hb hu hS hS₀
  -- The mean over `S` is controlled by the deviation and by `∫_S ‖u‖²`.
  have hm : μ.real S * ‖m‖ ^ 2 ≤
      2 * ∫ x in Ω, ‖u x - m‖ ^ 2 ∂μ + 2 * ∫ x in S, ‖u x‖ ^ 2 ∂μ := by
    have hpt (x : E) : ‖m‖ ^ 2 ≤ 2 * ‖u x - m‖ ^ 2 + 2 * ‖u x‖ ^ 2 := by
      have h := norm_sub_le (u x) (u x - m)
      rw [sub_sub_cancel] at h
      nlinarith [sq_nonneg (‖u x‖ - ‖u x - m‖), norm_nonneg m]
    calc μ.real S * ‖m‖ ^ 2 = ∫ _ in S, ‖m‖ ^ 2 ∂μ := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ x in S, (2 * ‖u x - m‖ ^ 2 + 2 * ‖u x‖ ^ 2) ∂μ :=
        setIntegral_mono_on (integrableOn_const ((measure_mono hS).trans_lt
          hb.measure_lt_top).ne) (((hdev.mono_set hS).const_mul 2).fun_add
          ((hsq.mono_set hS).const_mul 2)) hSm fun x _ ↦ hpt x
      _ = 2 * ∫ x in S, ‖u x - m‖ ^ 2 ∂μ + 2 * ∫ x in S, ‖u x‖ ^ 2 ∂μ := by
        rw [integral_add ((hdev.mono_set hS).const_mul 2) ((hsq.mono_set hS).const_mul 2),
          integral_const_mul, integral_const_mul]
      _ ≤ _ := by
        gcongr 2 * ?_ + _
        exact setIntegral_mono_set hdev (ae_of_all _ fun _ ↦ by positivity) hS.eventuallyLE
  -- On `Ω`, `‖u‖²` is controlled by the deviation and the mean.
  have hU : ∫ x in Ω, ‖u x‖ ^ 2 ∂μ ≤
      2 * ∫ x in Ω, ‖u x - m‖ ^ 2 ∂μ + 2 * μ.real Ω * ‖m‖ ^ 2 := by
    have hpt (x : E) : ‖u x‖ ^ 2 ≤ 2 * ‖u x - m‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
      have h := norm_add_le (u x - m) m
      rw [sub_add_cancel] at h
      nlinarith [sq_nonneg (‖u x - m‖ - ‖m‖), norm_nonneg (u x)]
    calc ∫ x in Ω, ‖u x‖ ^ 2 ∂μ ≤ ∫ x in Ω, (2 * ‖u x - m‖ ^ 2 + 2 * ‖m‖ ^ 2) ∂μ :=
          setIntegral_mono_on hsq ((hdev.const_mul 2).fun_add
            (integrableOn_const hΩfin).integrable) hΩ.measurableSet fun x _ ↦ hpt x
      _ = _ := by
        rw [integral_add (hdev.const_mul 2) (integrableOn_const hΩfin).integrable,
          integral_const_mul, setIntegral_const, smul_eq_mul]
        ring
  refine le_of_mul_le_mul_left ?_ hs
  have e : μ.real S * ((2 + 4 * μ.real Ω / μ.real S) * C ^ 2 * ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2 ∂μ +
      4 * μ.real Ω / μ.real S * ∫ x in S, ‖u x‖ ^ 2 ∂μ) =
      (2 * μ.real S + 4 * μ.real Ω) * (C ^ 2 * ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2 ∂μ) +
        4 * μ.real Ω * ∫ x in S, ‖u x‖ ^ 2 ∂μ := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hU hs.le, mul_le_mul_of_nonneg_left hm hV,
    mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ 2 * μ.real S + 4 * μ.real Ω)]

end TauCeti
