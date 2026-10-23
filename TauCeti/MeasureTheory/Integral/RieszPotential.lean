/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.NormRpow
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Riesz potentials on sets of finite measure

Let `E` be a real normed space of finite dimension `n ≥ 1` with an additive Haar measure `μ`, let
`ω = μ(B(0, 1))`, and let `Ω ⊆ E` be measurable. For `0 < κ ≤ 1` this file studies the potential

`V f (x) = ∫_Ω ‖x - y‖ ^ (n (κ - 1)) f(y) dy`,

whose kernel is the Riesz kernel of order `n κ`. Its two main estimates are those of
Gilbarg–Trudinger, Lemma 7.12, which drive the Sobolev embeddings in the potential-theoretic
approach:

* the kernel integral `∫_Ω ‖x - y‖ ^ (n (κ - 1)) dy` is at most `κ⁻¹ ω ^ (1 - κ) μ(Ω) ^ κ`,
  uniformly in `x`;
* for `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < κ`, the potential maps `Lᵖ(Ω)` to `L^q(Ω)`:
  `‖V f‖_q ≤ ((1 - δ) / (κ - δ)) ^ (1 - δ) ω ^ (1 - κ) μ(Ω) ^ (κ - δ) ‖f‖_p`.

The kernel bound follows from a rearrangement inequality, valid in any metric measure space: a
radially nonincreasing function of `dist x y` integrates over `Ω` to at most its integral over a
closed ball about `x` of no smaller measure. The `Lᵖ`-`L^q` bound is then Young's inequality for
integral kernels (`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`), applied to the
kernel raised to the power `r = 1 / (1 - δ)`, which is again a Riesz kernel, of order
`n (κ - δ) / (1 - δ)`.

The case `κ = 1/n`, `p = n`, where the kernel is `‖x - y‖ ^ (1 - n)` and the bound holds for
every finite `q ≥ n` with a constant of order `q ^ (1 - 1/n)`, is the input to the borderline
Sobolev embedding of `W^{1,n}_0(Ω)`.

## Main declarations

* `TauCeti.setLIntegral_le_setLIntegral_closedBall_of_antitone`: balls maximise the integrals of
  radially nonincreasing kernels among sets of no larger measure.
* `TauCeti.setLIntegral_enorm_sub_rpow_le`: the kernel bound.
* `TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`: the `Lᵖ`-`L^q` bound for the potential.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.12.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

section Rearrangement

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X}

/-- **Balls maximise integrals of radially nonincreasing kernels.** If `f` is antitone and the
measurable set `Ω` has measure at most that of the closed ball `closedBall x R`, which is finite,
then `∫_Ω f (dist x y) dy ≤ ∫_{closedBall x R} f (dist x y) dy`. -/
theorem setLIntegral_le_setLIntegral_closedBall_of_antitone {f : ℝ → ℝ≥0∞} (hf : Antitone f)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (x : X) {R : ℝ} (hR : μ (closedBall x R) ≠ ∞)
    (hΩR : μ Ω ≤ μ (closedBall x R)) :
    ∫⁻ y in Ω, f (dist x y) ∂μ ≤ ∫⁻ y in closedBall x R, f (dist x y) ∂μ := by
  set B := closedBall x R
  have hB : MeasurableSet B := measurableSet_closedBall
  -- Off `B` the kernel is at most `f R`, and on `B` it is at least `f R`.
  have hout : ∫⁻ y in Ω \ B, f (dist x y) ∂μ ≤ f R * μ (Ω \ B) := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset (fun y hy => hy.2)
      (ae_restrict_of_forall_mem hB.compl fun y hy => hf ?_))
    exact (not_le.1 fun h => hy (mem_closedBall'.2 h)).le
  have hin : f R * μ (B \ Ω) ≤ ∫⁻ y in B \ Ω, f (dist x y) ∂μ := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset sdiff_subset
      (ae_restrict_of_forall_mem hB fun y hy => hf (mem_closedBall'.1 hy)))
  -- The part of `Ω` outside `B` is no larger than the part of `B` outside `Ω`.
  have hmeas : μ (Ω \ B) ≤ μ (B \ Ω) := by
    have h₁ := measure_inter_add_sdiff (μ := μ) Ω hB
    have h₂ := measure_inter_add_sdiff (μ := μ) B hΩ
    rw [inter_comm] at h₂
    have hfin : μ (Ω ∩ B) ≠ ∞ := ne_top_of_le_ne_top hR (measure_mono inter_subset_right)
    exact (ENNReal.add_le_add_iff_left hfin).1 (h₁.trans_le (hΩR.trans h₂.ge))
  calc
    ∫⁻ y in Ω, f (dist x y) ∂μ
        = ∫⁻ y in Ω ∩ B, f (dist x y) ∂μ + ∫⁻ y in Ω \ B, f (dist x y) ∂μ :=
      (lintegral_inter_add_sdiff _ Ω hB).symm
    _ ≤ ∫⁻ y in B ∩ Ω, f (dist x y) ∂μ + ∫⁻ y in B \ Ω, f (dist x y) ∂μ := by
      refine add_le_add (le_of_eq (by rw [inter_comm])) ?_
      exact hout.trans ((by gcongr : f R * μ (Ω \ B) ≤ f R * μ (B \ Ω)).trans hin)
    _ = ∫⁻ y in B, f (dist x y) ∂μ := lintegral_inter_add_sdiff _ B hΩ

end Rearrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Set E}

/-- **The kernel bound for Riesz potentials.** For `0 < κ ≤ 1`, a measurable `Ω` and any pole
`x`, `∫_Ω ‖x - y‖ ^ (n (κ - 1)) dy ≤ κ⁻¹ ω ^ (1 - κ) μ(Ω) ^ κ`, where `n` is the dimension and
`ω = μ(B(0, 1))`. Equality holds when `Ω` is a ball about `x`. -/
theorem setLIntegral_enorm_sub_rpow_le {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hΩ : MeasurableSet Ω) (x : E) :
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) ∂μ ≤
      ENNReal.ofReal (κ⁻¹ * μ.real (ball 0 1) ^ (1 - κ)) * μ Ω ^ κ := by
  set n := finrank ℝ E
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  set ω := μ.real (ball (0 : E) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  rcases eq_or_ne (μ Ω) ∞ with hΩt | hΩt
  · rw [hΩt, ENNReal.top_rpow_of_pos hκ, ENNReal.mul_top (by positivity)]
    exact le_top
  -- The closed ball about `x` with the same measure as `Ω`.
  set R := (μ.real Ω / ω) ^ (n : ℝ)⁻¹
  have hR : 0 ≤ R := by positivity
  have hRn : R ^ n = μ.real Ω / ω := Real.rpow_inv_natCast_pow (by positivity) finrank_pos.ne'
  have hball : μ (closedBall x R) = μ Ω := by
    rw [Measure.addHaar_closedBall μ x hR, hRn, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hω.ne', ofReal_measureReal hΩt]
  -- The kernel is a nonincreasing function of the distance to the pole.
  have hanti : Antitone fun t : ℝ => ENNReal.ofReal t ^ ((n : ℝ) * (κ - 1)) := by
    intro s t hst
    have hexp : (n : ℝ) * (κ - 1) = -((n : ℝ) * (1 - κ)) := by ring
    dsimp only
    rw [hexp, ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hst)
      (mul_nonneg hn.le (by linarith)))
  have hkernel : ∀ y, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) =
      ENNReal.ofReal (dist x y) ^ ((n : ℝ) * (κ - 1)) := fun y => by
    rw [dist_eq_norm, ofReal_norm]
  calc
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) ∂μ
        ≤ ∫⁻ y in closedBall x R, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) ∂μ := by
      simp_rw [hkernel]
      exact setLIntegral_le_setLIntegral_closedBall_of_antitone hanti hΩ x (hball ▸ hΩt)
        hball.ge
    _ = ENNReal.ofReal (n * ω * (R ^ ((n : ℝ) + n * (κ - 1)) / (n + n * (κ - 1)))) :=
      setLIntegral_closedBall_enorm_sub_rpow (by nlinarith) hR x
    _ = ENNReal.ofReal (κ⁻¹ * ω ^ (1 - κ)) * μ Ω ^ κ := by
      have hpow : R ^ ((n : ℝ) + n * (κ - 1)) = (μ.real Ω / ω) ^ κ := by
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        field_simp
        ring
      have hω' : ω ^ (1 - κ) = ω / ω ^ κ := by rw [Real.rpow_sub hω, Real.rpow_one]
      rw [hpow, Real.div_rpow measureReal_nonneg hω.le, ← ofReal_measureReal hΩt,
        ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg hκ.le,
        ← ENNReal.ofReal_mul (by positivity), hω']
      rw [show (n : ℝ) + n * (κ - 1) = n * κ by ring]
      congr 1
      field_simp

/-- **Riesz potentials on sets of finite measure map `Lᵖ` to `L^q`** (Gilbarg–Trudinger,
Lemma 7.12). Let `1 ≤ p ≤ q < ∞`, let `δ = 1/p - 1/q` and let `δ < κ ≤ 1`. For a measurable
`Ω` and `f` almost everywhere measurable on `Ω`, the potential
`V f (x) = ∫_Ω ‖x - y‖ ^ (n (κ - 1)) f(y) dy` satisfies

`‖V f‖_{L^q(Ω)} ≤ ((1 - δ) / (κ - δ)) ^ (1 - δ) ω ^ (1 - κ) μ(Ω) ^ (κ - δ) ‖f‖_{Lᵖ(Ω)}`,

where `n` is the dimension and `ω = μ(B(0, 1))`. -/
theorem eLpNorm_setLIntegral_enorm_sub_rpow_mul_le {p q : ℝ≥0} {κ δ : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hδ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = δ) (hκ : δ < κ) (hκ1 : κ ≤ 1)
    (hΩ : MeasurableSet Ω) {f : E → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict Ω)) :
    eLpNorm (fun x => ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((finrank ℝ E : ℝ) * (κ - 1)) * f y ∂μ) q
        (μ.restrict Ω) ≤
      ENNReal.ofReal (((1 - δ) / (κ - δ)) ^ (1 - δ) * μ.real (ball 0 1) ^ (1 - κ)) *
        μ Ω ^ (κ - δ) * eLpNorm f p (μ.restrict Ω) := by
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hq0 : (0 : ℝ) < q := by linarith
  have hδ1 : δ < 1 := hκ.trans_le hκ1
  -- Young's inequality applies with the exponent `r = 1 / (1 - δ)`, and the `r`-th power of the
  -- kernel is the Riesz kernel of order `n κ'`, `κ' = (κ - δ) / (1 - δ)`.
  set r : ℝ := (1 - δ)⁻¹
  set κ' : ℝ := (κ - δ) / (1 - δ)
  have hκ'0 : 0 < κ' := div_pos (sub_pos.2 hκ) (sub_pos.2 hδ1)
  have hκ'1 : κ' ≤ 1 := (div_le_one (sub_pos.2 hδ1)).2 (by linarith)
  have hr : (p : ℝ)⁻¹ + r⁻¹ = 1 + (q : ℝ)⁻¹ := by rw [inv_inv]; linarith
  set A := ENNReal.ofReal (κ'⁻¹ * ω ^ (1 - κ')) * μ Ω ^ κ'
  have hA : ∀ x, ∫⁻ y in Ω, (‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1))) ^ r ∂μ ≤ A := fun x => by
    have hexp : (n : ℝ) * (κ - 1) * r = n * (κ' - 1) := by
      simp only [r, κ']
      field_simp [(sub_pos.2 hδ1).ne']
      ring
    simp_rw [← ENNReal.rpow_mul, hexp]
    exact setLIntegral_enorm_sub_rpow_le hκ'0 hκ'1 hΩ x
  have hk : Measurable (Function.uncurry fun x y : E => ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1))) := by
    fun_prop
  have hyoung := lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq hk hf hp' hpq' hr
    (ae_of_all _ hA) (ae_of_all _ fun y => by simpa only [enorm_sub_rev y] using hA y)
  have hV : AEMeasurable
      (fun x => ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * (κ - 1)) * f y ∂μ) (μ.restrict Ω) :=
    (hk.aemeasurable.mul hf.comp_snd).lintegral_prod_right'
  rw [eLpNorm_nnreal_eq_lintegral (zero_lt_one.trans_le (hp.trans hpq)).ne'
      hV.aestronglyMeasurable,
    eLpNorm_nnreal_eq_lintegral (zero_lt_one.trans_le hp).ne' hf.aestronglyMeasurable]
  simp only [enorm_eq_self]
  calc
    _ ≤ (A ^ ((q : ℝ) * (1 - (p : ℝ)⁻¹)) * A *
          (∫⁻ y in Ω, f y ^ (p : ℝ) ∂μ) ^ ((q : ℝ) / p)) ^ (1 / (q : ℝ)) :=
      ENNReal.rpow_le_rpow hyoung (by positivity)
    _ = A ^ (1 - δ) * (∫⁻ y in Ω, f y ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
      have hb : 0 ≤ (q : ℝ) * (1 - (p : ℝ)⁻¹) :=
        mul_nonneg hq0.le (sub_nonneg.2 (inv_le_one_of_one_le₀ hp'))
      have hA1 : A ^ ((q : ℝ) * (1 - (p : ℝ)⁻¹)) * A = A ^ ((q : ℝ) * (1 - (p : ℝ)⁻¹) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ hb zero_le_one, ENNReal.rpow_one]
      rw [hA1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      congr 2
      · rw [← hδ]
        field_simp
        ring
      · field_simp
    _ = _ := by
      have hexp : κ' * (1 - δ) = κ - δ := by
        simp only [κ']
        field_simp [(sub_pos.2 hδ1).ne']
      have hexp' : (1 - κ') * (1 - δ) = 1 - κ := by
        simp only [κ']
        field_simp [(sub_pos.2 hδ1).ne']
        ring
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, hexp,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hω.le, hexp', inv_div]

end TauCeti
