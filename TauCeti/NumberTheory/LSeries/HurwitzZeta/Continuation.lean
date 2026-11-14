/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Series
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.NumberTheory.LSeries.HurwitzZeta.TaylorKernel

/-!
# Joint meromorphic continuation and Bernoulli values of the complex Hurwitz zeta function

For `0 < c.re`, the Dirichlet series `complexHurwitzSeries s c = ∑' n : ℕ, (n + c) ^ (-s)` on
`1 < s.re` extends meromorphically in `s ∈ ℂ`, jointly holomorphically with `c` in `{0 < c.re}`,
with a single simple pole at `s = 1` of residue `1`.

Starting from the Gamma-Laplace integral on `1 < s.re` and `0 < c.re`, splitting the integration
domain `(0, ∞)` at `t = 1` and subtracting the order-`M` Taylor polynomial of `hurwitzKernel c` at
`t = 0` produces a stage-`M` meromorphic representation on `{-(M : ℝ) < s.re} × {0 < c.re}`. The
apparent poles at `s = 1 - k` (`1 ≤ k ≤ M`) are cancelled by the simple zeros of `(Gamma s)⁻¹`
via the entire quotient `invGammaDiv (k - 1) s = (∏ j < k - 1, (s + j)) / Gamma (s + k)`.

Consecutive stages agree identically on overlapping half-planes, gluing into canonical functions
`complexHurwitzZeta` (jointly holomorphic on `{p | p.1 ≠ 1 ∧ 0 < p.2.re}`) and `complexHurwitzReg`
(jointly holomorphic on `{p | 0 < p.2.re}`), with `complexHurwitzReg 1 c = 1`,
`complexHurwitzReg s c = (s - 1) * complexHurwitzZeta s c` for `s ≠ 1`, and nonpositive integer
special values `complexHurwitzZeta (-m) c = -B_{m + 1}(c) / (m + 1)`.

Analytic continuation off `s = 1` extends the `c ↦ c + 1` shift identity and the comparison with
`HurwitzZeta.hurwitzZeta` on `(0, 1]`, yielding Hurwitz decompositions for `ZMod.LFunction` and
`DirichletCharacter.LFunction`.

## Main definitions and results

* `TauCeti.complexHurwitzZeta` and `TauCeti.complexHurwitzReg`: canonical continued Hurwitz zeta
  function and its regularized `(s - 1)`-multiplied entire-in-`s` companion.
* `TauCeti.differentiableOn_complexHurwitzZeta` and `TauCeti.differentiableOn_complexHurwitzReg`:
  joint holomorphy on `{p | p.1 ≠ 1 ∧ 0 < p.2.re}` and `{p | 0 < p.2.re}`.
* `TauCeti.complexHurwitzZeta_eq_complexHurwitzSeries`: agreement with `complexHurwitzSeries` on
  `1 < s.re` and `0 < c.re`.
* `TauCeti.complexHurwitzReg_one` and `TauCeti.tendsto_sub_one_mul_complexHurwitzZeta`: simple
  pole of residue `1` at `s = 1`.
* `TauCeti.complexHurwitzZeta_neg_nat` and `TauCeti.complexHurwitzZeta_zero`: Bernoulli polynomial
  values at nonpositive integers.
* `TauCeti.complexHurwitzContinuation_exists`: packaged joint continuation theorem.
* `ZMod.LFunction_eq_sum_Icc_complexHurwitzZeta` and
  `DirichletCharacter.LFunction_eq_sum_Icc_complexHurwitzZeta`: finite Hurwitz decompositions of
  periodic and Dirichlet L-functions.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  **24** (2012), 49–84, §9.
* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  Res. Math. Sci. **3** (2016), Paper No. 2, §6.
* F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, §25.11.
-/

public section

open Complex Set Filter MeasureTheory Metric
open scoped Topology Real

namespace TauCeti

/-! ### Entire reciprocal-Gamma quotients `(Gamma s)⁻¹ / (s + m)` -/

/-- The entire function `(∏ j ∈ range m, (s + j)) * (Gamma (s + m + 1))⁻¹`, which equals
`(Gamma s)⁻¹ / (s + m)` away from `s = -m` and takes value `(-1) ^ m * m!` at `s = -m`. -/
private noncomputable def invGammaDiv (m : ℕ) (s : ℂ) : ℂ :=
  (∏ j ∈ Finset.range m, (s + j)) * (Complex.Gamma (s + m + 1))⁻¹

private theorem differentiable_invGammaDiv (m : ℕ) : Differentiable ℂ (invGammaDiv m) := by
  unfold invGammaDiv
  refine Differentiable.mul ?_ (Complex.differentiable_one_div_Gamma.comp
    ((differentiable_id.add (differentiable_const _)).add (differentiable_const _)))
  induction m with
  | zero => simp
  | succ m ih =>
    simp_rw [Finset.prod_range_succ]
    exact ih.mul (differentiable_id.add (differentiable_const _))

private theorem mul_invGammaDiv (m : ℕ) (s : ℂ) :
    (s + m) * invGammaDiv m s = (Complex.Gamma s)⁻¹ := by
  induction m with
  | zero =>
    simpa [invGammaDiv] using (Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s).symm
  | succ m ih =>
    have hstep := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + m + 1)
    have hshift : s + ↑(m + 1) + 1 = s + m + 1 + 1 := by push_cast; ring
    have hsm : s + ↑(m + 1) = s + m + 1 := by push_cast; ring
    unfold invGammaDiv at ih ⊢
    rw [Finset.prod_range_succ, hshift, hsm]
    calc (s + m + 1) * (((∏ j ∈ Finset.range m, (s + j)) * (s + m)) *
          (Complex.Gamma (s + m + 1 + 1))⁻¹)
        = (s + m) * ((∏ j ∈ Finset.range m, (s + j)) *
            ((s + m + 1) * (Complex.Gamma (s + m + 1 + 1))⁻¹)) := by ring
      _ = (s + m) * ((∏ j ∈ Finset.range m, (s + j)) * (Complex.Gamma (s + m + 1))⁻¹) := by
            rw [← hstep]
      _ = (Complex.Gamma s)⁻¹ := ih

private theorem invGammaDiv_neg_nat (k n : ℕ) :
    invGammaDiv k (-(n : ℂ)) = if k = n then (-1 : ℂ) ^ n * n.factorial else 0 := by
  rcases lt_trichotomy k n with hlt | rfl | hgt
  · simp only [hlt.ne, ↓reduceIte, invGammaDiv]
    have harg : -(n : ℂ) + k + 1 = -((n - 1 - k : ℕ) : ℂ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [harg, Complex.Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  · simp only [↓reduceIte, invGammaDiv]
    have h1 : -(k : ℂ) + k + 1 = 1 := by ring
    rw [h1, Complex.Gamma_one, inv_one, mul_one]; clear h1
    induction k with
    | zero => simp
    | succ k ih =>
      have hprod : (∏ j ∈ Finset.range (k + 1), (-((k + 1 : ℕ) : ℂ) + j)) =
          (-((k + 1 : ℕ) : ℂ)) * ∏ j ∈ Finset.range k, (-(k : ℂ) + j) := by
        rw [Finset.prod_range_succ']
        simp only [Nat.cast_zero, add_zero, mul_comm]
        exact congrArg _ (Finset.prod_congr rfl fun _ _ => by push_cast; ring)
      rw [hprod, ih, Nat.factorial_succ, pow_succ]; push_cast; ring
  · simp only [hgt.ne', ↓reduceIte, invGammaDiv]
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hgt) (by ring), zero_mul]

/-! ### Joint holomorphy of the subtracted head integral on `(0, 1]` -/

private noncomputable def hurwitzHeadIntegral (M : ℕ) (s c : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t

private theorem exists_hurwitzTaylorQuot_ball_bound (M : ℕ) (c₀ : ℂ) :
    ∃ B ≥ 0, ∀ c ∈ closedBall c₀ 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖hurwitzTaylorQuot M c t‖ ≤ B := by
  let K : Set (ℂ × ℂ) := closedBall c₀ 1 ×ˢ (Complex.ofReal '' Icc (0 : ℝ) 1)
  have hK : IsCompact K := (isCompact_closedBall c₀ 1).prod (isCompact_Icc.image continuous_ofReal)
  have hKU : K ⊆ univ ×ˢ ball 0 2 := by
    rintro ⟨_, _⟩ ⟨_, t, ht, rfl⟩
    refine ⟨trivial, ?_⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1]; linarith [ht.2]
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((analyticOnNhd_hurwitzTaylorQuot M).continuousOn.mono hKU)
  exact ⟨max B 0, le_max_right _ _, fun c hc t ht =>
    (hB (c, t) ⟨hc, t, ht, rfl⟩).trans (le_max_left _ _)⟩

private theorem aestronglyMeasurable_hurwitzHeadIntegrand (M : ℕ) (s c : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t)
      (volume.restrict (Ioc 0 1)) := by
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
  have ht_ball : (t : ℂ) ∈ ball (0 : ℂ) 2 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
  have hc1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (s + M - 1)) t :=
    continuous_ofReal.continuousAt.cpow continuousAt_const (ofReal_mem_slitPlane.mpr ht.1)
  have hc2 : ContinuousAt (fun u : ℝ => hurwitzTaylorQuot M c u) t :=
    ContinuousAt.comp (g := fun p : ℂ × ℂ => hurwitzTaylorQuot M p.1 p.2)
      (f := fun u : ℝ => (c, (u : ℂ)))
      (analyticOnNhd_hurwitzTaylorQuot M (c, t) ⟨trivial, ht_ball⟩).continuousAt
      (continuous_const.prodMk continuous_ofReal).continuousAt
  exact (hc1.mul hc2).continuousWithinAt

private theorem integrableOn_hurwitzHeadIntegrand (M : ℕ) {s c : ℂ} (hs : -(M : ℝ) < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t) (Ioc 0 1) := by
  obtain ⟨B, _, hB⟩ := exists_hurwitzTaylorQuot_ball_bound M c
  have hint : IntegrableOn (fun t : ℝ => B * t ^ (s.re + M - 1)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul B
  refine Integrable.mono' hint (aestronglyMeasurable_hurwitzHeadIntegrand M s c) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1]
  have hre : (s + (M : ℂ) - 1).re = s.re + M - 1 := by simp
  rw [hre, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (hB c (mem_closedBall_self zero_le_one) t (Ioc_subset_Icc_self ht))
    (Real.rpow_nonneg ht.1.le _)

private theorem continuousOn_hurwitzHeadIntegral_pi (M : ℕ) :
    ContinuousOn (fun w : Fin 2 → ℂ => hurwitzHeadIntegral M (w 0) (w 1))
      {w | -(M : ℝ) < (w 0).re} := by
  intro w₀ hw₀
  have hs₀ : -(M : ℝ) < (w₀ 0).re := hw₀
  let δ := min 1 (((w₀ 0).re + (M : ℝ)) / 2)
  have hδ : 0 < δ := lt_min one_pos (by linarith)
  obtain ⟨B, hB0, hB⟩ := exists_hurwitzTaylorQuot_ball_bound M (w₀ 1)
  have hcont_t : ∀ᶠ (t : ℝ) in ae (volume.restrict (Ioc (0 : ℝ) 1)),
      ContinuousAt (fun w : Fin 2 → ℂ =>
        (t : ℂ) ^ (w 0 + M - 1) * hurwitzTaylorQuot M (w 1) t) w₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht_ball : (t : ℂ) ∈ ball (0 : ℂ) 2 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
    have hc1 : ContinuousAt (fun w : Fin 2 → ℂ => (t : ℂ) ^ (w 0 + M - 1)) w₀ :=
      continuousAt_const.cpow
        ((((continuous_apply 0).add continuous_const).sub continuous_const).continuousAt)
        (ofReal_mem_slitPlane.mpr ht.1)
    have hc2 : ContinuousAt (fun w : Fin 2 → ℂ => hurwitzTaylorQuot M (w 1) t) w₀ :=
      ContinuousAt.comp (g := fun q : ℂ × ℂ => hurwitzTaylorQuot M q.1 q.2)
        (f := fun w : Fin 2 → ℂ => (w 1, (t : ℂ)))
        (analyticOnNhd_hurwitzTaylorQuot M (w₀ 1, t) ⟨trivial, ht_ball⟩).continuousAt
        ((continuous_apply 1).prodMk continuous_const).continuousAt
    exact hc1.mul hc2
  have hbint : Integrable (fun t : ℝ => B * t ^ (δ - 1)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul B
  refine ContinuousAt.continuousWithinAt ?_
  unfold hurwitzHeadIntegral
  refine MeasureTheory.continuousAt_of_dominated
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun (w : Fin 2 → ℂ) (t : ℝ) =>
      (t : ℂ) ^ (w 0 + (M : ℂ) - 1) * hurwitzTaylorQuot M (w 1) t)
    (x₀ := w₀) (bound := fun t => B * t ^ (δ - 1))
    (Eventually.of_forall fun w => aestronglyMeasurable_hurwitzHeadIntegrand M (w 0) (w 1))
    ?_ hbint hcont_t
  filter_upwards [ball_mem_nhds w₀ hδ] with w hw
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hw_norm : ‖w - w₀‖ < δ := by simpa [dist_eq_norm] using hw
  have hs_re : δ ≤ (w 0).re + M := by
    have h0 : ‖w 0 - w₀ 0‖ < δ := (norm_le_pi_norm (w - w₀) 0).trans_lt hw_norm
    have h1 := (abs_lt.mp ((abs_re_le_norm (w 0 - w₀ 0)).trans_lt h0)).1
    rw [sub_re] at h1
    linarith [min_le_right 1 (((w₀ 0).re + (M : ℝ)) / 2)]
  have hc_mem : w 1 ∈ closedBall (w₀ 1) 1 := by
    rw [mem_closedBall, dist_eq_norm]
    exact ((norm_le_pi_norm (w - w₀) 1).trans hw_norm.le).trans (min_le_left _ _)
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1]
  have hre : (w 0 + (M : ℂ) - 1).re = (w 0).re + M - 1 := by simp
  rw [hre, mul_comm]
  exact mul_le_mul (hB (w 1) hc_mem t (Ioc_subset_Icc_self ht))
    (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith))
    (Real.rpow_nonneg ht.1.le _) hB0

private theorem differentiableAt_hurwitzHeadIntegral_fst (M : ℕ) {s₀ c₀ : ℂ}
    (hs₀ : -(M : ℝ) < s₀.re) :
    DifferentiableAt ℂ (fun s => hurwitzHeadIntegral M s c₀) s₀ := by
  let δ := (s₀.re + (M : ℝ)) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨B, _, hB⟩ := exists_hurwitzTaylorQuot_ball_bound M c₀
  have hc₀ : c₀ ∈ closedBall c₀ 1 := mem_closedBall_self zero_le_one
  have hbint : Integrable (fun t : ℝ => B * δ⁻¹ * t ^ (δ - 1)) (volume.restrict (Ioc 0 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul (B * δ⁻¹)
  have hlog_meas : AEStronglyMeasurable (fun t : ℝ => Complex.log t)
      (volume.restrict (Ioc 0 1)) :=
    (ContinuousOn.clog (s := Ioc (0 : ℝ) 1) continuous_ofReal.continuousOn fun _ ht =>
      ofReal_mem_slitPlane.mpr ht.1).aestronglyMeasurable measurableSet_Ioc
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ =>
        ((t : ℂ) ^ (s₀ + (M : ℂ) - 1) * Complex.log t * 1) * hurwitzTaylorQuot M c₀ t)
      (volume.restrict (Ioc 0 1)) :=
    ((aestronglyMeasurable_hurwitzHeadIntegrand M s₀ c₀).mul hlog_meas).congr
      (ae_of_all _ fun t => by simp only [Pi.mul_apply]; ring)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 1))
    (F := fun (s : ℂ) (t : ℝ) => (t : ℂ) ^ (s + (M : ℂ) - 1) * hurwitzTaylorQuot M c₀ t)
    (F' := fun (s : ℂ) (t : ℝ) =>
      ((t : ℂ) ^ (s + (M : ℂ) - 1) * Complex.log t * 1) * hurwitzTaylorQuot M c₀ t)
    (bound := fun t : ℝ => B * δ⁻¹ * t ^ (δ - 1))
    (ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s => aestronglyMeasurable_hurwitzHeadIntegrand M s c₀)
    (integrableOn_hurwitzHeadIntegrand M hs₀) hF'_meas ?_ hbint ?_
  · exact hd.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s hs
    have hs_re : 2 * δ ≤ s.re + M := by
      have h0 : ‖s - s₀‖ < δ := by simpa [dist_eq_norm] using hs
      have h1 := (abs_lt.mp ((abs_re_le_norm (s - s₀)).trans_lt h0)).1
      rw [sub_re] at h1; dsimp [δ] at h1 ⊢; linarith
    have hlog : ‖Complex.log (t : ℂ)‖ ≤ δ⁻¹ * t ^ (-δ) := by
      rw [← Complex.ofReal_log ht.1.le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (Real.log_nonpos ht.1.le ht.2), le_inv_mul_iff₀ hδ]
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht.1 (-δ))
      rw [Real.log_rpow ht.1] at h1; linarith
    have hrpow : t ^ (s.re + M - 1) ≤ t ^ (2 * δ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)
    have hre : (s + (M : ℂ) - 1).re = s.re + M - 1 := by simp
    rw [mul_one, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, hre]
    calc t ^ (s.re + M - 1) * ‖Complex.log (t : ℂ)‖ * ‖hurwitzTaylorQuot M c₀ t‖
        ≤ t ^ (2 * δ - 1) * (δ⁻¹ * t ^ (-δ)) * B :=
          mul_le_mul (mul_le_mul hrpow hlog (norm_nonneg _) (Real.rpow_nonneg ht.1.le _))
            (hB c₀ hc₀ t (Ioc_subset_Icc_self ht)) (norm_nonneg _)
            (mul_nonneg (Real.rpow_nonneg ht.1.le _)
              (mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg ht.1.le _)))
      _ = B * δ⁻¹ * (t ^ (2 * δ - 1) * t ^ (-δ)) := by ring
      _ = B * δ⁻¹ * t ^ (δ - 1) := by rw [← Real.rpow_add ht.1]; ring_nf
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s _
    exact ((((hasDerivAt_id s).add_const (M : ℂ)).sub_const 1).const_cpow
      (Or.inl (ofReal_ne_zero.mpr ht.1.ne'))).mul_const (hurwitzTaylorQuot M c₀ t)

private theorem differentiableAt_hurwitzHeadIntegral_snd (M : ℕ) {s₀ c₀ : ℂ}
    (hs₀ : -(M : ℝ) < s₀.re) :
    DifferentiableAt ℂ (fun c => hurwitzHeadIntegral M s₀ c) c₀ := by
  let K : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) 1
  let φ : ℝ → ℂ := fun t => ((max (0 : ℝ) (min 1 t) : ℝ) : ℂ)
  have hK : IsCompact K := isCompact_Icc.image continuous_ofReal
  have hφ : Continuous φ :=
    continuous_ofReal.comp (continuous_const.max (continuous_const.min continuous_id))
  have hφK : ∀ t : ℝ, φ t ∈ K := fun t =>
    ⟨_, ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, rfl⟩
  have hf : ∀ y ∈ K, AnalyticAt ℂ (fun q : ℂ × ℂ => hurwitzTaylorQuot M q.1 q.2) (c₀, y) := by
    rintro _ ⟨t, ht, rfl⟩
    refine analyticOnNhd_hurwitzTaylorQuot M (c₀, t) ⟨trivial, ?_⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1]; linarith [ht.2]
  have hg : Integrable (fun t : ℝ => (t : ℂ) ^ (s₀ + (M : ℂ) - 1))
      (volume.restrict (Ioc 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
  have han := analyticAt_integral_smul hK hφ hφK hf hg
  have heq : (fun c => ∫ t in Ioc (0 : ℝ) 1,
        ((t : ℂ) ^ (s₀ + (M : ℂ) - 1)) • hurwitzTaylorQuot M c (φ t)) =
      fun c => hurwitzHeadIntegral M s₀ c := by
    ext c
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [φ, smul_eq_mul, min_eq_right ht.2, max_eq_right ht.1.le]
  rw [← heq]
  exact han.differentiableAt

private theorem analyticOnNhd_hurwitzHeadIntegral (M : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzHeadIntegral M p.1 p.2)
      {p | -(M : ℝ) < p.1.re} := by
  have han : AnalyticOnNhd ℂ (fun w : Fin 2 → ℂ => hurwitzHeadIntegral M (w 0) (w 1))
      {w | -(M : ℝ) < (w 0).re} :=
    (continuousOn_hurwitzHeadIntegral_pi M).analyticOnNhd_of_differentiableAt_update
      (isOpen_lt continuous_const (continuous_re.comp (continuous_apply 0))) fun w hw i => by
        fin_cases i
        · simpa using differentiableAt_hurwitzHeadIntegral_fst M hw
        · simpa using differentiableAt_hurwitzHeadIntegral_snd M hw
  intro p hp
  have hpi : AnalyticAt ℂ (fun q : ℂ × ℂ => ![q.1, q.2]) p :=
    analyticAt_pi_iff.mpr fun i => by fin_cases i; exacts [analyticAt_fst, analyticAt_snd]
  exact (han ![p.1, p.2] hp).comp_of_eq hpi rfl

/-! ### Joint holomorphy of the exponential tail integral on `(1, ∞)` -/

private noncomputable def hurwitzTailIntegral (s c : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t)))

private theorem one_sub_exp_neg_one_pos : 0 < 1 - Real.exp (-1) := by
  linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)]

private theorem norm_div_one_sub_exp_le {c : ℂ} {t : ℝ} (ht : 1 < t) :
    ‖Complex.exp (-c * t) / (1 - Complex.exp (-t))‖ ≤
      (1 - Real.exp (-1))⁻¹ * Real.exp (-c.re * t) := by
  have hlow : 1 - Real.exp (-1) ≤ ‖1 - Complex.exp (-t)‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (Complex.exp (-(t : ℂ)))
    rw [norm_one, Complex.norm_exp, neg_re, ofReal_re] at h1
    linarith [Real.exp_le_exp.mpr (by linarith : -t ≤ -1)]
  rw [norm_div, Complex.norm_exp]
  have hre : (-c * (t : ℂ)).re = -c.re * t := by simp
  rw [hre, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ one_sub_exp_neg_one_pos hlow) (Real.exp_pos _).le

private theorem integrableOn_rpow_mul_exp_Ioi_one {A η : ℝ} (hA : -1 < A) (hη : 0 < η) :
    IntegrableOn (fun t : ℝ => t ^ A * Real.exp (-η * t)) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A) (b := η) hA one_pos hη
  simp only [Real.rpow_one] at h
  exact h.mono_set (Ioi_subset_Ioi zero_le_one)

private theorem aestronglyMeasurable_hurwitzTailIntegrand (s c : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))))
      (volume.restrict (Ioi 1)) := by
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  have ht1 : 1 < t := ht
  have hne : 1 - Complex.exp (-(t : ℂ)) ≠ 0 := fun h0 => by
    have h1 := norm_sub_norm_le (1 : ℂ) (Complex.exp (-(t : ℂ)))
    rw [h0, norm_zero, norm_one, Complex.norm_exp, neg_re, ofReal_re] at h1
    linarith [Real.exp_le_exp.mpr (by linarith : -t ≤ -1), one_sub_exp_neg_one_pos]
  exact ((continuous_ofReal.continuousAt.cpow continuousAt_const
    (ofReal_mem_slitPlane.mpr (zero_lt_one.trans ht1))).mul
      (((continuous_const.mul continuous_ofReal).cexp.continuousAt).div
        (continuous_const.sub (continuous_ofReal.neg.cexp)).continuousAt hne)).continuousWithinAt

private theorem integrableOn_hurwitzTailIntegrand (s : ℂ) {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))))
      (Ioi 1) := by
  let A := max 0 (s.re - 1)
  have hA : -1 < A := by linarith [le_max_left (0 : ℝ) (s.re - 1)]
  refine Integrable.mono'
    ((integrableOn_rpow_mul_exp_Ioi_one hA hc).const_mul (1 - Real.exp (-1))⁻¹)
    (aestronglyMeasurable_hurwitzTailIntegrand s c) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
  calc t ^ (s.re - 1) * ‖Complex.exp (-c * t) / (1 - Complex.exp (-t))‖
      ≤ t ^ A * ((1 - Real.exp (-1))⁻¹ * Real.exp (-c.re * t)) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht.le (le_max_right _ _))
          (norm_div_one_sub_exp_le ht) (norm_nonneg _) (Real.rpow_nonneg ht0.le _)
    _ = (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-c.re * t)) := by ring

private theorem continuousOn_hurwitzTailIntegral_pi :
    ContinuousOn (fun w : Fin 2 → ℂ => hurwitzTailIntegral (w 0) (w 1))
      {w | 0 < (w 1).re} := by
  intro w₀ hw₀
  have hc₀ : 0 < (w₀ 1).re := hw₀
  let η := (w₀ 1).re / 2
  have hη : 0 < η := by dsimp [η]; linarith
  let r := min 1 η
  have hr : 0 < r := lt_min one_pos hη
  let A := max 0 (w₀ 0).re
  have hA : -1 < A := by linarith [le_max_left (0 : ℝ) (w₀ 0).re]
  have hcont_t : ∀ᶠ (t : ℝ) in ae (volume.restrict (Ioi (1 : ℝ))),
      ContinuousAt (fun w : Fin 2 → ℂ =>
        (t : ℂ) ^ (w 0 - 1) * (Complex.exp (-(w 1) * t) / (1 - Complex.exp (-t)))) w₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (continuousAt_const.cpow (((continuous_apply 0).sub continuous_const).continuousAt)
      (ofReal_mem_slitPlane.mpr (zero_lt_one.trans ht))).mul
        (((((continuous_apply 1).neg.mul continuous_const).cexp).div_const _).continuousAt)
  have hbint : Integrable
      (fun t : ℝ => (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)))
      (volume.restrict (Ioi (1 : ℝ))) :=
    (integrableOn_rpow_mul_exp_Ioi_one hA hη).const_mul _
  refine ContinuousAt.continuousWithinAt ?_
  unfold hurwitzTailIntegral
  refine MeasureTheory.continuousAt_of_dominated
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun (w : Fin 2 → ℂ) (t : ℝ) =>
      (t : ℂ) ^ (w 0 - 1) * (Complex.exp (-(w 1) * t) / (1 - Complex.exp (-t))))
    (x₀ := w₀) (bound := fun t => (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)))
    (Eventually.of_forall fun w => aestronglyMeasurable_hurwitzTailIntegrand (w 0) (w 1))
    ?_ hbint hcont_t
  filter_upwards [ball_mem_nhds w₀ hr] with w hw
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hw_norm : ‖w - w₀‖ < r := by simpa [dist_eq_norm] using hw
  have hs_le : (w 0).re - 1 ≤ A := by
    have h0 : ‖w 0 - w₀ 0‖ < 1 :=
      ((norm_le_pi_norm (w - w₀) 0).trans_lt hw_norm).trans_le (min_le_left _ _)
    have h1 := (abs_lt.mp ((abs_re_le_norm (w 0 - w₀ 0)).trans_lt h0)).2
    rw [sub_re] at h1
    linarith [le_max_right (0 : ℝ) (w₀ 0).re]
  have hc_ge : η ≤ (w 1).re := by
    have h0 : ‖w 1 - w₀ 1‖ < η :=
      ((norm_le_pi_norm (w - w₀) 1).trans_lt hw_norm).trans_le (min_le_right _ _)
    have h1 := (abs_lt.mp ((abs_re_le_norm (w 1 - w₀ 1)).trans_lt h0)).1
    rw [sub_re] at h1; dsimp [η] at h1 ⊢; linarith
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
  calc t ^ ((w 0).re - 1) * ‖Complex.exp (-(w 1) * t) / (1 - Complex.exp (-t))‖
      ≤ t ^ A * ((1 - Real.exp (-1))⁻¹ * Real.exp (-(w 1).re * t)) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht.le hs_le)
          (norm_div_one_sub_exp_le ht) (norm_nonneg _) (Real.rpow_nonneg ht0.le _)
    _ ≤ t ^ A * ((1 - Real.exp (-1))⁻¹ * Real.exp (-η * t)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
            (inv_pos.mpr one_sub_exp_neg_one_pos).le)
          (Real.rpow_nonneg ht0.le _)
    _ = (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)) := by ring

private theorem differentiableAt_hurwitzTailIntegral_fst (s₀ : ℂ) {c₀ : ℂ} (hc₀ : 0 < c₀.re) :
    DifferentiableAt ℂ (fun s => hurwitzTailIntegral s c₀) s₀ := by
  let A := max 0 s₀.re + 1
  have hA : -1 < A := by dsimp [A]; linarith [le_max_left (0 : ℝ) s₀.re]
  have hbint : Integrable
      (fun t : ℝ => (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-c₀.re * t)))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_rpow_mul_exp_Ioi_one hA hc₀).const_mul _
  have hlog_meas : AEStronglyMeasurable (fun t : ℝ => Complex.log t)
      (volume.restrict (Ioi 1)) :=
    (continuous_ofReal.continuousOn.clog fun _ ht =>
      ofReal_mem_slitPlane.mpr (zero_lt_one.trans ht)).aestronglyMeasurable measurableSet_Ioi
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => ((t : ℂ) ^ (s₀ - 1) * Complex.log t * 1) *
        (Complex.exp (-c₀ * t) / (1 - Complex.exp (-t))))
      (volume.restrict (Ioi 1)) :=
    ((aestronglyMeasurable_hurwitzTailIntegrand s₀ c₀).mul hlog_meas).congr
      (ae_of_all _ fun t => by simp only [Pi.mul_apply]; ring)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 1))
    (F := fun (s : ℂ) (t : ℝ) =>
      (t : ℂ) ^ (s - 1) * (Complex.exp (-c₀ * t) / (1 - Complex.exp (-t))))
    (F' := fun (s : ℂ) (t : ℝ) =>
      ((t : ℂ) ^ (s - 1) * Complex.log t * 1) *
        (Complex.exp (-c₀ * t) / (1 - Complex.exp (-t))))
    (bound := fun t : ℝ => (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-c₀.re * t)))
    (ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => aestronglyMeasurable_hurwitzTailIntegrand s c₀)
    (integrableOn_hurwitzTailIntegrand s₀ hc₀) hF'_meas ?_ hbint ?_
  · exact hd.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hs_le : s.re - 1 ≤ A - 1 := by
      have h0 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h1 := (abs_lt.mp ((abs_re_le_norm (s - s₀)).trans_lt h0)).2
      rw [sub_re] at h1; dsimp [A]; linarith [le_max_right (0 : ℝ) s₀.re]
    have hlog : ‖Complex.log (t : ℂ)‖ ≤ t := by
      rw [← Complex.ofReal_log ht0.le, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg ht.le)]
      linarith [Real.log_le_sub_one_of_pos ht0]
    have hmul_t : t ^ (A - 1) * t = t ^ A := by
      rw [← Real.rpow_add_one ht0.ne', sub_add_cancel]
    rw [mul_one, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
    calc t ^ (s.re - 1) * ‖Complex.log (t : ℂ)‖ *
          ‖Complex.exp (-c₀ * t) / (1 - Complex.exp (-t))‖
        ≤ (t ^ (A - 1) * t) * ((1 - Real.exp (-1))⁻¹ * Real.exp (-c₀.re * t)) :=
          mul_le_mul (mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht.le hs_le) hlog
            (norm_nonneg _) (Real.rpow_nonneg ht0.le _))
            (norm_div_one_sub_exp_le ht) (norm_nonneg _)
            (mul_nonneg (Real.rpow_nonneg ht0.le _) ht0.le)
      _ = (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-c₀.re * t)) := by rw [hmul_t]; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    exact (((hasDerivAt_id s).sub_const 1).const_cpow
      (Or.inl (ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'))).mul_const _

private theorem differentiableAt_hurwitzTailIntegral_snd (s₀ : ℂ) {c₀ : ℂ} (hc₀ : 0 < c₀.re) :
    DifferentiableAt ℂ (fun c => hurwitzTailIntegral s₀ c) c₀ := by
  let η := c₀.re / 2
  have hη : 0 < η := by dsimp [η]; linarith
  let A := max 0 s₀.re
  have hA : -1 < A := by linarith [le_max_left (0 : ℝ) s₀.re]
  have hbint : Integrable
      (fun t : ℝ => (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_rpow_mul_exp_Ioi_one hA hη).const_mul _
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s₀ - 1) *
        ((Complex.exp (-c₀ * t) * (-(t : ℂ))) / (1 - Complex.exp (-t))))
      (volume.restrict (Ioi 1)) :=
    ((aestronglyMeasurable_hurwitzTailIntegrand s₀ c₀).mul
      continuous_ofReal.neg.aestronglyMeasurable).congr
      (ae_of_all _ fun t => by simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 1))
    (F := fun (c : ℂ) (t : ℝ) =>
      (t : ℂ) ^ (s₀ - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))))
    (F' := fun (c : ℂ) (t : ℝ) => (t : ℂ) ^ (s₀ - 1) *
      ((Complex.exp (-c * t) * (-(t : ℂ))) / (1 - Complex.exp (-t))))
    (bound := fun t : ℝ => (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)))
    (ball_mem_nhds c₀ hη)
    (Eventually.of_forall fun c => aestronglyMeasurable_hurwitzTailIntegrand s₀ c)
    (integrableOn_hurwitzTailIntegrand s₀ hc₀) hF'_meas ?_ hbint ?_
  · exact hd.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht c hc
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hc_ge : η ≤ c.re := by
      have h0 : ‖c - c₀‖ < η := by simpa [dist_eq_norm] using hc
      have h1 := (abs_lt.mp ((abs_re_le_norm (c - c₀)).trans_lt h0)).1
      rw [sub_re] at h1; dsimp [η] at h1 ⊢; linarith
    have hmul_eq : (t : ℂ) ^ (s₀ - 1) *
        ((Complex.exp (-c * t) * (-(t : ℂ))) / (1 - Complex.exp (-t))) =
        (-(t : ℂ)) * (t : ℂ) ^ (s₀ - 1) *
          (Complex.exp (-c * t) / (1 - Complex.exp (-t))) := by ring
    rw [hmul_eq, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht0.le,
      norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re, mul_comm t, ← Real.rpow_add_one ht0.ne',
      sub_add_cancel]
    calc t ^ s₀.re * ‖Complex.exp (-c * t) / (1 - Complex.exp (-t))‖
        ≤ t ^ A * ((1 - Real.exp (-1))⁻¹ * Real.exp (-c.re * t)) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht.le (le_max_right _ _))
            (norm_div_one_sub_exp_le ht) (norm_nonneg _) (Real.rpow_nonneg ht0.le _)
      _ ≤ t ^ A * ((1 - Real.exp (-1))⁻¹ * Real.exp (-η * t)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
              (inv_pos.mpr one_sub_exp_neg_one_pos).le)
            (Real.rpow_nonneg ht0.le _)
      _ = (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ c _
    have h1 : HasDerivAt (fun w : ℂ => -w * t) (-(t : ℂ)) c := by
      simpa using ((hasDerivAt_id c).neg.mul_const (t : ℂ))
    exact (h1.cexp.div_const (1 - Complex.exp (-t))).const_mul ((t : ℂ) ^ (s₀ - 1))

private theorem analyticOnNhd_hurwitzTailIntegral :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzTailIntegral p.1 p.2) {p | 0 < p.2.re} := by
  have han : AnalyticOnNhd ℂ (fun w : Fin 2 → ℂ => hurwitzTailIntegral (w 0) (w 1))
      {w | 0 < (w 1).re} :=
    continuousOn_hurwitzTailIntegral_pi.analyticOnNhd_of_differentiableAt_update
      (isOpen_lt continuous_const (continuous_re.comp (continuous_apply 1))) fun w hw i => by
        fin_cases i
        · simpa using differentiableAt_hurwitzTailIntegral_fst (w 0) hw
        · simpa using differentiableAt_hurwitzTailIntegral_snd (w 0) hw
  intro p hp
  have hpi : AnalyticAt ℂ (fun q : ℂ × ℂ => ![q.1, q.2]) p :=
    analyticAt_pi_iff.mpr fun i => by fin_cases i; exacts [analyticAt_fst, analyticAt_snd]
  exact (han ![p.1, p.2] hp).comp_of_eq hpi rfl

/-! ### Stage-`M` holomorphic core and canonical global definitions -/

private noncomputable def hurwitzStageCore (M : ℕ) (s c : ℂ) : ℂ :=
  (Complex.Gamma s)⁻¹ * (hurwitzHeadIntegral M s c + hurwitzTailIntegral s c) +
    ∑ k ∈ Finset.Icc 1 M, hurwitzBernoulliCoeff k c * invGammaDiv (k - 1) s

private theorem analyticOnNhd_hurwitzStageCore (M : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzStageCore M p.1 p.2)
      {p | -(M : ℝ) < p.1.re ∧ 0 < p.2.re} := by
  have hopen : IsOpen {p : ℂ × ℂ | -(M : ℝ) < p.1.re ∧ 0 < p.2.re} :=
    (isOpen_lt continuous_const (continuous_re.comp continuous_fst)).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd))
  refine DifferentiableOn.analyticOnNhd_of_finiteDimensional (fun p hp => ?_) hopen
  have hd_invG : DifferentiableAt ℂ (fun q : ℂ × ℂ => (Complex.Gamma q.1)⁻¹) p :=
    (Complex.differentiable_one_div_Gamma p.1).comp p differentiableAt_fst
  have hd_head : DifferentiableAt ℂ (fun q : ℂ × ℂ => hurwitzHeadIntegral M q.1 q.2) p :=
    (analyticOnNhd_hurwitzHeadIntegral M p hp.1).differentiableAt
  have hd_tail : DifferentiableAt ℂ (fun q : ℂ × ℂ => hurwitzTailIntegral q.1 q.2) p :=
    (analyticOnNhd_hurwitzTailIntegral p hp.2).differentiableAt
  have hd_sum : DifferentiableAt ℂ
      (fun q : ℂ × ℂ =>
        ∑ k ∈ Finset.Icc 1 M, hurwitzBernoulliCoeff k q.2 * invGammaDiv (k - 1) q.1) p :=
    DifferentiableAt.fun_sum fun k _ =>
      ((differentiable_hurwitzBernoulliCoeff k p.2).comp p differentiableAt_snd).mul
        ((differentiable_invGammaDiv (k - 1) p.1).comp p differentiableAt_fst)
  exact ((hd_invG.mul (hd_head.add hd_tail)).add hd_sum).differentiableWithinAt

private theorem integral_Ioc_cpow_sub_one {w : ℂ} (hw : 0 < w.re) :
    (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1)) = 1 / w := by
  have hw0 : w ≠ 0 := fun h => lt_irrefl (0 : ℝ) (by rwa [h, zero_re] at hw)
  rw [← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp; linarith))]
  simp [sub_add_cancel, Complex.zero_cpow hw0]

private theorem hurwitzHeadIntegral_eq_add_succ (M : ℕ) {s : ℂ}
    (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzHeadIntegral M s c =
      hurwitzBernoulliCoeff (M + 1) c / (s + M) + hurwitzHeadIntegral (M + 1) s c := by
  have hre : 0 < (s + M).re := by simp; linarith
  have hint1 : IntegrableOn
      (fun t : ℝ => hurwitzBernoulliCoeff (M + 1) c * (t : ℂ) ^ (s + M - 1)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))).const_mul _
  have hint2 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s + ↑(M + 1) - 1) * hurwitzTaylorQuot (M + 1) c t) (Ioc 0 1) :=
    integrableOn_hurwitzHeadIntegrand (M + 1) (by push_cast; linarith)
  have hcongr : EqOn
      (fun t : ℝ => (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t)
      (fun t : ℝ => hurwitzBernoulliCoeff (M + 1) c * (t : ℂ) ^ (s + M - 1) +
        (t : ℂ) ^ (s + ↑(M + 1) - 1) * hurwitzTaylorQuot (M + 1) c t)
      (Ioc 0 1) := fun t ht => by
    dsimp only
    have ht_ball : (t : ℂ) ∈ ball (0 : ℂ) 2 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
    have hpow : (t : ℂ) ^ (s + M - 1) * (t : ℂ) = (t : ℂ) ^ (s + ↑(M + 1) - 1) := by
      have h := (Complex.cpow_add (s + M - 1) 1 (ofReal_ne_zero.mpr ht.1.ne')).symm
      rw [Complex.cpow_one] at h
      exact h.trans (congrArg _ (by push_cast; ring))
    rw [hurwitzTaylorQuot_eq_add_mul_succ M c ht_ball, mul_add, mul_comm ((t : ℂ) ^ _),
      ← mul_assoc ((t : ℂ) ^ _), hpow]
  have hexp : s + (M : ℂ) - 1 = (s + M) - 1 := by ring
  unfold hurwitzHeadIntegral
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hcongr,
    MeasureTheory.integral_add hint1 hint2, MeasureTheory.integral_const_mul, hexp,
    integral_Ioc_cpow_sub_one hre, mul_one_div]

private theorem hurwitzStageCore_succ_eq (M : ℕ) {s : ℂ} (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzStageCore (M + 1) s c = hurwitzStageCore M s c := by
  have hsm_ne : s + M ≠ 0 := fun h0 => by
    have hre := congrArg Complex.re h0; simp at hre; linarith
  have hdiv : (Complex.Gamma s)⁻¹ * (hurwitzBernoulliCoeff (M + 1) c / (s + M)) =
      hurwitzBernoulliCoeff (M + 1) c * invGammaDiv M s := by
    rw [← mul_invGammaDiv M s]; field_simp
  unfold hurwitzStageCore
  rw [hurwitzHeadIntegral_eq_add_succ M hs c, Finset.sum_Icc_succ_top (by omega),
    Nat.add_sub_cancel]
  linear_combination -hdiv

private theorem hurwitzStageCore_eq_of_le {M N : ℕ} (hMN : M ≤ N) {s : ℂ}
    (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzStageCore N s c = hurwitzStageCore M s c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
  clear hMN
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, hurwitzStageCore_succ_eq (M + d) (by push_cast; linarith) c, ih]

private noncomputable def hurwitzStageIndex (s : ℂ) : ℕ :=
  ⌊max 0 (1 - s.re)⌋₊ + 1

private noncomputable def hurwitzCore (s c : ℂ) : ℂ :=
  hurwitzStageCore (hurwitzStageIndex s) s c

private theorem hurwitzCore_eq_stage {M : ℕ} {s : ℂ} (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzCore s c = hurwitzStageCore M s c := by
  have hidx : -(hurwitzStageIndex s : ℝ) < s.re := by
    unfold hurwitzStageIndex
    have h1 : 1 - s.re ≤ max 0 (1 - s.re) := le_max_right _ _
    have h2 : max 0 (1 - s.re) < (⌊max 0 (1 - s.re)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    push_cast; linarith
  unfold hurwitzCore
  rcases le_total M (hurwitzStageIndex s) with hle | hge
  · exact hurwitzStageCore_eq_of_le hle hs c
  · exact (hurwitzStageCore_eq_of_le hge hidx c).symm

private theorem analyticOnNhd_hurwitzCore :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzCore p.1 p.2) {p | 0 < p.2.re} := by
  intro p₀ hp₀
  set N := ⌊max 0 (2 - p₀.1.re)⌋₊ + 2
  have hN_re : -(N : ℝ) < p₀.1.re - 1 := by
    have h1 : 2 - p₀.1.re ≤ max 0 (2 - p₀.1.re) := le_max_right _ _
    have h2 : max 0 (2 - p₀.1.re) < (⌊max 0 (2 - p₀.1.re)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    push_cast [N]; linarith
  have hp₀_mem : p₀ ∈ {p : ℂ × ℂ | -(N : ℝ) < p.1.re ∧ 0 < p.2.re} := ⟨by linarith, hp₀⟩
  have hopen : {p : ℂ × ℂ | -(N : ℝ) < p.1.re ∧ 0 < p.2.re} ∈ 𝓝 p₀ :=
    ((isOpen_lt continuous_const (continuous_re.comp continuous_fst)).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd))).mem_nhds hp₀_mem
  refine (analyticOnNhd_hurwitzStageCore N p₀ hp₀_mem).congr ?_
  filter_upwards [hopen] with p hp
  exact (hurwitzCore_eq_stage hp.1 p.2).symm

/-- The canonical meromorphic continuation of `complexHurwitzSeries s c` in `s ∈ ℂ`, jointly
holomorphic on `{p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
noncomputable def complexHurwitzZeta (s c : ℂ) : ℂ :=
  (Complex.Gamma s)⁻¹ / (s - 1) + hurwitzCore s c

/-- The canonical regularized Hurwitz function on `{p : ℂ × ℂ | 0 < p.2.re}`, jointly
holomorphic across `s = 1` with `complexHurwitzReg 1 c = 1` and
`complexHurwitzReg s c = (s - 1) * complexHurwitzZeta s c` for `s ≠ 1`. -/
noncomputable def complexHurwitzReg (s c : ℂ) : ℂ :=
  (Complex.Gamma s)⁻¹ + (s - 1) * hurwitzCore s c

/-- Away from `s = 1`, `complexHurwitzReg s c = (s - 1) * complexHurwitzZeta s c`. -/
theorem complexHurwitzReg_eq_sub_one_mul {s : ℂ} (hs : s ≠ 1) (c : ℂ) :
    complexHurwitzReg s c = (s - 1) * complexHurwitzZeta s c := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold complexHurwitzReg complexHurwitzZeta
  field_simp

/-- At `s = 1`, the regularized Hurwitz function takes value `1`. -/
@[simp]
theorem complexHurwitzReg_one (c : ℂ) : complexHurwitzReg 1 c = 1 := by
  simp [complexHurwitzReg, Complex.Gamma_one]

/-- `(s, c) ↦ complexHurwitzReg s c` is jointly analytic on `{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem analyticOnNhd_complexHurwitzReg :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => complexHurwitzReg p.1 p.2) {p | 0 < p.2.re} := by
  have hanG : AnalyticOnNhd ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) univ :=
    Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ
  intro p hp
  exact ((hanG p.1 trivial).comp analyticAt_fst).add
    ((analyticAt_fst.sub analyticAt_const).mul (analyticOnNhd_hurwitzCore p hp))

/-- `(s, c) ↦ complexHurwitzReg s c` is jointly complex differentiable on
`{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem differentiableOn_complexHurwitzReg :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => complexHurwitzReg p.1 p.2) {p | 0 < p.2.re} :=
  analyticOnNhd_complexHurwitzReg.differentiableOn

/-- `(s, c) ↦ complexHurwitzZeta s c` is jointly analytic on
`{p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
theorem analyticOnNhd_complexHurwitzZeta :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => complexHurwitzZeta p.1 p.2)
      {p | p.1 ≠ 1 ∧ 0 < p.2.re} := by
  intro p₀ hp₀
  have hdiv : AnalyticAt ℂ (fun p : ℂ × ℂ => complexHurwitzReg p.1 p.2 / (p.1 - 1)) p₀ :=
    (analyticOnNhd_complexHurwitzReg p₀ hp₀.2).div
      (analyticAt_fst.sub analyticAt_const) (sub_ne_zero.mpr hp₀.1)
  refine hdiv.congr ?_
  filter_upwards [(isOpen_ne.preimage continuous_fst).mem_nhds hp₀.1] with p hp
  rw [complexHurwitzReg_eq_sub_one_mul hp p.2, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hp)]

/-- `(s, c) ↦ complexHurwitzZeta s c` is jointly complex differentiable on
`{p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
theorem differentiableOn_complexHurwitzZeta :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => complexHurwitzZeta p.1 p.2)
      {p | p.1 ≠ 1 ∧ 0 < p.2.re} :=
  analyticOnNhd_complexHurwitzZeta.differentiableOn

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta s c` is complex differentiable at every
`s ≠ 1`. -/
theorem differentiableAt_complexHurwitzZeta_fst {s c : ℂ} (hs : s ≠ 1) (hc : 0 < c.re) :
    DifferentiableAt ℂ (fun w => complexHurwitzZeta w c) s :=
  (AnalyticAt.comp (g := fun p : ℂ × ℂ => complexHurwitzZeta p.1 p.2)
    (f := fun w : ℂ => (w, c))
    (analyticOnNhd_complexHurwitzZeta (s, c) ⟨hs, hc⟩)
    (analyticAt_id.prod analyticAt_const)).differentiableAt

/-- `complexHurwitzZeta s c` has a simple pole of residue `1` at `s = 1` for every `0 < c.re`. -/
theorem tendsto_sub_one_mul_complexHurwitzZeta {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun s => (s - 1) * complexHurwitzZeta s c) (𝓝[≠] 1) (𝓝 1) := by
  have hcont : ContinuousAt (fun s => complexHurwitzReg s c) 1 :=
    (AnalyticAt.comp (g := fun p : ℂ × ℂ => complexHurwitzReg p.1 p.2)
      (f := fun s : ℂ => (s, c))
      (analyticOnNhd_complexHurwitzReg (1, c) hc)
      (analyticAt_id.prod analyticAt_const)).continuousAt
  have hlim : Tendsto (fun s => complexHurwitzReg s c) (𝓝[≠] 1) (𝓝 1) := by
    simpa [complexHurwitzReg_one c] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun s hs =>
    complexHurwitzReg_eq_sub_one_mul hs c)

/-! ### Agreement with `complexHurwitzSeries` on `1 < s.re` and `0 < c.re` -/

private theorem complexHurwitzZeta_eq_integral_Ioi {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    complexHurwitzZeta s c =
      (Complex.Gamma s)⁻¹ *
        ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))) := by
  have hs0 : -((0 : ℕ) : ℝ) < s.re := by simp; linarith
  have hs1 : 0 < (s - 1).re := by simp; linarith
  have hint_pow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 2)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
  have hpt : EqOn
      (fun t : ℝ =>
        (t : ℂ) ^ (s + (0 : ℕ) - 1) * hurwitzTaylorQuot 0 c t + (t : ℂ) ^ (s - 2))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))))
      (Ioc 0 1) := fun t ht => by
    dsimp only
    have ht_ball : (t : ℂ) ∈ ball (0 : ℂ) 2 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
    have hdecomp := hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot 0 c ht_ball
    simp only [Finset.range_one, Finset.sum_singleton, hurwitzBernoulliCoeff_zero, pow_zero,
      mul_one, zero_add, pow_one] at hdecomp
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hpow1 : (t : ℂ) ^ (s + (0 : ℕ) - 1) = (t : ℂ) ^ (s - 2) * (t : ℂ) := by
      have h := Complex.cpow_add (s - 2) 1 ht_ne
      rw [Complex.cpow_one] at h
      exact (congrArg _ (by push_cast; ring)).trans h
    have hpow2 : (t : ℂ) ^ (s - 2) * (t : ℂ) = (t : ℂ) ^ (s - 1) := by
      have h := (Complex.cpow_add (s - 2) 1 ht_ne).symm
      rw [Complex.cpow_one] at h
      exact h.trans (congrArg _ (by ring))
    rw [hpow1, mul_assoc, ← hdecomp, hurwitzKernel_of_ne_zero c ht_ne]
    calc (t : ℂ) ^ (s - 2) * ((t : ℂ) * Complex.exp (-c * t) / (1 - Complex.exp (-t)) - 1) +
          (t : ℂ) ^ (s - 2)
        = ((t : ℂ) ^ (s - 2) * (t : ℂ)) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))) := by
            ring
      _ = (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))) := by rw [hpow2]
  have hhead_add : hurwitzHeadIntegral 0 s c + 1 / (s - 1) =
      ∫ t in Ioc (0 : ℝ) 1,
        (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))) := by
    have hexp : s - (2 : ℂ) = (s - 1) - 1 := by ring
    have h1div : (1 : ℂ) / (s - 1) = ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 2) := by
      rw [hexp, integral_Ioc_cpow_sub_one hs1]
    unfold hurwitzHeadIntegral
    rw [h1div, ← MeasureTheory.integral_add
      (integrableOn_hurwitzHeadIntegrand 0 (s := s) (c := c) hs0) hint_pow]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt
  have hint_Ioc : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))))
      (Ioc 0 1) :=
    ((integrableOn_hurwitzHeadIntegrand 0 (s := s) (c := c) hs0).add hint_pow).congr_fun
      hpt measurableSet_Ioc
  rw [complexHurwitzZeta, hurwitzCore_eq_stage hs0 c]
  unfold hurwitzStageCore hurwitzTailIntegral
  have hempty : Finset.Icc 1 0 = ∅ := by simp
  rw [hempty, Finset.sum_empty, add_zero]
  have hcomb : (Complex.Gamma s)⁻¹ / (s - 1) +
        (Complex.Gamma s)⁻¹ *
          (hurwitzHeadIntegral 0 s c +
            ∫ t in Ioi (1 : ℝ),
              (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t)))) =
      (Complex.Gamma s)⁻¹ *
        ((hurwitzHeadIntegral 0 s c + 1 / (s - 1)) +
          ∫ t in Ioi (1 : ℝ),
            (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t)))) := by ring
  rw [hcomb, hhead_add, ← MeasureTheory.setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi hint_Ioc (integrableOn_hurwitzTailIntegrand s hc),
    Ioc_union_Ioi_eq_Ioi zero_le_one]

/-- On the absolute-convergence domain `1 < s.re` and `0 < c.re`, `complexHurwitzZeta s c` equals
`complexHurwitzSeries s c`. -/
theorem complexHurwitzZeta_eq_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    complexHurwitzZeta s c = complexHurwitzSeries s c := by
  have hs_pos : 0 < s.re := by linarith
  rw [complexHurwitzZeta_eq_integral_Ioi hs hc]
  let F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (s - 1) * Complex.exp (-(((n : ℂ) + c) * t))
  have hF_int : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => by
    refine Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs_pos ?_
    simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hF_sum : Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖F n t‖) := by
    have hc_slit : (c.re : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hc
    have hbase := summable_norm_natCast_add_cpow_neg (s := (s.re : ℂ)) (by simp [hs]) hc_slit
    refine (hbase.mul_right (Real.Gamma s.re)).congr fun n => ?_
    have hpos : 0 < (n : ℝ) + c.re := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hcongr : EqOn (fun t : ℝ => ‖F n t‖)
        (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-(((n : ℝ) + c.re) * t))) (Ioi 0) :=
      fun t ht => by
        have ht' : 0 < t := ht
        simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_exp, sub_re,
          one_re, neg_re, mul_re, add_re, natCast_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs_pos hpos, one_div, Real.inv_rpow hpos.le,
      ← Real.rpow_neg hpos.le, ← ofReal_natCast, ← ofReal_add,
      norm_cpow_eq_rpow_re_of_pos hpos, neg_re, ofReal_re]
  have hgeom : EqOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t))))
      (fun t : ℝ => ∑' n : ℕ, F n t) (Ioi 0) := fun t ht => by
    dsimp only
    have ht' : 0 < t := ht
    have hlt : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
      rw [Complex.norm_exp, neg_re, ofReal_re]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hlt, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [F]; rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 2; ring
  have hterm : ∀ n : ℕ,
      (∫ t in Ioi (0 : ℝ), F n t) = Complex.Gamma s * ((n : ℂ) + c) ^ (-s) := fun n =>
    Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs_pos
      (by simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hgeom,
    ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  simp_rw [hterm]
  rw [tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ (Complex.Gamma_ne_zero_of_re_pos hs_pos),
    one_mul]
  exact (hasSum_complexHurwitzSeries hs (mem_slitPlane_iff.mpr (Or.inl hc))).tsum_eq

/-! ### Nonpositive integer Bernoulli values -/

/-- At every nonpositive integer `-m`, the canonical continuation evaluates to
`-B_{m + 1}(c) / (m + 1)`. -/
theorem complexHurwitzZeta_neg_nat (m : ℕ) (c : ℂ) :
    complexHurwitzZeta (-(m : ℂ)) c =
      -((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval c / (m + 1) := by
  have hlt : -((m + 1 : ℕ) : ℝ) < (-(m : ℂ)).re := by push_cast; simp
  rw [complexHurwitzZeta, hurwitzCore_eq_stage hlt c]
  unfold hurwitzStageCore
  rw [Complex.Gamma_neg_nat_eq_zero, inv_zero, zero_div, zero_add, zero_mul, zero_add]
  have hterm : ∀ k ∈ Finset.Icc 1 (m + 1),
      hurwitzBernoulliCoeff k c * invGammaDiv (k - 1) (-(m : ℂ)) =
        if k = m + 1 then
          hurwitzBernoulliCoeff (m + 1) c * ((-1 : ℂ) ^ m * m.factorial)
        else 0 := fun k hk => by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [invGammaDiv_neg_nat (k - 1) m]
    have heq : (k - 1 = m) ↔ (k = m + 1) := by omega
    by_cases hkm : k = m + 1
    · subst hkm; simp
    · simp [hkm, heq.not.mpr hkm]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.Icc 1 (m + 1)) (m + 1)]
  have hmem : m + 1 ∈ Finset.Icc 1 (m + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  simp only [hmem, ↓reduceIte, hurwitzBernoulliCoeff_eq_map_eval, Nat.factorial_succ]
  have hfm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hm1 : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hsign : (-1 : ℂ) ^ (m + 1) * (-1 : ℂ) ^ m = -1 := by
    rw [pow_succ', mul_assoc, ← mul_pow]; norm_num
  push_cast; field_simp
  linear_combination ((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval c * hsign

/-- At `s = 0`, `complexHurwitzZeta 0 c = 1 / 2 - c`. -/
@[simp]
theorem complexHurwitzZeta_zero (c : ℂ) : complexHurwitzZeta 0 c = 1 / 2 - c := by
  have h := complexHurwitzZeta_neg_nat 0 c
  simp only [Nat.cast_zero, neg_zero, zero_add, div_one, Polynomial.bernoulli_one,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eq_ratCast, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at h
  rw [h]; push_cast; ring

/-- Special-value identity: `complexHurwitzZeta (-1) 1 = -1 / 12`. -/
theorem complexHurwitzZeta_neg_one_one : complexHurwitzZeta (-1) 1 = -1 / 12 := by
  have h := complexHurwitzZeta_neg_nat 1 1
  have hb2 := hurwitzBernoulliCoeff_two 1
  rw [hurwitzBernoulliCoeff_eq_map_eval] at hb2
  simp only [even_two, Even.neg_pow, one_pow, one_mul, Nat.factorial_two, Nat.cast_ofNat] at hb2
  simp only [Nat.cast_one] at h
  rw [h]; linear_combination -hb2

/-! ### Packaged milestone statement -/

/-- Joint meromorphic continuation of the complex-parameter Hurwitz zeta function, with its
regularized `(s - 1)`-multiplied companion, unit residue at `s = 1`, and Bernoulli polynomial
values at all nonpositive integers. -/
theorem complexHurwitzContinuation_exists :
    ∃ H R : ℂ × ℂ → ℂ,
      DifferentiableOn ℂ H {p | p.1 ≠ 1 ∧ 0 < p.2.re} ∧
      DifferentiableOn ℂ R {p | 0 < p.2.re} ∧
      ∀ c : ℂ, 0 < c.re →
        (∀ s : ℂ, 1 < s.re → H (s, c) = complexHurwitzSeries s c) ∧
        R (1, c) = 1 ∧
        (∀ s : ℂ, s ≠ 1 → R (s, c) = (s - 1) * H (s, c)) ∧
        (∀ m : ℕ, H (-(m : ℂ), c) =
          -((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval c / (m + 1)) :=
  ⟨fun p => complexHurwitzZeta p.1 p.2, fun p => complexHurwitzReg p.1 p.2,
    differentiableOn_complexHurwitzZeta, differentiableOn_complexHurwitzReg, fun c hc =>
      ⟨fun _ hs => complexHurwitzZeta_eq_complexHurwitzSeries hs hc,
        complexHurwitzReg_one c,
        fun _ hs => complexHurwitzReg_eq_sub_one_mul hs c,
        fun m => complexHurwitzZeta_neg_nat m c⟩⟩

/-! ### Analytic continuation of the shift, circle comparison, and Dirichlet specialization -/

private theorem eqOn_compl_one_of_eq_on_one_lt_re {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ))
    (hfg : ∀ z : ℂ, 1 < z.re → f z = g z) :
    EqOn f g ({1}ᶜ : Set ℂ) :=
  (hf.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd isOpen_compl_singleton)
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 1).isPreconnected
    (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    (eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 1 < (2 : ℂ).re))
      fun z hz => hfg z hz)

/-- The `c ↦ c + 1` shift identity extends to all `s ≠ 1` and `0 < c.re`. -/
theorem complexHurwitzZeta_add_one {s c : ℂ} (hs : s ≠ 1) (hc : 0 < c.re) :
    complexHurwitzZeta s (c + 1) = complexHurwitzZeta s c - c ^ (-s) := by
  have hc1 : 0 < (c + 1).re := by simp; linarith
  have hc_ne : c ≠ 0 := fun h0 => lt_irrefl (0 : ℝ) (by rwa [h0, zero_re] at hc)
  have hdf : DifferentiableOn ℂ (fun z => complexHurwitzZeta z (c + 1)) ({1}ᶜ : Set ℂ) :=
    fun _ hz => (differentiableAt_complexHurwitzZeta_fst hz hc1).differentiableWithinAt
  have hdg : DifferentiableOn ℂ (fun z => complexHurwitzZeta z c - c ^ (-z)) ({1}ᶜ : Set ℂ) :=
    fun _ hz => ((differentiableAt_complexHurwitzZeta_fst hz hc).sub
      (differentiableAt_id.neg.const_cpow (Or.inl hc_ne))).differentiableWithinAt
  exact eqOn_compl_one_of_eq_on_one_lt_re hdf hdg (fun z hz => by
    rw [complexHurwitzZeta_eq_complexHurwitzSeries hz hc1,
      complexHurwitzZeta_eq_complexHurwitzSeries hz hc,
      complexHurwitzSeries_add_one hz (mem_slitPlane_iff.mpr (Or.inl hc))]) hs

/-- For real `x ∈ (0, 1]` and `s ≠ 1`, `complexHurwitzZeta s x` agrees with Mathlib's
`HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`. -/
theorem complexHurwitzZeta_ofReal_eq_hurwitzZeta {s : ℂ} {x : ℝ} (hs : s ≠ 1)
    (hx : x ∈ Ioc 0 1) :
    complexHurwitzZeta s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  have hx_re : 0 < (x : ℂ).re := by simp [hx.1]
  have hdf : DifferentiableOn ℂ (fun z => complexHurwitzZeta z x) ({1}ᶜ : Set ℂ) :=
    fun _ hz => (differentiableAt_complexHurwitzZeta_fst hz hx_re).differentiableWithinAt
  have hdg : DifferentiableOn ℂ (HurwitzZeta.hurwitzZeta (x : UnitAddCircle))
      ({1}ᶜ : Set ℂ) :=
    fun _ hz => (HurwitzZeta.differentiableAt_hurwitzZeta _ hz).differentiableWithinAt
  exact eqOn_compl_one_of_eq_on_one_lt_re hdf hdg (fun z hz => by
    rw [complexHurwitzZeta_eq_complexHurwitzSeries hz hx_re,
      complexHurwitzSeries_ofReal_eq_hurwitzZeta hz hx]) hs

/-- At `c = 1` and `s ≠ 1`, `complexHurwitzZeta s 1 = riemannZeta s`. -/
theorem complexHurwitzZeta_one {s : ℂ} (hs : s ≠ 1) :
    complexHurwitzZeta s 1 = riemannZeta s := by
  have h := complexHurwitzZeta_ofReal_eq_hurwitzZeta (x := 1) hs (right_mem_Ioc.mpr zero_lt_one)
  rwa [ofReal_one, AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h

end TauCeti

namespace HurwitzZeta

/-- For `x ∈ (0, 1]` and every `k : ℕ` (including `k = 0`), `hurwitzZeta (x : UnitAddCircle) (-k)`
equals `-B_{k + 1}(x) / (k + 1)`. -/
theorem hurwitzZeta_neg_nat_of_mem_Ioc (k : ℕ) {x : ℝ} (hx : x ∈ Ioc 0 1) :
    hurwitzZeta (x : UnitAddCircle) (-k) =
      -((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) / (k + 1) := by
  have hne : (-(k : ℂ)) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h; simp at hre; linarith
  rw [← TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta hne hx,
    TauCeti.complexHurwitzZeta_neg_nat]

/-- For `x ∈ (0, 1]`, `hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x`. -/
theorem hurwitzZeta_apply_zero_of_mem_Ioc {x : ℝ} (hx : x ∈ Ioc 0 1) :
    hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x := by
  rw [← TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta zero_ne_one hx,
    TauCeti.complexHurwitzZeta_zero]

end HurwitzZeta

namespace ZMod

/-- Reindexing `ZMod N` over `a ∈ {1, ..., N}` expresses `ZMod.LFunction Φ s` for all `s ∈ ℂ`
(including `s = 1`) in terms of the positive residue representatives `a / N ∈ (0, 1]`. -/
theorem LFunction_eq_sum_Icc_hurwitzZeta {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N,
          Φ a * HurwitzZeta.hurwitzZeta ((a / N : ℝ) : UnitAddCircle) s := by
  rw [ZMod.LFunction]
  congr 1
  symm
  refine Finset.sum_bij (fun a _ => (a : ZMod N)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    fun _ _ => by rw [ZMod.toAddCircle_natCast]
  · intro a₁ ha₁ a₂ ha₂ heq
    obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp ha₁
    obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp ha₂
    rcases eq_or_lt_of_le h1b with rfl | h1lt <;> rcases eq_or_lt_of_le h2b with rfl | h2lt
    · rfl
    · rw [ZMod.natCast_self] at heq
      have hv := congrArg ZMod.val heq.symm
      rw [ZMod.val_natCast_of_lt h2lt, ZMod.val_zero] at hv; omega
    · rw [ZMod.natCast_self] at heq
      have hv := congrArg ZMod.val heq
      rw [ZMod.val_natCast_of_lt h1lt, ZMod.val_zero] at hv; omega
    · have hv := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt h1lt, ZMod.val_natCast_of_lt h2lt] at hv
  · intro j _
    have hN : 0 < N := NeZero.pos N
    by_cases hj : j.val = 0
    · refine ⟨N, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
      rw [ZMod.natCast_self]
      exact ((ZMod.val_eq_zero j).mp hj).symm
    · exact ⟨j.val, Finset.mem_Icc.mpr ⟨by omega, (ZMod.val_lt j).le⟩,
        ZMod.natCast_zmod_val j⟩

/-- Away from `s = 1`, `ZMod.LFunction Φ s` is `(N : ℂ) ^ (-s)` times the finite sum of
`Φ a * TauCeti.complexHurwitzZeta s (a / N)` over `a ∈ {1, ..., N}`. -/
theorem LFunction_eq_sum_Icc_complexHurwitzZeta {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : s ≠ 1) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzZeta s ((a : ℂ) / N) := by
  rw [LFunction_eq_sum_Icc_hurwitzZeta]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hx : (a : ℝ) / N ∈ Ioc 0 1 :=
    ⟨div_pos (by exact_mod_cast ha1) hN, (div_le_one hN).mpr (by exact_mod_cast haN)⟩
  rw [← TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta hs hx]
  push_cast; rfl

/-- On `1 < s.re`, `ZMod.LFunction Φ s` equals `(N : ℂ) ^ (-s)` times the finite sum of
`Φ a * TauCeti.complexHurwitzSeries s (a / N)` over `a ∈ {1, ..., N}`. -/
theorem LFunction_eq_sum_Icc_complexHurwitzSeries {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzSeries s ((a : ℂ) / N) := by
  have hs1 : s ≠ 1 := fun h => lt_irrefl (1 : ℝ) (by rwa [h, one_re] at hs)
  rw [LFunction_eq_sum_Icc_complexHurwitzZeta Φ hs1]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have hre : 0 < ((a : ℂ) / N).re := by
    have heq : ((a : ℂ) / N) = (((a : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, ofReal_re]
    exact div_pos (by exact_mod_cast (Finset.mem_Icc.mp ha).1) (Nat.cast_pos.mpr (NeZero.pos N))
  rw [TauCeti.complexHurwitzZeta_eq_complexHurwitzSeries hs hre]

end ZMod

namespace DirichletCharacter

/-- For any Dirichlet character `χ` modulo `N ≥ 1` (primitive or imprimitive, including principal
characters) and all `s ∈ ℂ`, `χ.LFunction s` is `N ^ (-s)` times the finite circle-Hurwitz sum
over `a ∈ {1, ..., N}`. -/
theorem LFunction_eq_sum_Icc_hurwitzZeta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) :
    χ.LFunction s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N,
          χ a * HurwitzZeta.hurwitzZeta ((a / N : ℝ) : UnitAddCircle) s :=
  ZMod.LFunction_eq_sum_Icc_hurwitzZeta χ s

/-- Away from `s = 1`, `χ.LFunction s` equals
`N ^ (-s) * ∑ a ∈ Icc 1 N, χ a * complexHurwitzZeta s (a / N)`. -/
theorem LFunction_eq_sum_Icc_complexHurwitzZeta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ≠ 1) :
    χ.LFunction s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, χ a * TauCeti.complexHurwitzZeta s ((a : ℂ) / N) :=
  ZMod.LFunction_eq_sum_Icc_complexHurwitzZeta χ hs

/-- On `1 < s.re`, `χ.LFunction s` equals
`N ^ (-s) * ∑ a ∈ Icc 1 N, χ a * complexHurwitzSeries s (a / N)`. -/
theorem LFunction_eq_sum_Icc_complexHurwitzSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, χ a * TauCeti.complexHurwitzSeries s ((a : ℂ) / N) :=
  ZMod.LFunction_eq_sum_Icc_complexHurwitzSeries χ hs

end DirichletCharacter

end
