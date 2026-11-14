/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Analytic.ConvergenceRadius
import TauCeti.Analysis.Complex.Schwarz

/-!
# Cauchy's inequality for homogeneous terms and truncated Taylor remainders

Let `f : E → V` have the formal multilinear series `p` on an open ball about `x` in a complex
normed space `E`, with values in a complex normed space `V`, and suppose `‖f‖ ≤ M` on that ball.

Restricting along the complex line `ζ ↦ x + ζ • y` and pairing with a norming dual functional
reduces the homogeneous term `p n (fun _ ↦ y)` to a one-variable Cauchy coefficient on the unit
circle, giving **Cauchy's inequality** `‖p n (fun _ ↦ y)‖ ≤ M` for every `y` in the open ball of
the same radius about `0`, without requiring `V` to be complete.

Combining this bound on the terms of degree `< T` with Schwarz's lemma for a zero of order `T` on
the slice `w ↦ f (x + (w / ‖z‖) • z) - p.partialSum T ((w / ‖z‖) • z)` yields the **truncated
Taylor remainder estimate**
`‖f (x + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T`
for `‖z‖ < R`, again without requiring `V` to be complete. In transcendence proofs (Waldschmidt,
Lemma 4.13) this controls the value of an auxiliary function on a smaller ball once its Taylor
coefficients of degree `< T` have been made small by Siegel's lemma; the factor `1 + T` replaces
the Hilbert-space factor `1 + √T` from Parseval's identity so that any normed target space `V` is
allowed.

## Main results

* `HasFPowerSeriesOnBall.norm_apply_le_of_forall_mem_eball` and
  `HasFPowerSeriesOnBall.norm_apply_le`: Cauchy's inequality `‖p n (fun _ ↦ y)‖ ≤ M` for every
  homogeneous term on `Metric.eball` and `Metric.ball`.
* `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` and
  `HasFPowerSeriesOnBall.norm_sub_partialSum_le`: the Taylor remainder bound
  `(1 + T) * M * (‖z‖ / R) ^ T` about an arbitrary centre `x` and about `0`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren 326,
  Springer (2000), §4.5, Lemma 4.13, pp. 134–135.
* Michail Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
  commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/Interpolation.lean`, Apache 2.0).
-/

public section

open Filter Metric Topology
open scoped ENNReal NNReal

namespace HasFPowerSeriesOnBall

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **Cauchy's inequality for homogeneous terms** on an `eball`: if `f` has the power series `p`
on `Metric.eball x r` and `‖f‖ ≤ M` there, then `‖p n (fun _ ↦ y)‖ ≤ M` for every
`y ∈ Metric.eball 0 r` and every `n : ℕ`. -/
theorem norm_apply_le_of_forall_mem_eball {f : E → V} {p : FormalMultilinearSeries ℂ E V}
    {x : E} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p x r)
    {M : ℝ} (hM : ∀ w ∈ Metric.eball x r, ‖f w‖ ≤ M) (n : ℕ) {y : E}
    (hy : y ∈ Metric.eball (0 : E) r) : ‖p n (fun _ ↦ y)‖ ≤ M := by
  obtain ⟨ℓ, hℓ1, hℓv⟩ := exists_dual_vector'' ℂ (p n (fun _ ↦ y))
  let u : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight y
  have hyr : ‖y‖ₑ < r := by simpa [mem_eball_zero_iff] using hy
  have hu_le : ‖u‖ ≤ ‖y‖ := u.opNorm_le_bound (norm_nonneg y) fun ζ ↦ by
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul, mul_comm]
  have hur : ‖u‖ₑ < r := (eNorm_le_iff_norm_le.2 hu_le).trans_lt hyr
  have h1r : (1 : ℝ≥0∞) < r / ‖u‖ₑ := by
    rcases eq_or_ne ‖u‖ₑ 0 with hu0 | hu0
    · simp [hu0, ENNReal.div_zero hf.r_pos.ne']
    · exact (ENNReal.lt_div_iff_mul_lt (Or.inl hu0) (Or.inl eNorm_ne_top)).2 (by simpa)
  -- Translate `ℓ ∘ f` to `0` and restrict along `u : ζ ↦ ζ • y`.
  let f₀ : E → ℂ := fun z ↦ (ℓ ∘ f) (x + z)
  have hf₀ : HasFPowerSeriesOnBall f₀ (ℓ.compFormalMultilinearSeries p) 0 r :=
    { r_le := (ℓ.comp_hasFPowerSeriesOnBall hf).r_le
      r_pos := hf.r_pos
      hasSum := fun hz ↦ by
        simpa only [f₀, zero_add] using (ℓ.comp_hasFPowerSeriesOnBall hf).hasSum hz }
  have hg : HasFPowerSeriesOnBall (f₀ ∘ u)
      ((ℓ.compFormalMultilinearSeries p).compContinuousLinearMap u) 0 (r / ‖u‖ₑ) :=
    ((map_zero u).symm ▸ hf₀).compContinuousLinearMap
  have hsub : closedBall (0 : ℂ) (1 : ℝ≥0) ⊆ Metric.eball (0 : ℂ) (r / ‖u‖ₑ) := fun ζ hζ ↦ by
    have hζ1 : ‖ζ‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_one.2 (by simpa [mem_closedBall_zero_iff] using hζ)
    simpa [mem_eball_zero_iff] using hζ1.trans_lt h1r
  have hd : DifferentiableOn ℂ (f₀ ∘ u) (closedBall (0 : ℂ) (1 : ℝ≥0)) :=
    (hg.analyticOnNhd.mono hsub).differentiableOn
  have heq : (ℓ.compFormalMultilinearSeries p).compContinuousLinearMap u =
      cauchyPowerSeries (f₀ ∘ u) 0 (1 : ℝ≥0) :=
    hg.hasFPowerSeriesAt.eq_formalMultilinearSeries
      (hd.hasFPowerSeriesOnBall zero_lt_one).hasFPowerSeriesAt
  have happly : ‖p n (fun _ ↦ y)‖ = ‖cauchyPowerSeries (f₀ ∘ u) 0 (1 : ℝ≥0) n (fun _ ↦ 1)‖ := by
    have hval := congr_arg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q n (fun _ ↦ 1)) heq
    have hfun : (u ∘ fun _ : Fin n ↦ (1 : ℂ)) = fun _ ↦ y := funext fun _ ↦ by simp [u]
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, hfun, hℓv] at hval
    have hnorm : ‖(‖p n (fun _ ↦ y)‖ : ℂ)‖ = ‖p n (fun _ ↦ y)‖ := by simp
    exact hnorm.symm.trans (congr_arg norm hval)
  rw [happly, cauchyPowerSeries_apply]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (by positivity) (C := M) fun ζ hζ ↦ ?_).trans (by simp)
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 (by simpa using hζ)
  have hmem : x + ζ • y ∈ Metric.eball x r := by
    rw [Metric.mem_eball, edist_dist, dist_eq_norm, add_sub_cancel_left, norm_smul, hζ1,
      one_mul, ofReal_norm]
    exact hyr
  have hfu : ‖(f₀ ∘ u) ζ‖ ≤ M := by
    dsimp [f₀, u]
    calc ‖ℓ (f (x + ζ • y))‖ ≤ ‖ℓ‖ * ‖f (x + ζ • y)‖ := ℓ.le_opNorm _
      _ ≤ 1 * M := mul_le_mul hℓ1 (hM _ hmem) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  simpa [norm_smul, hζ1] using hfu

/-- **Cauchy's inequality for homogeneous terms**: if `f` has the power series `p` on
`Metric.ball x R` and `‖f‖ ≤ M` there, then `‖p n (fun _ ↦ y)‖ ≤ M` whenever `‖y‖ < R`. -/
theorem norm_apply_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {x : E} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ w ∈ Metric.ball x R, ‖f w‖ ≤ M)
    (n : ℕ) {y : E} (hy : ‖y‖ < R) : ‖p n (fun _ ↦ y)‖ ≤ M := by
  rw [← Metric.eball_coe] at hM
  refine hf.norm_apply_le_of_forall_mem_eball hM n ?_
  rwa [Metric.eball_coe, mem_ball_zero_iff]

/-- The truncated Taylor remainder estimate when the target space `V` is complete, proved by
slicing along `w ↦ (w / ‖z‖) • z` and applying Schwarz's lemma at order `T`. -/
private theorem norm_add_sub_partialSum_le_of_completeSpace [CompleteSpace V] {f : E → V}
    {p : FormalMultilinearSeries ℂ E V} {x : E} {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x R)
    {M : ℝ} (hM : ∀ y ∈ Metric.ball x R, ‖f y‖ ≤ M) (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f (x + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  have hR : 0 < (R : ℝ) := (norm_nonneg z).trans_lt hz
  rcases Nat.eq_zero_or_pos T with rfl | hTpos
  · have hxz : x + z ∈ Metric.ball x R := by simpa [dist_eq_norm] using hz
    simpa [FormalMultilinearSeries.partialSum] using hM (x + z) hxz
  rcases eq_or_ne z 0 with rfl | hz0
  · -- At `z = 0`, `p.partialSum T 0 = p 0 0 = f x` since `1 ≤ T` and `p k 0 = 0` for `k ≥ 1`.
    have hp0 : p.partialSum T 0 = f x := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hTpos.ne'
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ', hf.coeff_zero,
        Finset.sum_eq_zero fun j _ ↦ (p (j + 1)).map_coord_zero 0 rfl, zero_add]
    simp [hp0, zero_pow hTpos.ne']
  have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz0
  let v : E := ((‖z‖ : ℂ)⁻¹) • z
  have hv_norm : ‖v‖ = 1 := by simp [v, norm_smul, inv_mul_cancel₀ hznorm.ne']
  let u : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  have hu_norm (w : ℂ) : ‖u w‖ = ‖w‖ := by simp [u, norm_smul, hv_norm]
  let g : ℂ → V := fun w ↦ f (x + u w) - p.partialSum T (u w)
  have hpoly (w : ℂ) : p.partialSum T (u w) = ∑ k ∈ Finset.range T, w ^ k • p k (fun _ ↦ v) := by
    unfold FormalMultilinearSeries.partialSum
    exact Finset.sum_congr rfl fun k _ ↦ by
      simpa [u] using (p k).map_smul_univ (fun _ : Fin k ↦ w) (fun _ : Fin k ↦ v)
  have hg_an : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) := fun w hw ↦ by
    have hwu : x + u w ∈ Metric.eball x R := by
      rw [Metric.eball_coe, mem_ball_iff_norm, add_sub_cancel_left, hu_norm]
      simpa using hw
    have hu_an : AnalyticAt ℂ (fun ζ ↦ x + u ζ) w := analyticAt_const.fun_add (u.analyticAt w)
    have hf_an : AnalyticAt ℂ (fun ζ ↦ f (x + u ζ)) w :=
      (hf.analyticOnNhd (x + u w) hwu).fun_comp_of_eq hu_an rfl
    have hp_an : AnalyticAt ℂ (fun ζ ↦ p.partialSum T (u ζ)) w := by
      simp_rw [hpoly]
      exact Finset.analyticAt_fun_sum _ fun k _ ↦ (analyticAt_id.pow k).smul analyticAt_const
    exact hf_an.sub hp_an
  have hg_ord : (T : ℕ∞) ≤ analyticOrderAt g 0 := by
    rw [(hg_an 0 (mem_ball_self hR)).natCast_le_analyticOrderAt_iff_isBigO]
    have hbig := (hf.hasFPowerSeriesAt.isBigO_sub_partialSum_pow T).comp_tendsto
      (u.continuous.tendsto' 0 0 (map_zero u))
    exact Asymptotics.isBigO_norm_right.1
      (by simpa only [Function.comp_def, hu_norm, sub_zero, norm_pow] using hbig)
  have hg_bound (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) R) : ‖g w‖ ≤ (1 + T) * M := by
    have hwR : ‖u w‖ < R := by simpa [hu_norm] using hw
    have hxz : x + u w ∈ Metric.ball x R := by simpa [dist_eq_norm] using hwR
    calc ‖g w‖ ≤ ‖f (x + u w)‖ + ‖p.partialSum T (u w)‖ := norm_sub_le _ _
      _ ≤ M + ∑ k ∈ Finset.range T, ‖p k (fun _ ↦ u w)‖ :=
          add_le_add (hM _ hxz) (norm_sum_le _ _)
      _ ≤ M + ∑ _k ∈ Finset.range T, M :=
          add_le_add le_rfl (Finset.sum_le_sum fun k _ ↦ hf.norm_apply_le hM k hwR)
      _ = (1 + T) * M := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hwz : (‖z‖ : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Complex.norm_real, abs_of_pos hznorm] using hz
  have huz : u (‖z‖ : ℂ) = z := by
    have hne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hznorm.ne'
    simp [u, v, smul_smul, mul_inv_cancel₀ hne]
  have hest := Complex.norm_le_mul_div_pow_of_le_analyticOrderAt
    hg_an.differentiableOn hg_bound hg_ord hwz
  simpa [g, huz, Complex.norm_real, abs_of_pos hznorm] using hest

/-- **Truncated Taylor remainder estimate** about an arbitrary centre `x`: if `f` has the power
series `p` on `Metric.ball x R` and `‖f‖ ≤ M` there, then
`‖f (x + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T` for every `T : ℕ` and `‖z‖ < R`. -/
theorem norm_add_sub_partialSum_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {x : E}
    {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x R)
    {M : ℝ} (hM : ∀ y ∈ Metric.ball x R, ‖f y‖ ≤ M) (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f (x + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  -- Pair the remainder vector with a norming functional in `StrongDual ℂ V` to reduce to `V = ℂ`.
  obtain ⟨ℓ, hℓ1, hℓv⟩ := exists_dual_vector'' ℂ (f (x + z) - p.partialSum T z)
  have hMℓ : ∀ y ∈ Metric.ball x R, ‖(ℓ ∘ f) y‖ ≤ M := fun y hy ↦
    (ℓ.le_opNorm (f y)).trans ((mul_le_mul hℓ1 (hM y hy) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul M))
  have hest := (ℓ.comp_hasFPowerSeriesOnBall hf).norm_add_sub_partialSum_le_of_completeSpace
    hMℓ T hz
  have hlhs : ‖(ℓ ∘ f) (x + z) - (ℓ.compFormalMultilinearSeries p).partialSum T z‖ =
      ‖f (x + z) - p.partialSum T z‖ := by
    rw [Function.comp_apply, ℓ.compFormalMultilinearSeries_partialSum, ← map_sub, hℓv]
    simp
  rwa [hlhs] at hest

/-- **Truncated Taylor remainder estimate** about the origin: if `f` has the power series `p` on
`Metric.ball 0 R` and `‖f‖ ≤ M` there, then
`‖f z - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T` for every `T : ℕ` and `‖z‖ < R`. -/
theorem norm_sub_partialSum_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p 0 R) {M : ℝ} (hM : ∀ y ∈ Metric.ball (0 : E) R, ‖f y‖ ≤ M)
    (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f z - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  simpa only [zero_add] using hf.norm_add_sub_partialSum_le hM T hz

end HasFPowerSeriesOnBall
