/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Analytic.ConvergenceRadius

/-!
# Cauchy's inequality for homogeneous terms and truncated Taylor remainders

Let `f : E → V` have the formal multilinear series `p` on an open ball about `x` in a complex
normed space `E`, with values in a complex normed space `V`, and suppose `‖f‖ ≤ M` on that ball.

Restricting along the complex line `ζ ↦ x + ζ • y` and pairing with a norming dual functional
reduces the homogeneous term `p n (fun _ ↦ y)` to a one-variable Cauchy coefficient on the unit
circle, giving **Cauchy's inequality** `‖p n (fun _ ↦ y)‖ ≤ M` for every `y` in the open ball of
the same radius about `0`, without requiring `V` to be complete.

Combining this bound on the terms of degree `< T` with Mathlib's higher-order Schwarz lemma
(`Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`) applied to the scalarized remainder
`w ↦ (ℓ ∘ f) (x + w) - (ℓ.compFormalMultilinearSeries p).partialSum T w` on `Metric.ball 0 R`
yields the **truncated Taylor remainder estimate**
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
  let u : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ y
  have hyr : ‖y‖ₑ < r := by simpa [mem_eball_zero_iff] using hy
  have hu : ‖u‖ₑ = ‖y‖ₑ := by simp [u, eNorm_eq_nnNorm]
  have h1r : (1 : ℝ≥0∞) < r / ‖u‖ₑ := by
    rcases eq_or_ne ‖u‖ₑ 0 with hu0 | hu0
    · simp [hu0, ENNReal.div_zero hf.r_pos.ne']
    · exact (ENNReal.lt_div_iff_mul_lt (Or.inl hu0) (Or.inl eNorm_ne_top)).2 (by simpa [hu])
  have hf₀ : HasFPowerSeriesOnBall (fun z ↦ (ℓ ∘ f) (x + z))
      (ℓ.compFormalMultilinearSeries p) 0 r := by
    simpa [add_comm] using (ℓ.comp_hasFPowerSeriesOnBall hf).comp_sub (-x)
  let g : ℂ → ℂ := fun ζ ↦ (ℓ ∘ f) (x + ζ • y)
  have hg : HasFPowerSeriesOnBall g
      ((ℓ.compFormalMultilinearSeries p).compContinuousLinearMap u) 0 (r / ‖u‖ₑ) :=
    ((map_zero u).symm ▸ hf₀).compContinuousLinearMap
  have hsub : closedBall (0 : ℂ) (1 : ℝ≥0) ⊆ Metric.eball (0 : ℂ) (r / ‖u‖ₑ) := fun ζ hζ ↦ by
    rw [mem_eball_zero_iff, ← ofReal_norm]
    exact (ENNReal.ofReal_le_one.2 (by simpa using hζ)).trans_lt h1r
  have hd : DifferentiableOn ℂ g (closedBall (0 : ℂ) (1 : ℝ≥0)) :=
    (hg.analyticOnNhd.mono hsub).differentiableOn
  have heq : (ℓ.compFormalMultilinearSeries p).compContinuousLinearMap u =
      cauchyPowerSeries g 0 (1 : ℝ≥0) :=
    hg.hasFPowerSeriesAt.eq_formalMultilinearSeries
      (hd.hasFPowerSeriesOnBall zero_lt_one).hasFPowerSeriesAt
  have happly : ‖p n (fun _ ↦ y)‖ = ‖cauchyPowerSeries g 0 (1 : ℝ≥0) n (fun _ ↦ 1)‖ := by
    have hval := congr_arg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q n (fun _ ↦ 1)) heq
    simpa [-FormalMultilinearSeries.apply_eq_prod_smul_coeff, u, Function.comp_def, hℓv] using
      congr_arg norm hval
  rw [happly, cauchyPowerSeries_apply]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (by positivity) (C := M) fun ζ hζ ↦ ?_).trans (by simp)
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 (by simpa using hζ)
  have hmem : x + ζ • y ∈ Metric.eball x r := by
    simpa [Metric.mem_eball, edist_dist, dist_eq_norm, norm_smul, hζ1, ofReal_norm] using hyr
  simpa [g, norm_smul, hζ1] using
    (ℓ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hℓ1).trans (hM _ hmem))

/-- **Cauchy's inequality for homogeneous terms**: if `f` has the power series `p` on
`Metric.ball x R` and `‖f‖ ≤ M` there, then `‖p n (fun _ ↦ y)‖ ≤ M` whenever `‖y‖ < R`. -/
theorem norm_apply_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {x : E} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ w ∈ Metric.ball x R, ‖f w‖ ≤ M)
    (n : ℕ) {y : E} (hy : ‖y‖ < R) : ‖p n (fun _ ↦ y)‖ ≤ M := by
  rw [← Metric.eball_coe] at hM
  refine hf.norm_apply_le_of_forall_mem_eball hM n ?_
  rwa [Metric.eball_coe, mem_ball_zero_iff]

/-- **Truncated Taylor remainder estimate** about an arbitrary centre `x`: if `f` has the power
series `p` on `Metric.ball x R` and `‖f‖ ≤ M` there, then
`‖f (x + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T` for every `T : ℕ` and `‖z‖ < R`. -/
theorem norm_add_sub_partialSum_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {x : E}
    {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x R)
    {M : ℝ} (hM : ∀ y ∈ Metric.ball x R, ‖f y‖ ≤ M) (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f (x + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  rcases Nat.eq_zero_or_pos T with rfl | hTpos
  · simpa using hM (x + z) (by simpa [dist_eq_norm] using hz)
  -- Pair with a norming dual functional to work in the complete target space `ℂ`.
  obtain ⟨ℓ, hℓ1, hℓv⟩ := exists_dual_vector'' ℂ (f (x + z) - p.partialSum T z)
  have hfℓ := ℓ.comp_hasFPowerSeriesOnBall hf
  have hMℓ : ∀ y ∈ Metric.ball x R, ‖(ℓ ∘ f) y‖ ≤ M := fun y hy ↦
    (ℓ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hℓ1).trans (hM y hy))
  let pℓ := ℓ.compFormalMultilinearSeries p
  let g : E → ℂ := fun w ↦ (ℓ ∘ f) (x + w) - pℓ.partialSum T w
  have hg0 : g 0 = 0 := by
    simp [g, pℓ, p.partialSum_apply_zero_of_pos hTpos, hf.coeff_zero]
  have hfd : DifferentiableOn ℂ (fun w ↦ (ℓ ∘ f) (x + w)) (Metric.ball (0 : E) R) := by
    simpa [Metric.eball_coe, add_comm] using (hfℓ.comp_sub (-x)).differentiableOn
  have hpd : Differentiable ℂ (pℓ.partialSum T) :=
    Differentiable.fun_sum fun k _ ↦
      ((pℓ k).contDiff (n := 1)).comp (contDiff_pi.2 fun _ ↦ contDiff_id) |>.differentiable
        one_ne_zero
  have hmaps : Set.MapsTo g (Metric.ball (0 : E) R) (Metric.closedBall (g 0) ((1 + T) * M)) := by
    intro w hw
    have hwR : ‖w‖ < R := by simpa using hw
    rw [mem_closedBall, hg0, dist_zero_right]
    calc ‖g w‖ ≤ ‖(ℓ ∘ f) (x + w)‖ + ‖pℓ.partialSum T w‖ := norm_sub_le _ _
      _ ≤ M + ∑ k ∈ Finset.range T, ‖pℓ k (fun _ ↦ w)‖ :=
          add_le_add (hMℓ _ (by simpa [dist_eq_norm] using hwR)) (norm_sum_le _ _)
      _ ≤ M + ∑ _k ∈ Finset.range T, M :=
          add_le_add le_rfl (Finset.sum_le_sum fun k _ ↦ hfℓ.norm_apply_le hMℓ k hwR)
      _ = (1 + T) * M := by simp [nsmul_eq_mul]; ring
  have hlittle : (fun w ↦ g w - g 0) =o[𝓝 (0 : E)] fun w ↦ ‖w - 0‖ ^ (T - 1) := by
    rw [hg0]
    simpa only [g, sub_zero] using
      (hfℓ.hasFPowerSeriesAt.isBigO_sub_partialSum_pow T).trans_isLittleO
        (by simpa only [sub_zero] using
          Asymptotics.isLittleO_pow_sub_pow_sub (0 : E) (Nat.sub_lt hTpos zero_lt_one))
  have hest := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    (f := g) (hfd.fun_sub hpd.differentiableOn) hmaps hlittle (by simpa using hz)
  have hlhs : ‖g z‖ = ‖f (x + z) - p.partialSum T z‖ := by
    simp [g, pℓ, ← map_sub, hℓv]
  rwa [hg0, dist_zero_right, dist_zero_right, Nat.sub_add_cancel hTpos, hlhs] at hest

/-- **Truncated Taylor remainder estimate** about the origin: if `f` has the power series `p` on
`Metric.ball 0 R` and `‖f‖ ≤ M` there, then
`‖f z - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T` for every `T : ℕ` and `‖z‖ < R`. -/
theorem norm_sub_partialSum_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p 0 R) {M : ℝ} (hM : ∀ y ∈ Metric.ball (0 : E) R, ‖f y‖ ≤ M)
    (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f z - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  simpa only [zero_add] using hf.norm_add_sub_partialSum_le hM T hz

end HasFPowerSeriesOnBall
