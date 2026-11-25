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
the same radius about `0`, and by continuity of `p n` also on the closed ball `‖v‖ ≤ R` (and
`‖y‖ₑ ≤ r`), without requiring `V` to be complete. By homogeneity, this gives the scaling form
`‖p n (fun _ ↦ v)‖ * R ^ n ≤ M * ‖v‖ ^ n` for every `v : E`.

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

* `HasFPowerSeriesOnBall.norm_apply_le_of_forall_norm_eq_one`,
  `HasFPowerSeriesOnBall.norm_apply_le_of_forall_mem_eball`, and
  `HasFPowerSeriesOnBall.norm_apply_le`: Cauchy's inequality `‖p n (fun _ ↦ y)‖ ≤ M` for
  homogeneous terms: when `‖f (x + ζ • y)‖ ≤ M` on the unit circle `‖ζ‖ = 1` with `‖y‖ₑ < r`,
  when `‖f‖ ≤ M` on `Metric.eball x r` with `‖y‖ₑ ≤ r`, and when `‖f‖ ≤ M` on `Metric.ball x R`
  with `‖y‖ ≤ R`.
* `HasFPowerSeriesOnBall.norm_apply_mul_pow_le`: the homogeneous scaling form
  `‖p n (fun _ ↦ v)‖ * R ^ n ≤ M * ‖v‖ ^ n` for every `v : E`, when `‖f‖ ≤ M` on
  `Metric.ball x R`.
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

/-- **Cauchy's inequality on a complex circle** for a homogeneous term: if `f` has the power
series `p` on `Metric.eball x r`, `‖y‖ₑ < r`, and `‖f (x + ζ • y)‖ ≤ M` for every `ζ : ℂ` with
`‖ζ‖ = 1` and `‖ζ • y‖ₑ < r`, then `‖p n (fun _ ↦ y)‖ ≤ M`. -/
theorem norm_apply_le_of_forall_norm_eq_one {f : E → V} {p : FormalMultilinearSeries ℂ E V}
    {x : E} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p x r)
    {M : ℝ} (n : ℕ) {y : E} (hy : ‖y‖ₑ < r)
    (hM : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖ζ • y‖ₑ < r → ‖f (x + ζ • y)‖ ≤ M) :
    ‖p n (fun _ ↦ y)‖ ≤ M := by
  obtain ⟨ℓ, hℓ1, hℓv⟩ := exists_dual_vector'' ℂ (p n (fun _ ↦ y))
  let u : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ y
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
  have hζy : ‖ζ • y‖ₑ < r := by
    rwa [eNorm_smul, ← ofReal_norm, hζ1, ENNReal.ofReal_one, one_mul]
  simpa [g, hζ1] using
    (ℓ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hℓ1).trans (hM ζ hζ1 hζy))

/-- **Cauchy's inequality for homogeneous terms** on an `eball`: if `f` has the power series `p`
on `Metric.eball x r` and `‖f‖ ≤ M` there, then `‖p n (fun _ ↦ y)‖ ≤ M` for every `y : E` with
`‖y‖ₑ ≤ r` and every `n : ℕ`. -/
theorem norm_apply_le_of_forall_mem_eball {f : E → V} {p : FormalMultilinearSeries ℂ E V}
    {x : E} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p x r)
    {M : ℝ} (hM : ∀ w ∈ Metric.eball x r, ‖f w‖ ≤ M) (n : ℕ) {y : E}
    (hy : ‖y‖ₑ ≤ r) : ‖p n (fun _ ↦ y)‖ ≤ M := by
  have hball {z : E} (hz : ‖z‖ₑ < r) : ‖p n (fun _ ↦ z)‖ ≤ M :=
    hf.norm_apply_le_of_forall_norm_eq_one n hz fun ζ _ hζz ↦ by
      refine hM _ ?_
      rwa [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_left]
  rcases hy.lt_or_eq with hy_lt | hy_eq
  · exact hball hy_lt
  · have hy0 : 0 < ‖y‖ := by
      rw [← ofReal_norm] at hy_eq
      exact ENNReal.ofReal_pos.1 (hy_eq ▸ hf.r_pos)
    have hmaps : Set.MapsTo (fun z : E ↦ ‖p n (fun _ ↦ z)‖) (Metric.ball (0 : E) ‖y‖) (Set.Iic M) :=
      fun z hz ↦ hball <| by
        calc ‖z‖ₑ = ENNReal.ofReal ‖z‖ := (ofReal_norm z).symm
          _ < ENNReal.ofReal ‖y‖ := (ENNReal.ofReal_lt_ofReal_iff hy0).2 (mem_ball_zero_iff.1 hz)
          _ = r := (ofReal_norm y).trans hy_eq
    have hcont : Continuous fun z : E ↦ ‖p n (fun _ ↦ z)‖ :=
      ((p n).coe_continuous.comp (continuous_pi fun _ ↦ continuous_id)).norm
    have hcl := hmaps.closure_left hcont isClosed_Iic
    rw [closure_ball (0 : E) hy0.ne'] at hcl
    exact hcl (by simp)

/-- **Cauchy's inequality for homogeneous terms**: if `f` has the power series `p` on
`Metric.ball x R` and `‖f‖ ≤ M` there, then `‖p n (fun _ ↦ v)‖ ≤ M` whenever `‖v‖ ≤ R`. -/
theorem norm_apply_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {x : E} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ w ∈ Metric.ball x R, ‖f w‖ ≤ M)
    (n : ℕ) {v : E} (hv : ‖v‖ ≤ R) : ‖p n (fun _ ↦ v)‖ ≤ M := by
  rw [← Metric.eball_coe] at hM
  refine hf.norm_apply_le_of_forall_mem_eball hM n ?_
  rwa [← ofReal_norm, ENNReal.ofReal_le_coe]

/-- **Cauchy's inequality for homogeneous terms (homogeneous scaling form).** If `f : E → V` has
formal power series `p` on `Metric.ball x R` and satisfies `‖f w‖ ≤ M` there, then
`‖p n (fun _ ↦ v)‖ * R ^ n ≤ M * ‖v‖ ^ n` for every `n : ℕ` and `v : E`. Neither `E` nor `V` is
assumed complete. -/
theorem norm_apply_mul_pow_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {x : E} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ w ∈ Metric.ball x R, ‖f w‖ ≤ M)
    (n : ℕ) (v : E) : ‖p n (fun _ ↦ v)‖ * (R : ℝ) ^ n ≤ M * ‖v‖ ^ n := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hf.r_pos
  rcases eq_or_ne v 0 with rfl | hv
  · rcases n.eq_zero_or_pos with rfl | hn
    · simpa [hf.coeff_zero] using hM x (mem_ball_self hR)
    · have h0 : p n (fun _ ↦ (0 : E)) = 0 := (p n).map_coord_zero ⟨0, hn⟩ rfl
      simp [h0, zero_pow hn.ne']
  · have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hc0 : 0 ≤ (R : ℝ) / ‖v‖ := div_nonneg hR.le hv0.le
    have hy_norm : ‖((R / ‖v‖ : ℝ) : ℂ) • v‖ = R := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0, div_mul_cancel₀ _ hv0.ne']
    have hle := hf.norm_apply_le hM n hy_norm.le
    have hsmul : ‖p n (fun _ ↦ ((R / ‖v‖ : ℝ) : ℂ) • v)‖ =
        (R : ℝ) ^ n / ‖v‖ ^ n * ‖p n (fun _ ↦ v)‖ := by
      rw [(p n).map_smul_univ (fun _ ↦ ((R / ‖v‖ : ℝ) : ℂ)) (fun _ ↦ v)]
      simp only [Finset.prod_const, Finset.card_fin, norm_smul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hc0, div_pow]
    rw [hsmul] at hle
    calc ‖p n (fun _ ↦ v)‖ * (R : ℝ) ^ n
        = ((R : ℝ) ^ n / ‖v‖ ^ n * ‖p n (fun _ ↦ v)‖) * ‖v‖ ^ n := by
          field_simp [hv0.ne']
      _ ≤ M * ‖v‖ ^ n := mul_le_mul_of_nonneg_right hle (pow_nonneg hv0.le n)

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
          add_le_add le_rfl (Finset.sum_le_sum fun k _ ↦ hfℓ.norm_apply_le hMℓ k hwR.le)
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
