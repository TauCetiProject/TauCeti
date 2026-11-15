/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.Schwarz

/-!
# Cauchy bounds on homogeneous terms and truncated Taylor remainders

Let `f : E → V` have a formal multilinear power series `p` on the open ball `ball c R` of a complex
normed space `E`, with values in a complex normed space `V`, and satisfy `‖f y‖ ≤ M` on `ball c R`.
Composing with a continuous linear functional `φ : StrongDual ℂ V` of norm at most `1` (or with the
isometric embedding into the uniform completion of `V`) and restricting to complex lines
`w ↦ c + w • u` reduces estimates on `f` and `p` to holomorphic functions on discs in `ℂ`, so
neither `E` nor `V` need be complete.

Applying Cauchy's derivative estimate on interior circles `sphere 0 r` (`0 < r < R`) and letting
`r → R⁻` yields the sharp homogeneous-term bound `‖p n (fun _ ↦ v)‖ * R ^ n ≤ M * ‖v‖ ^ n` for
every `v : E`, and hence `‖p n (fun _ ↦ v)‖ ≤ M` whenever `‖v‖ ≤ R`.

Combining this coefficient bound with `Complex.norm_le_mul_div_pow_of_le_analyticOrderAt` along the
complex line through `z` bounds the Taylor remainder of order `T`: for `‖z‖ < R`,
`‖f (c + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T`. Along `w ↦ c + w • u` (`‖u‖ = 1`),
the remainder `g w = f (c + w • u) - p.partialSum T (w • u)` has norm at most `M + T * M` on
`ball 0 R` and analytic order at least `T` at `0`. Waldschmidt's Lemma 4.13 gives the constant
`1 + √T` for scalar-valued functions via Parseval's identity on the circle; the triangle inequality
gives `1 + T` in an arbitrary complex normed space.

## Main results

* `HasFPowerSeriesOnBall.norm_apply_mul_pow_le`: the homogeneous Cauchy inequality
  `‖p n (fun _ ↦ v)‖ * R ^ n ≤ M * ‖v‖ ^ n`.
* `HasFPowerSeriesOnBall.norm_apply_le_of_norm_le`: `‖p n (fun _ ↦ v)‖ ≤ M` for `‖v‖ ≤ R`.
* `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` and
  `HasFPowerSeriesOnBall.norm_sub_partialSum_le`: the truncated Taylor remainder bound
  `‖f (c + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T` for `‖z‖ < R`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Lemma 4.13, pp. 134–135.
* Truncated Taylor remainder bounds for complex power series also appear in Michail Karatarakis's
  formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit `1d51891b5b`,
  `Interpolation.lean`, Apache 2.0).
-/

public section

open Filter Finset Metric Topology
open scoped ENNReal NNReal Uniformity

namespace HasFPowerSeriesOnBall

/-- Scalar one-variable case of `HasFPowerSeriesOnBall.norm_apply_mul_pow_le`: Cauchy's estimate on
interior circles `sphere 0 r` (`0 < r < R`), followed by `r → R⁻`. -/
private theorem norm_apply_one_mul_pow_le_of_scalar {g : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ≥0} (hg : HasFPowerSeriesOnBall g q 0 R) {M : ℝ}
    (hM : ∀ w ∈ ball (0 : ℂ) R, ‖g w‖ ≤ M) (n : ℕ) :
    ‖q n (fun _ ↦ 1)‖ * (R : ℝ) ^ n ≤ M := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hg.r_pos
  have hder : iteratedDeriv n g 0 = n.factorial • q n (fun _ ↦ 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hg.factorial_smul 1 n]
  have hsub (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) R) : ‖q n (fun _ ↦ 1)‖ * r ^ n ≤ M := by
    have hcb : closedBall (0 : ℂ) r ⊆ eball (0 : ℂ) R := by
      rw [eball_coe]
      exact closedBall_subset_ball hr.2
    have hdiff : DiffContOnCl ℂ g (ball 0 r) :=
      (hg.analyticOnNhd.mono hcb).differentiableOn.diffContOnCl_ball subset_rfl
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr.1 hdiff
      fun z hz ↦ hM z (sphere_subset_closedBall.trans (closedBall_subset_ball hr.2) hz)
    rw [hder, ← Nat.cast_smul_eq_nsmul ℂ, norm_smul, Complex.norm_natCast,
      le_div_iff₀ (pow_pos hr.1 n)] at hcauchy
    exact le_of_mul_le_mul_left (by linarith) (Nat.cast_pos.2 n.factorial_pos)
  have hcont : Continuous fun r : ℝ ↦ ‖q n (fun _ ↦ 1)‖ * r ^ n := by fun_prop
  refine le_of_tendsto (hcont.continuousWithinAt (s := Set.Iio (R : ℝ))) ?_
  filter_upwards [Ioo_mem_nhdsLT hR] with r hr using hsub r hr

section NormedSpace

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Restricting `f` to a complex ray `w ↦ c + w • u` with `‖u‖ ≤ 1` preserves the power series
radius `R`. -/
private theorem hasFPowerSeriesOnBall_smul {f : E → V} {p : FormalMultilinearSeries ℂ E V}
    {c : E} {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p c R) {u : E} (hu : ‖u‖ ≤ 1) :
    HasFPowerSeriesOnBall (fun w : ℂ ↦ f (c + w • u))
      (p.compContinuousLinearMap (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) u)) 0 R := by
  let L : ℂ →L[ℂ] E := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) u
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one fun w ↦ by
    simpa [L, norm_smul] using mul_le_of_le_one_right (norm_nonneg w) hu
  have hLe : ‖L‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 hL
  have htrans : HasFPowerSeriesOnBall (fun y ↦ f (c + y)) p (L 0) R := by
    simpa [sub_neg_eq_add, add_comm c] using hf.comp_sub (-c)
  refine (htrans.compContinuousLinearMap (u := L) (x := 0)).mono hf.r_pos ?_
  exact ENNReal.le_div_iff_mul_le (Or.inr hf.r_pos.ne') (Or.inl ENNReal.coe_ne_top) |>.2
    (mul_le_of_le_one_right zero_le hLe)

/-- **Cauchy's inequality for homogeneous terms.** If `f : E → V` has formal power series `p` on
`ball c R` and satisfies `‖f y‖ ≤ M` there, then `‖p n (fun _ ↦ v)‖ * R ^ n ≤ M * ‖v‖ ^ n` for
every `n : ℕ` and `v : E`. Neither `E` nor `V` is assumed complete. -/
theorem norm_apply_mul_pow_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {c : E} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p c R) {M : ℝ} (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M) (n : ℕ)
    (v : E) : ‖p n (fun _ ↦ v)‖ * (R : ℝ) ^ n ≤ M * ‖v‖ ^ n := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hf.r_pos
  rcases eq_or_ne v 0 with rfl | hv
  · rcases n.eq_zero_or_pos with rfl | hn
    · simpa [hf.coeff_zero] using hM c (mem_ball_self hR)
    · have h0 : p n (fun _ ↦ (0 : E)) = 0 := (p n).map_coord_zero ⟨0, hn⟩ rfl
      simp [h0, zero_pow hn.ne']
  · set u : E := (‖v‖ : ℂ)⁻¹ • v
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
    have hv_eq : v = (‖v‖ : ℂ) • u := by
      simp [u, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv))]
    obtain ⟨φ, hφ_norm, hφ_val⟩ := exists_dual_vector'' ℂ (p n (fun _ ↦ u))
    let L : ℂ →L[ℂ] E := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) u
    have hps := φ.comp_hasFPowerSeriesOnBall (hasFPowerSeriesOnBall_smul hf hu.le)
    have hbound (w : ℂ) (hw : w ∈ ball (0 : ℂ) R) : ‖(φ ∘ fun w : ℂ ↦ f (c + w • u)) w‖ ≤ M := by
      have hmem : c + w • u ∈ ball c R := by
        rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, hu, mul_one]
        simpa using hw
      exact (φ.le_opNorm _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hφ_norm).trans (hM _ hmem))
    have hscalar := norm_apply_one_mul_pow_le_of_scalar hps hbound n
    have hterm :
        ‖(φ.compFormalMultilinearSeries (p.compContinuousLinearMap L) n) (fun _ ↦ 1)‖ =
          ‖p n (fun _ ↦ u)‖ := by
      change ‖φ (p n (fun _ ↦ (1 : ℂ) • u))‖ = ‖p n (fun _ ↦ u)‖
      simp [one_smul, hφ_val]
    rw [hterm] at hscalar
    have hscale : ‖p n (fun _ ↦ v)‖ = ‖v‖ ^ n * ‖p n (fun _ ↦ u)‖ := by
      have hsmul : p n (fun _ ↦ v) = (‖v‖ : ℂ) ^ n • p n (fun _ ↦ u) := by
        conv_lhs => rw [hv_eq]
        simpa using (p n).map_smul_univ (fun _ ↦ (‖v‖ : ℂ)) (fun _ ↦ u)
      rw [hsmul, norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖p n (fun _ ↦ v)‖ * (R : ℝ) ^ n
        = (‖p n (fun _ ↦ u)‖ * (R : ℝ) ^ n) * ‖v‖ ^ n := by rw [hscale]; ring
      _ ≤ M * ‖v‖ ^ n := mul_le_mul_of_nonneg_right hscalar (by positivity)

/-- **Cauchy's inequality on the closed ball of radius `R`.** If `f : E → V` has formal power
series `p` on `ball c R` and `‖f y‖ ≤ M` there, then `‖p n (fun _ ↦ v)‖ ≤ M` whenever `‖v‖ ≤ R`. -/
theorem norm_apply_le_of_norm_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {c : E}
    {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p c R) {M : ℝ} (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M)
    (n : ℕ) {v : E} (hv : ‖v‖ ≤ R) : ‖p n (fun _ ↦ v)‖ ≤ M := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hf.r_pos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hR))
  have h := (hf.norm_apply_mul_pow_le hM n v).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv n) hM0)
  exact le_of_mul_le_mul_right h (pow_pos hR n)

/-- Complete-codomain case of `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le`. -/
private theorem norm_add_sub_partialSum_le_of_completeSpace [CompleteSpace V] {f : E → V}
    {p : FormalMultilinearSeries ℂ E V} {c : E} {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p c R)
    {M : ℝ} (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M) (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f (c + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hf.r_pos
  rcases eq_or_ne z 0 with rfl | hz0
  · rcases T.eq_zero_or_pos with rfl | hT0
    · simpa [FormalMultilinearSeries.partialSum] using hM c (mem_ball_self hR)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT0.ne'
      have hzero (j : ℕ) : p (j + 1) (fun _ ↦ (0 : E)) = 0 := (p (j + 1)).map_coord_zero 0 rfl
      simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ', hf.coeff_zero, hzero,
        zero_pow (Nat.succ_ne_zero k)]
  · set u : E := (‖z‖ : ℂ)⁻¹ • z
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz0)]
    have hz_eq : (‖z‖ : ℂ) • u = z := by
      simp [u, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0))]
    set q : FormalMultilinearSeries ℂ ℂ V :=
      p.compContinuousLinearMap (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) u)
    have hq : HasFPowerSeriesOnBall (fun w : ℂ ↦ f (c + w • u)) q 0 R :=
      hasFPowerSeriesOnBall_smul hf hu.le
    have hq_apply (k : ℕ) (w : ℂ) : q k (fun _ ↦ w) = p k (fun _ ↦ w • u) := rfl
    set g : ℂ → V := fun w ↦ f (c + w • u) - q.partialSum T w
    have hg_an : AnalyticOnNhd ℂ g (ball 0 R) := fun w hw ↦
      (hq.analyticOnNhd w (by rwa [eball_coe])).sub <| Finset.analyticAt_fun_sum _ fun k _ ↦ by
        rw [show (fun ζ : ℂ ↦ q k (fun _ ↦ ζ)) = fun ζ ↦ ζ ^ k • q k (fun _ ↦ 1) from
          funext fun _ ↦ by simp]
        fun_prop
    have hg_bound (w : ℂ) (hw : w ∈ ball (0 : ℂ) R) : ‖g w‖ ≤ (1 + T) * M := by
      have hwu : ‖w • u‖ < R := by simpa [norm_smul, hu] using hw
      have hfw : ‖f (c + w • u)‖ ≤ M := hM _ (by simpa [mem_ball_iff_norm] using hwu)
      have hpart : ‖q.partialSum T w‖ ≤ T * M := (norm_sum_le _ _).trans <|
        (Finset.sum_le_sum fun k _ ↦ hf.norm_apply_le_of_norm_le hM k hwu.le).trans (by simp)
      linarith [norm_sub_le (f (c + w • u)) (q.partialSum T w)]
    have hg_ord : (T : ℕ∞) ≤ analyticOrderAt g 0 := by
      have hO : g =O[𝓝 (0 : ℂ)] fun w ↦ (w - 0) ^ T := by
        simpa only [g, zero_add, sub_zero, ← norm_pow, Asymptotics.isBigO_norm_right] using
          hq.hasFPowerSeriesAt.isBigO_sub_partialSum_pow T
      exact (hg_an 0 (mem_ball_self hR)).natCast_le_analyticOrderAt_iff_isBigO.2 hO
    have hw_mem : (‖z‖ : ℂ) ∈ ball (0 : ℂ) R := by
      simpa [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)] using hz
    have hschwarz := Complex.norm_le_mul_div_pow_of_le_analyticOrderAt hg_an.differentiableOn
      hg_bound hg_ord hw_mem
    have hg_eval : g (‖z‖ : ℂ) = f (c + z) - p.partialSum T z := by
      simp only [g, FormalMultilinearSeries.partialSum, hq_apply, hz_eq]
    simpa [hg_eval, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)] using hschwarz

/-- **Truncated Taylor remainder bound** around an arbitrary centre `c : E` (Waldschmidt,
Lemma 4.13, normed-space form): if `f : E → V` has formal power series `p` on `ball c R` and
`‖f y‖ ≤ M` there, then `‖f (c + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T` for every
`T : ℕ` and `z : E` with `‖z‖ < R`. Neither `E` nor `V` is assumed complete. -/
theorem norm_add_sub_partialSum_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {c : E}
    {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p c R) {M : ℝ} (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M)
    (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f (c + z) - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  let e : V →L[ℂ] UniformSpace.Completion V := UniformSpace.Completion.toComplL
  have he (y : E) (hy : y ∈ ball c R) : ‖(e ∘ f) y‖ ≤ M := by
    simpa [e, Function.comp_apply, UniformSpace.Completion.norm_coe] using hM y hy
  have h := norm_add_sub_partialSum_le_of_completeSpace (e.comp_hasFPowerSeriesOnBall hf) he T hz
  have hpsum : (e.compFormalMultilinearSeries p).partialSum T z = e (p.partialSum T z) := by
    simp [FormalMultilinearSeries.partialSum, map_sum]
  rw [Function.comp_apply, hpsum, ← map_sub] at h
  exact (UniformSpace.Completion.norm_coe (f (c + z) - p.partialSum T z)).symm.trans_le h

/-- **Truncated Taylor remainder bound** around `0 : E` (Waldschmidt, Lemma 4.13, normed-space
form): if `f : E → V` has formal power series `p` on `ball 0 R` and `‖f y‖ ≤ M` there, then
`‖f z - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T` for every `T : ℕ` and `z : E` with
`‖z‖ < R`. Neither `E` nor `V` is assumed complete. -/
theorem norm_sub_partialSum_le {f : E → V} {p : FormalMultilinearSeries ℂ E V} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p 0 R) {M : ℝ} (hM : ∀ y ∈ ball (0 : E) R, ‖f y‖ ≤ M)
    (T : ℕ) {z : E} (hz : ‖z‖ < R) :
    ‖f z - p.partialSum T z‖ ≤ (1 + T) * M * (‖z‖ / R) ^ T := by
  simpa using hf.norm_add_sub_partialSum_le hM T hz

end NormedSpace

end HasFPowerSeriesOnBall
