/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Analytic.TaylorSeries
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Analytic.ConvergenceRadius
import TauCeti.Analysis.Analytic.ExtractZeros
import TauCeti.Analysis.Complex.Weierstrass

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

For holomorphic functions `f : 𝕜 → F` into a complete space, the iterated divided differences
`(Function.swap dslope z₀)^[n] f` supply the analytic Taylor remainder quotients:
`f z - ∑ j ∈ Finset.range n, (z - z₀) ^ j • ((j.factorial : 𝕜)⁻¹ • iteratedDeriv j f z₀) =
  (z - z₀) ^ n • (Function.swap dslope z₀)^[n] f z`,
with value `(n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀` at `z = z₀` and joint analyticity
`(x, w) ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (x, y)) w` for holomorphic families
`f : E × ℂ → ℂ` on finite-dimensional complex normed spaces `E` via Weierstrass division.

## Main results

* `HasFPowerSeriesOnBall.norm_apply_le_of_forall_mem_eball` and
  `HasFPowerSeriesOnBall.norm_apply_le`: Cauchy's inequality `‖p n (fun _ ↦ y)‖ ≤ M` for every
  homogeneous term on `Metric.eball` and `Metric.ball`.
* `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` and
  `HasFPowerSeriesOnBall.norm_sub_partialSum_le`: the Taylor remainder bound
  `(1 + T) * M * (‖z‖ / R) ^ T` about an arbitrary centre `x` and about `0`.
* `AnalyticAt.dslope_snd`, `AnalyticAt.iterate_dslope_snd`, and `AnalyticOnNhd.iterate_dslope_snd`:
  joint analyticity of iterated second-variable divided differences for families `E × ℂ → ℂ`.
* `AnalyticAt.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv` and
  `AnalyticAt.coeff_taylorSeries_eq_inv_factorial_smul_iteratedDeriv`: Taylor quotient value at
  the centre and Taylor-series coefficient in terms of `iteratedDeriv`.
* `AnalyticAt.sub_sum_inv_factorial_smul_iteratedDeriv_eq_pow_smul_iterate_dslope` and
  `AnalyticAt.iterate_dslope_eq_inv_factorial_smul_add_sub_smul_succ`: Taylor decomposition and
  successor recurrence for iterated divided-difference remainders.

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

section AnalyticRemainder

section ParametricDSlope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- If `f : E × ℂ → ℂ` is jointly analytic at `(x₀, z₀)` and at `(x₀, w₀)`, then the second-variable
divided difference `(x, w) ↦ dslope (fun y ↦ f (x, y)) z₀ w` is jointly analytic at `(x₀, w₀)`. -/
theorem AnalyticAt.dslope_snd {f : E × ℂ → ℂ} {x₀ : E} {z₀ w₀ : ℂ}
    (hf₀ : AnalyticAt ℂ f (x₀, z₀)) (hf : AnalyticAt ℂ f (x₀, w₀)) :
    AnalyticAt ℂ (fun p : E × ℂ ↦ dslope (fun y ↦ f (p.1, y)) z₀ p.2) (x₀, w₀) := by
  rcases eq_or_ne w₀ z₀ with rfl | hne
  · obtain ⟨q, r, hq, _, hdiv⟩ :=
      hf₀.exists_weierstrassDivision_monicOfCoeff (d := 1) (c := fun _ _ ↦ 0)
        (fun _ ↦ analyticAt_const) (fun _ ↦ rfl)
    have hq_nhds : ∀ᶠ p : E × ℂ in 𝓝 (x₀, w₀), AnalyticAt ℂ q p :=
      (isOpen_analyticAt ℂ q).mem_nhds hq
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hdiv.and hq_nhds)
    refine hq.congr (eventually_of_mem (prod_mem_nhds hU hV) ?_)
    rintro ⟨x, w⟩ hxw
    obtain ⟨hx, hw⟩ := hxw
    have hUV' : ∀ {y : ℂ}, y ∈ V →
        f (x, y) = Polynomial.eval (y - w₀) (TauCeti.Polynomial.monicOfCoeff fun _ ↦ 0) *
          q (x, y) + ∑ i : Fin 1, r i x * (y - w₀) ^ (i : ℕ) ∧ AnalyticAt ℂ q (x, y) :=
      fun {y} hy ↦ hUV (Set.mk_mem_prod hx hy)
    have hfz : f (x, w₀) = r 0 x := by
      have h := (hUV' (mem_of_mem_nhds hV)).1
      simpa [TauCeti.Polynomial.eval_monicOfCoeff] using h
    have hrel : ∀ y ∈ V, f (x, y) - f (x, w₀) = (y - w₀) * q (x, y) := fun y hy ↦ by
      have h := (hUV' hy).1
      simp only [TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_one, Fin.val_zero,
        pow_one, pow_zero, mul_one, add_zero] at h
      rw [h, hfz, add_sub_cancel_right]
    dsimp only
    symm
    by_cases hwy : w = w₀
    · rw [hwy]
      have hcont : ContinuousAt (fun y : ℂ ↦ q (x, y)) w₀ :=
        ((hUV' (mem_of_mem_nhds hV)).2.comp (analyticAt_const.prod analyticAt_id)).continuousAt
      have hslope : Tendsto (slope (fun y ↦ f (x, y)) w₀) (𝓝[≠] w₀) (𝓝 (q (x, w₀))) := by
        refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [inter_mem (nhdsWithin_le_nhds hV) self_mem_nhdsWithin] with y ⟨hyV, hyne⟩
        rw [slope_def_field, hrel y hyV, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hyne)]
      rw [dslope_same, (hasDerivAt_iff_tendsto_slope.mpr hslope).deriv]
    · rw [dslope_of_ne _ hwy, slope_def_field, hrel w hw,
        mul_div_cancel_left₀ _ (sub_ne_zero.mpr hwy)]
  · have hfx₀ : AnalyticAt ℂ (fun p : E × ℂ ↦ f (p.1, z₀)) (x₀, w₀) :=
      AnalyticAt.comp (g := f) (f := fun p : E × ℂ ↦ (p.1, z₀)) hf₀
        (analyticAt_fst.prod analyticAt_const)
    have hq : AnalyticAt ℂ (fun p : E × ℂ ↦ (p.2 - z₀)⁻¹ * (f p - f (p.1, z₀))) (x₀, w₀) :=
      ((analyticAt_snd.sub analyticAt_const).inv (sub_ne_zero.mpr hne)).mul (hf.sub hfx₀)
    refine hq.congr ?_
    filter_upwards [(continuousAt_snd.eventually_ne hne)] with p hp
    symm
    rw [dslope_of_ne _ hp, slope_def_field, div_eq_inv_mul]

/-- If `f : E × ℂ → ℂ` is jointly analytic at `(x₀, z₀)` and at `(x₀, w₀)`, then for every
`n : ℕ` the `n`-th iterated divided difference
`(x, w) ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (x, y)) w` is jointly analytic at `(x₀, w₀)`. -/
theorem AnalyticAt.iterate_dslope_snd {f : E × ℂ → ℂ} {x₀ : E} {z₀ w₀ : ℂ}
    (hf₀ : AnalyticAt ℂ f (x₀, z₀)) (hf : AnalyticAt ℂ f (x₀, w₀)) :
    ∀ n : ℕ, AnalyticAt ℂ
      (fun p : E × ℂ ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) (x₀, w₀)
  | 0 => by simpa only [Function.iterate_zero_apply] using hf
  | n + 1 => by
    have ih₀ : AnalyticAt ℂ
        (fun p : E × ℂ ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) (x₀, z₀) :=
      hf₀.iterate_dslope_snd hf₀ n
    have ih : AnalyticAt ℂ
        (fun p : E × ℂ ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) (x₀, w₀) :=
      hf₀.iterate_dslope_snd hf n
    simpa only [Function.iterate_succ_apply'] using ih₀.dslope_snd ih

/-- If `f : E × ℂ → ℂ` is analytic on `S` and `∀ p ∈ S, (p.1, z₀) ∈ S`, then for every
`n : ℕ` the `n`-th iterated second-variable divided difference at `z₀` is analytic on `S`. -/
theorem AnalyticOnNhd.iterate_dslope_snd {f : E × ℂ → ℂ} {S : Set (E × ℂ)} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f S) (hz₀ : ∀ p ∈ S, (p.1, z₀) ∈ S) (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun p : E × ℂ ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) S :=
  fun p hp ↦ (hf (p.1, z₀) (hz₀ p hp)).iterate_dslope_snd (hf p hp) n

end ParametricDSlope

/-- If `f : 𝕜 → F` is analytic at `z₀` into a complete space, the `n`-th iterated divided
difference at `z₀` evaluates at `z₀` to `(n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀`. -/
theorem AnalyticAt.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : 𝕜 → F} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    (Function.swap dslope z₀)^[n] f z₀ = (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀ := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨r, hr⟩ := hp
  have hfact := hr.factorial_smul 1 n
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hfact
  have hcoeff : n.factorial • p.coeff n = iteratedDeriv n f z₀ := by
    rw [FormalMultilinearSeries.coeff]
    exact hfact
  have hp_eq : p.coeff n = (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀ := by
    have hne : (n.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [← hcoeff, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hr.hasFPowerSeriesAt.iterate_dslope_apply_eq_coeff n, hp_eq]

/-- For an analytic function `f : 𝕜 → A` into a complete normed `𝕜`-algebra, the `n`-th
coefficient of `TauCeti.taylorSeries f z₀` is `(n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀`. -/
theorem AnalyticAt.coeff_taylorSeries_eq_inv_factorial_smul_iteratedDeriv
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    {f : 𝕜 → A} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    PowerSeries.coeff n (TauCeti.taylorSeries f z₀) =
      (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀ := by
  rw [TauCeti.coeff_taylorSeries, hf.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv n]

/-- **Taylor's formula with analytic divided-difference remainder**: for `f : 𝕜 → F` analytic at
`z₀` into a complete space,
`f z - ∑ j ∈ Finset.range n, (z - z₀) ^ j • ((j.factorial : 𝕜)⁻¹ • iteratedDeriv j f z₀) =
  (z - z₀) ^ n • (Function.swap dslope z₀)^[n] f z`. -/
theorem AnalyticAt.sub_sum_inv_factorial_smul_iteratedDeriv_eq_pow_smul_iterate_dslope
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : 𝕜 → F} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) (z : 𝕜) :
    f z - ∑ j ∈ Finset.range n, (z - z₀) ^ j • ((j.factorial : 𝕜)⁻¹ • iteratedDeriv j f z₀) =
      (z - z₀) ^ n • (Function.swap dslope z₀)^[n] f z := by
  have h := TauCeti.sum_add_pow_sub_smul_iterate_dslope f z₀ z n
  have hsum : ∑ j ∈ Finset.range n, (z - z₀) ^ j • (Function.swap dslope z₀)^[j] f z₀ =
      ∑ j ∈ Finset.range n, (z - z₀) ^ j • ((j.factorial : 𝕜)⁻¹ • iteratedDeriv j f z₀) :=
    Finset.sum_congr rfl fun j _ ↦ by
      rw [hf.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv j]
  rw [hsum] at h
  exact sub_eq_of_eq_add' h.symm

/-- Successor recurrence for iterated divided-difference remainders of an analytic function
`f : 𝕜 → F` at `z₀`. -/
theorem AnalyticAt.iterate_dslope_eq_inv_factorial_smul_add_sub_smul_succ
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : 𝕜 → F} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) (z : 𝕜) :
    (Function.swap dslope z₀)^[n] f z =
      (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f z₀ +
        (z - z₀) • (Function.swap dslope z₀)^[n + 1] f z := by
  have h := eq_add_of_sub_eq' (sub_smul_dslope ((Function.swap dslope z₀)^[n] f) z₀ z).symm
  rw [hf.iterate_dslope_apply_eq_inv_factorial_smul_iteratedDeriv n] at h
  simpa only [Function.iterate_succ_apply'] using h

end AnalyticRemainder
