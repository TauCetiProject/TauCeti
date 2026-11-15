/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Analytic.ConvergenceRadius
import TauCeti.Analysis.Calculus.FormalMultilinearSeries

/-!
# Taylor terms and symmetric Taylor series of analytic functions

If `f` has the power series `∑ₖ pₖ` at `x`, then along the rays `t ↦ x + t • y` the Taylor
remainder of order `k` is of size `tᵏ`, and after division by `tᵏ` it converges to the term of
degree `k`:

`t⁻ᵏ • (f (x + t • y) - ∑_{j < k} pⱼ (t • y, …, t • y)) → pₖ (y, …, y)` as `t → 0`,

uniformly for `y` in a bounded set
(`HasFPowerSeriesAt.tendstoUniformlyOn_inv_pow_smul_sub_partialSum`).
The homogeneous terms of a power series are thereby recovered as limits of rescaled values of the
function, which lets properties of `f` that are stable under dilation, translation and uniform
limits pass to its Taylor terms.

Over `ℝ` or `ℂ`, when the codomain is complete, symmetrizing `p` via the iterated Fréchet
derivatives replaces `p` on the exact same convergence ball by the canonical Taylor series
`n ↦ (n!)⁻¹ • iteratedFDeriv 𝕜 n f x`, which depends only on `f` and `x`
(`HasFPowerSeriesOnBall.inv_factorial_smul_iteratedFDeriv`,
`HasFPowerSeriesAt.inv_factorial_smul_iteratedFDeriv`). Over any characteristic-zero field, if all
iterated Fréchet derivatives of an analytic function into a complete space vanish at `x`, then the
function vanishes on a neighbourhood of `x`
(`AnalyticAt.eventuallyEq_zero_of_iteratedFDeriv_eq_zero`).
-/

public section

open Filter Metric Set Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
  {x : E}

namespace HasFPowerSeriesAt

/-- **The rescaled Taylor remainder tends to the next term.** If `f` has power series `p` at `x`,
then `t⁻ᵏ • (f (x + t • y) - p.partialSum k (t • y))` tends to `pₖ (y, …, y)` as `t → 0`,
uniformly for `y` in any bounded set. -/
theorem tendstoUniformlyOn_inv_pow_smul_sub_partialSum (hp : HasFPowerSeriesAt f p x) (k : ℕ)
    {s : Set E} (hs : Bornology.IsBounded s) :
    TendstoUniformlyOn
      (fun (t : 𝕜) (y : E) ↦ (t ^ k)⁻¹ • (f (x + t • y) - p.partialSum k (t • y)))
      (fun y ↦ p k fun _ ↦ y) (𝓝[≠] 0) s := by
  obtain ⟨R, -, hsR⟩ := hs.subset_closedBall_lt 0 0
  obtain ⟨C, hC, hO⟩ := (hp.isBigO_sub_partialSum_pow (k + 1)).exists_pos
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff_ball.1 hO.bound
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Choose `t` small enough that `t • y` stays in `ball 0 δ` and the error is below `ε`.
  have hevent : ∀ᶠ t : 𝕜 in 𝓝[≠] 0, ‖t‖ * R < δ ∧ ‖t‖ * (C * R ^ (k + 1)) < ε := by
    have h₁ : Tendsto (fun t : 𝕜 ↦ (‖t‖ * R, ‖t‖ * (C * R ^ (k + 1)))) (𝓝[≠] 0) (𝓝 (0, 0)) := by
      refine (Tendsto.prodMk_nhds ?_ ?_).mono_left nhdsWithin_le_nhds <;>
        simpa using tendsto_norm_zero.mul_const _
    exact h₁.eventually (prod_mem_nhds (Iio_mem_nhds hδ) (Iio_mem_nhds hε))
  filter_upwards [hevent, self_mem_nhdsWithin] with t ⟨htδ, htε⟩ (ht : t ≠ 0)
  intro y hy
  have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 (hsR hy)
  have hty : ‖t • y‖ < δ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left hyR (norm_nonneg t)).trans_lt htδ
  have hrem := hbound (t • y) (mem_ball_zero_iff.2 hty)
  have htk : t ^ k ≠ 0 := pow_ne_zero _ ht
  -- The difference is `t⁻ᵏ` times the Taylor remainder of order `k + 1` at `t • y`.
  have hdiff : (t ^ k)⁻¹ • (f (x + t • y) - p.partialSum k (t • y)) - (p k fun _ ↦ y) =
      (t ^ k)⁻¹ • (f (x + t • y) - p.partialSum (k + 1) (t • y)) := by
    rw [p.partialSum_succ, p.apply_smul, sub_add_eq_sub_sub, smul_sub _ _ (t ^ k • _),
      inv_smul_smul₀ htk]
  rw [dist_comm, dist_eq_norm, hdiff, norm_smul, norm_inv, norm_pow]
  calc (‖t‖ ^ k)⁻¹ * ‖f (x + t • y) - p.partialSum (k + 1) (t • y)‖
      ≤ (‖t‖ ^ k)⁻¹ * (C * ‖t • y‖ ^ (k + 1)) := by
        gcongr
        simpa using hrem
    _ = ‖t‖ * (C * ‖y‖ ^ (k + 1)) := by
        rw [norm_smul, mul_pow]
        field_simp [norm_ne_zero_iff.2 ht]
        ring
    _ ≤ ‖t‖ * (C * R ^ (k + 1)) := by gcongr
    _ < ε := htε

end HasFPowerSeriesAt

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ENNReal}

/-- Over `ℝ` or `ℂ`, any power series representing `f` on `eball x r` can be replaced on the same
ball by the canonical symmetric Taylor series `n ↦ (n!)⁻¹ • iteratedFDeriv 𝕜 n f x`, because
symmetrizing over the `n!` permutations of `Fin n` does not increase the operator norm. -/
theorem HasFPowerSeriesOnBall.inv_factorial_smul_iteratedFDeriv
    (hp : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall f (fun n ↦ (n.factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x) x r where
  r_le := by
    have hnorm (n : ℕ) :
        ‖(n.factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x‖ ≤ (1 : NNReal) ^ n * ‖p n‖ := by
      have hsum : ‖iteratedFDeriv 𝕜 n f x‖ ≤ (n.factorial : ℝ) * ‖p n‖ := by
        refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
        rw [hp.iteratedFDeriv_eq_sum_of_completeSpace v]
        calc ‖∑ σ : Equiv.Perm (Fin n), p n fun i ↦ v (σ i)‖
            ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n fun i ↦ v (σ i)‖ := norm_sum_le _ _
          _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v (σ i)‖ :=
              Finset.sum_le_sum fun σ _ ↦ (p n).le_opNorm _
          _ = ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ :=
              Finset.sum_congr rfl fun σ _ ↦ by rw [Equiv.prod_comp σ (fun i ↦ ‖v i‖)]
          _ = (n.factorial : ℝ) * ‖p n‖ * ∏ i, ‖v i‖ := by
              simp [Finset.sum_const, Fintype.card_perm, mul_assoc]
      rw [NNReal.coe_one, one_pow, one_mul, norm_smul, norm_inv, RCLike.norm_natCast]
      exact (inv_pos.2 (Nat.cast_pos.2 n.factorial_pos)).le |> fun h0 ↦
        (mul_le_mul_of_nonneg_left hsum h0).trans_eq
          (inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 n.factorial_ne_zero) _)
    exact hp.r_le.trans <| ENNReal.le_of_forall_pos_nnreal_lt fun ρ _ hρ ↦
      p.le_radius_of_norm_le_mul_pow hnorm (by simpa using hρ)
  r_pos := hp.r_pos
  hasSum hy := hp.hasSum_iteratedFDeriv hy

/-- Over `ℝ` or `ℂ`, a function admitting a power series at `x` admits the canonical symmetric
Taylor series `n ↦ (n!)⁻¹ • iteratedFDeriv 𝕜 n f x` at `x`. -/
theorem HasFPowerSeriesAt.inv_factorial_smul_iteratedFDeriv (hp : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt f (fun n ↦ (n.factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x) x :=
  let ⟨r, hr⟩ := hp
  ⟨r, hr.inv_factorial_smul_iteratedFDeriv⟩

end RCLike

/-- If `f` is analytic at `x` over a characteristic-zero field into a complete space and all of its
iterated Fréchet derivatives at `x` vanish, then `f` vanishes on a neighbourhood of `x`. -/
theorem AnalyticAt.eventuallyEq_zero_of_iteratedFDeriv_eq_zero [CharZero 𝕜] [CompleteSpace F]
    (hf : AnalyticAt 𝕜 f x) (h : ∀ n : ℕ, iteratedFDeriv 𝕜 n f x = 0) : f =ᶠ[𝓝 x] 0 := by
  obtain ⟨p, r, hp⟩ := hf
  filter_upwards [Metric.eball_mem_nhds x hp.r_pos] with y hy
  have hy0 : y - x ∈ Metric.eball (0 : E) r := by
    simpa [Metric.mem_eball, edist_dist, dist_eq_norm] using hy
  have hsum := hp.hasSum_iteratedFDeriv hy0
  simp only [h, zero_apply, smul_zero, add_sub_cancel] at hsum
  exact hsum.unique hasSum_zero
