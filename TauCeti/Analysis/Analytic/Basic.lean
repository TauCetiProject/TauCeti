/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
import TauCeti.Analysis.Analytic.ConvergenceRadius
import TauCeti.Analysis.Calculus.FormalMultilinearSeries

/-!
# The leading term of a rescaled Taylor remainder

If `f` has the power series `∑ₖ pₖ` at `x`, then along the rays `t ↦ x + t • y` the Taylor
remainder of order `k` is of size `tᵏ`, and after division by `tᵏ` it converges to the term of
degree `k`:

`t⁻ᵏ • (f (x + t • y) - ∑_{j < k} pⱼ (t • y, …, t • y)) → pₖ (y, …, y)` as `t → 0`,

uniformly for `y` in a bounded set
(`HasFPowerSeriesAt.tendstoUniformlyOn_inv_pow_smul_sub_partialSum`).
The homogeneous terms of a power series are thereby recovered as limits of rescaled values of the
function, which lets properties of `f` that are stable under dilation, translation and uniform
limits pass to its Taylor terms.
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
