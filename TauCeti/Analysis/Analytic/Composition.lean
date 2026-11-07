/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Quantitative radius of convergence for composed multilinear series

Mathlib's `HasFPowerSeriesWithinAt.comp` and `FormalMultilinearSeries.comp_summable_nnreal`
establish that the composition of two convergent multilinear series converges on *some* positive
radius, losing a universal factor from counting compositions of `n`.

By majorizing the sum over compositions directly through `compChangeOfVariables_sum`, no
combinatoric loss occurs: whenever `r` lies below the inner radius and the positive-degree majorant
`∑' k, ‖p (k + 1)‖₊ * r ^ (k + 1)` lies strictly below the outer radius `rg`, the composed series
`q.comp p` has radius at least `r` and represents `g ∘ f` on the entire ball of radius `r`. For
instance, composing `(1 - u)⁻²` on the unit ball with a quadratic perturbation `L₁ h + L₂ (h, h)`
bounded by `2 ‖h‖ / δ + (‖h‖ / δ)²` preserves the exact ball `‖h‖ < (√2 - 1) δ` on which
`2 (r / δ) + (r / δ)² < 1`.
-/

public section

open Filter Topology
open scoped NNReal ENNReal

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

/-- If the positive-degree majorant `S = ∑' k, ‖p (k + 1)‖₊ * r ^ (k + 1)` of `p` at radius `r`
is summable and strictly smaller than `q.radius`, then the composition blocks
`‖q.compAlongComposition p c‖₊ * r ^ n` are summable over all compositions `(n, c)`. -/
theorem comp_summable_nnreal_of_tsum_lt (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (hp : Summable fun k : ℕ ↦ ‖p (k + 1)‖₊ * r ^ (k + 1))
    (hq : ((∑' k : ℕ, ‖p (k + 1)‖₊ * r ^ (k + 1) : ℝ≥0) : ℝ≥0∞) < q.radius) :
    Summable fun i : Σ n, Composition n ↦ ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 := by
  let a (m : ℕ) : ℝ≥0 := ‖q m‖₊
  let w (k : ℕ) : ℝ≥0 := ‖p k‖₊ * r ^ k
  set S : ℝ≥0 := ∑' k : ℕ, w (k + 1)
  have hqS : Summable fun m : ℕ ↦ a m * S ^ m := q.summable_nnnorm_mul_pow hq
  refine NNReal.summable_coe.1 <| summable_of_sum_le (fun _ ↦ by positivity)
    (c := ((∑' m : ℕ, a m * S ^ m : ℝ≥0) : ℝ)) fun s ↦ ?_
  obtain ⟨K, hK⟩ := (compPartialSumTarget_tendsto_atTop.eventually (eventually_ge_atTop s)).exists
  rw [← NNReal.coe_sum]
  exact NNReal.coe_le_coe.2 <| calc
    ∑ i ∈ s, ‖q.compAlongComposition p i.2‖₊ * r ^ i.1
      ≤ ∑ i ∈ compPartialSumTarget 0 K K, ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 :=
        Finset.sum_le_sum_of_subset hK
    _ ≤ ∑ i ∈ compPartialSumTarget 0 K K, a i.2.length * ∏ j, w (i.2.blocksFun j) := by
        refine Finset.sum_le_sum fun ⟨n, c⟩ _ ↦ ?_
        calc ‖q.compAlongComposition p c‖₊ * r ^ n
          _ ≤ (a c.length * ∏ j, ‖p (c.blocksFun j)‖₊) * r ^ n :=
              mul_le_mul' (q.compAlongComposition_nnnorm p c) le_rfl
          _ = a c.length * ∏ j, w (c.blocksFun j) := by
              simp only [w, mul_assoc, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
                c.sum_blocksFun]
    _ = ∑ m ∈ Finset.Ico 0 K,
          ∑ b ∈ Fintype.piFinset (fun _ : Fin m ↦ Finset.Ico 1 K), a m * ∏ j, w (b j) := by
        symm
        rw [Finset.sum_sigma']
        refine compChangeOfVariables_sum 0 K K _ _ ?_
        rintro ⟨m, b⟩ he
        have hlen := compChangeOfVariables_length 0 K K he
        congr 1
        · exact congrArg a hlen.symm
        · rw [← (finCongr hlen.symm).prod_comp]
          refine Finset.prod_congr rfl fun j _ ↦ congrArg w ?_
          exact (compChangeOfVariables_blocksFun 0 K K he j).symm
    _ = ∑ m ∈ Finset.Ico 0 K, a m * (∑ k ∈ Finset.Ico 1 K, w k) ^ m := by
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        rw [← Finset.mul_sum, ← Finset.sum_pow']
    _ ≤ ∑ m ∈ Finset.Ico 0 K, a m * S ^ m := by
        gcongr with m
        rw [Finset.sum_Ico_eq_sum_range]
        simp_rw [add_comm 1]
        exact hp.sum_le_tsum (Finset.range (K - 1)) fun _ _ ↦ zero_le
    _ ≤ ∑' m : ℕ, a m * S ^ m :=
        hqS.sum_le_tsum (Finset.Ico 0 K) fun _ _ ↦ zero_le

/-- Quantitative Cauchy majorant bound on the convergence radius of `q.comp p`. -/
theorem le_comp_radius_of_tsum_lt (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (hp : Summable fun k : ℕ ↦ ‖p (k + 1)‖₊ * r ^ (k + 1))
    (hq : ((∑' k : ℕ, ‖p (k + 1)‖₊ * r ^ (k + 1) : ℝ≥0) : ℝ≥0∞) < q.radius) :
    (r : ℝ≥0∞) ≤ (q.comp p).radius :=
  q.le_comp_radius_of_summable p r (q.comp_summable_nnreal_of_tsum_lt p hp hq)

end FormalMultilinearSeries

open FormalMultilinearSeries

private theorem HasFPowerSeriesWithinOnBall.mem_eball_of_tsum_lt
    {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x y : E} {rf rg : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall f p s x rf)
    (h'y : x + y ∈ insert x s) (hy : y ∈ Metric.eball 0 rf)
    (hp : Summable fun k : ℕ ↦ ‖p (k + 1)‖₊ * ‖y‖₊ ^ (k + 1))
    (hbound : ((∑' k : ℕ, ‖p (k + 1)‖₊ * ‖y‖₊ ^ (k + 1) : ℝ≥0) : ℝ≥0∞) < rg) :
    f (x + y) ∈ Metric.eball (f x) rg := by
  have htail : HasSum (fun k : ℕ ↦ p (k + 1) fun _ ↦ y) (f (x + y) - f x) := by
    have h1 := (hasSum_nat_add_iff' 1).2 (hf.hasSum h'y hy)
    simpa [Finset.sum_range_one, hf.coeff_zero fun _ ↦ y] using h1
  have hnorm : ‖f (x + y) - f x‖₊ ≤ ∑' k : ℕ, ‖p (k + 1)‖₊ * ‖y‖₊ ^ (k + 1) := by
    refine le_of_tendsto' (continuous_nnnorm.tendsto _ |>.comp htail.tendsto_sum_nat) fun N ↦ ?_
    calc ‖∑ k ∈ Finset.range N, p (k + 1) fun _ ↦ y‖₊
      _ ≤ ∑ k ∈ Finset.range N, ‖p (k + 1) fun _ ↦ y‖₊ := nnnorm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, ‖p (k + 1)‖₊ * ‖y‖₊ ^ (k + 1) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          simpa [Finset.prod_const, Finset.card_fin] using (p (k + 1)).le_opNNNorm fun _ ↦ y
      _ ≤ ∑' k : ℕ, ‖p (k + 1)‖₊ * ‖y‖₊ ^ (k + 1) :=
          hp.sum_le_tsum (Finset.range N) fun _ _ ↦ zero_le
  rw [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm]
  exact (ENNReal.coe_le_coe.2 hnorm).trans_lt hbound

/-- Quantitative ball version of `HasFPowerSeriesWithinAt.comp`: if `g` has power series `q`
within `t` on a ball of radius `rg` around `f x`, `f` has power series `p` within `s` on a ball of
radius `rf` around `x` mapping `s` into `t`, and for every `r' < r` (`0 < r ≤ rf`) the
positive-degree majorant `∑' k, ‖p (k + 1)‖₊ * r' ^ (k + 1)` is strictly less than `rg`, then
`g ∘ f` has the composed power series `q.comp p` within `s` on the whole ball of radius `r`. -/
theorem HasFPowerSeriesWithinOnBall.comp {g : F → G} {f : E → F}
    {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F}
    {x : E} {t : Set F} {s : Set E} {rg rf r : ℝ≥0∞}
    (hg : HasFPowerSeriesWithinOnBall g q t (f x) rg)
    (hf : HasFPowerSeriesWithinOnBall f p s x rf)
    (hs : Set.MapsTo f s t) (hr : 0 < r) (hrf : r ≤ rf)
    (hbound : ∀ r' : ℝ≥0, (r' : ℝ≥0∞) < r →
      ((∑' k : ℕ, ‖p (k + 1)‖₊ * r' ^ (k + 1) : ℝ≥0) : ℝ≥0∞) < rg) :
    HasFPowerSeriesWithinOnBall (g ∘ f) (q.comp p) s x r where
  r_le := ENNReal.le_of_forall_nnreal_lt fun r' hr' ↦
    q.le_comp_radius_of_tsum_lt p
      ((NNReal.summable_nat_add_iff 1).2
        (p.summable_nnnorm_mul_pow (hr'.trans_le (hrf.trans hf.r_le))))
      ((hbound r' hr').trans_le hg.r_le)
  r_pos := hr
  hasSum {y} h'y hy := by
    have hy_lt : (‖y‖₊ : ℝ≥0∞) < r := by simpa [edist_zero_right, enorm_eq_nnnorm] using hy
    have y_mem : y ∈ Metric.eball 0 rf := Metric.eball_subset_eball hrf hy
    have hp_sum : Summable fun k : ℕ ↦ ‖p (k + 1)‖₊ * ‖y‖₊ ^ (k + 1) :=
      (NNReal.summable_nat_add_iff 1).2
        (p.summable_nnnorm_mul_pow (hy_lt.trans_le (hrf.trans hf.r_le)))
    have fy_eball : f (x + y) ∈ Metric.eball (f x) rg :=
      hf.mem_eball_of_tsum_lt h'y y_mem hp_sum (hbound ‖y‖₊ hy_lt)
    have hr_comp :=
      q.comp_summable_nnreal_of_tsum_lt p hp_sum ((hbound ‖y‖₊ hy_lt).trans_le hg.r_le)
    have hA : Tendsto (fun n ↦ (n, ∑ a ∈ Finset.Ico 1 n, p a fun _ ↦ y))
        atTop (atTop ×ˢ 𝓝 (f (x + y) - f x)) := by
      refine tendsto_id.prodMk <| Tendsto.congr' ?_
        ((hf.hasSum h'y y_mem).tendsto_sum_nat.sub tendsto_const_nhds)
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [sub_eq_iff_eq_add', Finset.range_eq_Ico, ← hf.coeff_zero fun _ ↦ y,
        Finset.sum_eq_sum_Ico_succ_bot hn]
    have hB : Tendsto (fun n ↦ q.partialSum n (∑ a ∈ Finset.Ico 1 n, p a fun _ ↦ y))
        atTop (𝓝 (g (f (x + y)))) := by
      have hq_prod := hg.tendsto_partialSum_prod (y := f (x + y) - f x)
        (by simpa [edist_eq_enorm_sub] using fy_eball) (by simpa using hs.insert x h'y)
      rw [add_sub_cancel] at hq_prod
      exact hq_prod.comp hA
    have hC : Tendsto (fun n ↦ ∑ i ∈ compPartialSumTarget 0 n n,
        q.compAlongComposition p i.2 fun _ ↦ y) atTop (𝓝 (g (f (x + y)))) := by
      simpa [comp_partialSum] using hB
    have hD : HasSum (fun i : Σ n, Composition n ↦ q.compAlongComposition p i.2 fun _ ↦ y)
        (g (f (x + y))) := by
      refine tendsto_nhds_of_cauchySeq_of_subseq ?_ compPartialSumTarget_tendsto_atTop hC
      refine cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr_comp) ?_
      rintro ⟨n, c⟩
      simpa [Finset.prod_const, Finset.card_fin] using
        (q.compAlongComposition p c).le_opNorm fun _ ↦ y
    refine hD.sigma fun n ↦ ?_
    simp only [compAlongComposition_apply, FormalMultilinearSeries.comp, sum_apply]
    exact hasSum_fintype _

/-- Quantitative ball version of `HasFPowerSeriesAt.comp`: if `g` has power series `q` on a ball
of radius `rg` around `f x`, `f` has power series `p` on a ball of radius `rf` around `x`, and for
every `r' < r` (`0 < r ≤ rf`) the positive-degree majorant `∑' k, ‖p (k + 1)‖₊ * r' ^ (k + 1)` is
strictly less than `rg`, then `g ∘ f` has the composed power series `q.comp p` on the ball of
radius `r` around `x`. -/
theorem HasFPowerSeriesOnBall.comp {g : F → G} {f : E → F}
    {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F}
    {x : E} {rg rf r : ℝ≥0∞}
    (hg : HasFPowerSeriesOnBall g q (f x) rg)
    (hf : HasFPowerSeriesOnBall f p x rf)
    (hr : 0 < r) (hrf : r ≤ rf)
    (hbound : ∀ r' : ℝ≥0, (r' : ℝ≥0∞) < r →
      ((∑' k : ℕ, ‖p (k + 1)‖₊ * r' ^ (k + 1) : ℝ≥0) : ℝ≥0∞) < rg) :
    HasFPowerSeriesOnBall (g ∘ f) (q.comp p) x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hg hf ⊢
  exact hg.comp hf (Set.mapsTo_univ _ _) hr hrf hbound
