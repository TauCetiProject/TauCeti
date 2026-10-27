/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.NumberTheory.LSeries.SumCoeff
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Order.Filter.AtTopBot

/-!
# Ordered boundary limits of Dirichlet series at `s = 1`

At the boundary point `s = 1` of the half-plane `1 < re s`, a Dirichlet series with coefficients
`a : ℕ → ℂ` is studied through the ordered partial sums `∑ n ∈ Finset.Icc 1 N, a n / n`. Their
limit, when it exists, is a conditional limit of finite cutoffs: it says nothing about
unconditional summability at `1` or about the totalized value `LSeries a 1`. This file collects
the basic facts about such limits that do not depend on how the limit was obtained.

* **Abelian theorem.** If the ordered sums tend to `L` and the series converges absolutely on
  `1 < σ`, then `LSeries a σ → L` as the real number `σ` decreases to `1`. The proof writes
  `LSeries a (1 + ε)` as `ε ∫_1^∞ t ^ (-ε - 1) S(t) dt`, with `S(t)` the partial sum up to `t`,
  using Mathlib's `LSeries_eq_mul_integral`, and averages `S(t) → L` against these weights.
* **Uniqueness.** Consequently the ordered limit equals `F 1` for every function `F` that sums
  the series at real `σ > 1` and satisfies `F σ → F 1` as `σ → 1⁺`, for instance any extension
  continuous at `1`. Two continuous extensions of the series to the closed half-plane
  `σ ≤ re s` agree there.
* **Linearity.** Ordered limits are additive and homogeneous in the coefficients.

Limits over real cutoffs `∑ n ≤ x` are equivalent to those over natural cutoffs by
`TauCeti.tendsto_comp_natFloor_iff`.

The Abelian theorem is classical (see Hardy and Riesz); its proof here follows the integral
representation and the split of the range of integration used in Mathlib's
`LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div`.

## Main declarations

* `TauCeti.LSeries.tendsto_LSeries_nhdsGT_one`: the Abelian theorem at `s = 1`.
* `TauCeti.LSeries.eq_of_tendsto_sum_Icc_div`: the ordered limit is the boundary value of any
  extension that is continuous at `1` along the real axis.
* `TauCeti.LSeries.eqOn_of_LSeriesHasSum`: uniqueness of continuous extensions to a closed
  half-plane.
* `TauCeti.LSeries.tendsto_sum_Icc_div_add`, `tendsto_sum_Icc_div_smul`,
  `tendsto_sum_Icc_div_neg`, `tendsto_sum_Icc_div_sub`: linearity of ordered limits.

## References

* G. H. Hardy and M. Riesz, *The General Theory of Dirichlet's Series*, Cambridge Tracts in
  Mathematics and Mathematical Physics 18, Cambridge University Press, 1915.
-/

public section

open Filter MeasureTheory Set Complex
open scoped Topology

namespace TauCeti.LSeries

/-- **Abelian theorem for Dirichlet series at `s = 1`.** If the ordered partial sums
`∑ n ∈ Icc 1 N, a n / n` tend to `L` and the Dirichlet series of `a` converges absolutely at
every real `σ > 1`, then `LSeries a σ → L` as `σ` decreases to `1`. -/
theorem tendsto_LSeries_nhdsGT_one {a : ℕ → ℂ} {L : ℂ}
    (hlim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / n) atTop (𝓝 L))
    (hsum : ∀ σ : ℝ, 1 < σ → LSeriesSummable a σ) :
    Tendsto (fun σ : ℝ ↦ LSeries a σ) (𝓝[>] 1) (𝓝 L) := by
  set f : ℕ → ℂ := fun n ↦ a n / n
  set S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k
  -- Dividing the coefficients by `n` shifts the Dirichlet series by one.
  have hterm (s : ℂ) : LSeries.term f s = LSeries.term a (s + 1) := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_one, div_div, mul_comm]
  have hS : LocallyIntegrableOn S (Ici 1) := by
    simpa [S] using locallyIntegrableOn_mul_sum_Icc f zero_le_one (locallyIntegrableOn_const 1)
  have hshift : Tendsto (fun σ : ℝ ↦ σ - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      exact sub_pos.mpr hσ
  refine ((tendsto_smul_integral_Ioi_rpow_smul_nhdsGT_zero hS
    (tendsto_comp_natFloor_iff.mpr hlim)).comp hshift).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have hsummable : LSeriesSummable f ((σ - 1 : ℝ) : ℂ) := by
    simpa [LSeriesSummable, hterm] using hsum σ hσ
  have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    simpa using hlim.isBigO_one ℝ
  rw [Function.comp_apply, show LSeries a σ = LSeries f ((σ - 1 : ℝ) : ℂ) by
      simp [LSeries, hterm],
    LSeries_eq_mul_integral f le_rfl (by simpa using hσ) hsummable hO, real_smul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
  rw [real_smul, mul_comm, ofReal_cpow (by linarith)]
  push_cast
  simp only [S]
  ring_nf

/-- **Uniqueness of the ordered boundary limit.** If the ordered partial sums
`∑ n ∈ Icc 1 N, a n / n` tend to `L`, and `F σ` is the sum of the Dirichlet series of `a` at every
real `σ > 1` with `F σ → F 1` as `σ` decreases to `1`, then `F 1 = L`. No holomorphy of `F` and no
bound on `a` is needed; any extension continuous at `1` from the half-plane `1 < re s` qualifies. -/
theorem eq_of_tendsto_sum_Icc_div {a : ℕ → ℂ} {L : ℂ} {F : ℂ → ℂ}
    (hlim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / n) atTop (𝓝 L))
    (hF : Tendsto (fun σ : ℝ ↦ F σ) (𝓝[>] 1) (𝓝 (F 1)))
    (hseries : ∀ σ : ℝ, 1 < σ → LSeriesHasSum a σ (F σ)) :
    F 1 = L := by
  refine tendsto_nhds_unique (hF.congr' ?_)
    (tendsto_LSeries_nhdsGT_one hlim fun σ hσ ↦ (hseries σ hσ).LSeriesSummable)
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  exact (hseries σ hσ).LSeries_eq.symm

/-- **Uniqueness of boundary extensions.** Two functions continuous on the closed half-plane
`σ ≤ re s` that both sum the Dirichlet series of `a` on the open half-plane `σ < re s` agree
on the closed half-plane. -/
theorem eqOn_of_LSeriesHasSum {a : ℕ → ℂ} {σ : ℝ} {F G : ℂ → ℂ}
    (hF : ContinuousOn F {s | σ ≤ s.re}) (hG : ContinuousOn G {s | σ ≤ s.re})
    (hFa : ∀ s : ℂ, σ < s.re → LSeriesHasSum a s (F s))
    (hGa : ∀ s : ℂ, σ < s.re → LSeriesHasSum a s (G s)) :
    EqOn F G {s | σ ≤ s.re} :=
  EqOn.of_subset_closure (s := {s : ℂ | σ < s.re})
    (fun s hs ↦ (hFa s hs).LSeries_eq.symm.trans (hGa s hs).LSeries_eq) hF hG
    (fun _ hs ↦ mem_ofPred.mpr (le_of_lt hs)) (by rw [closure_setOfPred_lt_re])

section Linearity

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] {a b : ℕ → K} {L L' : K}

/-- Ordered boundary limits are additive in the coefficients. -/
theorem tendsto_sum_Icc_div_add [ContinuousAdd K]
    (ha : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / n) atTop (𝓝 L))
    (hb : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, b n / n) atTop (𝓝 L')) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (a + b) n / n) atTop (𝓝 (L + L')) := by
  simpa [add_div, Finset.sum_add_distrib] using ha.add hb

/-- Ordered boundary limits are homogeneous in the coefficients. -/
theorem tendsto_sum_Icc_div_smul [ContinuousMul K] (c : K)
    (ha : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (c • a) n / n) atTop (𝓝 (c • L)) := by
  simpa [mul_div_assoc, Finset.mul_sum] using ha.const_mul c

/-- Negating the coefficients negates the ordered boundary limit. -/
theorem tendsto_sum_Icc_div_neg [ContinuousNeg K]
    (ha : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (-a) n / n) atTop (𝓝 (-L)) := by
  simpa [neg_div] using ha.neg

/-- Ordered boundary limits are subtractive in the coefficients. -/
theorem tendsto_sum_Icc_div_sub [ContinuousSub K]
    (ha : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / n) atTop (𝓝 L))
    (hb : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, b n / n) atTop (𝓝 L')) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (a - b) n / n) atTop (𝓝 (L - L')) := by
  simpa [sub_div, Finset.sum_sub_distrib] using ha.sub hb

end Linearity

end TauCeti.LSeries
