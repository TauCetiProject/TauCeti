/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic constructions: slices and geometric-power series

Mathlib's `AnalyticAt.curry_right` says that a function analytic at `p` on a product has an
analytic slice `y ↦ f (p.1, y)` at `p.2`. Since the analytic locus is open, the same holds for the
slices `y ↦ f (x, y)` with `x` near `p.1` (`AnalyticAt.eventually_analyticAt_curry_right`).

In any normed `𝕜`-algebra `A` with summable geometric series (not necessarily commutative), the
higher geometric series `∑ₙ C(n + k, k) xⁿ` has convergence radius at least `1` and represents
`(1 - x)⁻¹ʳ ^ (k + 1)` on the open unit ball (`TauCeti.hasFPowerSeriesOnBall_inverse_one_sub_pow`),
extending Mathlib's `hasFPowerSeriesOnBall_inverse_one_sub` (`k = 0`).
-/

public section

open Filter Topology

section Slices

variable {𝕜 E E' F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The slices `y ↦ f (x, y)` of a function analytic at `p` are analytic at `p.2` for every `x`
near `p.1`. -/
theorem AnalyticAt.eventually_analyticAt_curry_right {f : E × E' → F} {p : E × E'}
    (hf : AnalyticAt 𝕜 f p) : ∀ᶠ x in 𝓝 p.1, AnalyticAt 𝕜 (fun y ↦ f (x, y)) p.2 :=
  ((continuous_id.prodMk continuous_const).tendsto p.1).eventually hf.eventually_analyticAt
    |>.mono fun _ hx ↦ hx.curry_right

end Slices

section FinsetSum

open scoped ENNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Finite sums of functions admitting power series on a common ball within `s` admit the summed
power series on the same ball. -/
@[to_fun Finset.hasFPowerSeriesWithinOnBall_fun_sum]
theorem Finset.hasFPowerSeriesWithinOnBall_sum {ι : Type*} {f : ι → E → F}
    {p : ι → FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}
    (I : Finset ι) (hr : 0 < r)
    (h : ∀ i ∈ I, HasFPowerSeriesWithinOnBall (f i) (p i) s x r) :
    HasFPowerSeriesWithinOnBall (∑ i ∈ I, f i) (∑ i ∈ I, p i) s x r := by
  classical
  induction I using Finset.induction with
  | empty => exact ⟨by simp, hr, fun _ _ ↦ hasSum_zero⟩
  | insert a I haI ih =>
    rw [Finset.sum_insert haI, Finset.sum_insert haI]
    exact (h a (Finset.mem_insert_self a I)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Finite sums of functions admitting power series on a common ball admit the summed power series
on the same ball. -/
@[to_fun Finset.hasFPowerSeriesOnBall_fun_sum]
theorem Finset.hasFPowerSeriesOnBall_sum {ι : Type*} {f : ι → E → F}
    {p : ι → FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0∞}
    (I : Finset ι) (hr : 0 < r)
    (h : ∀ i ∈ I, HasFPowerSeriesOnBall (f i) (p i) x r) :
    HasFPowerSeriesOnBall (∑ i ∈ I, f i) (∑ i ∈ I, p i) x r := by
  classical
  induction I using Finset.induction with
  | empty => exact ⟨by simp, hr, fun _ ↦ hasSum_zero⟩
  | insert a I haI ih =>
    rw [Finset.sum_insert haI, Finset.sum_insert haI]
    exact (h a (Finset.mem_insert_self a I)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end FinsetSum

namespace TauCeti

open scoped NNReal ENNReal Ring

/-- The scalar multilinear series `∑ₙ C(n + k, k) xⁿ` in any normed `𝕜`-algebra `A` has radius of
convergence at least `1`. -/
theorem one_le_ofScalars_choose_radius (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] (k : ℕ) :
    1 ≤ (FormalMultilinearSeries.ofScalars A fun n : ℕ ↦ ((n + k).choose k : 𝕜)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [ENNReal.coe_lt_one_iff] at hr
  apply FormalMultilinearSeries.le_radius_of_summable
  rw [← summable_nat_add_iff 1]
  have hmaj : Summable fun n : ℕ ↦ (((n + 1 + k).choose k : ℕ) : ℝ) * (r : ℝ) ^ (n + 1) :=
    (summable_nat_add_iff (f := fun m : ℕ ↦ (((m + k).choose k : ℕ) : ℝ) * (r : ℝ) ^ m) 1).2
      (summable_choose_mul_geometric_of_norm_lt_one k (by simpa using hr))
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hmaj
  gcongr
  refine (FormalMultilinearSeries.ofScalars_norm_le A _ (n + 1) (Nat.succ_pos n)).trans ?_
  simpa using Nat.norm_cast_le (α := 𝕜) ((n + 1 + k).choose k)

/-- In a normed `𝕜`-algebra `A` with summable geometric series, `(1 - x)⁻¹ʳ ^ (k + 1)` is
represented on the open unit ball by the scalar series `∑ₙ C(n + k, k) xⁿ`. -/
theorem hasFPowerSeriesOnBall_inverse_one_sub_pow (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] (k : ℕ) :
    HasFPowerSeriesOnBall (fun x : A ↦ (1 - x)⁻¹ʳ ^ (k + 1))
      (FormalMultilinearSeries.ofScalars A fun n : ℕ ↦ ((n + k).choose k : 𝕜)) 0 1 where
  r_le := one_le_ofScalars_choose_radius 𝕜 A k
  r_pos := zero_lt_one
  hasSum {y} hy := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] at hy
    rw [zero_add]
    convert hasSum_choose_mul_geometric_of_norm_lt_one' k hy using 1
    ext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- In a normed `𝕜`-algebra `A` with summable geometric series, `x ↦ (1 - x)⁻¹ʳ ^ (k + 1)` is
analytic at `0`. -/
theorem analyticAt_inverse_one_sub_pow (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] (k : ℕ) :
    AnalyticAt 𝕜 (fun x : A ↦ (1 - x)⁻¹ʳ ^ (k + 1)) 0 :=
  (hasFPowerSeriesOnBall_inverse_one_sub_pow 𝕜 A k).analyticAt

end TauCeti
