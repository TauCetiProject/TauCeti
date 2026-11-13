/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic constructions: products and finite sums

Mathlib's `AnalyticAt.curry_right` says that a function analytic at `p` on a product has an
analytic slice `y ↦ f (p.1, y)` at `p.2`. Since the analytic locus is open, the same holds for the
slices `y ↦ f (x, y)` with `x` near `p.1` (`AnalyticAt.eventually_analyticAt_curry_right`).

Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic
(`TauCeti.analyticAt_sumElim`, `TauCeti.analyticOnNhd_sumElim`).

Finite sums of functions admitting power series on a common ball admit the summed power series on
that ball (`Finset.hasFPowerSeriesOnBall_sum`, `Finset.hasFPowerSeriesWithinOnBall_sum`), and
precomposing by a linear isometry preserves the exact convergence radius `r` without dividing by an
operator norm (`HasFPowerSeriesOnBall.compLinearIsometry`,
`HasFPowerSeriesWithinOnBall.compLinearIsometry`).
-/

public section

open Filter Topology

section Products

variable {𝕜 E E' F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The slices `y ↦ f (x, y)` of a function analytic at `p` are analytic at `p.2` for every `x`
near `p.1`. -/
theorem AnalyticAt.eventually_analyticAt_curry_right {f : E × E' → F} {p : E × E'}
    (hf : AnalyticAt 𝕜 f p) : ∀ᶠ x in 𝓝 p.1, AnalyticAt 𝕜 (fun y ↦ f (x, y)) p.2 :=
  ((continuous_id.prodMk continuous_const).tendsto p.1).eventually hf.eventually_analyticAt
    |>.mono fun _ hx ↦ hx.curry_right

namespace TauCeti

/-- Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic. -/
theorem analyticAt_sumElim {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : (ι → E) × (ι' → E)} :
    AnalyticAt 𝕜 (fun p : (ι → E) × (ι' → E) ↦ Sum.elim p.1 p.2) p := by
  refine analyticAt_pi_iff.2 fun i ↦ ?_
  cases i with
  | inl i => exact (analyticAt_pi_iff.1 analyticAt_fst) i
  | inr i => exact (analyticAt_pi_iff.1 analyticAt_snd) i

/-- Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic. -/
theorem analyticOnNhd_sumElim {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {s : Set ((ι → E) × (ι' → E))} :
    AnalyticOnNhd 𝕜 (fun p : (ι → E) × (ι' → E) ↦ Sum.elim p.1 p.2) s :=
  fun _ _ ↦ analyticAt_sumElim

end TauCeti

end Products

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
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact I.hasFPowerSeriesWithinOnBall_sum hr h

end FinsetSum

section LinearIsometry

open scoped ENNReal NNReal

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Precomposing a power series within `s` by a linear isometry preserves the convergence radius
`r` without dividing by an operator norm. -/
theorem HasFPowerSeriesWithinOnBall.compLinearIsometry {v : E →ₗᵢ[𝕜] F} {f : F → G}
    {pf : FormalMultilinearSeries 𝕜 F G} {s : Set F} {x : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall f pf s (v x) r) :
    HasFPowerSeriesWithinOnBall (f ∘ v)
      (pf.compContinuousLinearMap v.toContinuousLinearMap) (v ⁻¹' s) x r := by
  have hu_le : ‖v.toContinuousLinearMap‖ₑ ≤ 1 := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_le_one_iff, ← NNReal.coe_le_coe]
    exact v.norm_toContinuousLinearMap_le
  have hr_le : r ≤ r / ‖v.toContinuousLinearMap‖ₑ :=
    (ENNReal.le_div_iff_mul_le (Or.inr hf.r_pos.ne') (Or.inl eNorm_ne_top)).2
      (mul_le_of_le_one_right' hu_le)
  exact (hf.compContinuousLinearMap (u := v.toContinuousLinearMap)).of_le hf.r_pos hr_le

/-- Precomposing a power series on a ball by a linear isometry preserves the convergence radius
`r` without dividing by an operator norm. -/
theorem HasFPowerSeriesOnBall.compLinearIsometry {v : E →ₗᵢ[𝕜] F} {f : F → G}
    {pf : FormalMultilinearSeries 𝕜 F G} {x : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f pf (v x) r) :
    HasFPowerSeriesOnBall (f ∘ v) (pf.compContinuousLinearMap v.toContinuousLinearMap) x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.compLinearIsometry

end LinearIsometry
