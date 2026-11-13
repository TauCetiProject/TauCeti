/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Analysis.Normed.Module.InfiniteSum

/-!
# Analytic constructions: products, finite sums, and one-variable Cauchy products

Mathlib's `AnalyticAt.curry_right` says that a function analytic at `p` on a product has an
analytic slice `y ↦ f (p.1, y)` at `p.2`. Since the analytic locus is open, the same holds for the
slices `y ↦ f (x, y)` with `x` near `p.1` (`AnalyticAt.eventually_analyticAt_curry_right`).

Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic
(`TauCeti.analyticAt_sumElim`, `TauCeti.analyticOnNhd_sumElim`).

Finite sums of functions admitting power series on a common ball admit the summed power series on
that ball (`Finset.hasFPowerSeriesOnBall_sum`, `Finset.hasFPowerSeriesWithinOnBall_sum`).

In one variable, pointwise evaluation `z ↦ A z (v z)` of a continuous-linear-map-valued series on a
vector-valued series and multiplication `f * g` in a normed algebra admit the explicit
Cauchy-product formal power series on the same ball (`HasFPowerSeriesOnBall.clm_apply`,
`HasFPowerSeriesOnBall.mul`).
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

section CauchyProduct

open scoped BigOperators ENNReal NNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise evaluation `z ↦ A z (v z)` of a continuous-linear-map-valued function `A` and a
vector-valued function `v` admitting one-variable power series `p` and `q` on `Metric.eball z₀ r`
admits the Cauchy-product power series on `Metric.eball z₀ r`. -/
theorem HasFPowerSeriesOnBall.clm_apply
    {A : 𝕜 → E →L[𝕜] F} {v : 𝕜 → E}
    {p : FormalMultilinearSeries 𝕜 𝕜 (E →L[𝕜] F)} {q : FormalMultilinearSeries 𝕜 𝕜 E}
    {z₀ : 𝕜} {r : ℝ≥0∞}
    (hA : HasFPowerSeriesOnBall A p z₀ r) (hv : HasFPowerSeriesOnBall v q z₀ r) :
    HasFPowerSeriesOnBall (fun z ↦ A z (v z))
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ∑ k ∈ Finset.range (n + 1), p.coeff (n - k) (q.coeff k))
      z₀ r := by
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_, hA.r_pos, fun {y} hy ↦ ?_⟩
  · have hsumA : Summable fun n ↦ ‖p.coeff n‖ * (R : ℝ) ^ n := by
      simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef] using
        p.summable_norm_mul_pow (hRr.trans_le hA.r_le)
    have hsumv : Summable fun n ↦ ‖q.coeff n‖ * (R : ℝ) ^ n := by
      simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef] using
        q.summable_norm_mul_pow (hRr.trans_le hv.r_le)
    have hconv := summable_sum_mul_range_of_summable_mul
      (f := fun k ↦ ‖q.coeff k‖ * (R : ℝ) ^ k) (g := fun m ↦ ‖p.coeff m‖ * (R : ℝ) ^ m)
      (hsumv.mul_of_nonneg hsumA (fun _ ↦ by positivity) (fun _ ↦ by positivity))
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hconv
    rw [TauCeti.norm_mkPiRingSeries]
    calc
      ‖∑ k ∈ Finset.range (n + 1), p.coeff (n - k) (q.coeff k)‖ * (R : ℝ) ^ n
          ≤ ∑ k ∈ Finset.range (n + 1), ‖p.coeff (n - k) (q.coeff k)‖ * (R : ℝ) ^ n := by
            rw [← Finset.sum_mul]
            gcongr
            exact norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            (‖q.coeff k‖ * (R : ℝ) ^ k) * (‖p.coeff (n - k)‖ * (R : ℝ) ^ (n - k)) := by
            refine Finset.sum_le_sum fun k hk ↦ ?_
            have hkn : k + (n - k) = n :=
              Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
            calc
              ‖p.coeff (n - k) (q.coeff k)‖ * (R : ℝ) ^ n
                  ≤ (‖p.coeff (n - k)‖ * ‖q.coeff k‖) * (R : ℝ) ^ (k + (n - k)) := by
                    rw [hkn]
                    gcongr
                    exact (p.coeff (n - k)).le_opNorm (q.coeff k)
              _ = (‖q.coeff k‖ * (R : ℝ) ^ k) * (‖p.coeff (n - k)‖ * (R : ℝ) ^ (n - k)) := by
                    rw [pow_add]
                    ring
  · have hyA := Metric.eball_subset_eball hA.r_le hy
    have hyv := Metric.eball_subset_eball hv.r_le hy
    have hprod := (hA.hasSum hy).clm_apply_range (hv.hasSum hy)
      (p.summable_norm_apply hyA) (q.summable_norm_apply hyv)
    refine hprod.congr_fun fun n ↦ ?_
    rw [TauCeti.mkPiRingSeries_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k + (n - k) = n := Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_apply,
      map_smul, smul_smul]
    rw [← pow_add, hkn]

/-- The product of two functions from `𝕜` into a normed `𝕜`-algebra admitting formal power series
`p` and `q` on `Metric.eball z₀ r` admits the Cauchy-product power series on `Metric.eball z₀ r`. -/
@[to_fun]
theorem HasFPowerSeriesOnBall.mul
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {f g : 𝕜 → A} {p q : FormalMultilinearSeries 𝕜 𝕜 A} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (hg : HasFPowerSeriesOnBall g q z₀ r) :
    HasFPowerSeriesOnBall (f * g)
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ∑ k ∈ Finset.range (n + 1), p.coeff (n - k) * q.coeff k)
      z₀ r := by
  simpa [Pi.mul_def] using
    ((ContinuousLinearMap.mul 𝕜 A).comp_hasFPowerSeriesOnBall hf).clm_apply hg

end CauchyProduct
