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
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Analytic constructions: products, finite sums, and one-variable Cauchy products

Mathlib's `AnalyticAt.curry_right` says that a function analytic at `p` on a product has an
analytic slice `y ↦ f (p.1, y)` at `p.2`. Since the analytic locus is open, the same holds for the
slices `y ↦ f (x, y)` with `x` near `p.1` (`AnalyticAt.eventually_analyticAt_curry_right`).

Concatenating two finite families of vectors, `p ↦ Sum.elim p.1 p.2`, is analytic
(`TauCeti.analyticAt_sumElim`, `TauCeti.analyticOnNhd_sumElim`), as is the slice
`ζ ↦ Sum.elim x (fun _ ↦ ζ)` fixing the first block (`TauCeti.analyticAt_sumElim_const`).

Finite sums of functions admitting power series on a common ball admit the summed power series on
that ball (`Finset.hasFPowerSeriesOnBall_sum`, `Finset.hasFPowerSeriesWithinOnBall_sum`), and
precomposing by a linear isometry preserves the exact convergence radius `r` without dividing by an
operator norm (`HasFPowerSeriesOnBall.compLinearIsometry`,
`HasFPowerSeriesWithinOnBall.compLinearIsometry`).

In one variable, pointwise evaluation `z ↦ A z (v z)` of a continuous-linear-map-valued series on a
vector-valued series, scalar multiplication `f • g` over a normed algebra, and multiplication
`f * g` in a normed algebra admit the explicit Cauchy-product formal power series on the same ball
(`HasFPowerSeriesWithinOnBall.clm_apply`, `HasFPowerSeriesOnBall.clm_apply`,
`HasFPowerSeriesWithinOnBall.smul`, `HasFPowerSeriesOnBall.smul`,
`HasFPowerSeriesWithinOnBall.mul`, `HasFPowerSeriesOnBall.mul`).

For a fixed pole `w`, the reciprocal kernel `z ↦ (w - z)⁻¹` is analytic near `s` if and only if
`w ∉ s` (`TauCeti.analyticOnNhd_sub_inv_iff`).
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

/-- Fixing the first block `x : ι → E` and varying a constant second block gives an analytic
slice `ζ ↦ Sum.elim x (fun _ : ι' ↦ ζ)` into `ι ⊕ ι' → E`. -/
theorem analyticAt_sumElim_const {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (x : ι → E) (w : E) :
    AnalyticAt 𝕜 (fun ζ : E ↦ Sum.elim x (fun _ : ι' ↦ ζ)) w :=
  analyticAt_pi_iff.2 fun j ↦ by
    cases j with
    | inl _ => exact analyticAt_const
    | inr _ => exact analyticAt_id

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
  rw [← LinearIsometry.coe_toContinuousLinearMap] at hf ⊢
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

section CauchyProduct

open scoped BigOperators ENNReal NNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise evaluation `z ↦ A z (v z)` of a continuous-linear-map-valued function `A` and a
vector-valued function `v` admitting one-variable power series `p` and `q` on `Metric.eball z₀ r`
within `s` admits the Cauchy-product power series on `Metric.eball z₀ r` within `s`. -/
theorem HasFPowerSeriesWithinOnBall.clm_apply
    {A : 𝕜 → E →L[𝕜] F} {v : 𝕜 → E}
    {p : FormalMultilinearSeries 𝕜 𝕜 (E →L[𝕜] F)} {q : FormalMultilinearSeries 𝕜 𝕜 E}
    {s : Set 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hA : HasFPowerSeriesWithinOnBall A p s z₀ r) (hv : HasFPowerSeriesWithinOnBall v q s z₀ r) :
    HasFPowerSeriesWithinOnBall (fun z ↦ A z (v z))
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ∑ k ∈ Finset.range (n + 1), p.coeff (n - k) (q.coeff k))
      s z₀ r := by
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_, hA.r_pos, fun {y} h'y hy ↦ ?_⟩
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
    exact (TauCeti.norm_sum_range_clm_apply_mul_pow_le p.coeff q.coeff R.property n).trans_eq
      (Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _)
  · have hyA := Metric.eball_subset_eball hA.r_le hy
    have hyv := Metric.eball_subset_eball hv.r_le hy
    have hprod := (hA.hasSum h'y hy).sum_clm_apply_range_of_summable_norm (hv.hasSum h'y hy)
      (p.summable_norm_apply hyA) (q.summable_norm_apply hyv)
    refine hprod.congr_fun fun n ↦ ?_
    rw [TauCeti.mkPiRingSeries_apply, Finset.smul_sum,
      ← Finset.sum_range_reflect (fun j ↦ (p j fun _ ↦ y) (q (n - j) fun _ ↦ y))]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkle,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_apply, map_smul, smul_smul]
    rw [← pow_add, Nat.add_sub_of_le hkle]

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
  rw [← hasFPowerSeriesWithinOnBall_univ] at hA hv ⊢
  exact hA.clm_apply hv

/-- Pointwise scalar multiplication `f • g` of a normed-`𝕜`-algebra-valued function `f` and a
module-valued function `g` admitting formal power series `p` and `q` on `Metric.eball z₀ r` within
`s` admits the Cauchy-product power series on `Metric.eball z₀ r` within `s`. -/
@[to_fun]
theorem HasFPowerSeriesWithinOnBall.smul
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E]
    {f : 𝕜 → A} {g : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 A}
    {q : FormalMultilinearSeries 𝕜 𝕜 E} {s : Set 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall f p s z₀ r)
    (hg : HasFPowerSeriesWithinOnBall g q s z₀ r) :
    HasFPowerSeriesWithinOnBall (f • g)
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ∑ k ∈ Finset.range (n + 1), p.coeff (n - k) • q.coeff k)
      s z₀ r := by
  simpa [Pi.smul_def'] using
    ((ContinuousLinearMap.lsmul 𝕜 A).comp_hasFPowerSeriesWithinOnBall hf).clm_apply hg

/-- Pointwise scalar multiplication `f • g` of a normed-`𝕜`-algebra-valued function `f` and a
module-valued function `g` admitting formal power series `p` and `q` on `Metric.eball z₀ r` admits
the Cauchy-product power series on `Metric.eball z₀ r`. -/
@[to_fun]
theorem HasFPowerSeriesOnBall.smul
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E]
    {f : 𝕜 → A} {g : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 A}
    {q : FormalMultilinearSeries 𝕜 𝕜 E} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (hg : HasFPowerSeriesOnBall g q z₀ r) :
    HasFPowerSeriesOnBall (f • g)
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ∑ k ∈ Finset.range (n + 1), p.coeff (n - k) • q.coeff k)
      z₀ r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf hg ⊢
  exact hf.smul hg

/-- The product of two functions from `𝕜` into a normed `𝕜`-algebra admitting formal power series
`p` and `q` on `Metric.eball z₀ r` within `s` admits the Cauchy-product power series on
`Metric.eball z₀ r` within `s`. -/
@[to_fun]
theorem HasFPowerSeriesWithinOnBall.mul
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {f g : 𝕜 → A} {p q : FormalMultilinearSeries 𝕜 𝕜 A} {s : Set 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesWithinOnBall f p s z₀ r)
    (hg : HasFPowerSeriesWithinOnBall g q s z₀ r) :
    HasFPowerSeriesWithinOnBall (f * g)
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ∑ k ∈ Finset.range (n + 1), p.coeff (n - k) * q.coeff k)
      s z₀ r :=
  hf.smul hg

/-- The product of two functions from `𝕜` into a normed `𝕜`-algebra admitting formal power series
`p` and `q` on `Metric.eball z₀ r` admits the Cauchy-product power series on `Metric.eball z₀ r`. -/
@[to_fun]
theorem HasFPowerSeriesOnBall.mul
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {f g : 𝕜 → A} {p q : FormalMultilinearSeries 𝕜 𝕜 A} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (hg : HasFPowerSeriesOnBall g q z₀ r) :
    HasFPowerSeriesOnBall (f * g)
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ∑ k ∈ Finset.range (n + 1), p.coeff (n - k) * q.coeff k)
      z₀ r :=
  hf.smul hg

end CauchyProduct

namespace TauCeti

/-- The reciprocal kernel `z ↦ (w - z)⁻¹` is analytic near `s` if and only if `w ∉ s`. -/
@[simp]
theorem analyticOnNhd_sub_inv_iff {𝕜 𝕝 : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝] {s : Set 𝕝} {w : 𝕝} :
    AnalyticOnNhd 𝕜 (fun z ↦ (w - z)⁻¹) s ↔ w ∉ s := by
  constructor
  · intro hf hws
    have hcont : ContinuousAt (fun z : 𝕝 ↦ (w - z)⁻¹) (w - 0) := by
      rw [sub_zero]
      exact (hf w hws).continuousAt
    have h0 : ContinuousAt (Inv.inv : 𝕝 → 𝕝) 0 := by
      simpa only [Function.comp_def, sub_sub_cancel] using
        hcont.comp (continuousAt_const.sub continuousAt_id)
    exact NormedField.continuousAt_inv.mp h0 rfl
  · intro hws
    exact (analyticOnNhd_const.sub analyticOnNhd_id).inv fun z hz (h : w - z = 0) ↦
      hws (sub_eq_zero.mp h ▸ hz)

end TauCeti
