/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.Analysis.Analytic.Constructions

/-!
# Division of a multi-index power series by a coordinate

When all terms have degree at least `m` in one coordinate, shifting the exponents in that
coordinate gives an analytic quotient on the original open polydisc. The argument works
over any nontrivially normed field. Subtracting the restriction to a coordinate hyperplane
then gives an analytic extension of the coordinate divided difference across the hyperplane.

## References

The exponent shift follows Michail Karatarakis's formalization of Baker's theorem in
`mkaratarakis/mathlib4`, commit `1d51891b5be7ceeca95b4583cad39e0681c5e453`,
`Mathlib/NumberTheory/Transcendental/Baker/CoordinateDivision.lean` (Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped NNReal ENNReal

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem summable_norm_shift_single [DecidableEq ι] {c : (ι → ℕ) → F}
    {r : ℝ} (hr : 0 < r) (i : ι) (m : ℕ)
    (hc : Summable fun α : ι → ℕ ↦ ‖c α‖ * r ^ (∑ j, α j)) :
    Summable fun α : ι → ℕ ↦ ‖c (α + Pi.single i m)‖ * r ^ (∑ j, α j) := by
  have h := (hc.comp_injective (add_left_injective (Pi.single i m))).mul_left (r ^ m)⁻¹
  refine h.congr fun α ↦ ?_
  simp only [Function.comp_apply, Pi.add_apply, sum_add_distrib, Fintype.sum_pi_single', pow_add]
  field_simp

private theorem hasSum_monomial_shift_single [DecidableEq ι] {c : (ι → ℕ) → F}
    (i : ι) (m : ℕ) (hzero : ∀ α, α i < m → c α = 0) {y : ι → 𝕜} {a : F}
    (h : HasSum (fun α : ι → ℕ ↦ (∏ j, y j ^ α j) • c (α + Pi.single i m)) a) :
    HasSum (fun α : ι → ℕ ↦ (∏ j, y j ^ α j) • c α) (y i ^ m • a) := by
  let s : ι → ℕ := Pi.single i m
  refine (Function.Injective.hasSum_iff (add_left_injective s) (fun α hα ↦ ?_)).1 ?_
  · have hi : α i < m := by
      by_contra! hmi
      apply hα
      refine ⟨fun j ↦ α j - s j, funext fun j ↦ ?_⟩
      simp only [Pi.add_apply]
      apply Nat.sub_add_cancel
      rcases eq_or_ne j i with rfl | hji
      · simpa [s] using hmi
      · simp [s, Pi.single_eq_of_ne hji]
    simp [hzero α hi]
  · refine (h.const_smul (y i ^ m)).congr_fun fun α ↦ ?_
    have hs : ∏ j, y j ^ s j = y i ^ m := by
      rw [prod_eq_single i]
      · simp [s]
      · intro j _ hj
        simp [s, Pi.single_eq_of_ne hj]
      · simp
    simp only [Function.comp_apply, Pi.add_apply, pow_add, prod_mul_distrib, hs, smul_smul]
    rw [mul_comm]

namespace TauCeti

/-- If a multi-index expansion has no terms of degree less than `m` in coordinate `i`,
then its sum is divisible by the `m`-th power of that coordinate. The quotient is analytic
throughout the open polydisc on which the expansion is normally convergent. -/
theorem exists_analyticOnNhd_eq_coord_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {x : ι → 𝕜} {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hc : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ j, α j))
    (hf : ∀ y : ι → 𝕜, ‖y‖ < r →
      HasSum (fun α : ι → ℕ ↦ (∏ j, y j ^ α j) • c α) (f (x + y)))
    (i : ι) (m : ℕ) (hzero : ∀ α, α i < m → c α = 0) :
    ∃ g : (ι → 𝕜) → F, AnalyticOnNhd 𝕜 g (Metric.eball 0 r) ∧
      ∀ y : ι → 𝕜, ‖y‖ < r → f (x + y) = y i ^ m • g y := by
  classical
  let d : (ι → ℕ) → F := fun α ↦ c (α + Pi.single i m)
  have hd : Summable fun α : ι → ℕ ↦ ‖d α‖ * (r : ℝ) ^ (∑ j, α j) :=
    summable_norm_shift_single (NNReal.coe_pos.mpr hr) i m hc
  obtain ⟨p, hp, -⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) d hr hd
  refine ⟨_, hp.analyticOnNhd, fun y hy ↦ (hf y hy).unique ?_⟩
  exact hasSum_monomial_shift_single i m hzero
    (summable_norm_prod_pow_smul_of_le hd hy.le).of_norm.hasSum

end TauCeti

/-- Vanishing of Taylor coefficients below order `m` in coordinate `i` gives an analytic
factor after removing `(z i - x i)^m` near the centre `x`. -/
theorem AnalyticAt.exists_eventuallyEq_coord_sub_pow_smul [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (i : ι) (m : ℕ)
    (hzero : ∀ α : ι → ℕ, α i < m → TauCeti.mvTaylorCoeff f x α = 0) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g x ∧
      f =ᶠ[𝓝 x] fun z ↦ (z i - x i) ^ m • g z := by
  obtain ⟨r, hr, hc, hsum⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨g, hg, hfg⟩ := TauCeti.exists_analyticOnNhd_eq_coord_pow_smul hr hc hsum i m hzero
  refine ⟨fun z ↦ g (z - x), ?_, ?_⟩
  · exact (hg 0 (Metric.mem_eball_self (ENNReal.coe_pos.2 hr))).comp_of_eq (by fun_prop)
      (sub_self x)
  · filter_upwards [Metric.ball_mem_nhds x (NNReal.coe_pos.mpr hr)] with z hz
    simpa only [add_sub_cancel, Pi.sub_apply] using hfg (z - x)
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)

/-- Fixing a coordinate at its value at the centre keeps precisely the Taylor coefficients
whose exponent in that coordinate is zero. -/
theorem AnalyticAt.mvTaylorCoeff_comp_update_same [DecidableEq ι]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (i : ι)
    (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (fun z ↦ f (Function.update z i (x i))) x α =
      if α i = 0 then TauCeti.mvTaylorCoeff f x α else 0 := by
  obtain ⟨r, hr, hc, hsum⟩ := hf.exists_hasSum_mvTaylorCoeff
  apply TauCeti.mvTaylorCoeff_eq_of_hasSum hr (ρ := r) ?_ ?_ α
  · refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun β ↦ ?_) hc
    split_ifs <;> simp [mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _)]
  · intro y hy
    have hnorm : ‖Function.update y i 0‖ ≤ ‖y‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simp
      · simpa [Function.update_of_ne hj] using norm_le_pi_norm y j
    have hupdate : x + Function.update y i 0 = Function.update (x + y) i (x i) := by
      ext j
      rcases eq_or_ne j i with rfl | hj <;> simp [Function.update_of_ne, *]
    rw [← hupdate]
    refine (hsum _ (hnorm.trans_lt hy)).congr_fun fun β ↦ ?_
    by_cases hβ : β i = 0
    · rw [ite_eq_left hβ]
      congr 1
      exact prod_congr rfl fun j _ ↦ by
        rcases eq_or_ne j i with rfl | hj <;> simp [Function.update_of_ne, *]
    · rw [ite_eq_right hβ, smul_zero, prod_eq_zero (mem_univ i) (by simp [hβ]), zero_smul]

/-- Subtracting the restriction to the coordinate hyperplane through `x` gives a function
divisible near `x` by the corresponding coordinate difference, with analytic quotient. -/
theorem AnalyticAt.exists_eventuallyEq_coord_sub_smul [CompleteSpace F] [DecidableEq ι]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (i : ι) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g x ∧
      (fun z ↦ f z - f (Function.update z i (x i))) =ᶠ[𝓝 x]
        fun z ↦ (z i - x i) • g z := by
  have hupdate : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ Function.update z i (x i)) x :=
    analyticAt_id.update analyticAt_const
  have hrestrict := hf.fun_comp_of_eq hupdate (Function.update_eq_self i x)
  obtain ⟨g, hg, hfg⟩ := (hf.sub hrestrict).exists_eventuallyEq_coord_sub_pow_smul i 1
    (fun α hα ↦ by
      rw [hf.mvTaylorCoeff_sub hrestrict, hf.mvTaylorCoeff_comp_update_same,
        ite_eq_left (Nat.lt_one_iff.1 hα), sub_self])
  exact ⟨g, hg, hfg.mono fun z hz ↦ by simpa only [Pi.sub_apply, pow_one] using hz⟩

section DividedDifference

variable [DecidableEq ι]
  {f : (ι → 𝕜) → F} {x : ι → 𝕜} {i : ι} {ζ : 𝕜}

/-- Away from its base hyperplane, a coordinate divided difference is analytic wherever the
two evaluations are analytic. -/
theorem AnalyticAt.dslope_update_of_ne (hf : AnalyticAt 𝕜 f x)
    (hζ : AnalyticAt 𝕜 f (Function.update x i ζ)) (hne : x i ≠ ζ) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  have hcoord : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ z i) x :=
    (ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x
  have h := ((hcoord.sub analyticAt_const).inv (sub_ne_zero.mpr hne)).smul
    (hf.sub (hζ.fun_comp (f := fun z : ι → 𝕜 ↦ Function.update z i ζ)
      (analyticAt_id.update analyticAt_const)))
  apply h.congr
  filter_upwards [(hcoord.continuousAt.eventually_ne hne)] with z hz
  simp [dslope_of_ne _ hz, slope]

private theorem AnalyticAt.dslope_update_of_factorization [CompleteSpace F]
    {g : (ι → 𝕜) → F} (hg : AnalyticAt 𝕜 g x)
    (hfg : (fun z ↦ f z - f (Function.update z i (x i))) =ᶠ[𝓝 x]
      fun z ↦ (z i - x i) • g z) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) x := by
  apply hg.congr
  filter_upwards [hfg.eventually_nhds, hg.eventually_analyticAt] with z hz hgz
  by_cases hzi : z i = x i
  · -- On the hyperplane, differentiating along the slice gives the quotient.
    have hu : AnalyticAt 𝕜 (Function.update z i) (x i) :=
      analyticAt_const.update analyticAt_id
    have huz : Function.update z i (x i) = z := by rw [← hzi, Function.update_eq_self]
    have heq := hu.continuousAt.tendsto.eventually (huz ▸ hz)
    have hg' := hgz.fun_comp_of_eq hu huz
    have hd := ((hasDerivAt_id (x i)).sub_const (x i)).smul hg'.differentiableAt.hasDerivAt
    have heq' : (fun w ↦ f (Function.update z i w) - f z) =ᶠ[𝓝 (x i)]
        (fun w ↦ (w - x i) • g (Function.update z i w)) := by
      filter_upwards [heq] with w hw
      simpa [Function.update_idem, ← hzi] using hw
    have hd' := hd.congr_of_eventuallyEq heq'
    have hd'' := hd'.add_const (f z)
    simpa [dslope_same, ← hzi] using hd''.deriv.symm
  · -- Away from the hyperplane the nonzero scalar factor cancels.
    have heq := mem_of_mem_nhds hz
    simp only [dslope_of_ne _ hzi, slope, Function.update_eq_self, vsub_eq_sub]
    exact ((inv_smul_eq_iff₀ (sub_ne_zero.mpr hzi)).2 heq).symm

/-- A coordinate divided difference extends analytically across its base hyperplane. -/
theorem AnalyticAt.dslope_update_same [CompleteSpace F] (hf : AnalyticAt 𝕜 f x) (i : ι) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) x := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_eventuallyEq_coord_sub_smul i
  exact hg.dslope_update_of_factorization hfg

/-- Coordinate divided differences are analytic wherever both evaluations are analytic. -/
theorem TauCeti.analyticAt_dslope_update [CompleteSpace F] (i : ι) (ζ : 𝕜)
    (hf : AnalyticAt 𝕜 f x) (hζ : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  by_cases hxi : x i = ζ
  · simpa only [hxi] using hf.dslope_update_same i
  · exact hf.dslope_update_of_ne hζ hxi

end DividedDifference
