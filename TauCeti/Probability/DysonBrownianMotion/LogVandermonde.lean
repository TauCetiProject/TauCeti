/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The logarithmic Vandermonde collision barrier

`TauCeti.Probability.logVandermonde x` is the sum of `log |x i - x j|` over `i < j`.
It is smooth away from collisions. Its first variation is the inverse-gap sum, and its
second variation is a negative sum of squares. These are the deterministic derivatives used
when applying Itô's formula to the logarithmic-gap potential of a repulsive particle system.

The potential tends to minus infinity along every collision-free family converging to a
finite colliding configuration. Thus a lower bound for the potential rules out collisions
as long as the coordinates have finite limits. No assertion about its value or smoothness
at a colliding configuration is intended: `Real.log 0 = 0` is a totalization convention.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §4.3.1, proof of Lemma 4.3.3.
-/

public section

noncomputable section

open Finset Filter
open scoped Topology ContDiff

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderTop ι]

/-- The logarithm of the absolute Vandermonde product, away from collisions.
On the decreasing chamber every gap in the sum is positive. -/
def logVandermonde (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, Real.log (x i - x j)

/-- The defining pair sum for the logarithmic Vandermonde potential. -/
theorem logVandermonde_def (x : ι → ℝ) :
    logVandermonde x = ∑ i, ∑ j ∈ Ioi i, Real.log (x i - x j) := (rfl)

/-- Away from collisions the potential is the logarithm of the Vandermonde product.
`Real.log` already takes the absolute value of a nonzero real argument. -/
theorem logVandermonde_eq_log_prod {x : ι → ℝ} (hx : Function.Injective x) :
    logVandermonde x = Real.log (∏ i, ∏ j ∈ Ioi i, (x i - x j)) := by
  have hgap i j (hj : j ∈ Ioi i) : x i - x j ≠ 0 :=
    sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne)
  rw [Real.log_prod (fun i _ ↦ prod_ne_zero_iff.mpr (hgap i))]
  simp only [logVandermonde_def, Real.log_prod (hgap _)]

/-- The logarithmic Vandermonde is smooth of every order at a collision-free configuration. -/
theorem contDiffAt_logVandermonde {x : ι → ℝ} (hx : Function.Injective x) {m : ℕ∞ω} :
    ContDiffAt ℝ m logVandermonde x := by
  unfold logVandermonde
  refine ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j hj ↦ ?_
  exact ((contDiff_apply ℝ (fun _ : ι ↦ ℝ) i).contDiffAt.sub
    (contDiff_apply ℝ (fun _ : ι ↦ ℝ) j).contDiffAt).log
      (sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne))

/-- The Fréchet derivative of the logarithmic Vandermonde is the inverse-gap linear form. -/
theorem hasFDerivAt_logVandermonde {x : ι → ℝ} (hx : Function.Injective x) :
    HasFDerivAt logVandermonde
      (∑ i, ∑ j ∈ Ioi i, (x i - x j)⁻¹ •
        ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j)) x := by
  unfold logVandermonde
  refine HasFDerivAt.fun_sum fun i _ ↦ HasFDerivAt.fun_sum fun j hj ↦ ?_
  exact ((hasFDerivAt_apply i x).sub (hasFDerivAt_apply j x)).log
    (sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne))

/-- The first variation in an arbitrary direction, without unfolding the potential. -/
theorem fderiv_logVandermonde_apply {x : ι → ℝ} (hx : Function.Injective x) (v : ι → ℝ) :
    fderiv ℝ logVandermonde x v = ∑ i, ∑ j ∈ Ioi i, (v i - v j) / (x i - x j) := by
  rw [(hasFDerivAt_logVandermonde hx).fderiv]
  simp [div_eq_mul_inv, mul_comm]

/-- The mixed second variation: differentiate the first variation in direction `v`,
while evaluating the resulting linear form on `w`. -/
private theorem hasDerivAt_fderiv_logVandermonde_add_smul {x : ι → ℝ}
    (hx : Function.Injective x) (v w : ι → ℝ) :
    HasDerivAt (fun t : ℝ ↦ fderiv ℝ logVandermonde (x + t • v) w)
      (-∑ i, ∑ j ∈ Ioi i, (v i - v j) * (w i - w j) / (x i - x j) ^ 2) 0 := by
  have hne : ∀ᶠ t : ℝ in 𝓝 0, Function.Injective (x + t • v) := by
    simp only [Function.Injective, eventually_all]
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · have hgap : ContinuousAt (fun t : ℝ ↦ (x + t • v) i - (x + t • v) j) 0 := by
        fun_prop
      filter_upwards [hgap.eventually_ne (by simpa using sub_ne_zero.mpr (hx.ne hij))]
        with t ht h
      exact False.elim (ht (sub_eq_zero.mpr h))
  have heq : (fun t : ℝ ↦ fderiv ℝ logVandermonde (x + t • v) w) =ᶠ[𝓝 0]
      (fun t ↦ ∑ i, ∑ j ∈ Ioi i, (w i - w j) / ((x + t • v) i - (x + t • v) j)) :=
    hne.mono fun t ht ↦ fderiv_logVandermonde_apply ht w
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  rw [← sum_neg_distrib]
  simp_rw [← sum_neg_distrib]
  refine HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j hj ↦ ?_
  have hgap : x i - x j ≠ 0 := sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne)
  have hd : HasDerivAt (fun t : ℝ ↦ (x + t • v) i - (x + t • v) j)
      (v i - v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i) |>.fun_sub
      (((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (x j))
  convert (hd.inv (by simpa using hgap)).const_mul (w i - w j) using 1 <;>
    simp [div_eq_mul_inv]; ring

/-- The Hessian as a bilinear form, in the Fréchet-derivative representation used
in the multivariate Itô formula. -/
theorem fderiv_fderiv_logVandermonde_apply {x : ι → ℝ}
    (hx : Function.Injective x) (v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ logVandermonde) x v w =
      -∑ i, ∑ j ∈ Ioi i, (v i - v j) * (w i - w j) / (x i - x j) ^ 2 := by
  have ha : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf := (contDiffAt_logVandermonde hx (m := 2)).fderiv_right (m := 1) (by norm_num)
    |>.differentiableAt_one.hasFDerivAt
  have he : HasDerivAt (fun t : ℝ ↦ fderiv ℝ logVandermonde (x + t • v) w)
      (fderiv ℝ (fderiv ℝ logVandermonde) x v w) 0 := by
    simpa using (hf.comp_hasDerivAt_of_eq 0 ha (by simp)).clm_apply (hasDerivAt_const 0 w)
  exact he.unique (hasDerivAt_fderiv_logVandermonde_add_smul hx v w)

/-- The quadratic form of the Hessian is a negative sum of squared gap ratios. -/
theorem fderiv_fderiv_logVandermonde_self {x : ι → ℝ}
    (hx : Function.Injective x) (v : ι → ℝ) :
    fderiv ℝ (fderiv ℝ logVandermonde) x v v =
      -∑ i, ∑ j ∈ Ioi i, ((v i - v j) / (x i - x j)) ^ 2 := by
  simpa [div_pow, pow_two, div_mul_div_comm] using
    fderiv_fderiv_logVandermonde_apply hx v v

/-- The sum of the coordinate second derivatives is minus twice the inverse-square
gap sum. Multiplication by `1 / (β * n)` gives the Itô correction for Dyson noise. -/
theorem sum_fderiv_fderiv_logVandermonde_single {x : ι → ℝ} (hx : Function.Injective x) :
    ∑ k, fderiv ℝ (fderiv ℝ logVandermonde) x (Pi.single k 1) (Pi.single k 1) =
      -2 * ∑ i, ∑ j ∈ Ioi i, ((x i - x j) ^ 2)⁻¹ := by
  have hsingle {i j : ι} (hij : i ≠ j) :
      ∑ k : ι, ((Pi.single k 1 : ι → ℝ) i - (Pi.single k 1 : ι → ℝ) j) ^ 2 = 2 := by
    have hterm (k : ι) : ((Pi.single k 1 : ι → ℝ) i - (Pi.single k 1 : ι → ℝ) j) ^ 2 =
        (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp_all [Pi.single_apply, eq_comm]
    simp_rw [hterm, sum_add_distrib]
    norm_num
  simp_rw [fderiv_fderiv_logVandermonde_self hx, div_pow]
  rw [sum_neg_distrib, sum_comm]
  have hsum : ∑ i, ∑ k, ∑ j ∈ Ioi i,
      ((Pi.single k 1 : ι → ℝ) i - (Pi.single k 1 : ι → ℝ) j) ^ 2 / (x i - x j) ^ 2 =
      2 * ∑ i, ∑ j ∈ Ioi i, ((x i - x j) ^ 2)⁻¹ := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro j hj
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul, hsingle (mem_Ioi.mp hj).ne]
  rw [hsum]
  ring

/-- Every collision at a finite limiting configuration sends the logarithmic
Vandermonde to minus infinity, even if several gaps vanish at once. -/
theorem tendsto_logVandermonde_atBot {α : Type*} {l : Filter α}
    {X : α → ι → ℝ} {y : ι → ℝ} (hX : Tendsto X l (𝓝 y))
    (hinj : ∀ᶠ a in l, Function.Injective (X a)) (hy : ¬Function.Injective y) :
    Tendsto (fun a ↦ logVandermonde (X a)) l atBot := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hy
  have hz : (∏ i, ∏ j ∈ Ioi i, (y i - y j)) = 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact prod_eq_zero (mem_univ i) (prod_eq_zero (mem_Ioi.mpr hlt) (sub_eq_zero.mpr hij))
    · exact prod_eq_zero (mem_univ j) (prod_eq_zero (mem_Ioi.mpr hlt)
        (sub_eq_zero.mpr hij.symm))
  have hp : Tendsto (fun a ↦ ∏ i, ∏ j ∈ Ioi i, (X a i - X a j)) l (𝓝 0) := by
    rw [← hz]
    exact tendsto_finsetProd _ fun i _ ↦ tendsto_finsetProd _ fun j _ ↦
      (hX.apply_nhds i).sub (hX.apply_nhds j)
  have hpne : ∀ᶠ a in l, (∏ i, ∏ j ∈ Ioi i, (X a i - X a j)) ≠ 0 :=
    hinj.mono fun a ha ↦ prod_ne_zero_iff.mpr fun i _ ↦ prod_ne_zero_iff.mpr fun j hj ↦
      sub_ne_zero.mpr (ha.ne (mem_Ioi.mp hj).ne)
  exact (Real.tendsto_log_nhdsNE_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hp, hpne⟩)).congr'
    (hinj.mono fun a ha ↦ (logVandermonde_eq_log_prod ha).symm)

/-- A collision-free family with a finite limit and an eventual lower bound on the
logarithmic Vandermonde has a collision-free limit. No ordering of the particles is required. -/
theorem injective_of_tendsto_of_logVandermonde_bddBelow {α : Type*} {l : Filter α} [NeBot l]
    {X : α → ι → ℝ} {y : ι → ℝ} (hX : Tendsto X l (𝓝 y))
    (hinj : ∀ᶠ a in l, Function.Injective (X a))
    (hbound : ∃ C : ℝ, ∀ᶠ a in l, C ≤ logVandermonde (X a)) : Function.Injective y := by
  by_contra hy
  obtain ⟨C, hC⟩ := hbound
  have hlt := (tendsto_logVandermonde_atBot hX hinj hy).eventually (eventually_lt_atBot C)
  obtain ⟨a, ha, hlt⟩ := (hC.and hlt).exists
  exact (not_lt_of_ge ha) hlt

end TauCeti.Probability
