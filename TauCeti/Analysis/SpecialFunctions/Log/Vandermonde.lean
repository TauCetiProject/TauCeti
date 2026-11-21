/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Topology.Constructions.Pi

/-!
# The logarithmic Vandermonde collision barrier

`TauCeti.logVandermonde x` is the sum of `log |x i - x j|` over `i < j`.
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

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderTop ι]

/-- The logarithm of the absolute Vandermonde product, away from collisions.
On the decreasing chamber every gap in the sum is positive. -/
def logVandermonde (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, Real.log (x i - x j)

/-- The defining pair sum for the logarithmic Vandermonde potential. -/
theorem logVandermonde_def (x : ι → ℝ) :
    logVandermonde x = ∑ i, ∑ j ∈ Ioi i, Real.log (x i - x j) := (rfl)

/-- With at most one index there are no gaps, so the logarithmic Vandermonde is zero. -/
@[simp] theorem logVandermonde_of_subsingleton [Subsingleton ι] (x : ι → ℝ) :
    logVandermonde x = 0 := by
  rw [logVandermonde_def]
  refine sum_eq_zero fun i _ ↦ sum_eq_zero fun j hj ↦ ?_
  exact ((mem_Ioi.mp hj).ne (Subsingleton.elim i j)).elim

/-- Relabeling the coordinates preserves the logarithmic Vandermonde. -/
@[simp] theorem logVandermonde_comp_perm (x : ι → ℝ) (σ : Equiv.Perm ι) :
    logVandermonde (x ∘ σ) = logVandermonde x := by
  simp only [logVandermonde_def, Function.comp_apply]
  exact sum_sum_Ioi_comp_perm (fun i j ↦ Real.log (x i - x j)) σ fun i j ↦ by
    rw [← neg_sub (x j) (x i), Real.log_neg_eq_log]

/-- Negating every coordinate preserves the logarithmic Vandermonde. -/
@[simp] theorem logVandermonde_neg (x : ι → ℝ) : logVandermonde (-x) = logVandermonde x := by
  simp only [logVandermonde_def, Pi.neg_apply, neg_sub_neg]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [← neg_sub (x i) (x j), Real.log_neg_eq_log]

/-- Translating every coordinate by the same amount preserves the logarithmic Vandermonde. -/
@[simp] theorem logVandermonde_add_const (x : ι → ℝ) (c : ℝ) :
    logVandermonde (fun i ↦ x i + c) = logVandermonde x := by
  simp [logVandermonde_def]

/-- Subtracting the same constant from every coordinate preserves the logarithmic Vandermonde. -/
@[simp] theorem logVandermonde_sub_const (x : ι → ℝ) (c : ℝ) :
    logVandermonde (fun i ↦ x i - c) = logVandermonde x := by
  simpa only [sub_eq_add_neg] using logVandermonde_add_const x (-c)

/-- A nonzero rescaling of a collision-free configuration adds one `Real.log c` per gap. -/
theorem logVandermonde_smul {c : ℝ} (hc : c ≠ 0) {x : ι → ℝ} (hx : Function.Injective x) :
    logVandermonde (c • x) = ((Fintype.card ι).choose 2 : ℝ) * Real.log c + logVandermonde x := by
  have hlog (i j : ι) (hj : j ∈ Ioi i) :
      Real.log ((c • x) i - (c • x) j) = Real.log c + Real.log (x i - x j) := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_sub] using
      Real.log_mul hc (sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne))
  have hcount : (∑ i : ι, ∑ _j ∈ Ioi i, Real.log c) =
      ((Fintype.card ι).choose 2 : ℝ) * Real.log c := by
    have hIoi (i : ι) : Ioi i = univ.filter (i < ·) := by ext; simp
    calc
      (∑ i : ι, ∑ _j ∈ Ioi i, Real.log c) =
          ∑ _p ∈ ((univ : Finset ι) ×ˢ univ).filter (fun p ↦ p.1 < p.2), Real.log c := by
            simp only [hIoi, sum_filter, sum_product]
      _ = _ := by rw [sum_const, card_product_filter_lt, card_univ, nsmul_eq_mul]
  rw [logVandermonde_def, logVandermonde_def, ← hcount, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by rw [← sum_add_distrib]; exact sum_congr rfl (hlog i)

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

/-- The coordinate first derivative sums inverse gaps from the chosen coordinate to all others. -/
theorem fderiv_logVandermonde_single {x : ι → ℝ} (hx : Function.Injective x) (k : ι) :
    fderiv ℝ logVandermonde x (Pi.single k 1) = ∑ j ∈ univ.erase k, (x k - x j)⁻¹ := by
  rw [fderiv_logVandermonde_apply hx]
  simp_rw [div_eq_mul_inv]
  have h := sum_mul_sum_erase_eq_sum_sum_Ioi (Pi.single k 1) (fun i j ↦ (x i - x j)⁻¹)
    (fun {i j} _ ↦ by rw [← neg_sub (x i) (x j), inv_neg])
  simpa [Pi.single_apply, ite_mul] using h.symm

/-- The Hessian as a bilinear form, in the Fréchet-derivative representation used
in the multivariate Itô formula. -/
theorem fderiv_fderiv_logVandermonde_apply {x : ι → ℝ}
    (hx : Function.Injective x) (v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ logVandermonde) x v w =
      -∑ i, ∑ j ∈ Ioi i, (v i - v j) * (w i - w j) / (x i - x j) ^ 2 := by
  let gap (i j : ι) : (ι → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j
  have hinj : ∀ᶠ y in 𝓝 x, Function.Injective y := isOpen_setOf_injective.mem_nhds hx
  have heq : fderiv ℝ logVandermonde =ᶠ[𝓝 x]
      fun y ↦ ∑ i, ∑ j ∈ Ioi i, (gap i j y)⁻¹ • gap i j :=
    hinj.mono fun y hy ↦ (hasFDerivAt_logVandermonde hy).fderiv
  rw [heq.fderiv_eq]
  have hterm (i j : ι) (hj : j ∈ Ioi i) :=
    have hne : gap i j x ≠ 0 := sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne)
    ((hasDerivAt_inv hne).comp_hasFDerivAt x (gap i j).hasFDerivAt).smul_const (gap i j)
  have hd := HasFDerivAt.fun_sum (u := univ) fun i _ ↦ HasFDerivAt.fun_sum (hterm i)
  simp only [Function.comp_apply] at hd
  rw [hd.fderiv]
  simp [gap, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ← sum_neg_distrib]

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

/-- A finite limit is collision-free if the family is frequently collision-free with its
logarithmic Vandermonde above a common lower bound. -/
theorem injective_of_tendsto_of_frequently_le_logVandermonde {α : Type*} {l : Filter α}
    {X : α → ι → ℝ} {y : ι → ℝ} (hX : Tendsto X l (𝓝 y))
    (hbound : ∃ C : ℝ, ∃ᶠ a in l, Function.Injective (X a) ∧ C ≤ logVandermonde (X a)) :
    Function.Injective y := by
  by_contra hy
  obtain ⟨C, hC⟩ := hbound
  let l' := l ⊓ 𝓟 {a | Function.Injective (X a) ∧ C ≤ logVandermonde (X a)}
  have : NeBot l' := frequently_iff_neBot.mp hC
  have he : ∀ᶠ a in l', Function.Injective (X a) ∧ C ≤ logVandermonde (X a) :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ ha ↦ ha)
  exact not_isBoundedUnder_of_tendsto_atBot
    (tendsto_logVandermonde_atBot (hX.mono_left inf_le_left) (he.mono fun _ ha ↦ ha.1) hy)
    (isBoundedUnder_of_eventually_ge (he.mono fun _ ha ↦ ha.2))

end TauCeti
