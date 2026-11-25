/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FullyNonlinear.AdmissiblePair
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic

/-!
# Checks for admissible pairs

Three pairs `(f, Γ)` that test the definition of an admissible pair
(`TauCeti.IsAdmissiblePair`).

* The Monge–Ampère pair `((∏_i μ_i)^{1/n}, Γ_n)` has `∂_j f(μ) = n⁻¹ (∏_i μ_i)^{1/n} / μ_j`, so
  the product of its partial derivatives is `n⁻ⁿ` identically, not only bounded below by it. For
  `n = 2` at `(1, 4)` the partials are `1` and `1/4`.
* `f(λ) = σ_1(λ) − ε|λ|` on `Γ_1`, with `|ε| < 1` and the Euclidean norm `|λ|`, is an admissible
  pair, since `∂_j f = 1 − ε λ_j / |λ| > 0`. For `0 < δ < ε` its value at `(1, −1 + δ) ∈ Γ_1` is
  negative, so an admissible pair need not be positive off `Γ_n`.
* `f(λ) = max_j λ_j` is symmetric and positively homogeneous of degree one, but in dimension at
  least two it is not differentiable at `e = (1, …, 1)`, so it is no admissible pair on `Γ_n`.

## Main declarations

* `TauCeti.Examples.AdmissiblePair.prod_fderiv_prod_rpow_apply_single`: the product of the
  partial derivatives of the Monge–Ampère function is `n⁻ⁿ` on `Γ_n`.
* `TauCeti.Examples.AdmissiblePair.isAdmissiblePair_sum_sub_mul_sqrt`: the pair
  `(σ_1 − ε|λ|, Γ_1)`.
* `TauCeti.Examples.AdmissiblePair.sum_sub_mul_sqrt_neg`: its negative value at `(1, −1 + δ)`.
* `TauCeti.Examples.AdmissiblePair.not_isAdmissiblePair_sup'`: `max_j λ_j` is not an admissible
  pair on `Γ_n`.

## References

* `TauCetiRoadmap/ComplexHessianEquations/README.md`, §2.4, Checks.
-/

public section

noncomputable section

open Finset

namespace TauCeti.Examples.AdmissiblePair

variable {ι : Type*} [Fintype ι]

section DecidableEq

variable [DecidableEq ι]

/-! ### The Monge–Ampère pair -/

/-- The partial derivatives of the Monge–Ampère function `(∏_i μ_i)^{1/n}` on `Γ_n`:
`∂_j f(μ) = n⁻¹ (∏_i μ_i)^{1/n} / μ_j`. -/
theorem fderiv_prod_rpow_apply_single {μ : ι → ℝ} (hμ : ∀ i, 0 < μ i) (j : ι) :
    fderiv ℝ (fun ν : ι → ℝ ↦ (∏ i, ν i) ^ (Fintype.card ι : ℝ)⁻¹) μ (Pi.single j 1) =
      (Fintype.card ι : ℝ)⁻¹ * (∏ i, μ i) ^ (Fintype.card ι : ℝ)⁻¹ / μ j := by
  have hP : 0 < ∏ i, μ i := prod_pos fun i _ ↦ hμ i
  have hsplit : ∏ i, μ i = μ j * ∏ i ∈ univ.erase j, μ i :=
    (mul_prod_erase univ μ (mem_univ j)).symm
  rw [((hasFDerivAt_finsetProd (u := univ) (x := μ)).differentiableAt.hasFDerivAt.rpow_const
    (Or.inl hP.ne')).fderiv, smul_apply, fderiv_prod_apply_single, smul_eq_mul,
    Real.rpow_sub_one hP.ne']
  have hj : μ j ≠ 0 := (hμ j).ne'
  field_simp
  rw [hsplit, mul_comm (μ j)]

/-- The product of the partial derivatives of the Monge–Ampère function is `n⁻ⁿ` at every point
of `Γ_n`, so `n⁻ⁿ` is its best structural constant. -/
theorem prod_fderiv_prod_rpow_apply_single {μ : ι → ℝ} (hμ : ∀ i, 0 < μ i) :
    ∏ j, fderiv ℝ (fun ν : ι → ℝ ↦ (∏ i, ν i) ^ (Fintype.card ι : ℝ)⁻¹) μ (Pi.single j 1) =
      (Fintype.card ι : ℝ)⁻¹ ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hP : 0 < ∏ i, μ i := prod_pos fun i _ ↦ hμ i
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp_rw [fderiv_prod_rpow_apply_single hμ, div_eq_mul_inv, prod_mul_distrib, prod_const,
    prod_inv_distrib, card_univ]
  rw [← Real.rpow_natCast ((∏ i, μ i) ^ _), ← Real.rpow_mul hP.le, inv_mul_cancel₀ hn,
    Real.rpow_one, mul_assoc, mul_inv_cancel₀ hP.ne', mul_one]

/-- For `n = 2` at `μ = (1, 4)` the partial derivatives of `(μ_1 μ_2)^{1/2}` are `1` and `1/4`,
with product `1/4 = 2⁻²`. -/
theorem fderiv_prod_rpow_one_four :
    fderiv ℝ (fun ν : Fin 2 → ℝ ↦ (∏ i, ν i) ^ (2 : ℝ)⁻¹) (![1, 4] : Fin 2 → ℝ)
        (Pi.single 0 1) = 1 ∧
      fderiv ℝ (fun ν : Fin 2 → ℝ ↦ (∏ i, ν i) ^ (2 : ℝ)⁻¹) (![1, 4] : Fin 2 → ℝ)
        (Pi.single 1 1) = 1 / 4 := by
  have hμ : ∀ i, 0 < (![1, 4] : Fin 2 → ℝ) i := by simp [Fin.forall_fin_two]
  have h4 : (4 : ℝ) ^ (2 : ℝ)⁻¹ = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h : ∀ j, fderiv ℝ (fun ν : Fin 2 → ℝ ↦ (∏ i, ν i) ^ (2 : ℝ)⁻¹) (![1, 4] : Fin 2 → ℝ)
      (Pi.single j 1) =
        2⁻¹ * (∏ i, (![1, 4] : Fin 2 → ℝ) i) ^ (2 : ℝ)⁻¹ / (![1, 4] : Fin 2 → ℝ) j :=
    fun j ↦ by
      have := fderiv_prod_rpow_apply_single hμ j
      simp only [Fintype.card_fin, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.cast_ofNat] at this
      exact this
  rw [h, h]
  simp [Fin.prod_univ_two, h4]

/-! ### The pair `σ_1 − ε|λ|` on `Γ_1` -/

/-- `σ_1(μ) − ε|μ|`, with the Euclidean norm `|μ| = √(Σ_i μ_i²)`. -/
def sumSubMulSqrt (ε : ℝ) (μ : ι → ℝ) : ℝ :=
  ∑ i, μ i - ε * √(∑ i, μ i ^ 2)

omit [DecidableEq ι] in
theorem sumSubMulSqrt_def (ε : ℝ) (μ : ι → ℝ) :
    sumSubMulSqrt ε μ = ∑ i, μ i - ε * √(∑ i, μ i ^ 2) :=
  (rfl)

/-- The partial derivatives `∂_j (σ_1 − ε|μ|) = 1 − ε μ_j / |μ|` away from `0`. -/
theorem fderiv_sumSubMulSqrt_apply_single (ε : ℝ) {μ : ι → ℝ} (hμ : μ ≠ 0) (j : ι) :
    fderiv ℝ (sumSubMulSqrt ε) μ (Pi.single j 1) = 1 - ε * (μ j / √(∑ i, μ i ^ 2)) := by
  have hpos : 0 < ∑ i, μ i ^ 2 := by
    refine lt_of_le_of_ne (sum_nonneg fun i _ ↦ sq_nonneg _) fun h ↦ hμ (funext fun i ↦ ?_)
    simpa using (sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (μ i))).1 h.symm i (mem_univ i)
  have hi : ∀ i, HasFDerivAt (fun ν : ι → ℝ ↦ ν i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) μ := fun i ↦ hasFDerivAt_apply i μ
  have hsq : HasFDerivAt (fun ν : ι → ℝ ↦ ∑ i, ν i ^ 2) _ μ :=
    HasFDerivAt.fun_sum fun i _ ↦ (hi i).pow 2
  have hsum : HasFDerivAt (fun ν : ι → ℝ ↦ ∑ i, ν i) _ μ :=
    HasFDerivAt.fun_sum fun i _ ↦ hi i
  have hf : HasFDerivAt (sumSubMulSqrt ε) _ μ := hsum.sub ((hsq.sqrt hpos.ne').const_smul ε)
  rw [hf.fderiv]
  simp [Pi.single_apply]
  field_simp
  simp

/-- For `|ε| < 1`, the pair `(σ_1 − ε|λ|, Γ_1)` is an admissible pair: the partial derivatives
`1 − ε λ_j / |λ|` are positive since `|λ_j| ≤ |λ|`. -/
theorem isAdmissiblePair_sum_sub_mul_sqrt [Nonempty ι] {ε : ℝ} (hε : |ε| < 1) :
    IsAdmissiblePair {μ : ι → ℝ | 0 < ∑ i, μ i} (sumSubMulSqrt ε) where
  isAdmissibleCone := isAdmissibleCone_setOf_sum_pos
  contDiffOn := by
    intro μ hμ
    have hne : ∑ i, μ i ^ 2 ≠ 0 := by
      refine (lt_of_le_of_ne (sum_nonneg fun i _ ↦ sq_nonneg _) fun h ↦ ?_).ne'
      have h0 : ∀ i, μ i = 0 := fun i ↦ by
        simpa using (sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (μ i))).1 h.symm i (mem_univ i)
      simp [h0] at hμ
    refine ContDiffAt.contDiffWithinAt ?_
    unfold sumSubMulSqrt
    exact (by fun_prop : ContDiff ℝ 1 fun ν : ι → ℝ ↦ ∑ i, ν i).contDiffAt.sub
      (contDiffAt_const.mul ((by fun_prop : ContDiff ℝ 1 fun ν : ι → ℝ ↦ ∑ i, ν i ^ 2)
        |>.contDiffAt.sqrt hne))
  apply_comp_perm σ μ _ := by
    simp only [sumSubMulSqrt, Function.comp_apply]
    rw [Equiv.sum_comp σ μ, Equiv.sum_comp σ fun i ↦ μ i ^ 2]
  apply_smul {t} ht μ _ := by
    simp only [sumSubMulSqrt, Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_sum]
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
    ring
  fderiv_single_pos {μ} hμ j := by
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      simp at hμ
    rw [fderiv_sumSubMulSqrt_apply_single ε hμ0]
    have hs : 0 < √(∑ i, μ i ^ 2) := by
      refine Real.sqrt_pos.2 (lt_of_le_of_ne (sum_nonneg fun i _ ↦ sq_nonneg _) fun h ↦ hμ0 ?_)
      exact funext fun i ↦ by
        simpa using (sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (μ i))).1 h.symm i (mem_univ i)
    have hj : |μ j| ≤ √(∑ i, μ i ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (single_le_sum (fun i _ ↦ sq_nonneg (μ i)) (mem_univ j))
    have hq : |μ j / √(∑ i, μ i ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos hs]
      exact div_le_one_of_le₀ hj hs.le
    have : ε * (μ j / √(∑ i, μ i ^ 2)) < 1 := by
      calc ε * (μ j / √(∑ i, μ i ^ 2)) ≤ |ε * (μ j / √(∑ i, μ i ^ 2))| := le_abs_self _
        _ = |ε| * |μ j / √(∑ i, μ i ^ 2)| := abs_mul _ _
        _ ≤ |ε| * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    linarith

/-- The point `(1, −1 + δ)` lies in `Γ_1 ⊂ ℝ²` for `δ > 0`, and for `0 < δ < ε` the admissible
pair `σ_1 − ε|λ|` is negative there: `δ − ε √(1 + (1 − δ)²) < 0`. -/
theorem sum_sub_mul_sqrt_neg {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε) :
    (![1, -1 + δ] : Fin 2 → ℝ) ∈ {μ : Fin 2 → ℝ | 0 < ∑ i, μ i} ∧
      sumSubMulSqrt ε (![1, -1 + δ] : Fin 2 → ℝ) < 0 := by
  refine ⟨by simp [Fin.sum_univ_two, hδ], ?_⟩
  simp only [sumSubMulSqrt, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have h1 : 1 ≤ √(1 ^ 2 + (-1 + δ) ^ 2) :=
    Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (-1 + δ)])
  nlinarith

end DecidableEq

/-! ### `max_j λ_j` is not an admissible pair -/

/-- `max_j λ_j` is invariant under permutations of the coordinates. -/
theorem sup'_comp_perm [Nonempty ι] (σ : Equiv.Perm ι) (μ : ι → ℝ) :
    univ.sup' univ_nonempty (μ ∘ σ) = univ.sup' univ_nonempty μ :=
  le_antisymm (sup'_le _ _ fun i _ ↦ le_sup' μ (mem_univ (σ i)))
    (sup'_le _ _ fun i _ ↦ le_sup'_of_le (μ ∘ σ) (mem_univ (σ.symm i)) (by simp))

/-- `max_j λ_j` is positively homogeneous of degree one. -/
theorem sup'_smul [Nonempty ι] {t : ℝ} (ht : 0 ≤ t) (μ : ι → ℝ) :
    univ.sup' univ_nonempty (t • μ) = t * univ.sup' univ_nonempty μ :=
  (mul₀_sup' ht μ univ univ_nonempty).symm

/-- In dimension at least two, `max_j λ_j` is not differentiable at `e = (1, …, 1)`: along the
line `e + t e_a` it is `1 + max(t, 0)`. -/
theorem not_differentiableAt_sup' [Nontrivial ι] :
    ¬ DifferentiableAt ℝ (fun μ : ι → ℝ ↦ univ.sup' univ_nonempty μ) fun _ ↦ 1 := by
  classical
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  set L : ℝ → ι → ℝ := fun t ↦ (fun _ ↦ 1) + t • Pi.single a 1
  have hL : ∀ t, univ.sup' univ_nonempty (L t) = 1 + max t 0 := fun t ↦ by
    refine le_antisymm (sup'_le _ _ fun i _ ↦ ?_) ?_
    · by_cases hi : i = a
      · subst hi
        simp [L]
      · simp [L, hi]
    · rw [← max_add_add_left, add_zero]
      refine max_le ?_ ?_
      · exact le_sup'_of_le (L t) (mem_univ a) (by simp [L])
      · exact le_sup'_of_le (L t) (mem_univ b) (by simp [L, hab.symm])
  have hdL : DifferentiableAt ℝ L 0 := by fun_prop
  have hcomp : DifferentiableAt ℝ (fun t ↦ univ.sup' univ_nonempty (L t)) 0 := by
    refine DifferentiableAt.comp (f := L) (g := fun μ : ι → ℝ ↦ univ.sup' univ_nonempty μ) 0
      ?_ hdL
    simpa [L] using h
  simp_rw [hL] at hcomp
  have habs : DifferentiableAt ℝ (fun t : ℝ ↦ 2 * (1 + max t 0 - 1) - t) 0 :=
    ((hcomp.sub_const 1).const_mul 2).sub differentiableAt_id
  refine not_differentiableAt_abs_zero (habs.congr_of_eventuallyEq (Filter.Eventually.of_forall
    fun t ↦ ?_))
  rcases le_total t 0 with ht | ht
  · simp [abs_of_nonpos ht, max_eq_right ht]
  · simp [abs_of_nonneg ht, max_eq_left ht]
    ring

/-- In dimension at least two, `(max_j λ_j, Γ_n)` is not an admissible pair, although
`max_j λ_j` is symmetric (`sup'_comp_perm`) and positively homogeneous (`sup'_smul`): it is not
differentiable at `e ∈ Γ_n`. -/
theorem not_isAdmissiblePair_sup' [DecidableEq ι] [Nontrivial ι] :
    ¬ IsAdmissiblePair {μ : ι → ℝ | ∀ i, 0 < μ i} fun μ ↦ univ.sup' univ_nonempty μ :=
  fun h ↦ not_differentiableAt_sup' (h.differentiableAt (μ := fun _ ↦ 1) fun _ ↦ one_pos)

end TauCeti.Examples.AdmissiblePair
