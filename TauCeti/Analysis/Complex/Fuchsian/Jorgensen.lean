/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Endpoint
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Jørgensen's inequality for hyperbolic elements

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup and let `A, B ∈ SL(2, ℝ)` lift elements of `Γ`, with
`A` hyperbolic, that is `|tr A| > 2`. **Jørgensen's inequality** says that unless `B` normalises
`⟨A⟩` in the simplest possible way, `B A B⁻¹ = A` or `B A B⁻¹ = A⁻¹` in `PSL(2, ℝ)`,

`|tr² A - 4| + |tr [A, B] - 2| ≥ 1`.

The two exceptional cases are the elements `B` preserving the pair of fixed points of `A` on the
ideal boundary: they fix both, or exchange them. Thus in a discrete group a hyperbolic element of
small translation length forces every element that does not preserve its fixed points to have
commutator trace far from `2`. This is a standard input for collar and Margulis-type estimates
in Fuchsian groups. For parabolic `A` the corresponding statement is Shimizu's lemma,
`Subgroup.inv_le_abs_apply_one_zero_of_upperRightHom_mem`.

The proof is Jørgensen's. Conjugate `A` to the dilation `D = diag(u, u⁻¹)`, `u = exp (s / 2)`
(`TauCeti.UpperHalfPlane.exists_eq_conj_dilation_of_two_lt_abs_trace`). For `B = !![a, b; c, d]`
one has `tr² D - 4 = (u - u⁻¹)²` and `tr [D, B] - 2 = -(u - u⁻¹)² b c`, so the inequality reads
`(u - u⁻¹)² (1 + |b c|) ≥ 1`. If it fails, the iteration `B₀ = B`, `Bₙ₊₁ = Bₙ D Bₙ⁻¹` stays in `Γ`
and the products `βₙ = bₙ cₙ` satisfy `βₙ₊₁ = -(1 + βₙ) βₙ (u - u⁻¹)²`, so they tend to `0`
geometrically. Conjugating `Bₙ₊₁` by a suitable power of `D` balances its two off-diagonal
entries, and the resulting elements of `Γ` converge to `D`. Discreteness makes one of them equal
to `D`, so some `Bₙ₊₁` is diagonal. Running the iteration backwards, `B` is diagonal or
antidiagonal, which is to say `B D B⁻¹ = D^{±1}`.

## Main results

* `Subgroup.one_le_four_mul_sinh_sq_mul_of_dilation_mem`: Jørgensen's inequality for the
  dilation `z ↦ exp s * z`, in coordinates.
* `Subgroup.one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two`: Jørgensen's
  inequality for a hyperbolic element, in trace form.

## References

* Troels Jørgensen, *On discrete groups of Möbius transformations*, American Journal of
  Mathematics 98 (1976), 739–749.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §5.4.
-/

public section

open Filter Matrix MulAction
open scoped MatrixGroups Pointwise Topology commutatorElement

namespace Subgroup

open Matrix.SpecialLinearGroup (dilation dilation_inv dilation_zpow)

attribute [local simp] Matrix.adjugate_fin_two

/-! ### Conjugates of a dilation -/

private theorem conj_dilation_apply_zero_zero (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 0 0 =
      Real.exp (s / 2) + (Real.exp (s / 2) - Real.exp (-(s / 2))) * (X 0 1 * X 1 0) := by
  have h := X.fin_two_mul_sub_mul_eq_one
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination Real.exp (s / 2) * h

private theorem conj_dilation_apply_zero_one (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 0 1 = X 0 0 * X 0 1 * (Real.exp (-(s / 2)) - Real.exp (s / 2)) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem conj_dilation_apply_one_zero (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 1 0 = X 1 0 * X 1 1 * (Real.exp (s / 2) - Real.exp (-(s / 2))) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem conj_dilation_apply_one_one (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 1 1 =
      Real.exp (-(s / 2)) - (Real.exp (s / 2) - Real.exp (-(s / 2))) * (X 0 1 * X 1 0) := by
  have h := X.fin_two_mul_sub_mul_eq_one
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination Real.exp (-(s / 2)) * h

private theorem exp_half_mul (r : ℝ) :
    Real.exp (r / 2) * Real.exp (r / 2) = Real.exp r ∧
      Real.exp (-(r / 2)) * Real.exp (-(r / 2)) = Real.exp (-r) ∧
      Real.exp (r / 2) * Real.exp (-(r / 2)) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [← Real.exp_add]
  · rw [add_halves]
  · rw [← neg_add, add_halves]
  · rw [add_neg_cancel, Real.exp_zero]

/-- Conjugation by a dilation rescales the two off-diagonal entries inversely. -/
private theorem dilation_conj_apply (r : ℝ) (X : SL(2, ℝ)) :
    (dilation r * X * (dilation r)⁻¹) 0 0 = X 0 0 ∧
      (dilation r * X * (dilation r)⁻¹) 0 1 = Real.exp r * X 0 1 ∧
      (dilation r * X * (dilation r)⁻¹) 1 0 = Real.exp (-r) * X 1 0 ∧
      (dilation r * X * (dilation r)⁻¹) 1 1 = X 1 1 := by
  obtain ⟨hr, hr', h1⟩ := exp_half_mul r
  simp only [dilation_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_dilation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, neg_neg, neg_div]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination X 0 0 * h1
  · linear_combination X 0 1 * hr
  · linear_combination X 1 0 * hr'
  · linear_combination X 1 1 * h1

/-- A matrix of `SL(2, ℝ)` that is diagonal or antidiagonal conjugates the dilation `D` to `D` or
to `D⁻¹`: it fixes or exchanges the fixed points `0` and `∞` of `D`. -/
private theorem conj_dilation_eq_of_diag_or_antidiag (s : ℝ) {X : SL(2, ℝ)}
    (hX : (X 0 1 = 0 ∧ X 1 0 = 0) ∨ (X 0 0 = 0 ∧ X 1 1 = 0)) :
    (X : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (X : PSL(2, ℝ))⁻¹ = (dilation s : PSL(2, ℝ)) ∨
      (X : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (X : PSL(2, ℝ))⁻¹ =
        (dilation (-s) : PSL(2, ℝ)) := by
  simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  have h := X.fin_two_mul_sub_mul_eq_one
  rcases hX with ⟨hb, hc⟩ | ⟨ha, hd⟩
  · refine Or.inl (congrArg _ (Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ ?_))
    fin_cases i <;> fin_cases j <;>
      simp [conj_dilation_apply_zero_zero, conj_dilation_apply_zero_one,
        conj_dilation_apply_one_zero, conj_dilation_apply_one_one, hb, hc]
  · have hbc : X 0 1 * X 1 0 = -1 := by
      rw [ha, zero_mul] at h
      linarith
    refine Or.inr (congrArg _ (Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ ?_))
    fin_cases i <;> fin_cases j <;>
      simp [conj_dilation_apply_zero_zero, conj_dilation_apply_zero_one,
        conj_dilation_apply_one_zero, conj_dilation_apply_one_one, ha, hd, hbc, neg_div]

/-- If `X D X⁻¹` is diagonal for a nontrivial dilation `D`, then `X` is diagonal or antidiagonal. -/
private theorem diag_or_antidiag_of_conj_dilation {s : ℝ} (hs : s ≠ 0) {X : SL(2, ℝ)}
    (h01 : (X * dilation s * X⁻¹) 0 1 = 0) (h10 : (X * dilation s * X⁻¹) 1 0 = 0) :
    (X 0 1 = 0 ∧ X 1 0 = 0) ∨ (X 0 0 = 0 ∧ X 1 1 = 0) := by
  have huv : Real.exp (s / 2) - Real.exp (-(s / 2)) ≠ 0 := by
    rw [sub_ne_zero, Ne, Real.exp_eq_exp]
    intro h
    exact hs (by linarith)
  rw [conj_dilation_apply_zero_one] at h01
  rw [conj_dilation_apply_one_zero] at h10
  have hab : X 0 0 * X 0 1 = 0 :=
    (mul_eq_zero.1 h01).resolve_right fun h ↦ huv (by linear_combination -h)
  have hcd : X 1 0 * X 1 1 = 0 := (mul_eq_zero.1 h10).resolve_right huv
  have h := X.fin_two_mul_sub_mul_eq_one
  rcases mul_eq_zero.1 hab with ha | hb
  · have hc : X 1 0 ≠ 0 := by
      rintro hc
      rw [ha, hc] at h
      simp at h
    exact Or.inr ⟨ha, (mul_eq_zero.1 hcd).resolve_left hc⟩
  · have hd : X 1 1 ≠ 0 := by
      rintro hd
      rw [hb, hd] at h
      simp at h
    exact Or.inl ⟨hb, (mul_eq_zero.1 hcd).resolve_right hd⟩

/-! ### Jørgensen's iteration -/

/-- Jørgensen's iteration `X ↦ X A X⁻¹` starting from `B`. -/
private noncomputable def iter (A B : SL(2, ℝ)) : ℕ → SL(2, ℝ)
  | 0 => B
  | n + 1 => iter A B n * A * (iter A B n)⁻¹

private theorem iter_succ (A B : SL(2, ℝ)) (n : ℕ) :
    iter A B (n + 1) = iter A B n * A * (iter A B n)⁻¹ := rfl

private theorem iter_mem {Γ : Subgroup PSL(2, ℝ)} {A B : SL(2, ℝ)} (hA : (A : PSL(2, ℝ)) ∈ Γ)
    (hB : (B : PSL(2, ℝ)) ∈ Γ) (n : ℕ) : ((iter A B n : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
  induction n with
  | zero => exact hB
  | succ n ih =>
      rw [iter_succ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact Γ.mul_mem (Γ.mul_mem ih hA) (Γ.inv_mem ih)

/-- The off-diagonal products `βₙ` of the iteration satisfy `βₙ₊₁ = -(1 + βₙ) βₙ (u - u⁻¹)²`. -/
private theorem iter_succ_mul (s : ℝ) (B : SL(2, ℝ)) (n : ℕ) :
    iter (dilation s) B (n + 1) 0 1 * iter (dilation s) B (n + 1) 1 0 =
      -((1 + iter (dilation s) B n 0 1 * iter (dilation s) B n 1 0) *
        (iter (dilation s) B n 0 1 * iter (dilation s) B n 1 0) *
          (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2) := by
  have h := (iter (dilation s) B n).fin_two_mul_sub_mul_eq_one
  rw [iter_succ, conj_dilation_apply_zero_one, conj_dilation_apply_one_zero]
  linear_combination (-(Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 *
    (iter (dilation s) B n 0 1 * iter (dilation s) B n 1 0)) * h

/-- If `t (1 + |β₀|) ≤ 1`, where `t = (u - u⁻¹)²`, the products `βₙ` decay geometrically with
ratio `t (1 + |β₀|)`. -/
private theorem abs_iter_mul_le (s : ℝ) (B : SL(2, ℝ))
    (hμ : (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|) ≤ 1) (n : ℕ) :
    |iter (dilation s) B n 0 1 * iter (dilation s) B n 1 0| ≤
      ((Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|)) ^ n *
        |B 0 1 * B 1 0| := by
  set t := (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2
  set μ := t * (1 + |B 0 1 * B 1 0|)
  have ht0 : 0 ≤ t := sq_nonneg _
  have hμ0 : 0 ≤ μ := by positivity
  induction n with
  | zero => simp [iter]
  | succ n ih =>
      set β := iter (dilation s) B n 0 1 * iter (dilation s) B n 1 0
      have hβ : |β| ≤ |B 0 1 * B 1 0| :=
        ih.trans (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hμ0 hμ))
      have h1 : |1 + β| ≤ 1 + |B 0 1 * B 1 0| :=
        (abs_add_le 1 β).trans (by rw [abs_one]; linarith)
      rw [iter_succ_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg ht0]
      calc |1 + β| * |β| * t = t * |1 + β| * |β| := by ring
        _ ≤ t * (1 + |B 0 1 * B 1 0|) * (μ ^ n * |B 0 1 * B 1 0|) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 ht0) ih (abs_nonneg _) (by positivity)
        _ = μ ^ (n + 1) * |B 0 1 * B 1 0| := by ring

/-! ### Balancing the off-diagonal entries -/

/-- For `s > 0`, conjugating a matrix of `SL(2, ℝ)` by a suitable power of `dilation s` makes both
of its off-diagonal entries at most `exp s * ρ` in absolute value, as soon as their product is at
most `ρ ^ 2`. -/
private theorem exists_dilation_conj_le {s : ℝ} (hs : 0 < s) {X : SL(2, ℝ)} {ρ : ℝ} (hρ : 0 < ρ)
    (hX : |X 0 1 * X 1 0| ≤ ρ ^ 2) :
    ∃ k : ℤ, |(dilation (k * s) * X * (dilation (k * s))⁻¹) 0 1| ≤ Real.exp s * ρ ∧
      |(dilation (k * s) * X * (dilation (k * s))⁻¹) 1 0| ≤ Real.exp s * ρ := by
  simp only [(dilation_conj_apply _ _).2.1, (dilation_conj_apply _ _).2.2.1]
  generalize X 0 1 = x, X 1 0 = y at hX ⊢
  have hes : 1 ≤ Real.exp s := Real.one_le_exp hs.le
  have hρle : ρ ≤ Real.exp s * ρ := le_mul_of_one_le_left hρ.le hes
  rw [abs_mul] at hX
  by_cases hy : y = 0
  · by_cases hx : x = 0
    · exact ⟨0, by rw [hx, mul_zero, abs_zero]; positivity,
        by rw [hy, mul_zero, abs_zero]; positivity⟩
    -- make the first entry small: `k s ≤ log ρ - log |x|`
    have hx0 : 0 < |x| := abs_pos.2 hx
    refine ⟨⌊(Real.log ρ - Real.log |x|) / s⌋, ?_, by rw [hy, mul_zero, abs_zero]; positivity⟩
    have hk : (⌊(Real.log ρ - Real.log |x|) / s⌋ : ℝ) * s ≤ Real.log ρ - Real.log |x| :=
      (le_div_iff₀ hs).1 (Int.floor_le _)
    rw [abs_mul, Real.abs_exp]
    calc Real.exp (⌊(Real.log ρ - Real.log |x|) / s⌋ * s) * |x|
        ≤ Real.exp (Real.log ρ - Real.log |x|) * |x| :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hk) (abs_nonneg _)
      _ = ρ := by rw [Real.exp_sub, Real.exp_log hρ, Real.exp_log hx0]; field_simp
      _ ≤ Real.exp s * ρ := hρle
  -- make the second entry small: `log |y| - log ρ ≤ k s < log |y| - log ρ + s`
  have hy0 : 0 < |y| := abs_pos.2 hy
  set m := (Real.log |y| - Real.log ρ) / s
  refine ⟨⌈m⌉, ?_, ?_⟩
  · have hk : (⌈m⌉ : ℝ) * s ≤ Real.log |y| - Real.log ρ + s := by
      have := (Int.ceil_lt_add_one m).le
      rw [← le_div_iff₀ hs]
      calc (⌈m⌉ : ℝ) ≤ m + 1 := this
        _ = (Real.log |y| - Real.log ρ + s) / s := by rw [add_div, div_self hs.ne']
    rw [abs_mul, Real.abs_exp]
    calc Real.exp (⌈m⌉ * s) * |x| ≤ Real.exp (Real.log |y| - Real.log ρ + s) * |x| :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hk) (abs_nonneg _)
      _ = Real.exp s * (|x| * |y|) / ρ := by
          rw [Real.exp_add, Real.exp_sub, Real.exp_log hy0, Real.exp_log hρ]
          field_simp
      _ ≤ Real.exp s * ρ ^ 2 / ρ := by gcongr
      _ = Real.exp s * ρ := by field_simp
  · have hk : Real.log |y| - Real.log ρ ≤ (⌈m⌉ : ℝ) * s :=
      (div_le_iff₀ hs).1 (Int.le_ceil m)
    rw [abs_mul, Real.abs_exp]
    calc Real.exp (-(⌈m⌉ * s)) * |y| ≤ Real.exp (-(Real.log |y| - Real.log ρ)) * |y| :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hk)) (abs_nonneg _)
      _ = ρ := by
          rw [neg_sub, Real.exp_sub, Real.exp_log hy0, Real.exp_log hρ]
          field_simp
      _ ≤ Real.exp s * ρ := hρle

/-! ### Jørgensen's inequality -/

variable {Γ : Subgroup PSL(2, ℝ)} {s : ℝ} {B : SL(2, ℝ)}

/-- If the diagonal entries of a sequence of matrices of `SL(2, ℝ)` converge to those of a diagonal
matrix `D` and the products of its off-diagonal entries tend to `0`, then conjugating each term by a
suitable power of `dilation s`, `s > 0`, gives a sequence converging to `D`. -/
private theorem exists_tendsto_dilation_conj (hs : 0 < s) {M : ℕ → SL(2, ℝ)} {D : SL(2, ℝ)}
    (h00 : Tendsto (fun n ↦ M n 0 0) atTop (𝓝 (D 0 0)))
    (h11 : Tendsto (fun n ↦ M n 1 1) atTop (𝓝 (D 1 1))) (hD01 : D 0 1 = 0) (hD10 : D 1 0 = 0)
    (hβ : Tendsto (fun n ↦ M n 0 1 * M n 1 0) atTop (𝓝 0)) :
    ∃ k : ℕ → ℤ, Tendsto (fun n ↦ dilation (k n * s) * M n * (dilation (k n * s))⁻¹) atTop
      (𝓝 D) := by
  -- the radius `ρₙ = √|βₙ| + 1 / (n + 1)` bounds the balanced off-diagonal entries
  set ρ : ℕ → ℝ := fun n ↦ √|M n 0 1 * M n 1 0| + 1 / ((n : ℝ) + 1)
  have hρ0 (n : ℕ) : 0 < ρ n := by positivity
  have hρsq (n : ℕ) : |M n 0 1 * M n 1 0| ≤ ρ n ^ 2 := by
    have h := Real.sq_sqrt (abs_nonneg (M n 0 1 * M n 1 0))
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    nlinarith [Real.sqrt_nonneg |M n 0 1 * M n 1 0|]
  have hρ : Tendsto (fun n ↦ Real.exp s * ρ n) atTop (𝓝 0) := by
    have habs := hβ.abs
    rw [abs_zero] at habs
    have h := ((Real.continuous_sqrt.tendsto 0).comp habs).add
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.sqrt_zero, zero_add] at h
    have h' := h.const_mul (Real.exp s)
    rw [mul_zero] at h'
    exact h'
  choose k hk using fun n ↦ exists_dilation_conj_le hs (hρ0 n) (hρsq n)
  set C : ℕ → SL(2, ℝ) := fun n ↦ dilation (k n * s) * M n * (dilation (k n * s))⁻¹
  have h01 : Tendsto (fun n ↦ C n 0 1) atTop (𝓝 (D 0 1)) := by
    rw [hD01]
    refine squeeze_zero_norm (fun n ↦ ?_) hρ
    simpa only [C, Real.norm_eq_abs] using (hk n).1
  have h10 : Tendsto (fun n ↦ C n 1 0) atTop (𝓝 (D 1 0)) := by
    rw [hD10]
    refine squeeze_zero_norm (fun n ↦ ?_) hρ
    simpa only [C, Real.norm_eq_abs] using (hk n).2
  have hmat : Tendsto (fun n ↦ ((C n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) atTop
      (𝓝 (D : Matrix (Fin 2) (Fin 2) ℝ)) := by
    refine tendsto_pi_nhds.mpr (Fin.forall_fin_two.mpr ⟨tendsto_pi_nhds.mpr
      (Fin.forall_fin_two.mpr ⟨?_, h01⟩),
      tendsto_pi_nhds.mpr (Fin.forall_fin_two.mpr ⟨h10, ?_⟩)⟩)
    · simpa only [C, (dilation_conj_apply _ _).1] using h00
    · simpa only [C, (dilation_conj_apply _ _).2.2.2] using h11
  exact ⟨k, Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.tendsto_nhds_iff.mpr hmat⟩

/-- **Convergence.** If Jørgensen's inequality fails for the dilation `D` with `s > 0`, some
iterate `Bₙ₊₁` is diagonal: suitable conjugates of the iterates by powers of `D` converge to `D`
inside the discrete group `Γ`, so one of them is `±D`. -/
private theorem exists_iter_diag [DiscreteTopology Γ] (hs : 0 < s)
    (hD : (dilation s : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hlt : (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|) < 1) :
    ∃ n, iter (dilation s) B (n + 1) 0 1 = 0 ∧ iter (dilation s) B (n + 1) 1 0 = 0 := by
  set J := iter (dilation s) B
  -- the products `βₙ` of the off-diagonal entries tend to `0` geometrically
  have hβ : Tendsto (fun n ↦ J n 0 1 * J n 1 0) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ abs_iter_mul_le s B hlt.le n) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt).mul_const
      |B 0 1 * B 1 0|
  have h00 : Tendsto (fun n ↦ J (n + 1) 0 0) atTop (𝓝 ((dilation s : SL(2, ℝ)) 0 0)) := by
    simp only [J, iter_succ, conj_dilation_apply_zero_zero]
    simpa using tendsto_const_nhds.add (hβ.const_mul _)
  have h11 : Tendsto (fun n ↦ J (n + 1) 1 1) atTop (𝓝 ((dilation s : SL(2, ℝ)) 1 1)) := by
    simp only [J, iter_succ, conj_dilation_apply_one_one]
    simpa using tendsto_const_nhds.sub (hβ.const_mul _)
  obtain ⟨k, hk⟩ := exists_tendsto_dilation_conj hs h00 h11 (by simp) (by simp)
    ((tendsto_add_atTop_iff_nat 1).2 hβ)
  -- the conjugates lie in `Γ`, so by discreteness one of them is `±D`
  have hCmem (n : ℕ) :
      ((dilation (k n * s) * J (n + 1) * (dilation (k n * s))⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
    have hDk : ((dilation (k n * s) : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
      rw [← dilation_zpow, QuotientGroup.mk_zpow]
      exact Γ.zpow_mem hD _
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact Γ.mul_mem (Γ.mul_mem hDk (iter_mem hD hB _)) (Γ.inv_mem hDk)
  have hcont : Continuous (fun a : SL(2, ℝ) ↦ (a : PSL(2, ℝ))) := continuous_quot_mk
  have hconv : Tendsto (fun n ↦ (⟨_, hCmem n⟩ : Γ)) atTop (𝓝 (⟨_, hD⟩ : Γ)) :=
    tendsto_subtype_rng.mpr <| (hcont.tendsto _).comp hk
  rw [nhds_discrete, tendsto_pure] at hconv
  obtain ⟨n, hn⟩ := hconv.exists
  replace hn := congrArg Subtype.val hn
  rw [QuotientGroup.eq, Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one,
    inv_mul_eq_one, inv_mul_eq_iff_eq_mul, mul_neg_one] at hn
  have hoff : (dilation (k n * s) * J (n + 1) * (dilation (k n * s))⁻¹) 0 1 = 0 ∧
      (dilation (k n * s) * J (n + 1) * (dilation (k n * s))⁻¹) 1 0 = 0 := by
    rcases hn with h | h
    · rw [h]
      simp
    · have h01 := congrArg (fun M : SL(2, ℝ) ↦ M 0 1) h
      have h10 := congrArg (fun M : SL(2, ℝ) ↦ M 1 0) h
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at h01 h10
      have hd01 : (dilation s : SL(2, ℝ)) 0 1 = 0 := by simp
      have hd10 : (dilation s : SL(2, ℝ)) 1 0 = 0 := by simp
      exact ⟨by linarith, by linarith⟩
  simp only [(dilation_conj_apply _ _).2.1, (dilation_conj_apply _ _).2.2.1, mul_eq_zero,
    Real.exp_ne_zero, false_or] at hoff
  exact ⟨n, hoff⟩

/-- **Jørgensen's inequality for a dilation, failing case.** If `Γ` is discrete, contains the
dilation `D = dilation s` with `s > 0` and the class of `B`, and `(u - u⁻¹)² (1 + |b c|) < 1`, then
`B` is diagonal or antidiagonal. -/
private theorem diag_or_antidiag_of_lt [DiscreteTopology Γ] (hs : 0 < s)
    (hD : (dilation s : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hlt : (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|) < 1) :
    (B 0 1 = 0 ∧ B 1 0 = 0) ∨ (B 0 0 = 0 ∧ B 1 1 = 0) := by
  obtain ⟨n, hn⟩ := exists_iter_diag hs hD hB hlt
  -- run the iteration backwards: a diagonal `Bₙ₊₁` has a diagonal or antidiagonal predecessor,
  -- and an iterate `Bₙ₊₁`, a conjugate of `D`, has trace `u + u⁻¹ ≠ 0`, so is not antidiagonal
  induction n with
  | zero =>
      rw [iter_succ] at hn
      exact diag_or_antidiag_of_conj_dilation hs.ne' hn.1 hn.2
  | succ n ih =>
      rw [iter_succ (n := n + 1)] at hn
      have hprev := diag_or_antidiag_of_conj_dilation hs.ne' hn.1 hn.2
      refine ih (hprev.resolve_right fun ⟨ha, hd⟩ ↦ ?_)
      rw [iter_succ, conj_dilation_apply_zero_zero] at ha
      rw [iter_succ, conj_dilation_apply_one_one] at hd
      have := Real.exp_pos (s / 2)
      have := Real.exp_pos (-(s / 2))
      linarith

/-- **Jørgensen's inequality for a dilation.** Let `Γ ≤ PSL(2, ℝ)` be discrete and contain the
dilation `z ↦ exp s * z`, `s ≠ 0`, and the class of `B = !![a, b; c, d] ∈ SL(2, ℝ)`. Unless `B`
conjugates this dilation to itself or to its inverse, `4 sinh² (s / 2) (1 + |b c|) ≥ 1`. -/
theorem one_le_four_mul_sinh_sq_mul_of_dilation_mem [DiscreteTopology Γ] (hs : s ≠ 0)
    (hD : (dilation s : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (h₁ : (B : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (B : PSL(2, ℝ))⁻¹ ≠ dilation s)
    (h₂ : (B : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (B : PSL(2, ℝ))⁻¹ ≠ dilation (-s)) :
    1 ≤ 4 * Real.sinh (s / 2) ^ 2 * (1 + |B 0 1 * B 1 0|) := by
  by_contra hlt
  rw [not_le] at hlt
  have hsq (r : ℝ) : 4 * Real.sinh (r / 2) ^ 2 = (Real.exp (r / 2) - Real.exp (-(r / 2))) ^ 2 := by
    rw [Real.sinh_eq]
    ring
  have hB' : (B 0 1 = 0 ∧ B 1 0 = 0) ∨ (B 0 0 = 0 ∧ B 1 1 = 0) := by
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · refine diag_or_antidiag_of_lt (s := -s) (neg_pos.2 hneg) ?_ hB ?_
      · rw [← dilation_inv, QuotientGroup.mk_inv]
        exact Γ.inv_mem hD
      · rwa [← hsq, neg_div, Real.sinh_neg, neg_sq]
    · exact diag_or_antidiag_of_lt hpos hD hB (by rwa [← hsq])
  rcases conj_dilation_eq_of_diag_or_antidiag s hB' with h | h
  exacts [h₁ h, h₂ h]

/-! ### The trace form -/

private theorem trace_dilation (s : ℝ) :
    ((dilation s : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      Real.exp (s / 2) + Real.exp (-(s / 2)) := by
  simp [Matrix.trace_fin_two]

private theorem trace_commutatorElement_dilation (s : ℝ) (X : SL(2, ℝ)) :
    ((⁅dilation s, X⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      2 - (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (X 0 1 * X 1 0) := by
  have h := X.fin_two_mul_sub_mul_eq_one
  obtain ⟨hu, hv, huv⟩ := exp_half_mul s
  obtain ⟨h00, h01, h10, h11⟩ := dilation_conj_apply s X
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul _ X⁻¹, Matrix.trace_fin_two,
    Matrix.SpecialLinearGroup.coe_inv]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, h00, h01, h10, h11]
  linear_combination 2 * h + X 0 1 * X 1 0 * hu + X 0 1 * X 1 0 * hv -
    2 * (X 0 1 * X 1 0) * huv

/-- The two traces in Jørgensen's inequality, for `A` with the same class in `PSL(2, ℝ)` as the
conjugate `P D P⁻¹` of a dilation `D`, in terms of the entries of `X = P⁻¹ B P`. -/
private theorem abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_eq
    {A B P : SL(2, ℝ)} {s : ℝ}
    (hA : (A : PSL(2, ℝ)) = ((P * dilation s * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ))) :
    |(A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4| +
        |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| =
      4 * Real.sinh (s / 2) ^ 2 * (1 + |(P⁻¹ * B * P) 0 1 * (P⁻¹ * B * P) 1 0|) := by
  have hsq : 4 * Real.sinh (s / 2) ^ 2 = (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 := by
    rw [Real.sinh_eq]
    ring
  have trace_conj (M : SL(2, ℝ)) : ((P * M * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      (M : Matrix (Fin 2) (Fin 2) ℝ).trace := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  -- `A` is `± P D P⁻¹` in `SL(2, ℝ)`
  rw [QuotientGroup.eq, Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one,
    inv_mul_eq_one, inv_mul_eq_iff_eq_mul, mul_neg_one] at hA
  replace hA : A = P * dilation s * P⁻¹ ∨ A = -(P * dilation s * P⁻¹) :=
    hA.imp id fun h ↦ by rw [h, neg_neg]
  have htrA : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4 =
      (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 := by
    have h2 : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 =
        (Real.exp (s / 2) + Real.exp (-(s / 2))) ^ 2 := by
      rcases hA with h | h
      · rw [h, trace_conj, trace_dilation]
      · rw [h, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, neg_sq, trace_conj,
          trace_dilation]
    rw [h2]
    linear_combination 4 * (exp_half_mul s).2.2
  have hcomm : ⁅A, B⁆ = P * ⁅dilation s, P⁻¹ * B * P⁆ * P⁻¹ := by
    have h : ⁅P * dilation s * P⁻¹, B⁆ = P * ⁅dilation s, P⁻¹ * B * P⁆ * P⁻¹ := by
      simp only [commutatorElement_def]
      group
    rcases hA with hA' | hA'
    · rw [hA', h]
    · rw [hA', ← h]
      simp [commutatorElement_def]
  rw [htrA, hcomm, trace_conj, trace_commutatorElement_dilation, sub_sub_cancel_left, abs_neg,
    abs_mul, abs_sq, ← hsq]
  ring

/-- **Jørgensen's inequality for hyperbolic elements.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup
and let `A, B ∈ SL(2, ℝ)` lift elements of `Γ`, with `A` hyperbolic: `|tr A| > 2`. Unless `B`
conjugates the class of `A` to itself or to its inverse, that is, unless `B` fixes or exchanges
the two fixed points of `A` on the ideal boundary,
`|tr² A - 4| + |tr [A, B] - 2| ≥ 1`. -/
theorem one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two
    [DiscreteTopology Γ] {A : SL(2, ℝ)} (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hhyp : 2 < |(A : Matrix (Fin 2) (Fin 2) ℝ).trace|)
    (h₁ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ A)
    (h₂ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ (A : PSL(2, ℝ))⁻¹) :
    1 ≤ |(A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4| +
      |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| := by
  obtain ⟨g, s, hs, hAg⟩ := TauCeti.UpperHalfPlane.exists_eq_conj_dilation_of_two_lt_abs_trace hhyp
  obtain ⟨P, rfl⟩ := QuotientGroup.mk_surjective g
  -- move to the frame where `A` is the dilation: `X = P⁻¹ B P` and `Γ' = P⁻¹ Γ P`
  set X : SL(2, ℝ) := P⁻¹ * B * P with hX
  have hXcoe : (X : PSL(2, ℝ)) = (P : PSL(2, ℝ))⁻¹ * B * P := by
    rw [hX, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  set Γ' : Subgroup PSL(2, ℝ) := ConjAct.toConjAct (P : PSL(2, ℝ))⁻¹ • Γ
  have : DiscreteTopology Γ' := TauCeti.discreteTopology_of_conjAct_smul_eq rfl
  have hmem (x : PSL(2, ℝ)) (hx : x ∈ Γ) : (P : PSL(2, ℝ))⁻¹ * x * P ∈ Γ' := by
    have := Subgroup.smul_mem_pointwise_smul x (ConjAct.toConjAct (P : PSL(2, ℝ))⁻¹) Γ hx
    rwa [ConjAct.toConjAct_smul, inv_inv] at this
  have hD : (dilation s : PSL(2, ℝ)) ∈ Γ' := by
    have := hmem _ hA
    rwa [hAg, show (P : PSL(2, ℝ))⁻¹ * (P * (dilation s : PSL(2, ℝ)) * (P : PSL(2, ℝ))⁻¹) * P =
      dilation s by group] at this
  have hXmem : (X : PSL(2, ℝ)) ∈ Γ' := hXcoe ▸ hmem _ hB
  -- the exceptional cases correspond under the change of frame
  have hconj (y : PSL(2, ℝ))
      (hy : (X : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (X : PSL(2, ℝ))⁻¹ = y) :
      (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ = P * y * (P : PSL(2, ℝ))⁻¹ := by
    rw [← hy, hXcoe, hAg]
    group
  have h₁' : (X : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (X : PSL(2, ℝ))⁻¹ ≠ dilation s :=
    fun h ↦ h₁ ((hconj _ h).trans hAg.symm)
  have h₂' : (X : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (X : PSL(2, ℝ))⁻¹ ≠ dilation (-s) := by
    refine fun h ↦ h₂ ((hconj _ h).trans ?_)
    rw [hAg, ← dilation_inv, QuotientGroup.mk_inv]
    group
  have hAD : (A : PSL(2, ℝ)) = ((P * dilation s * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) := by
    rw [hAg, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_eq hAD]
  exact one_le_four_mul_sinh_sq_mul_of_dilation_mem hs hD hXmem h₁' h₂'

end Subgroup
