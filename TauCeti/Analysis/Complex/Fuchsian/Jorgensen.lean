/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Datum
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.Fuchsian.Shimizu
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Endpoint
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
import TauCeti.Analysis.SpecialFunctions.Exp.Half
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.GroupTheory.JorgensenSequence
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.Topology.Algebra.Matrix.SpecialLinearGroup

/-!
# Jørgensen's inequality

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup and let `A, B ∈ SL(2, ℝ)` lift elements of `Γ`.
**Jørgensen's inequality** says that unless `B` normalises `⟨A⟩` in a degenerate way,

`|tr² A - 4| + |tr [A, B] - 2| ≥ 1`.

For hyperbolic `A`, that is `|tr A| > 2`, the exceptional cases are `B A B⁻¹ = A` and
`B A B⁻¹ = A⁻¹` in `PSL(2, ℝ)`: the elements `B` preserving the pair of fixed points of `A` on
the ideal boundary, which they fix or exchange. For elliptic `A`, that is `|tr A| < 2`, the only
exceptional case is `B A B⁻¹ = A`: the elements `B` fixing the fixed point of `A` in `ℍ`. Thus in
a discrete group a hyperbolic element of small translation length, or an elliptic element of
small rotation angle, forces every element outside these exceptional cases to have commutator
trace far from `2`. This is a standard input for collar and Margulis-type estimates in Fuchsian
groups. For parabolic `A`, where `tr² A = 4`, the only exceptional case is again `B A B⁻¹ = A`:
the elements `B` fixing the fixed point of `A` on the ideal boundary. This case is Shimizu's lemma,
`Subgroup.inv_le_abs_apply_one_zero_of_upperRightHom_mem`: after conjugating `A` to the
translation `z ↦ z + w`, the trace `tr [A, B] - 2` is `w² c²`, where `c` is the lower-left entry
of the conjugated `B`. Since `A = ±1` commutes with every `B`, the three cases together give the
inequality for every pair of elements outside the exceptional cases.

The hyperbolic and elliptic proofs are Jørgensen's, and use his sequence `B₀ = B`,
`Bₙ₊₁ = Bₙ A Bₙ⁻¹` (`TauCeti.jorgensenSeq`), which stays in `Γ`.

For hyperbolic `A`, conjugate `A` to the dilation `D = diag(u, u⁻¹)`, `u = exp (s / 2)`
(`TauCeti.UpperHalfPlane.exists_eq_conj_dilation_of_two_lt_abs_trace`). For
`B = !![a, b; c, d]` one has `tr² D - 4 = (u - u⁻¹)²` and `tr [D, B] - 2 = -(u - u⁻¹)² b c`, so
the inequality reads `(u - u⁻¹)² (1 + |b c|) ≥ 1`. If it fails, the products `βₙ = bₙ cₙ` of the
iterates satisfy `βₙ₊₁ = -(1 + βₙ) βₙ (u - u⁻¹)²`, so they tend to `0` geometrically.
Conjugating `Bₙ₊₁` by a suitable power of `D` balances its two off-diagonal entries, and the
resulting elements of `Γ` converge to `D`. Discreteness makes one of them equal to `D`, so some
`Bₙ₊₁` is diagonal. Running the iteration backwards, `B` is diagonal or antidiagonal, which is to
say `B D B⁻¹ = D^{±1}`.

For elliptic `A` fixing `z ∈ ℍ`, put `κ = (4 - tr² A) / 2 > 0` and `cₙ = cosh (dist (Bₙ • z) z)`.
The point `z` is moved by `Bₙ₊₁` as far as `Bₙ⁻¹ • z` is moved by `A`, so the displacement
formula `Matrix.SpecialLinearGroup.cosh_dist_smul_of_smul_eq_self` gives
`cₙ₊₁ - 1 = κ (cₙ + 1) (cₙ - 1)`, and by
`Matrix.SpecialLinearGroup.trace_commutatorElement_of_smul_eq_self` the inequality reads
`κ (1 + c₀) ≥ 1`. If it fails and `B` does not fix `z`, the numbers `cₙ - 1 > 0` decrease
strictly, so the `Bₙ` are infinitely many distinct elements of `Γ` moving `z` a bounded distance,
contradicting proper discontinuity. No convergence argument is needed.

## Main results

* `Subgroup.one_le_four_mul_sinh_sq_mul_of_dilation_mem`: Jørgensen's inequality for the
  dilation `z ↦ exp s * z`, in coordinates.
* `one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_of_two_lt_abs_trace`, in
  the namespace `Subgroup`: Jørgensen's inequality for a hyperbolic element, in trace form.
* `Subgroup.one_le_four_sub_trace_sq_mul_cosh_sq_of_smul_eq_self`: Jørgensen's inequality for an
  elliptic element fixing `z`, in terms of the distance `B` moves `z`.
* `one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_of_abs_trace_lt_two`, in
  the namespace `Subgroup`: Jørgensen's inequality for an elliptic element, in trace form.
* `Subgroup.one_le_abs_trace_commutatorElement_sub_two_of_isParabolic`: Jørgensen's inequality for
  a parabolic element, which is Shimizu's lemma in trace form.
* `Subgroup.one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two`: Jørgensen's
  inequality for every element, in trace form.

## References

* Troels Jørgensen, *On discrete groups of Möbius transformations*, American Journal of
  Mathematics 98 (1976), 739–749.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §5.4.
-/

public section

open Filter Matrix MulAction
open scoped MatrixGroups OnePoint Pointwise Topology commutatorElement UpperHalfPlane

namespace Subgroup

open TauCeti (jorgensenSeq jorgensenSeq_zero jorgensenSeq_succ jorgensenSeq_mem
  map_jorgensenSeq)
open Matrix.ProjectiveSpecialLinearGroup (parabolicFixedPoint upperRightHom upperRightHom_apply
  mk_eq_mk_iff mk_smul_infty_eq_infty_iff mk_inv_mul_mul)
open Matrix.SpecialLinearGroup (dilation dilation_inv dilation_zpow conj_dilation_apply_zero_zero
  conj_dilation_apply_zero_one conj_dilation_apply_one_zero conj_dilation_apply_one_one
  dilation_conj_apply_zero_zero dilation_conj_apply_zero_one dilation_conj_apply_one_zero
  dilation_conj_apply_one_one diag_or_antidiag_of_conj_dilation trace_dilation
  trace_commutatorElement_dilation exists_tendsto_dilation_conj trace_mul_mul_inv)

attribute [local simp] Matrix.adjugate_fin_two

/-! ### Jørgensen's sequence for a dilation -/

/-- The off-diagonal products `βₙ` of the iteration satisfy `βₙ₊₁ = -(1 + βₙ) βₙ (u - u⁻¹)²`. -/
private theorem jorgensenSeq_succ_mul (s : ℝ) (B : SL(2, ℝ)) (n : ℕ) :
    jorgensenSeq (dilation s) B (n + 1) 0 1 * jorgensenSeq (dilation s) B (n + 1) 1 0 =
      -((1 + jorgensenSeq (dilation s) B n 0 1 * jorgensenSeq (dilation s) B n 1 0) *
        (jorgensenSeq (dilation s) B n 0 1 * jorgensenSeq (dilation s) B n 1 0) *
          (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2) := by
  have h := (jorgensenSeq (dilation s) B n).fin_two_mul_sub_mul_eq_one
  rw [jorgensenSeq_succ, conj_dilation_apply_zero_one, conj_dilation_apply_one_zero]
  linear_combination (-(Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 *
    (jorgensenSeq (dilation s) B n 0 1 * jorgensenSeq (dilation s) B n 1 0)) * h

/-- If `t (1 + |β₀|) ≤ 1`, where `t = (u - u⁻¹)²`, the products `βₙ` decay geometrically with
ratio `t (1 + |β₀|)`. -/
private theorem abs_jorgensenSeq_mul_le (s : ℝ) (B : SL(2, ℝ))
    (hμ : (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|) ≤ 1) (n : ℕ) :
    |jorgensenSeq (dilation s) B n 0 1 * jorgensenSeq (dilation s) B n 1 0| ≤
      ((Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|)) ^ n *
        |B 0 1 * B 1 0| := by
  set t := (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2
  set μ := t * (1 + |B 0 1 * B 1 0|)
  have ht0 : 0 ≤ t := sq_nonneg _
  have hμ0 : 0 ≤ μ := by positivity
  induction n with
  | zero => simp
  | succ n ih =>
      set β := jorgensenSeq (dilation s) B n 0 1 * jorgensenSeq (dilation s) B n 1 0
      have hβ : |β| ≤ |B 0 1 * B 1 0| :=
        ih.trans (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hμ0 hμ))
      have h1 : |1 + β| ≤ 1 + |B 0 1 * B 1 0| :=
        (abs_add_le 1 β).trans (by rw [abs_one]; linarith)
      rw [jorgensenSeq_succ_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg ht0]
      calc |1 + β| * |β| * t = t * |1 + β| * |β| := by ring
        _ ≤ t * (1 + |B 0 1 * B 1 0|) * (μ ^ n * |B 0 1 * B 1 0|) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 ht0) ih (abs_nonneg _) (by positivity)
        _ = μ ^ (n + 1) * |B 0 1 * B 1 0| := by ring

/-! ### Jørgensen's inequality -/

variable {Γ : Subgroup PSL(2, ℝ)} {s : ℝ} {B : SL(2, ℝ)}

/-- **Convergence.** If Jørgensen's inequality fails for the dilation `D` with `s > 0`, some
iterate `Bₙ₊₁` is diagonal: suitable conjugates of the iterates by powers of `D` converge to `D`
inside the discrete group `Γ`, so one of them is `±D`. -/
private theorem exists_jorgensenSeq_diag [DiscreteTopology Γ] (hs : 0 < s)
    (hD : (dilation s : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hlt : (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|) < 1) :
    ∃ n, jorgensenSeq (dilation s) B (n + 1) 0 1 = 0 ∧
      jorgensenSeq (dilation s) B (n + 1) 1 0 = 0 := by
  set J := jorgensenSeq (dilation s) B
  -- the products `βₙ` of the off-diagonal entries tend to `0` geometrically
  have hβ : Tendsto (fun n ↦ J n 0 1 * J n 1 0) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ abs_jorgensenSeq_mul_le s B hlt.le n) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt).mul_const
      |B 0 1 * B 1 0|
  have h00 : Tendsto (fun n ↦ J (n + 1) 0 0) atTop (𝓝 ((dilation s : SL(2, ℝ)) 0 0)) := by
    simp only [J, jorgensenSeq_succ, conj_dilation_apply_zero_zero]
    simpa using tendsto_const_nhds.add (hβ.const_mul _)
  have h11 : Tendsto (fun n ↦ J (n + 1) 1 1) atTop (𝓝 ((dilation s : SL(2, ℝ)) 1 1)) := by
    simp only [J, jorgensenSeq_succ, conj_dilation_apply_one_one]
    simpa using tendsto_const_nhds.sub (hβ.const_mul _)
  obtain ⟨k, hk⟩ := exists_tendsto_dilation_conj hs h00 h11 (by simp) (by simp)
    ((tendsto_add_atTop_iff_nat 1).2 hβ)
  -- the conjugates lie in `Γ`, so by discreteness one of them is `±D`
  have hCmem (n : ℕ) :
      ((dilation (k n * s) * J (n + 1) * dilation (-(k n * s)) : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
    have hDk : ((dilation (k n * s) : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
      rw [← dilation_zpow, QuotientGroup.mk_zpow]
      exact Γ.zpow_mem hD _
    have hJ : ((J (n + 1) : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
      rw [← QuotientGroup.mk'_apply, map_jorgensenSeq]
      exact jorgensenSeq_mem hD hB _
    simp only [← dilation_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact Γ.mul_mem (Γ.mul_mem hDk hJ) (Γ.inv_mem hDk)
  obtain ⟨n, hn⟩ := (eventually_mk_eq_of_tendsto hCmem hD hk).exists
  rw [Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff] at hn
  have hoff : (dilation (k n * s) * J (n + 1) * dilation (-(k n * s))) 0 1 = 0 ∧
      (dilation (k n * s) * J (n + 1) * dilation (-(k n * s))) 1 0 = 0 := by
    rcases hn with h | h
    · rw [← h]
      simp
    · have h01 := congrArg (fun M : SL(2, ℝ) ↦ M 0 1) h
      have h10 := congrArg (fun M : SL(2, ℝ) ↦ M 1 0) h
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at h01 h10
      have hd01 : (dilation s : SL(2, ℝ)) 0 1 = 0 := by simp
      have hd10 : (dilation s : SL(2, ℝ)) 1 0 = 0 := by simp
      exact ⟨by linarith, by linarith⟩
  simp only [dilation_conj_apply_zero_one, dilation_conj_apply_one_zero, mul_eq_zero,
    Real.exp_ne_zero, false_or] at hoff
  exact ⟨n, hoff⟩

/-- **Jørgensen's inequality for a dilation, failing case.** If `Γ` is discrete, contains the
dilation `D = dilation s` with `s > 0` and the class of `B`, and `(u - u⁻¹)² (1 + |b c|) < 1`, then
`B` is diagonal or antidiagonal. -/
private theorem diag_or_antidiag_of_lt [DiscreteTopology Γ] (hs : 0 < s)
    (hD : (dilation s : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hlt : (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (1 + |B 0 1 * B 1 0|) < 1) :
    (B 0 1 = 0 ∧ B 1 0 = 0) ∨ (B 0 0 = 0 ∧ B 1 1 = 0) := by
  obtain ⟨n, hn⟩ := exists_jorgensenSeq_diag hs hD hB hlt
  -- run the iteration backwards: a diagonal `Bₙ₊₁` has a diagonal or antidiagonal predecessor,
  -- and an iterate `Bₙ₊₁`, a conjugate of `D`, has trace `u + u⁻¹ ≠ 0`, so is not antidiagonal
  induction n with
  | zero =>
      rw [jorgensenSeq_succ, jorgensenSeq_zero] at hn
      exact diag_or_antidiag_of_conj_dilation hs.ne' hn.1 hn.2
  | succ n ih =>
      rw [jorgensenSeq_succ (n := n + 1)] at hn
      have hprev := diag_or_antidiag_of_conj_dilation hs.ne' hn.1 hn.2
      refine ih (hprev.resolve_right fun ⟨ha, hd⟩ ↦ ?_)
      rw [jorgensenSeq_succ, conj_dilation_apply_zero_zero] at ha
      rw [jorgensenSeq_succ, conj_dilation_apply_one_one] at hd
      have := Real.exp_pos (s / 2)
      have := Real.exp_pos (-(s / 2))
      linarith

/-- **Jørgensen's inequality for a dilation.** Let `Γ ≤ PSL(2, ℝ)` be discrete and contain the
dilation `z ↦ exp s * z` and the class of `B = !![a, b; c, d] ∈ SL(2, ℝ)`. Unless `B` conjugates
this dilation to itself or to its inverse, `4 sinh² (s / 2) (1 + |b c|) ≥ 1`. -/
theorem one_le_four_mul_sinh_sq_mul_of_dilation_mem [DiscreteTopology Γ]
    (hD : (dilation s : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (h₁ : (B : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (B : PSL(2, ℝ))⁻¹ ≠ dilation s)
    (h₂ : (B : PSL(2, ℝ)) * (dilation s : PSL(2, ℝ)) * (B : PSL(2, ℝ))⁻¹ ≠ dilation (-s)) :
    1 ≤ 4 * Real.sinh (s / 2) ^ 2 * (1 + |B 0 1 * B 1 0|) := by
  have hs : s ≠ 0 := by
    rintro rfl
    simp at h₁
  by_contra hlt
  rw [not_le] at hlt
  have hB' : (B 0 1 = 0 ∧ B 1 0 = 0) ∨ (B 0 0 = 0 ∧ B 1 1 = 0) := by
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · refine diag_or_antidiag_of_lt (s := -s) (neg_pos.2 hneg) ?_ hB ?_
      · rw [← dilation_inv, QuotientGroup.mk_inv]
        exact Γ.inv_mem hD
      · rwa [← Real.four_mul_sinh_half_sq, neg_div, Real.sinh_neg, neg_sq]
    · exact diag_or_antidiag_of_lt hpos hD hB (by rwa [← Real.four_mul_sinh_half_sq])
  simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h₁ h₂
  rcases hB' with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · exact h₁ (congrArg _ (Matrix.SpecialLinearGroup.conj_dilation_eq_dilation s h01 h10))
  · exact h₂ (congrArg _ (Matrix.SpecialLinearGroup.conj_dilation_eq_dilation_neg s h00 h11))

/-! ### The trace form -/

/-- The two traces in Jørgensen's inequality, for `A` with the same class in `PSL(2, ℝ)` as the
conjugate `P D P⁻¹` of a dilation `D`, in terms of the entries of `X = P⁻¹ B P`. -/
private theorem abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_eq
    {A B P : SL(2, ℝ)} {s : ℝ}
    (hA : (A : PSL(2, ℝ)) = ((P * dilation s * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ))) :
    |(A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4| +
        |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| =
      4 * Real.sinh (s / 2) ^ 2 * (1 + |(P⁻¹ * B * P) 0 1 * (P⁻¹ * B * P) 1 0|) := by
  -- `A` is `± P D P⁻¹` in `SL(2, ℝ)`
  replace hA : A = P * dilation s * P⁻¹ ∨ A = -(P * dilation s * P⁻¹) :=
    Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff.1 hA.symm
  have htrA : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4 =
      (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 := by
    have h2 : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 =
        (Real.exp (s / 2) + Real.exp (-(s / 2))) ^ 2 := by
      rcases hA with h | h
      · rw [h, trace_mul_mul_inv, trace_dilation]
      · rw [h, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, neg_sq, trace_mul_mul_inv,
          trace_dilation]
    rw [h2]
    linear_combination 4 * Real.exp_half_mul_exp_neg_half s
  have hcomm : ⁅A, B⁆ = P * ⁅dilation s, P⁻¹ * B * P⁆ * P⁻¹ := by
    have h : ⁅P * dilation s * P⁻¹, B⁆ = P * ⁅dilation s, P⁻¹ * B * P⁆ * P⁻¹ := by
      simp only [commutatorElement_def]
      group
    rcases hA with hA' | hA'
    · rw [hA', h]
    · rw [hA', ← h]
      simp [commutatorElement_def]
  rw [htrA, hcomm, trace_mul_mul_inv, trace_commutatorElement_dilation, sub_sub_cancel_left,
    abs_neg, abs_mul, abs_sq, ← Real.four_mul_sinh_half_sq]
  ring

/-- **Jørgensen's inequality for hyperbolic elements.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup
and let `A, B ∈ SL(2, ℝ)` lift elements of `Γ`, with `A` hyperbolic: `|tr A| > 2`. Unless `B`
conjugates the class of `A` to itself or to its inverse, that is, unless `B` fixes or exchanges
the two fixed points of `A` on the ideal boundary,
`|tr² A - 4| + |tr [A, B] - 2| ≥ 1`. -/
theorem one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_of_two_lt_abs_trace
    [DiscreteTopology Γ] {A : SL(2, ℝ)} (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hhyp : 2 < |(A : Matrix (Fin 2) (Fin 2) ℝ).trace|)
    (h₁ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ A)
    (h₂ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ (A : PSL(2, ℝ))⁻¹) :
    1 ≤ |(A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4| +
      |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| := by
  obtain ⟨g, s, -, hAg⟩ := TauCeti.UpperHalfPlane.exists_eq_conj_dilation_of_two_lt_abs_trace hhyp
  obtain ⟨P, rfl⟩ := QuotientGroup.mk_surjective g
  -- move to the frame where `A` is the dilation: `X = P⁻¹ B P` and `Γ' = P⁻¹ Γ P`
  set X : SL(2, ℝ) := P⁻¹ * B * P with hX
  have hXcoe : (X : PSL(2, ℝ)) = (P : PSL(2, ℝ))⁻¹ * B * P := mk_inv_mul_mul P B
  set Γ' : Subgroup PSL(2, ℝ) := ConjAct.toConjAct (P : PSL(2, ℝ))⁻¹ • Γ
  have : DiscreteTopology Γ' := TauCeti.discreteTopology_of_conjAct_smul_eq rfl
  have hD : (dilation s : PSL(2, ℝ)) ∈ Γ' := by
    have := (inv_mul_mul_mem_conjAct_smul_iff (P : PSL(2, ℝ)) _ Γ).2 hA
    rwa [hAg, show (P : PSL(2, ℝ))⁻¹ * (P * (dilation s : PSL(2, ℝ)) * (P : PSL(2, ℝ))⁻¹) * P =
      dilation s by group] at this
  have hXmem : (X : PSL(2, ℝ)) ∈ Γ' :=
    hXcoe ▸ (inv_mul_mul_mem_conjAct_smul_iff (P : PSL(2, ℝ)) _ Γ).2 hB
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
  exact one_le_four_mul_sinh_sq_mul_of_dilation_mem hD hXmem h₁' h₂'

/-! ### Elliptic elements -/

/-- Along Jørgensen's sequence `Bₙ` of an element `A` fixing `z`, the displacements
`cₙ = cosh (dist (Bₙ • z) z)` satisfy `cₙ₊₁ = 1 + (4 - tr² A) / 2 · (cₙ² - 1)`: the point `z` is
moved by `Bₙ₊₁ = Bₙ A Bₙ⁻¹` as far as `Bₙ⁻¹ • z` is moved by `A`. -/
private theorem cosh_dist_jorgensenSeq_succ_smul {A : SL(2, ℝ)} {z : ℍ}
    (hAz : A • z = z) (B : PSL(2, ℝ)) (n : ℕ) :
    Real.cosh (dist (jorgensenSeq (A : PSL(2, ℝ)) B (n + 1) • z) z) =
      1 + (4 - (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) / 2 *
        (Real.cosh (dist (jorgensenSeq (A : PSL(2, ℝ)) B n • z) z) ^ 2 - 1) := by
  set C := jorgensenSeq (A : PSL(2, ℝ)) B n
  have hd : dist (C⁻¹ • z) z = dist (C • z) z := by
    rw [← dist_smul C, smul_inv_smul, dist_comm]
  rw [jorgensenSeq_succ, ← dist_smul C⁻¹, mul_smul, mul_smul, inv_smul_smul,
    UpperHalfPlane.pslMk_smul, Matrix.SpecialLinearGroup.cosh_dist_smul_of_smul_eq_self hAz, hd,
    Real.sinh_sq]

/-- Jørgensen's inequality for an element `A` fixing `z`, in the form
`(4 - tr² A) (1 + cosh (dist (B • z) z)) / 2 ≥ 1`. If it fails, the displacements of `z` along
Jørgensen's sequence decrease strictly, giving infinitely many elements of `Γ` that move `z` a
bounded distance. -/
private theorem one_le_four_sub_trace_sq_mul_one_add_cosh_div_two [DiscreteTopology Γ]
    {A : SL(2, ℝ)} {B : PSL(2, ℝ)} {z : ℍ} (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : B ∈ Γ)
    (hAz : A • z = z) (hA₁ : (A : PSL(2, ℝ)) ≠ 1) (hBz : B • z ≠ z) :
    1 ≤ (4 - (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) * (1 + Real.cosh (dist (B • z) z)) / 2 := by
  set J := jorgensenSeq (A : PSL(2, ℝ)) B
  set κ := (4 - (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) / 2
  set c : ℕ → ℝ := fun n ↦ Real.cosh (dist (J n • z) z)
  have hc₀ : c 0 = Real.cosh (dist (B • z) z) := by simp [c, J]
  -- `A` is elliptic, so `κ > 0`
  have hκ : 0 < κ := by
    have hell := (Matrix.isElliptic_iff_abs_trace_lt_two A.det_coe).1
      (Matrix.SpecialLinearGroup.isElliptic_of_smul_eq_self_of_ne_one hAz hA₁)
    simp only [κ]
    nlinarith [abs_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ).trace,
      sq_abs (A : Matrix (Fin 2) (Fin 2) ℝ).trace]
  by_contra hlt
  have hlt' : κ * (1 + c 0) < 1 := by
    rw [not_le, ← hc₀] at hlt
    linear_combination hlt
  -- the displacements `cₙ - 1 > 0` decrease strictly, since `cₙ₊₁ - 1 = κ (cₙ + 1) (cₙ - 1)`
  have hstep (n : ℕ) (h₁ : 1 < c n) (h₀ : c n ≤ c 0) : 1 < c (n + 1) ∧ c (n + 1) < c n := by
    have hrec : c (n + 1) = 1 + κ * (c n ^ 2 - 1) := cosh_dist_jorgensenSeq_succ_smul hAz B n
    have hκc : κ * (c n + 1) < 1 := by nlinarith
    have hpos : 0 < κ * ((c n + 1) * (c n - 1)) := mul_pos hκ (by nlinarith)
    constructor <;> nlinarith
  have hdec (n : ℕ) : 1 < c n ∧ c n ≤ c 0 := by
    induction n with
    | zero => exact ⟨hc₀ ▸ Real.one_lt_cosh.2 (dist_ne_zero.2 hBz), le_rfl⟩
    | succ n ih =>
        have := hstep n ih.1 ih.2
        exact ⟨this.1, this.2.le.trans ih.2⟩
  have hanti : StrictAnti c :=
    strictAnti_nat_of_succ_lt fun n ↦ (hstep n (hdec n).1 (hdec n).2).2
  -- so the elements `Bₙ` of `Γ` are distinct, yet all move `z` at most as far as `B` does
  let f : ℕ → Γ := fun n ↦ ⟨J n, jorgensenSeq_mem hA hB n⟩
  have hinj : Function.Injective f := fun m n h ↦ by
    have hJ : J m = J n := congrArg Subtype.val h
    exact hanti.injective (by simp only [c, hJ])
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ)
    (isCompact_singleton (x := z)) (isCompact_closedBall z (dist (B • z) z))
  refine Set.infinite_range_of_injective hinj (hfin.subset ?_)
  rintro _ ⟨n, rfl⟩
  refine ⟨J n • z, ⟨z, rfl, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, ← abs_of_nonneg (dist_nonneg (x := J n • z)),
    ← abs_of_nonneg (dist_nonneg (x := B • z)), ← Real.cosh_le_cosh, ← hc₀]
  exact (hdec n).2

/-- **Jørgensen's inequality for an element fixing a point.** Let `Γ ≤ PSL(2, ℝ)` be discrete and
let `A ∈ SL(2, ℝ)` lift a nontrivial element of `Γ` fixing `z ∈ ℍ`. Every `B ∈ Γ` not fixing `z`
satisfies `(4 - tr² A) cosh² (dist (B • z) z / 2) ≥ 1`. When `A` acts as the rotation through
angle `2θ` about `z` this reads `2 |sin θ| cosh (dist (B • z) z / 2) ≥ 1`. -/
theorem one_le_four_sub_trace_sq_mul_cosh_sq_of_smul_eq_self [DiscreteTopology Γ]
    {A : SL(2, ℝ)} {B : PSL(2, ℝ)} {z : ℍ} (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : B ∈ Γ)
    (hAz : A • z = z) (hA₁ : (A : PSL(2, ℝ)) ≠ 1) (hBz : B • z ≠ z) :
    1 ≤ (4 - (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) * Real.cosh (dist (B • z) z / 2) ^ 2 := by
  have h := one_le_four_sub_trace_sq_mul_one_add_cosh_div_two hA hB hAz hA₁ hBz
  have hcosh := Real.cosh_two_mul (dist (B • z) z / 2)
  rw [mul_div_cancel₀ _ two_ne_zero, Real.sinh_sq] at hcosh
  rw [hcosh] at h
  linear_combination h

/-- **Jørgensen's inequality for elliptic elements.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup
and let `A, B ∈ SL(2, ℝ)` lift elements of `Γ`, with `A` elliptic: `|tr A| < 2`. Unless `B`
commutes with `A` in `PSL(2, ℝ)`, that is, unless `B` fixes the fixed point of `A` in `ℍ`,
`|tr² A - 4| + |tr [A, B] - 2| ≥ 1`. -/
theorem one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_of_abs_trace_lt_two
    [DiscreteTopology Γ] {A : SL(2, ℝ)} (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hell : |(A : Matrix (Fin 2) (Fin 2) ℝ).trace| < 2)
    (h₁ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ A) :
    1 ≤ |(A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4| +
      |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| := by
  have htr : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 < 4 := by
    nlinarith [abs_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ).trace,
      sq_abs (A : Matrix (Fin 2) (Fin 2) ℝ).trace]
  -- `A` is elliptic, so it fixes a point `z` of `ℍ`
  have hellA : (Matrix.SpecialLinearGroup.mapGL ℝ A).IsElliptic :=
    (Matrix.isElliptic_iff_abs_trace_lt_two A.det_coe).2 hell
  set z := UpperHalfPlane.fixedPt _ hellA
  have hAz : A • z = z :=
    (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt (by simp) hellA).2 rfl
  have hA₁ : (A : PSL(2, ℝ)) ≠ 1 := by
    intro h
    rw [← QuotientGroup.mk_one, Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff] at h
    have h' : A = 1 ∨ A = -1 := h.imp Eq.symm fun h ↦ by rw [h, neg_neg]
    rcases h' with rfl | rfl <;> norm_num [Matrix.trace_fin_two] at htr
  -- `B` does not fix `z`: otherwise it would commute with `A` in the stabilizer of `z`
  have hBz : (B : PSL(2, ℝ)) • z ≠ z := by
    intro hBz
    refine h₁ (mul_inv_eq_of_eq_mul ?_)
    have := (instIsMulCommutativeStabilizer Γ z).is_comm.comm
      (⟨⟨B, hB⟩, hBz⟩ : stabilizer Γ z) ⟨⟨A, hA⟩, hAz⟩
    simpa using congrArg (fun q : stabilizer Γ z ↦ ((q : Γ) : PSL(2, ℝ))) this
  have h := one_le_four_sub_trace_sq_mul_one_add_cosh_div_two hA hB hAz hA₁ hBz
  rw [UpperHalfPlane.pslMk_smul] at h
  rw [Matrix.SpecialLinearGroup.trace_commutatorElement_of_smul_eq_self hAz B,
    abs_of_neg (by linarith), add_sub_cancel_left, abs_of_nonneg]
  · linear_combination h
  · have := Real.one_le_cosh (dist (B • z) z)
    nlinarith

/-! ### Parabolic elements -/

/-- **Jørgensen's inequality for parabolic elements.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup
and let `A, B ∈ SL(2, ℝ)` lift elements of `Γ`, with `A` parabolic, so that `tr² A = 4`. Unless `B`
commutes with `A` in `PSL(2, ℝ)`, that is, unless `B` fixes the fixed point of `A` on the ideal
boundary, `|tr [A, B] - 2| ≥ 1`. This is Shimizu's lemma in trace form. -/
theorem one_le_abs_trace_commutatorElement_sub_two_of_isParabolic [DiscreteTopology Γ]
    {A : SL(2, ℝ)} (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (hpar : ProjectiveSpecialLinearGroup.IsParabolic (A : PSL(2, ℝ)))
    (h₁ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ A) :
    1 ≤ |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| := by
  set c := parabolicFixedPoint (A : PSL(2, ℝ))
  -- `B` does not fix `c`, since it does not commute with `A`
  have hBc : (B : PSL(2, ℝ)) • c ≠ c := fun hBc ↦
    h₁ (mul_inv_eq_of_eq_mul (commute_of_smul_parabolicFixedPoint hA hB hpar hBc).eq.symm)
  -- move `c` to `∞`, where `A` becomes the translation by some `x ≠ 0`
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (∞ : OnePoint ℝ) c
  obtain ⟨x, hx, hAx⟩ := hpar.exists_conj_eq_upperRightHom hσ
  obtain ⟨S, rfl⟩ := QuotientGroup.mk_surjective σ
  set T : SL(2, ℝ) := S⁻¹ * A * S with hT
  set X : SL(2, ℝ) := S⁻¹ * B * S with hX
  set Γ' : Subgroup PSL(2, ℝ) := ConjAct.toConjAct (S : PSL(2, ℝ))⁻¹ • Γ
  have : DiscreteTopology Γ' := TauCeti.discreteTopology_of_conjAct_smul_eq rfl
  have hTmem : (T : PSL(2, ℝ)) ∈ Γ' :=
    (mk_inv_mul_mul S A) ▸ (inv_mul_mul_mem_conjAct_smul_iff (S : PSL(2, ℝ)) _ Γ).2 hA
  have hXmem : (X : PSL(2, ℝ)) ∈ Γ' :=
    (mk_inv_mul_mul S B) ▸ (inv_mul_mul_mem_conjAct_smul_iff (S : PSL(2, ℝ)) _ Γ).2 hB
  have hTx : (T : PSL(2, ℝ)) = upperRightHom x := (mk_inv_mul_mul S A).trans hAx
  -- the conjugate `X` of `B` does not fix `∞`, so Shimizu's lemma bounds its lower-left entry
  have hX0 : X 1 0 ≠ 0 := by
    intro h
    have h' := (mk_smul_infty_eq_infty_iff X).2 h
    rw [mk_inv_mul_mul, mul_smul, mul_smul, hσ, inv_smul_eq_iff] at h'
    exact hBc (h'.trans hσ)
  have hshim := inv_le_abs_apply_one_zero_of_upperRightHom_mem hx (hTx ▸ hTmem) hXmem
    hX0
  -- `T = ±!![1, x; 0, 1]`, so `tr ⁅T, X⁆ - 2 = x² (X 1 0)²`
  have hTe : T 1 0 = 0 ∧ T 1 1 = T 0 0 ∧ T 0 1 ^ 2 = x ^ 2 := by
    rw [upperRightHom_apply, mk_eq_mk_iff] at hTx
    have hT' : T = SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x ∨
        T = -SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x := by
      rcases hTx with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    rcases hT' with h | h <;> rw [h] <;>
      simp [SpecialLinearGroup.transvection_coe]
  have hcomm : ⁅A, B⁆ = S * ⁅T, X⁆ * S⁻¹ := by
    simp only [hT, hX, commutatorElement_def]
    group
  have htr : ((⁅T, X⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2 = x ^ 2 * X 1 0 ^ 2 := by
    rw [SpecialLinearGroup.trace_commutatorElement_sub_two_fin_two, Matrix.det_fin_two, ← hTe.2.2]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hTe.1, hTe.2.1]
    ring
  rw [hcomm, trace_mul_mul_inv, htr, abs_of_nonneg (by positivity)]
  rw [inv_le_iff_one_le_mul₀ (abs_pos.2 hx)] at hshim
  nlinarith [abs_mul_abs_self x, abs_mul_abs_self (X 1 0), abs_nonneg x, abs_nonneg (X 1 0)]

/-! ### Every element -/

/-- **Jørgensen's inequality.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup and let
`A, B ∈ SL(2, ℝ)` lift elements of `Γ`. Unless `B` conjugates the class of `A` to itself or to
its inverse, `|tr² A - 4| + |tr [A, B] - 2| ≥ 1`. -/
theorem one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two
    [DiscreteTopology Γ] {A : SL(2, ℝ)} (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ)
    (h₁ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ A)
    (h₂ : (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ ≠ (A : PSL(2, ℝ))⁻¹) :
    1 ≤ |(A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4| +
      |((⁅A, B⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| := by
  rcases lt_trichotomy |(A : Matrix (Fin 2) (Fin 2) ℝ).trace| 2 with hlt | heq | hgt
  · exact one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_of_abs_trace_lt_two
      hA hB hlt h₁
  · -- `A` has trivial or parabolic class, and the trivial class commutes with `B`
    have htr : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = 4 := by
      rw [← sq_abs, heq]
      norm_num
    rcases ProjectiveSpecialLinearGroup.eq_one_or_isParabolic_of_trace_sq_eq_four htr with
      hA1 | hpar
    · exact absurd (by rw [hA1]; group) h₁
    · exact (one_le_abs_trace_commutatorElement_sub_two_of_isParabolic hA hB hpar h₁).trans
        (le_add_of_nonneg_left (abs_nonneg _))
  · exact one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two_of_two_lt_abs_trace
      hA hB hgt h₁ h₂

end Subgroup
