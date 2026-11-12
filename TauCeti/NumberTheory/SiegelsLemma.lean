/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SiegelsLemma
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.LinearAlgebra.Span.Defs

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exponent in Siegel's lemma is optimal

Siegel's lemma (Mathlib's `Int.Matrix.exists_ne_zero_int_vec_norm_le`) gives a nonzero integer
solution `x` of an `m × n` integer system `A x = 0`, `m < n`, with
`‖x‖ ≤ (n · max 1 ‖A‖) ^ (m / (n - m))` in the sup norms. This file shows that for `n = m + 1`
the exponent `m / (n - m) = m` cannot be lowered, whatever the constant.

The witness is the system `b xᵢ = xᵢ₊₁`, `0 ≤ i < m`, whose coefficient matrix
`TauCeti.Matrix.geomRecurrence b m` has entries `b`, `-1` and `0`. Its solutions are the
geometric progressions `xᵢ = bⁱ x₀`, so its kernel is spanned by `(1, b, …, bᵐ)` and every
nonzero integer solution has sup norm at least `|b| ^ m`, against Siegel's bound
`((m + 1) |b|) ^ m` for `|b| ≥ 1`.

## Main definitions

* `TauCeti.Matrix.geomRecurrence b m`: the `m × (m + 1)` matrix of the recurrence
  `b xᵢ - xᵢ₊₁ = 0`.

## Main results

* `TauCeti.Matrix.mulVec_geomRecurrence_eq_zero_iff`: the solutions are the geometric
  progressions of ratio `b`.
* `TauCeti.Matrix.ker_mulVecLin_geomRecurrence`: over a commutative ring the kernel is the span
  of `(1, b, …, bᵐ)`.
* `TauCeti.Matrix.norm_geomRecurrence`: for `0 < m`, the sup norm of the matrix is `max ‖b‖ 1`.
* `TauCeti.Matrix.pow_le_iSup_abs_of_mulVec_geomRecurrence_eq_zero`: over `ℤ`, every nonzero
  solution has sup norm at least `|b| ^ m`.
* `TauCeti.Int.Matrix.not_forall_exists_ne_zero_int_vec_norm_le`: for `0 < m` and any exponent
  `e < m` and constant `C`, not every `m × (m + 1)` integer system has a nonzero solution of sup
  norm at most `C · max 1 ‖A‖ ^ e`.

## References

* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuss. Akad.
  Wiss. (1929).
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, GTM 201, Springer,
  2000, §D.4.
-/

public section

open Filter

open scoped Matrix

attribute [local instance] Matrix.seminormedAddCommGroup

namespace TauCeti

namespace Matrix

variable {R : Type*}

section Ring

variable [Ring R]

/-- The `m × (m + 1)` coefficient matrix of the linear recurrence `b xᵢ - xᵢ₊₁ = 0` for
`0 ≤ i < m`: row `i` has `b` in column `i`, `-1` in column `i + 1` and `0` elsewhere. Its solutions
are the geometric progressions of ratio `b`. -/
def geomRecurrence (b : R) (m : ℕ) : _root_.Matrix (Fin m) (Fin (m + 1)) R :=
  _root_.Matrix.of fun i ↦ (Pi.single i.castSucc b - Pi.single i.succ 1 : Fin (m + 1) → R)

theorem geomRecurrence_apply (b : R) {m : ℕ} (i : Fin m) (j : Fin (m + 1)) :
    geomRecurrence b m i j = (if j = i.castSucc then b else 0) - if j = i.succ then 1 else 0 := by
  simp [geomRecurrence, Pi.single_apply]

@[simp]
theorem mulVec_geomRecurrence (b : R) {m : ℕ} (x : Fin (m + 1) → R) (i : Fin m) :
    (geomRecurrence b m *ᵥ x) i = b * x i.castSucc - x i.succ := by
  simp [_root_.Matrix.mulVec, dotProduct, geomRecurrence_apply, sub_mul, Finset.sum_sub_distrib]

/-- The solutions of `b xᵢ = xᵢ₊₁` are the geometric progressions `xᵢ = bⁱ x₀`. -/
theorem mulVec_geomRecurrence_eq_zero_iff {b : R} {m : ℕ} {x : Fin (m + 1) → R} :
    geomRecurrence b m *ᵥ x = 0 ↔ ∀ i, x i = b ^ (i : ℕ) * x 0 := by
  refine ⟨fun h i ↦ ?_, fun h ↦ funext fun i ↦ ?_⟩
  · induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      have hi : b * x i.castSucc = x i.succ := by
        simpa only [mulVec_geomRecurrence, Pi.zero_apply, sub_eq_zero] using congrFun h i
      calc
        x i.succ = b * x i.castSucc := hi.symm
        _ = b * (b ^ (i.castSucc : ℕ) * x 0) := by rw [ih]
        _ = b ^ (i.succ : ℕ) * x 0 := by
          simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', mul_assoc]
  · simp only [mulVec_geomRecurrence, Pi.zero_apply, sub_eq_zero, h i.castSucc, h i.succ,
      Fin.val_succ, Fin.val_castSucc, pow_succ', mul_assoc]

/-- A solution of `b xᵢ = xᵢ₊₁` vanishes as soon as its first coordinate does. -/
theorem eq_zero_of_mulVec_geomRecurrence_eq_zero {b : R} {m : ℕ} {x : Fin (m + 1) → R}
    (h : geomRecurrence b m *ᵥ x = 0) (h₀ : x 0 = 0) : x = 0 :=
  funext fun i ↦ by rw [mulVec_geomRecurrence_eq_zero_iff.1 h i, h₀, mul_zero, Pi.zero_apply]

end Ring

/-- Over a commutative ring the kernel of `b xᵢ = xᵢ₊₁` is free of rank one, spanned by the
geometric progression `(1, b, …, bᵐ)`. -/
theorem ker_mulVecLin_geomRecurrence [CommRing R] (b : R) (m : ℕ) :
    LinearMap.ker (geomRecurrence b m).mulVecLin = R ∙ fun i : Fin (m + 1) ↦ b ^ (i : ℕ) := by
  ext x
  rw [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply, mulVec_geomRecurrence_eq_zero_iff,
    Submodule.mem_span_singleton]
  refine ⟨fun h ↦ ⟨x 0, funext fun i ↦ by rw [h i, Pi.smul_apply, smul_eq_mul, mul_comm]⟩, ?_⟩
  rintro ⟨a, rfl⟩ i
  simp [mul_comm]

/-- The sup norm of the matrix of `b xᵢ = xᵢ₊₁` is `max ‖b‖ 1`, as soon as there is an
equation. -/
theorem norm_geomRecurrence [NormedRing R] [NormOneClass R] (b : R) {m : ℕ} (hm : 0 < m) :
    ‖geomRecurrence b m‖ = max ‖b‖ 1 := by
  refine le_antisymm ((_root_.Matrix.norm_le_iff (by positivity)).2 fun i j ↦ ?_) ?_
  · rw [geomRecurrence_apply]
    by_cases hc : j = i.castSucc
    · simp [hc, Fin.castSucc_lt_succ.ne]
    · by_cases hs : j = i.succ <;> simp [hc, hs, Fin.castSucc_lt_succ.ne']
  · have hb := _root_.Matrix.norm_apply_le_norm (geomRecurrence b m)
      (i := ⟨0, hm⟩) (j := Fin.castSucc ⟨0, hm⟩)
    have h₁ := _root_.Matrix.norm_apply_le_norm (geomRecurrence b m)
      (i := ⟨0, hm⟩) (j := Fin.succ ⟨0, hm⟩)
    simp only [geomRecurrence_apply, Fin.castSucc_lt_succ.ne, Fin.castSucc_lt_succ.ne',
      ↓reduceIte, sub_zero, zero_sub, norm_neg, norm_one] at hb h₁
    exact max_le hb h₁

/-- The last coordinate `xₘ = bᵐ x₀` of a nonzero integer solution of `b xᵢ = xᵢ₊₁` is at least
`|b| ^ m` in absolute value, since `x₀ ≠ 0`. -/
private theorem pow_abs_le_abs_last {b : ℤ} {m : ℕ} {x : Fin (m + 1) → ℤ} (hx : x ≠ 0)
    (h : geomRecurrence b m *ᵥ x = 0) : |b| ^ m ≤ |x (Fin.last m)| := by
  have h₀ : x 0 ≠ 0 := fun h₀ ↦ hx (eq_zero_of_mulVec_geomRecurrence_eq_zero h h₀)
  rw [mulVec_geomRecurrence_eq_zero_iff.1 h (Fin.last m), Fin.val_last, abs_mul, abs_pow]
  exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs h₀)

/-- **The lower bound in the system `b xᵢ = xᵢ₊₁`.** Every nonzero integer solution has sup norm
at least `|b| ^ m`. -/
theorem pow_le_iSup_abs_of_mulVec_geomRecurrence_eq_zero {b : ℤ} {m : ℕ}
    {x : Fin (m + 1) → ℤ} (hx : x ≠ 0) (h : geomRecurrence b m *ᵥ x = 0) :
    |b| ^ m ≤ ⨆ i, |x i| :=
  (pow_abs_le_abs_last hx h).trans
    (le_ciSup (f := fun i ↦ |x i|) (Set.finite_range _).bddAbove (Fin.last m))

/-- The lower bound `pow_le_iSup_abs_of_mulVec_geomRecurrence_eq_zero` in the norm of `ℤ^(m+1)`,
which is the sup norm in which Siegel's lemma is stated. -/
theorem pow_le_norm_of_mulVec_geomRecurrence_eq_zero {b : ℤ} {m : ℕ}
    {x : Fin (m + 1) → ℤ} (hx : x ≠ 0) (h : geomRecurrence b m *ᵥ x = 0) :
    |(b : ℝ)| ^ m ≤ ‖x‖ := by
  refine le_trans ?_ (norm_le_pi_norm x (Fin.last m))
  rw [Int.norm_eq_abs]
  exact_mod_cast pow_abs_le_abs_last hx h

end Matrix

namespace Int.Matrix

/-- **The exponent in Siegel's lemma is optimal.** For an `m × (m + 1)` integer system, Siegel's
lemma `Int.Matrix.exists_ne_zero_int_vec_norm_le` gives a nonzero integer solution of sup norm at
most `((m + 1) · max 1 ‖A‖) ^ m`. For `0 < m` no exponent `e < m` works, with any constant `C`:
the system `b xᵢ = xᵢ₊₁` with `b` large has no nonzero integer solution of sup norm at most
`C · max 1 ‖A‖ ^ e`. -/
theorem not_forall_exists_ne_zero_int_vec_norm_le {m : ℕ} (hm : 0 < m) {e : ℝ}
    (he : e < m) (C : ℝ) :
    ¬ ∀ A : _root_.Matrix (Fin m) (Fin (m + 1)) ℤ,
      ∃ x : Fin (m + 1) → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧ ‖x‖ ≤ C * max 1 ‖A‖ ^ e := by
  intro hA
  -- Choose an integer `b ≥ 1` with `C < b ^ (m - e)`.
  obtain ⟨b, hb₁, hbC⟩ := ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((eventually_ge_atTop 1).and
      ((tendsto_rpow_atTop (sub_pos.2 he)).eventually_gt_atTop C))).exists
  have hb₀ : (0 : ℝ) < b := one_pos.trans_le hb₁
  obtain ⟨x, hx, hAx, hxC⟩ := hA (Matrix.geomRecurrence (b : ℤ) m)
  have hnorm : max 1 ‖Matrix.geomRecurrence (b : ℤ) m‖ = b := by
    rw [Matrix.norm_geomRecurrence _ hm, Int.norm_natCast, max_eq_left hb₁, max_eq_right hb₁]
  have hlow := Matrix.pow_le_norm_of_mulVec_geomRecurrence_eq_zero hx hAx
  rw [Int.cast_natCast, abs_of_pos hb₀] at hlow
  rw [hnorm] at hxC
  -- `b ^ m ≤ ‖x‖ ≤ C · b ^ e < b ^ (m - e) · b ^ e = b ^ m`.
  have key : (b : ℝ) ^ ((m : ℝ) - e) * b ^ e ≤ C * b ^ e := by
    rw [← Real.rpow_add hb₀, sub_add_cancel, Real.rpow_natCast]
    exact hlow.trans hxC
  exact (mul_lt_mul_of_pos_right hbC (Real.rpow_pos_of_pos hb₀ e)).not_ge key

end Int.Matrix

end TauCeti
