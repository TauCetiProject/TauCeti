/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import TauCeti.Analysis.Quaternion.QuotientDeriv

/-!
# The quaternionic square map and one-sided quotient derivatives

The square map is real differentiable everywhere, but has a left or right quotient derivative
exactly at the real quaternions. At such a point `q` its slope is `q + q` on either side.
Consequently neither quotient differentiability predicate holds on a nonempty open set.
These examples distinguish real differentiability from the much more restrictive one-sided
quaternionic notions, even for a polynomial.

The derivative is computed using Mathlib's real product rule. The obstruction is that the term
`h ↦ q * h` in `h ↦ q * h + h * q` can be a right multiplication only when `q` is real, and dually.

## References

* O. Dzagnidze, *On the differentiability of quaternion functions*, arXiv:1203.5619v1,
  §1, p. 2, for the one-sided quotient derivatives.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979),
  199–225, Theorem 1, for the rigidity of these notions on open sets.
-/

public section

open scoped Quaternion

namespace TauCeti

/-- The square map has left slope `b` at `q` exactly when `q` is real and `b = q + q`. -/
@[simp]
theorem hasLeftQuotientFDerivAt_sq_iff (q b : ℍ) :
    HasLeftQuotientFDerivAt (fun x ↦ x ^ 2) q b ↔ q.im = 0 ∧ b = q + q := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) q).fun_mul' (hasFDerivAt_id q)
  simp only [id_eq, ← pow_two] at hd
  constructor
  · intro hb
    have heq := hd.unique hb.hasFDerivAt
    have h (x : ℍ) : q * x + x * q = x * b := by
      simpa using DFunLike.congr_fun heq x
    have hb' : b = q + q := by simpa using (h 1).symm
    have hleft : HasLeftQuotientFDerivAt (fun x ↦ q * x) q (b - q) := by
      rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt]
      have hm : (ContinuousLinearMap.mul ℝ ℍ).flip (b - q) =
          ContinuousLinearMap.mul ℝ ℍ q := by
        apply ContinuousLinearMap.ext
        intro x
        simpa [mul_sub] using (eq_sub_iff_add_eq.mpr (h x)).symm
      rw [hm]
      exact (hasRightQuotientFDerivAt_const_mul q q).hasFDerivAt
    refine ⟨?_, hb'⟩
    simpa [hb'] using hleft.im_eq_zero_of_hasRightQuotientFDerivAt
      (hasRightQuotientFDerivAt_const_mul q q)
  · rintro ⟨hq, rfl⟩
    have hreal : q = (q.re : ℍ) := by
      simpa [hq] using q.re_add_im.symm
    rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt]
    have hc (x : ℍ) : q * x = x * q := by
      rw [hreal]
      exact Quaternion.coe_commutes _ _
    convert hd using 1
    apply ContinuousLinearMap.ext
    intro x
    simp [hc]

/-- The square map has right slope `a` at `q` exactly when `q` is real and `a = q + q`. -/
@[simp]
theorem hasRightQuotientFDerivAt_sq_iff (q a : ℍ) :
    HasRightQuotientFDerivAt (fun x ↦ x ^ 2) q a ↔ q.im = 0 ∧ a = q + q := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) q).fun_mul' (hasFDerivAt_id q)
  simp only [id_eq, ← pow_two] at hd
  constructor
  · intro ha
    have heq := hd.unique ha.hasFDerivAt
    have h (x : ℍ) : q * x + x * q = a * x := by
      simpa using DFunLike.congr_fun heq x
    have ha' : a = q + q := by simpa using (h 1).symm
    have hright : HasRightQuotientFDerivAt (fun x ↦ x * q) q (a - q) := by
      rw [hasRightQuotientFDerivAt_iff_hasFDerivAt]
      have hm : ContinuousLinearMap.mul ℝ ℍ (a - q) =
          (ContinuousLinearMap.mul ℝ ℍ).flip q := by
        apply ContinuousLinearMap.ext
        intro x
        simpa [sub_mul] using
          (eq_sub_iff_add_eq.mpr ((add_comm (x * q) (q * x)).trans (h x))).symm
      rw [hm]
      exact (hasLeftQuotientFDerivAt_mul_const q q).hasFDerivAt
    exact ⟨(hasLeftQuotientFDerivAt_mul_const q q).im_eq_zero_of_hasRightQuotientFDerivAt
      hright, ha'⟩
  · rintro ⟨hq, rfl⟩
    have hreal : q = (q.re : ℍ) := by
      simpa [hq] using q.re_add_im.symm
    rw [hasRightQuotientFDerivAt_iff_hasFDerivAt]
    have hc (x : ℍ) : q * x = x * q := by
      rw [hreal]
      exact Quaternion.coe_commutes _ _
    convert hd using 1
    apply ContinuousLinearMap.ext
    intro x
    simp [hc]

/-- The square map is left quotient differentiable exactly at the real quaternions. -/
@[simp]
theorem leftQuotientDifferentiableAt_sq_iff (q : ℍ) :
    LeftQuotientDifferentiableAt (fun x ↦ x ^ 2) q ↔ q.im = 0 := by
  simp [leftQuotientDifferentiableAt_iff]

/-- The square map is right quotient differentiable exactly at the real quaternions. -/
@[simp]
theorem rightQuotientDifferentiableAt_sq_iff (q : ℍ) :
    RightQuotientDifferentiableAt (fun x ↦ x ^ 2) q ↔ q.im = 0 := by
  simp [rightQuotientDifferentiableAt_iff]

/-- The square map is left quotient differentiable on a set exactly when every point is real. -/
theorem leftQuotientDifferentiableOn_sq_iff (s : Set ℍ) :
    LeftQuotientDifferentiableOn (fun x ↦ x ^ 2) s ↔ ∀ q ∈ s, q.im = 0 := by
  simp [leftQuotientDifferentiableOn_iff]

/-- The square map is right quotient differentiable on a set exactly when every point is real. -/
theorem rightQuotientDifferentiableOn_sq_iff (s : Set ℍ) :
    RightQuotientDifferentiableOn (fun x ↦ x ^ 2) s ↔ ∀ q ∈ s, q.im = 0 := by
  simp [rightQuotientDifferentiableOn_iff]

/-- No nonempty open set supports left quotient differentiability of the square map. -/
theorem leftQuotientDifferentiableOn_sq_iff_eq_empty {s : Set ℍ} (hs : IsOpen s) :
    LeftQuotientDifferentiableOn (fun x ↦ x ^ 2) s ↔ s = ∅ := by
  constructor
  · intro hf
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs q hq
    have hi : ‖(⟨0, 1, 0, 0⟩ : ℍ)‖ = 1 := by
      rw [norm_eq_sqrt_real_inner, Quaternion.inner_self]
      norm_num [Quaternion.normSq_def']
    have hp : q + (ε / 2) • (⟨0, 1, 0, 0⟩ : ℍ) ∈ s := by
      apply hball
      simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (half_pos hε), hi, mul_one]
      exact half_lt_self hε
    have hqI : q.imI = 0 := by
      simpa using congrArg (fun x : ℍ ↦ x.imI)
        ((leftQuotientDifferentiableOn_sq_iff s).mp hf q hq)
    have hpI := congrArg (fun x : ℍ ↦ x.imI)
      ((leftQuotientDifferentiableOn_sq_iff s).mp hf _ hp)
    simp [hqI] at hpI
    linarith
  · rintro rfl
    simp [leftQuotientDifferentiableOn_iff]

/-- No nonempty open set supports right quotient differentiability of the square map. -/
theorem rightQuotientDifferentiableOn_sq_iff_eq_empty {s : Set ℍ} (hs : IsOpen s) :
    RightQuotientDifferentiableOn (fun x ↦ x ^ 2) s ↔ s = ∅ := by
  rw [rightQuotientDifferentiableOn_sq_iff, ← leftQuotientDifferentiableOn_sq_iff,
    leftQuotientDifferentiableOn_sq_iff_eq_empty hs]

end TauCeti
