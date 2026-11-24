/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The descent lemma

Let `f` be a real function on a real normed space `V` which is differentiable at every point of
the segment from `x` to `x + h`, and whose derivative satisfies
`‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖` at every point `y` of that segment. Then `f` lies
below its first-order expansion at `x` plus a quadratic term:

`f (x + h) ≤ f x + fderiv ℝ f x h + L / 2 * ‖h‖ ^ 2`.

The hypothesis compares the derivative only with its value at the base point `x`, and only along
the segment, so no global Lipschitz bound and no continuity of the derivative are assumed. Applied
to `f` and to `-f`, it bounds the first-order Taylor remainder of a function with `L`-Lipschitz
derivative by `L / 2 * ‖h‖ ^ 2` in absolute value, which is the inequality behind the convergence
analysis of gradient methods.

The constant `L` is an arbitrary real number. For `L < 0` the hypothesis at `y = x + h` forces
`h = 0`, and the inequality is then an equality.

## Main results

* `TauCeti.le_add_fderiv_add_of_lipschitz`: the descent lemma.

## References

* Y. Nesterov, *Lectures on convex optimization*, 2nd ed., Springer, 2018, Lemma 1.2.3.
-/

public section

namespace TauCeti

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ} {x h : V} {L : ℝ}

/-- **The descent lemma.** If `f` is differentiable at every point of the segment from `x` to
`x + h` and `‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖` for every `y` on that segment, then
`f (x + h) ≤ f x + fderiv ℝ f x h + L / 2 * ‖h‖ ^ 2`. -/
theorem le_add_fderiv_add_of_lipschitz
    (hf : ∀ y ∈ segment ℝ x (x + h), DifferentiableAt ℝ f y)
    (hL : ∀ y ∈ segment ℝ x (x + h), ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖) :
    f (x + h) ≤ f x + fderiv ℝ f x h + L / 2 * ‖h‖ ^ 2 := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ segment ℝ x (x + h) := fun t ht ↦ by
    rw [segment_eq_image']
    exact ⟨t, ht, by simp⟩
  -- The restriction of `f` to the segment, minus its first-order part and the quadratic term.
  let φ : ℝ → ℝ := fun t ↦ f (x + t • h) - t * fderiv ℝ f x h - L / 2 * ‖h‖ ^ 2 * t ^ 2
  have hφ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ
      (fderiv ℝ f (x + t • h) h - fderiv ℝ f x h - L / 2 * ‖h‖ ^ 2 * (2 * t)) t := fun t ht ↦ by
    have hline : HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have hquad : HasDerivAt (fun s : ℝ ↦ L / 2 * ‖h‖ ^ 2 * s ^ 2)
        (L / 2 * ‖h‖ ^ 2 * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖h‖ ^ 2)
    have hlin : HasDerivAt (fun s : ℝ ↦ s * fderiv ℝ f x h) (fderiv ℝ f x h) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ f x h)
    exact ((HasFDerivAt.comp_hasDerivAt t (hf _ (hmem t ht)).hasFDerivAt hline).sub hlin).sub hquad
  -- Its derivative is nonpositive on `[0, 1]`, by the hypothesis on the derivative of `f`.
  have hle : ∀ t ∈ Icc (0 : ℝ) 1,
      fderiv ℝ f (x + t • h) h - fderiv ℝ f x h - L / 2 * ‖h‖ ^ 2 * (2 * t) ≤ 0 := fun t ht ↦ by
    have hnorm : ‖x + t • h - x‖ = t * ‖h‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    have hop : (fderiv ℝ f (x + t • h) - fderiv ℝ f x) h ≤ L * (t * ‖h‖) * ‖h‖ :=
      (le_abs_self _).trans <| ((fderiv ℝ f (x + t • h) - fderiv ℝ f x).le_opNorm h).trans <|
        mul_le_mul_of_nonneg_right ((hL _ (hmem t ht)).trans_eq (by rw [hnorm])) (norm_nonneg h)
    rw [sub_apply] at hop
    linarith
  have hanti : AntitoneOn φ (Icc 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hφ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hφ t (interior_subset ht)).deriv ▸ hle t (interior_subset ht))
  have h01 : φ 1 ≤ φ 0 :=
    hanti (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  have h1 : φ 1 = f (x + h) - fderiv ℝ f x h - L / 2 * ‖h‖ ^ 2 := by simp [φ]
  have h0 : φ 0 = f x := by simp [φ]
  linarith

end TauCeti
