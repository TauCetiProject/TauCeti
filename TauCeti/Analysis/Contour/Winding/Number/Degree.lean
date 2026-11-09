/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Topology.Circle.Degree
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Winding.SegmentSum

/-!
# Winding numbers as degrees of direction loops

Let `γ` be a closed piecewise `C¹` path in `ℂ` avoiding a point `w`. Its direction loop
`t ↦ (γ t - w) / ‖γ t - w‖` is a loop in the unit circle, and the winding number of `γ` about `w`
is the degree `Circle.degree` of this loop
(`TauCeti.Contour.windingNumber_eq_degree_of_eq_div_norm`). Both are read off from one continuous
argument of `γ t - w`: its total change is the imaginary part of the logarithmic contour integral,
and it is also `2π` times the degree. The argument need not be differentiable.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4.
-/

public section

open MeasureTheory Set
open scoped unitInterval Interval

noncomputable section

namespace TauCeti.Contour

/-- **The winding number is the degree of the direction loop.** For a closed piecewise `C¹` path
`γ` avoiding `w`, the winding number of `γ` about `w` is the degree of the loop
`p t = (γ t - w) / ‖γ t - w‖` in the unit circle. Only `γ` is assumed piecewise `C¹`; the loop `p`
is specified pointwise. -/
theorem windingNumber_eq_degree_of_eq_div_norm {x w : ℂ} {u : Circle}
    (γ : Path x x) (p : Path u u) (hγ : IsPiecewiseC1On γ.extend 0 1)
    (havoid : ∀ t : I, γ t ≠ w)
    (hp : ∀ t : I, (p t : ℂ) = (γ t - w) / (‖γ t - w‖ : ℂ)) :
    windingNumber γ.extend 0 1 w = (Circle.degree p : ℂ) := by
  have hc : ContinuousOn γ.extend (Icc 0 1) := γ.continuous_extend.continuousOn
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ w := by
    intro t ht
    simpa only [Path.extend_apply γ ht] using havoid ⟨t, ht⟩
  obtain ⟨N, s, -, hs0, hs1, hsmono, -, hsavoid, hslit, hθ, hlift⟩ :=
    exists_continuousOn_arg_lift_with_partition (by norm_num : (0 : ℝ) ≤ 1) hc hn
  let θ : ℝ → ℝ := fun t ↦ Complex.arg (γ.extend 0 - w) +
    ∑ j ∈ Finset.range N, (Complex.log (segRatio γ.extend w (s j) (s (j + 1)) t)).im
  have hθp : ∀ t : I, Circle.exp (θ t) = p t := by
    intro t
    apply Subtype.ext
    rw [Circle.coe_exp, hp]
    have ht := hlift t t.property
    simp only [Path.extend_apply γ t.property] at ht
    change γ t - w = (‖γ t - w‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ)) at ht
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (havoid t))))).2
    rw [mul_comm Complex.I] at ht
    rw [mul_comm]
    exact ht.symm
  have hdeg := Circle.sub_eq_degree_mul p hθ.domRestrict hθp
  have hθ0 : θ 0 = Complex.arg (γ.extend 0 - w) := by
    suffices h : ∑ j ∈ Finset.range N,
        (Complex.log (segRatio γ.extend w (s j) (s (j + 1)) 0)).im = 0 by
      simp only [θ, h, add_zero]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [segRatio_eq_one_of_le (hs0 ▸ hsmono (Nat.zero_le j))
      (hsavoid j (Finset.mem_range.mp hj).le)]
    simp
  have hθ1 : θ 1 = Complex.arg (γ.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log ((γ.extend (s (j + 1)) - w) / (γ.extend (s j) - w))).im := by
    simp only [θ]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [segRatio_eq_endpoint_div_of_le (hsmono (Nat.le_succ j))
      ((hsmono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans_eq hs1)]
  change θ 1 - θ 0 = _ at hdeg
  rw [hθ1, hθ0, add_sub_cancel_left] at hdeg
  have hc' : ContinuousOn γ.extend (uIcc 0 1) := hγ.continuousOn
  have hn' : ∀ t ∈ uIcc (0 : ℝ) 1, γ.extend t ≠ w := by simpa using hn
  have hi := intervalIntegrable_inv_sub_mul_deriv hc' hn' hγ.intervalIntegrable_deriv
  obtain ⟨P, hP, hd⟩ := hγ.exists_countable_differentiableAt
  have hsum := integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im
    hP hs0 hs1 hsmono hc (by simpa using hd) hslit hi
  rw [windingNumber_eq_integral_of_avoidance hc' hn' hi, hsum, hdeg]
  simp only [Path.extend_zero, Path.extend_one, sub_self, Complex.ofReal_zero, zero_add,
    Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  field_simp

end TauCeti.Contour
