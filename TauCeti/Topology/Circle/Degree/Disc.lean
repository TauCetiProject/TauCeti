/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Degree
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Topology.Circle.Normalize

/-!
# Degrees of boundary direction maps of discs

Let `f : ℂ → ℂ` have no zero on the circle of radius `r` about `c`. Its *boundary direction map*
is the map `u : S¹ → S¹`, `u ζ = f (c + r ζ) / ‖f (c + r ζ)‖`, and the degree of its loop
`u.toBasedLoop` is the number of times `f` winds around `0` along the circle. No differentiability
is needed for this integer to make sense, and this file proves its basic properties for maps that
are merely continuous. The direction maps are specified pointwise, so the statements apply to any
construction of them.

* The degree is invariant under homotopies avoiding `0`: the direction maps of the two ends of a
  continuous family `F : [0, 1] × S¹ → ℂ` without zeros have the same degree
  (`Circle.degree_toBasedLoop_eq_of_homotopy_div_norm`).
* It vanishes when `f` is continuous and has no zero on the whole closed disc, since contracting
  the disc to its centre is such a homotopy to a constant map
  (`Circle.degree_toBasedLoop_eq_zero_of_forall_ne_zero`).
* Consequently, if the degree is not zero then `f` has a zero in the open disc
  (`Circle.exists_mem_ball_eq_zero_of_degree_toBasedLoop_ne_zero`).

When `f ∘ circleMap c r` is `C¹`, the degree is the contour winding number of `f` along the circle
(`TauCeti.Contour.windingNumber_comp_circleMap_eq_degree_toBasedLoop`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.1.
-/

public section

noncomputable section

open scoped unitInterval

namespace Circle

/-- **Homotopy invariance of the degree of direction maps.** Let `F : [0, 1] × S¹ → ℂ` be
continuous and without zeros. Then the direction maps `ζ ↦ F (0, ζ) / ‖F (0, ζ)‖` and
`ζ ↦ F (1, ζ) / ‖F (1, ζ)‖` of its two ends have the same degree. -/
theorem degree_toBasedLoop_eq_of_homotopy_div_norm (F : C(I × Circle, ℂ)) (hne : ∀ p, F p ≠ 0)
    {u₀ u₁ : C(Circle, Circle)} (h₀ : ∀ ζ, (u₀ ζ : ℂ) = F (0, ζ) / ‖F (0, ζ)‖)
    (h₁ : ∀ ζ, (u₁ ζ : ℂ) = F (1, ζ) / ‖F (1, ζ)‖) :
    degree u₀.toBasedLoop = degree u₁.toBasedLoop :=
  degree_eq_of_homotopy_div_norm _ _ (F.comp ((ContinuousMap.id I).prodMap TauCeti.unitToCircle))
    (fun _ ↦ hne _) (fun t ↦ by simp [h₀]) (fun t ↦ by simp [h₁])
    (fun s ↦ by simp [TauCeti.unitToCircle_zero, TauCeti.unitToCircle_one])

/-- **A map without zeros on a closed disc has boundary degree zero.** If `f` is continuous and
nonzero on the closed disc of radius `r ≥ 0` about `c`, its boundary direction map
`u ζ = f (c + r ζ) / ‖f (c + r ζ)‖` has degree `0`. -/
theorem degree_toBasedLoop_eq_zero_of_forall_ne_zero {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (Metric.closedBall c r))
    (hne : ∀ z ∈ Metric.closedBall c r, f z ≠ 0) {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = f (c + r * ζ) / ‖f (c + r * ζ)‖) :
    degree u.toBasedLoop = 0 := by
  -- The circles of radius `s r`, `s ∈ [0, 1]`, contract the boundary circle to the centre.
  have hmem (p : I × Circle) : c + ((p.1 * r : ℝ) : ℂ) * p.2 ∈ Metric.closedBall c r := by
    simpa [abs_of_nonneg p.1.property.1, abs_of_nonneg hr] using mul_le_of_le_one_left hr
        p.1.property.2
  let F : C(I × Circle, ℂ) :=
    ⟨fun p ↦ f (c + ((p.1 * r : ℝ) : ℂ) * p.2), hf.comp_continuous (by fun_prop) hmem⟩
  have hc : f c ≠ 0 := hne c (Metric.mem_closedBall_self hr)
  -- At `s = 0` the direction map is the constant direction of `f c`.
  have hx : (exp (Complex.arg (f c)) : ℂ) = f c / ‖f c‖ := by
    rw [coe_exp, eq_div_iff (by exact_mod_cast norm_ne_zero_iff.2 hc), mul_comm,
      Complex.norm_mul_exp_arg_mul_I]
  have h := degree_toBasedLoop_eq_of_homotopy_div_norm F (fun p ↦ hne _ (hmem p))
    (u₀ := ContinuousMap.const Circle (exp (Complex.arg (f c)))) (u₁ := u)
    (fun ζ ↦ by rw [ContinuousMap.const_apply, hx]; simp [F]) (fun ζ ↦ by rw [hu]; simp [F])
  rw [← h, degree_congr _ (Path.refl (exp (Complex.arg (f c))))
    fun t ↦ by rw [ContinuousMap.toBasedLoop_apply, ContinuousMap.const_apply, Path.refl_apply],
    degree_refl]

/-- **A map of nonzero boundary degree has a zero in the disc.** If `f` is continuous on the
closed disc of radius `r ≥ 0` about `c` and its boundary direction map
`u ζ = f (c + r ζ) / ‖f (c + r ζ)‖` has nonzero degree, then `f` vanishes somewhere in the open
disc. -/
theorem exists_mem_ball_eq_zero_of_degree_toBasedLoop_ne_zero {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : ContinuousOn f (Metric.closedBall c r)) {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = f (c + r * ζ) / ‖f (c + r * ζ)‖)
    (hdeg : degree u.toBasedLoop ≠ 0) : ∃ z ∈ Metric.ball c r, f z = 0 := by
  by_contra! h
  refine hdeg (degree_toBasedLoop_eq_zero_of_forall_ne_zero hr hf (fun z hz hz₀ ↦ ?_) hu)
  rcases (Metric.mem_closedBall.1 hz).lt_or_eq with hlt | heq
  · exact h z (Metric.mem_ball.2 hlt) hz₀
  -- A point of the boundary circle is `c + r ζ` for `ζ` its direction from `c`, and the equation
  -- for `u ζ` excludes a zero there.
  have hz : c + r * (exp (Complex.arg (z - c)) : ℂ) = z := by
    rw [← heq, dist_eq_norm, coe_exp, Complex.norm_mul_exp_arg_mul_I, add_sub_cancel]
  have h0 := hu (exp (Complex.arg (z - c)))
  rw [hz] at h0
  exact ne_zero_of_coe_eq_div_norm h0 hz₀

end Circle
