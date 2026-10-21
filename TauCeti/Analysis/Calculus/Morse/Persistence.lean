/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.ApproximatesLinearOn
import TauCeti.Analysis.Matrix.HermitianSignature.Continuity

/-!
# Persistence of nondegenerate critical points under small `C²` perturbations

A nondegenerate critical point `x` of `f` survives every sufficiently small `C²` perturbation:
on each sufficiently small closed ball around `x` there is a threshold `δ > 0` such that every
function `g` which is `C²` on the ball, whose differential at `x` has norm at most `δ`, and whose
second derivative stays within `δ` of that of `f` on the ball, has exactly one critical point in
the ball. That critical point is nondegenerate, its distance to `x` is linearly controlled by
`‖fderiv ℝ g x‖`, and its critical value differs from `g x` by a quadratic amount in
`‖fderiv ℝ g x‖`. In finite dimensions its Morse index is that of `x`.

Unlike the continuation theorem
`TauCeti.IsNondegenerateCriticalPoint.exists_contDiffAt_criticalPoint_continuation`, no
parametrised family is involved: the perturbation is an arbitrary function, and the size of the
admissible perturbation is uniform on the chosen ball. A perturbation that is `C²`-close to `f`
on the ball satisfies the hypotheses, since the differential of `f` vanishes at `x`.

The existence and uniqueness of the perturbed critical point follow from Mathlib's quantitative
inverse function theorem: on the ball the differential of `g` approximates the invertible Hessian
of `f` at `x`, so it is injective there and its image contains an explicit ball around
`fderiv ℝ g x`. The Morse index is preserved because the negative index of a nondegenerate
symmetric bilinear form is locally constant.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint.exists_criticalPoint_perturbation`: in a Banach space, a
  small perturbation has a unique critical point near `x`; it is nondegenerate, with controlled
  location and critical value.
* `TauCeti.IsNondegenerateCriticalPoint.exists_pos_forall_morseIndex_eq`: in finite dimensions,
  a `C²` function whose Hessian at a point is close to the Hessian of `f` at `x` has the same Morse
  index there.
* `TauCeti.IsNondegenerateCriticalPoint.exists_criticalPoint_perturbation_morseIndex_eq`: in
  finite dimensions the perturbed critical point moreover has the Morse index of `x`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, §2.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace TauCeti.IsNondegenerateCriticalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}

/-- **Persistence of a nondegenerate critical point under small `C²` perturbations.**

Let `x` be a nondegenerate critical point of `f` on a Banach space. For every sufficiently small
radius `r` there is `δ > 0` with the following property. If `g` is `C²` at every point of the
closed ball of radius `r` around `x`, the differential of `g` at `x` has norm at most `δ`, and the
second derivatives of `g` and `f` differ by at most `δ` on that ball, then `g` has a critical point
`y` in the ball, and it is the only one there. It is nondegenerate, lies within
`K * ‖fderiv ℝ g x‖` of `x`, and its critical value differs from `g x` by at most
`K * ‖fderiv ℝ g x‖ ^ 2`, for a constant `K` depending only on `f` and `x`. -/
theorem exists_criticalPoint_perturbation [CompleteSpace E]
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ K : ℝ, ∀ᶠ r in 𝓝[>] 0, ∃ δ > 0, ∀ g : E → ℝ,
      (∀ y ∈ closedBall x r, ContDiffAt ℝ 2 g y) →
      ‖fderiv ℝ g x‖ ≤ δ →
      (∀ y ∈ closedBall x r,
        ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ f) y‖ ≤ δ) →
      ∃ y ∈ closedBall x r, IsNondegenerateCriticalPoint g y ∧
        dist y x ≤ K * ‖fderiv ℝ g x‖ ∧ |g y - g x| ≤ K * ‖fderiv ℝ g x‖ ^ 2 ∧
        ∀ z ∈ closedBall x r, fderiv ℝ g z = 0 → z = y := by
  -- On a small ball, `fderiv ℝ g` approximates the invertible Hessian `L` of `f` at `x`, so it
  -- has a unique zero there; the remaining estimates are read off on the smaller ball of radius
  -- `2 * C * ‖fderiv ℝ g x‖` containing that zero.
  obtain ⟨L, hL⟩ := h.isInvertible
  -- `C` bounds the inverse of the Hessian `L` and is positive even on the zero space.
  let C : ℝ := ‖(L.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ + 1
  have hC : 0 < C := by positivity
  have hLsymm : ‖(L.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ ≤ C := le_add_of_nonneg_right zero_le_one
  obtain ⟨ε₀, hε₀, hinv⟩ := Metric.eventually_nhds_iff.1 h.isInvertible.eventually_nhds
  -- `κ` is the admissible distance from the Hessian `L` on the ball.
  let κ : ℝ := min (2 * C)⁻¹ (ε₀ / 2)
  have hκ : 0 < κ := by positivity
  have hκC : 2 * C * κ ≤ 1 :=
    calc 2 * C * κ ≤ 2 * C * (2 * C)⁻¹ := by gcongr; exact min_le_left _ _
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hκε₀ : κ < ε₀ := (min_le_right _ _).trans_lt (half_lt_self hε₀)
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
    (h.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually_mem (Metric.ball_mem_nhds (fderiv ℝ (fderiv ℝ f) x) (half_pos hκ)))
  let K : ℝ := 2 * C + 8 * (‖(L : E →L[ℝ] E →L[ℝ] ℝ)‖ + κ) * C ^ 2
  refine ⟨K, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  refine ⟨min (κ / 2) (r / (2 * C)), by have := hr.1; positivity, fun g hg hgx hgf ↦ ?_⟩
  have hdiff : ∀ y ∈ closedBall x r, DifferentiableAt ℝ (fderiv ℝ g) y := fun y hy ↦
    ((hg y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- On the ball the second derivative of `g` stays within `κ` of `L`.
  have hclose : ∀ y ∈ closedBall x r,
      ‖fderiv ℝ (fderiv ℝ g) y - (L : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ κ := fun y hy ↦ by
    have hfy : ‖fderiv ℝ (fderiv ℝ f) y - (L : E →L[ℝ] E →L[ℝ] ℝ)‖ < κ / 2 := by
      rw [hL]
      exact (mem_ball_iff_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).1 <|
        hρf (lt_of_le_of_lt (mem_closedBall.1 hy) hr.2)
    calc ‖fderiv ℝ (fderiv ℝ g) y - (L : E →L[ℝ] E →L[ℝ] ℝ)‖
        ≤ ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ f) y‖ +
            ‖fderiv ℝ (fderiv ℝ f) y - (L : E →L[ℝ] E →L[ℝ] ℝ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fderiv ℝ g) y)
            (fderiv ℝ (fderiv ℝ f) y) (L : E →L[ℝ] E →L[ℝ] ℝ)
      _ ≤ κ / 2 + κ / 2 := add_le_add ((hgf y hy).trans (min_le_left _ _)) hfy.le
      _ = κ := add_halves _
  have happrox : ApproximatesLinearOn (fderiv ℝ g) (L : E →L[ℝ] E →L[ℝ] ℝ)
      (closedBall x r) ⟨κ, hκ.le⟩ := fun y hy z hz ↦
    (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le' hdiff hclose hz hy
  set n := ‖fderiv ℝ g x‖
  have hεr : 2 * C * n ≤ r := by
    have : n ≤ r / (2 * C) := hgx.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  obtain ⟨y, hyε, hy0, huniq⟩ := happrox.exists_eq_zero_of_two_mul_norm_le hC hLsymm hκC hεr
  have hsub : closedBall x (2 * C * n) ⊆ closedBall x r := closedBall_subset_closedBall hεr
  have hKC : 2 * C ≤ K := by
    have : 0 ≤ 8 * (‖(L : E →L[ℝ] E →L[ℝ] ℝ)‖ + κ) * C ^ 2 := by positivity
    linarith
  refine ⟨y, hsub hyε, ⟨hg y (hsub hyε), hy0, hinv ?_⟩, ?_, ?_, huniq⟩
  · -- Nondegeneracy: the Hessian of `g` at `y` is within `κ < ε₀` of `L`.
    rw [← hL]
    exact (dist_eq_norm (fderiv ℝ (fderiv ℝ g) y) (L : E →L[ℝ] E →L[ℝ] ℝ)).trans_lt
      ((hclose y (hsub hyε)).trans_lt hκε₀)
  · calc dist y x ≤ 2 * C * n := mem_closedBall.1 hyε
      _ ≤ K * n := by gcongr
  · -- Value: near `y` the differential of `g` is bounded by `(‖L‖ + κ)` times the distance to `y`.
    let M : ℝ := ‖(L : E →L[ℝ] E →L[ℝ] ℝ)‖ + κ
    have hbound : ∀ w ∈ closedBall x (2 * C * n), ‖fderiv ℝ g w‖ ≤ M * (2 * (2 * C * n)) :=
      fun w hw ↦ by
        have hlip := happrox.lipschitzWith.dist_le_mul ⟨w, hsub hw⟩ ⟨y, hsub hyε⟩
        simp only [domRestrict_apply, hy0, dist_zero_right, Subtype.dist_eq] at hlip
        calc ‖fderiv ℝ g w‖ ≤ M * dist w y := hlip
          _ ≤ M * (2 * (2 * C * n)) := by
            gcongr
            linarith [dist_triangle_right w y x, mem_closedBall.1 hw, mem_closedBall.1 hyε]
    have hval := (convex_closedBall x (2 * C * n)).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw ↦ ((hg w (hsub hw)).differentiableAt (by norm_num))) hbound
      (mem_closedBall_self (by positivity)) hyε
    rw [Real.norm_eq_abs, ← dist_eq_norm] at hval
    calc |g y - g x| ≤ M * (2 * (2 * C * n)) * dist y x := hval
      _ ≤ M * (2 * (2 * C * n)) * (2 * C * n) := by gcongr; exact mem_closedBall.1 hyε
      _ = (8 * M * C ^ 2) * n ^ 2 := by ring
      _ ≤ K * n ^ 2 := by gcongr; linarith

/-- **The Morse index is stable under small changes of the Hessian.**

In finite dimensions, there is `ε > 0` such that every function `g` which is `C²` at a point `y`
and whose Hessian at `y` is within `ε` of the Hessian of `f` at the nondegenerate critical point
`x` has the Morse index of `f` at `x`. The point `y` need not be critical. -/
theorem exists_pos_forall_morseIndex_eq [FiniteDimensional ℝ E]
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ ε > 0, ∀ ⦃g : E → ℝ⦄ ⦃y : E⦄, ContDiffAt ℝ 2 g y →
      ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ f) x‖ < ε →
        morseIndex g y = morseIndex f x := by
  have hsymm {g : E → ℝ} {y : E} (hg : ContDiffAt ℝ 2 g y) :
      (fderiv ℝ (fderiv ℝ g) y).toBilinForm.IsSymm :=
    ⟨hg.isSymmSndFDerivAt (by simp)⟩
  have hmorse (g : E → ℝ) (y : E) :
      morseIndex g y = sigNeg (fderiv ℝ (fderiv ℝ g) y).toBilinForm.toQuadraticMap := by
    rw [morseIndex_def]
    congr 1
    ext v
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hessianQuadraticForm_apply,
      ContinuousLinearMap.toBilinForm_apply]
  -- The negative index is locally constant on the space of symmetric forms.
  let a : {B : E →L[ℝ] E →L[ℝ] ℝ // B.toBilinForm.IsSymm} :=
    ⟨fderiv ℝ (fderiv ℝ f) x, hsymm h.contDiffAt⟩
  have hnd : a.1.toBilinForm.Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft h.separatingLeft
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff
    (α := {B : E →L[ℝ] E →L[ℝ] ℝ // B.toBilinForm.IsSymm}) |>.1
    (ContinuousLinearMap.eventually_sigNeg_toBilinForm_eq_of_continuousAt (V := Subtype.val)
      (Eventually.of_forall fun B ↦ B.2) continuous_subtype_val.continuousAt hnd)
  refine ⟨ε, hε, fun g y hg hlt ↦ ?_⟩
  rw [hmorse, hmorse f x]
  refine hball (y := ⟨_, hsymm hg⟩) ?_
  rw [Subtype.dist_eq]
  exact (dist_eq_norm (fderiv ℝ (fderiv ℝ g) y) (fderiv ℝ (fderiv ℝ f) x)).trans_lt hlt

/-- **Persistence of a nondegenerate critical point with its Morse index.**

In finite dimensions, the unique critical point of a small `C²` perturbation provided by
`exists_criticalPoint_perturbation` moreover has the Morse index of `f` at `x`. -/
theorem exists_criticalPoint_perturbation_morseIndex_eq [FiniteDimensional ℝ E]
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ K : ℝ, ∀ᶠ r in 𝓝[>] 0, ∃ δ > 0, ∀ g : E → ℝ,
      (∀ y ∈ closedBall x r, ContDiffAt ℝ 2 g y) →
      ‖fderiv ℝ g x‖ ≤ δ →
      (∀ y ∈ closedBall x r,
        ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ f) y‖ ≤ δ) →
      ∃ y ∈ closedBall x r, IsNondegenerateCriticalPoint g y ∧
        morseIndex g y = morseIndex f x ∧
        dist y x ≤ K * ‖fderiv ℝ g x‖ ∧ |g y - g x| ≤ K * ‖fderiv ℝ g x‖ ^ 2 ∧
        ∀ z ∈ closedBall x r, fderiv ℝ g z = 0 → z = y := by
  obtain ⟨K, hK⟩ := h.exists_criticalPoint_perturbation
  obtain ⟨ε, hε, hindex⟩ := h.exists_pos_forall_morseIndex_eq
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
    (h.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually_mem (Metric.ball_mem_nhds (fderiv ℝ (fderiv ℝ f) x) (half_pos hε)))
  refine ⟨K, ?_⟩
  filter_upwards [hK, Ioo_mem_nhdsGT hρ] with r ⟨δ, hδ, hr⟩ hrρ
  refine ⟨min δ (ε / 2), by positivity, fun g hg hgx hgf ↦ ?_⟩
  obtain ⟨y, hy, hnd, hdist, hval, huniq⟩ := hr g hg (hgx.trans (min_le_left _ _))
    fun y hy ↦ (hgf y hy).trans (min_le_left _ _)
  refine ⟨y, hy, hnd, hindex (hg y hy) ?_, hdist, hval, huniq⟩
  have hfy : ‖fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ f) x‖ < ε / 2 := by
    exact (mem_ball_iff_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).1 <|
      hρf (lt_of_le_of_lt (mem_closedBall.1 hy) hrρ.2)
  calc ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ f) x‖
      ≤ ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ f) y‖ +
          ‖fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ f) x‖ :=
        norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fderiv ℝ g) y) (fderiv ℝ (fderiv ℝ f) y)
          (fderiv ℝ (fderiv ℝ f) x)
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt ((hgf y hy).trans (min_le_right _ _)) hfy
    _ = ε := add_halves _

end TauCeti.IsNondegenerateCriticalPoint
