/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.ApproximatesLinearOn
import TauCeti.Analysis.Normed.Operator.CompactFamily
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

The existence and uniqueness of the perturbed critical point follow from
`ContinuousLinearMap.IsInvertible.exists_eq_zero_perturbation`, which rests on Mathlib's
quantitative inverse function theorem: on the ball the differential of `g` approximates the
invertible Hessian of `f` at `x`, so it is injective there and its image contains an explicit ball
around `fderiv ℝ g x`. The Morse index is preserved because the negative index of a nondegenerate
symmetric bilinear form is locally constant.

Nondegeneracy of all critical points on a compact set `K` persists as well: there is
`δ > 0` such that every function `g`, `C²` on `K`, whose first and second derivatives stay within
`δ` of those of `f` on `K`, again has only nondegenerate critical points on `K`. At a point of `K`
either the differential of `f` is far from zero, and then so is that of `g`, or the second
derivative of `f` is far from the closed set of non-invertible operators, and then that of `g` is
invertible. Compactness makes the two alternatives uniform.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint.exists_criticalPoint_perturbation`: in a Banach space, a
  small perturbation has a unique critical point near `x`; it is nondegenerate, with controlled
  location and critical value.
* `TauCeti.IsNondegenerateCriticalPoint.exists_pos_forall_morseIndex_eq`: in finite dimensions,
  a `C²` function whose Hessian at a point is close to the Hessian of `f` at `x` has the same Morse
  index there.
* `TauCeti.IsNondegenerateCriticalPoint.exists_criticalPoint_perturbation_morseIndex_eq`: in
  finite dimensions the perturbed critical point moreover has the Morse index of `x`.
* `TauCeti.HasNondegenerateCriticalPointsOn.exists_pos_forall_hasNondegenerateCriticalPointsOn`:
  in a Banach space, a function `C²`-close to `f` on a compact set on which `f` has only
  nondegenerate critical points has only nondegenerate critical points there.

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
  -- On a small ball, the second derivative of `g` stays close to the invertible Hessian of `f`,
  -- so `fderiv ℝ g` has a unique zero there, with controlled location.
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
    (h.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  obtain ⟨K₀, c, hK₀⟩ := h.isInvertible.exists_eq_zero_perturbation hcont
  set A : ℝ := ‖fderiv ℝ (fderiv ℝ f) x‖ + c
  refine ⟨|K₀| + A / 2 * K₀ ^ 2, ?_⟩
  filter_upwards [hK₀] with r ⟨δ, hδ, hr⟩
  refine ⟨δ, hδ, fun g hg hgx hgf ↦ ?_⟩
  have hdiff : ∀ y ∈ closedBall x r, DifferentiableAt ℝ (fderiv ℝ g) y := fun y hy ↦
    ((hg y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  obtain ⟨happrox, y, hy, hy0, hinv, hdist, huniq⟩ := hr (fderiv ℝ g) hdiff hgf hgx
  set n := ‖fderiv ℝ g x‖
  refine ⟨y, hy, ⟨hg y hy, hy0, hinv⟩, ?_, ?_, huniq⟩
  · calc dist y x ≤ K₀ * n := hdist
      _ ≤ |K₀| * n := by gcongr; exact le_abs_self K₀
      _ ≤ (|K₀| + A / 2 * K₀ ^ 2) * n := by gcongr; exact le_add_of_nonneg_right (by positivity)
  · -- Value: near `y` the differential of `g` is bounded by `A` times the distance to `y`.
    calc |g y - g x| ≤ A / 2 * ‖y - x‖ ^ 2 :=
        Real.norm_eq_abs _ ▸ happrox.norm_sub_le_of_fderiv_eq_zero (convex_closedBall x r)
          (fun w hw ↦ (hg w hw).differentiableAt (by norm_num))
          (mem_closedBall_self (dist_nonneg.trans (mem_closedBall.1 hy))) hy hy0
      _ ≤ A / 2 * (K₀ * n) ^ 2 := by gcongr; rw [← dist_eq_norm]; exact hdist
      _ = A / 2 * K₀ ^ 2 * n ^ 2 := by ring
      _ ≤ (|K₀| + A / 2 * K₀ ^ 2) * n ^ 2 := by
        gcongr; exact le_add_of_nonneg_left (abs_nonneg K₀)

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
    rw [morseIndex_def, hessianQuadraticForm_def]
  -- The negative index is locally constant on the space of symmetric forms.
  let a : {B : E →L[ℝ] E →L[ℝ] ℝ // B.toBilinForm.IsSymm} :=
    ⟨fderiv ℝ (fderiv ℝ f) x, hsymm h.contDiffAt⟩
  have hnd : a.val.toBilinForm.Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft h.separatingLeft
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff
    (α := {B : E →L[ℝ] E →L[ℝ] ℝ // B.toBilinForm.IsSymm}) |>.1
    (ContinuousLinearMap.eventually_sigNeg_toBilinForm_eq_of_continuousAt (V := Subtype.val)
      a.property continuous_subtypeVal.continuousAt hnd)
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

namespace TauCeti.HasNondegenerateCriticalPointsOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

/-- **Nondegeneracy on a compact set persists under small `C²` perturbations.**

Let `f` have only nondegenerate critical points on a compact subset `K` of a Banach space, with
first and second derivatives continuous on `K`. Then there is `δ > 0` such that every function `g`
which is `C²` at each point of `K`, and whose first and second derivatives are within `δ` of those
of `f` at each point of `K`, again has only nondegenerate critical points on `K`. -/
theorem exists_pos_forall_hasNondegenerateCriticalPointsOn [CompleteSpace E] {K : Set E}
    (hK : IsCompact K) (hf₁ : ContinuousOn (fderiv ℝ f) K)
    (hf₂ : ContinuousOn (fderiv ℝ (fderiv ℝ f)) K) (hM : HasNondegenerateCriticalPointsOn f K) :
    ∃ δ > 0, ∀ g : E → ℝ, (∀ x ∈ K, ContDiffAt ℝ 2 g x) →
      (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ δ) →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ δ) →
      HasNondegenerateCriticalPointsOn g K := by
  -- Apply the compactness lemma to the differential and the Hessian of `f`.
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_isInvertible_of_norm_le hf₁ hf₂
    fun x hx h₀ ↦ (hasNondegenerateCriticalPointsOn_iff.1 hM hx h₀).isInvertible
  exact ⟨δ, hδ, fun g hg hg₁ hg₂ ↦ hasNondegenerateCriticalPointsOn_iff.2 fun x hx hgx ↦
    ⟨hg x hx, hgx, h x hx _ (by simpa [hgx] using hg₁ x hx) (hg₂ x hx)⟩⟩

end TauCeti.HasNondegenerateCriticalPointsOn
