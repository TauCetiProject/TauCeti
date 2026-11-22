/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
import TauCeti.Analysis.Calculus.ApproximatesLinearOn
import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Zeros
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

The existence, uniqueness and location of the perturbed critical point are the persistence of a
nondegenerate zero, `TauCeti.exists_zero_perturbation`, applied to the differential of `g`, which
is a perturbation of the differential of `f` with invertible derivative, the Hessian, at `x`. The
Morse index is preserved because the negative index of a nondegenerate symmetric bilinear form is
locally constant.

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
  -- The critical points of `g` are the zeros of `fderiv ℝ g`, a perturbation of `fderiv ℝ f`
  -- whose derivative at `x` is the invertible Hessian, so `TauCeti.exists_zero_perturbation`
  -- gives existence, uniqueness, nondegeneracy and location. The critical value is estimated by
  -- the mean value inequality on a ball where the Hessian of `f` stays close to its value at `x`.
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) x :=
    (h.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := TauCeti.exists_zero_perturbation hcont h.isInvertible
  obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually_mem (Metric.ball_mem_nhds (fderiv ℝ (fderiv ℝ f) x) (half_pos one_pos)))
  let M : ℝ := ‖fderiv ℝ (fderiv ℝ f) x‖ + 1
  let K : ℝ := |C| + M / 2 * C ^ 2
  refine ⟨K, ?_⟩
  filter_upwards [hC, Ioo_mem_nhdsGT hρ] with r hpert hr
  obtain ⟨δ, hδ, hpert⟩ := hpert
  refine ⟨min δ (1 / 2), by positivity, fun g hg hgx hgf ↦ ?_⟩
  have hd : ∀ y ∈ closedBall x r, DifferentiableAt ℝ (fderiv ℝ g) y := fun y hy ↦
    ((hg y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  obtain ⟨y, hy, hy0, hyinv, hyx, huniq⟩ := hpert (fderiv ℝ g) hd (hgx.trans (min_le_left _ _))
    fun w hw ↦ (hgf w hw).trans (min_le_left _ _)
  set n := ‖fderiv ℝ g x‖
  have hCK : C ≤ K := le_add_of_le_of_nonneg (le_abs_self C) (by positivity)
  refine ⟨y, hy, ⟨hg y hy, hy0, hyinv⟩, hyx.trans (by gcongr), ?_, huniq⟩
  -- On the ball the Hessian of `g` is within `1` of that of `f` at `x`.
  have happrox : ApproximatesLinearOn (fderiv ℝ g) (fderiv ℝ (fderiv ℝ f) x) (closedBall x r) 1 :=
    (convex_closedBall x r).approximatesLinearOn_of_nnnorm_fderiv_sub_le hd fun w hw ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]
      calc ‖fderiv ℝ (fderiv ℝ g) w - fderiv ℝ (fderiv ℝ f) x‖
          ≤ ‖fderiv ℝ (fderiv ℝ g) w - fderiv ℝ (fderiv ℝ f) w‖ +
              ‖fderiv ℝ (fderiv ℝ f) w - fderiv ℝ (fderiv ℝ f) x‖ :=
            norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fderiv ℝ g) w)
              (fderiv ℝ (fderiv ℝ f) w) (fderiv ℝ (fderiv ℝ f) x)
        _ ≤ 1 / 2 + 1 / 2 := add_le_add ((hgf w hw).trans (min_le_right _ _))
            ((mem_ball_iff_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).1
              (hρf (lt_of_le_of_lt (mem_closedBall.1 hw) hr.2))).le
        _ = 1 := add_halves 1
  have hyx' : ‖y - x‖ ≤ C * n := by rwa [← dist_eq_norm]
  calc |g y - g x| ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ + ((1 : ℝ≥0) : ℝ)) / 2 * ‖y - x‖ ^ 2 :=
      Real.norm_eq_abs _ ▸ happrox.norm_sub_le_of_fderiv_eq_zero (convex_closedBall x r)
        (fun w hw ↦ (hg w hw).differentiableAt (by norm_num)) (mem_closedBall_self hr.1.le) hy hy0
    _ ≤ M / 2 * (C * n) ^ 2 := by rw [NNReal.coe_one]; gcongr
    _ = M / 2 * C ^ 2 * n ^ 2 := by ring
    _ ≤ K * n ^ 2 := by gcongr; exact le_add_of_nonneg_left (abs_nonneg C)

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
  -- The non-invertible operators form a closed set `S`; if it is empty there is nothing to prove.
  set S : Set (E →L[ℝ] E →L[ℝ] ℝ) := {T | ¬T.IsInvertible}
  have hS : IsClosed S := ContinuousLinearMap.isOpen_setOfPred_isInvertible.isClosed_compl
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun g hg _ _ ↦ hasNondegenerateCriticalPointsOn_iff.2
      fun x hx hgx ↦ ⟨hg x hx, hgx, not_not.1 fun h ↦ ?_⟩⟩
    exact hSe.subset (show fderiv ℝ (fderiv ℝ g) x ∈ S from h)
  -- `φ x` is positive on `K`: at a critical point of `f` the Hessian lies outside `S`.
  set φ : E → ℝ := fun x ↦ ‖fderiv ℝ f x‖ + infDist (fderiv ℝ (fderiv ℝ f) x) S
  have hφ : ContinuousOn φ K := hf₁.norm.add ((continuous_infDist_pt S).comp_continuousOn hf₂)
  have hpos (x : E) (hx : x ∈ K) : 0 < φ x := by
    by_cases h₀ : fderiv ℝ f x = 0
    · have h := (hS.notMem_iff_infDist_pos hSne).1 fun h ↦
        h (hasNondegenerateCriticalPointsOn_iff.1 hM hx h₀).isInvertible
      simpa [φ, h₀] using h
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.2 h₀) infDist_nonneg
  -- By compactness, `φ` has a positive lower bound `m` on `K`.
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ x ∈ K, m ≤ φ x := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hφ
    exact ⟨φ x₀, hpos x₀ hx₀, fun x hx ↦ hmin hx⟩
  refine ⟨m / 3, by positivity, fun g hg hg₁ hg₂ ↦ hasNondegenerateCriticalPointsOn_iff.2
    fun x hx hgx ↦ ⟨hg x hx, hgx, not_not.1 fun h ↦ ?_⟩⟩
  -- At a critical point of `g` the differential of `f` is at most `m / 3`, so the Hessian of `f`
  -- is at distance at least `2m / 3` from `S`, while that of `g` lies in `S` within `m / 3` of it.
  have h₁ : ‖fderiv ℝ f x‖ ≤ m / 3 := by simpa [hgx] using hg₁ x hx
  have h₂ : infDist (fderiv ℝ (fderiv ℝ f) x) S ≤
      ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ f) x‖ :=
    (infDist_le_dist_of_mem (show fderiv ℝ (fderiv ℝ g) x ∈ S from h)).trans_eq
      ((dist_comm _ _).trans
        (dist_eq_norm (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ f) x)))
  linarith [hmK x hx, hg₂ x hx]

end TauCeti.HasNondegenerateCriticalPointsOn
