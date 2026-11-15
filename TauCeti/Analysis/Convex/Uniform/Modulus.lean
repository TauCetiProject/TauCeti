/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The modulus of convexity

The modulus of convexity measures the uniform deficit in the triangle inequality for
points of the closed unit ball separated by at least `ε`. We use
`1 - ‖x + y‖ / 2`, which agrees with the usual midpoint deficit in a real normed space.
The infimum is capped at one: thus the modulus is one when no admissible pair exists,
including for `ε > 2` and, in the zero space, for every positive `ε`.

`le_modulusOfConvexity_iff` characterizes lower bounds without unfolding the infimum.
For real normed spaces, positivity at every positive separation is equivalent to
`UniformConvexSpace`. Linear isometric embeddings can only decrease the modulus when
passing to the ambient space; isometric equivalences preserve it.

A space satisfying the two-point inequality

`‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2`

for all `x`, `y` has modulus at least `1 - √(1 - c * ε ^ 2 / 4)`
(`one_sub_sqrt_le_modulusOfConvexity`), hence at least the quadratic `c * ε ^ 2 / 8`
(`mul_sq_div_eight_le_modulusOfConvexity`). Inner product spaces satisfy it with `c = 1`, by the
parallelogram law, and the Ball–Carlen–Lieb inequality gives it for `Lᵖ`, `1 < p ≤ 2`, with
`c = p - 1`.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §5.2.
* K. Ball, E. A. Carlen and E. H. Lieb, *Sharp uniform convexity and smoothness inequalities for
  trace norms*, Invent. Math. 115 (1994), 463–482.
-/

public section

open Set

namespace TauCeti

variable (E : Type*) [SeminormedAddCommGroup E]

/-- The closed-unit-ball modulus of convexity, with value one if there is no pair
at distance at least `ε`. -/
noncomputable def modulusOfConvexity (ε : ℝ) : ℝ :=
  sInf (insert 1 {d | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ ε ≤ ‖x - y‖ ∧
    d = 1 - ‖x + y‖ / 2})

/-- The defining infimum of midpoint deficits, including the empty-pair convention. -/
theorem modulusOfConvexity_def (ε : ℝ) :
    modulusOfConvexity E ε =
      sInf (insert 1 {d | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ ε ≤ ‖x - y‖ ∧
        d = 1 - ‖x + y‖ / 2}) := (rfl)

private theorem modulus_bddBelow (ε : ℝ) :
    BddBelow (insert 1 {d | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ ε ≤ ‖x - y‖ ∧
      d = 1 - ‖x + y‖ / 2}) := by
  refine ⟨0, ?_⟩
  rintro d (rfl | ⟨x, y, hx, hy, -, rfl⟩)
  · norm_num
  · linarith [norm_add_le x y]

/-- A number is a lower bound for the modulus exactly when it is at most one and
bounds the midpoint deficit of every admissible pair. -/
theorem le_modulusOfConvexity_iff {ε a : ℝ} :
    a ≤ modulusOfConvexity E ε ↔ a ≤ 1 ∧
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ε ≤ ‖x - y‖ → a ≤ 1 - ‖x + y‖ / 2 := by
  rw [modulusOfConvexity, le_csInf_iff (modulus_bddBelow E ε) (insert_nonempty _ _)]
  constructor
  · intro h
    exact ⟨h _ (mem_insert _ _), fun x y hx hy hxy ↦
      h _ (mem_insert_of_mem _ ⟨x, y, hx, hy, hxy, rfl⟩)⟩
  · rintro ⟨ha, h⟩ d (rfl | ⟨x, y, hx, hy, hxy, rfl⟩)
    · exact ha
    · exact h x y hx hy hxy

/-- The modulus of convexity is nonnegative. -/
theorem modulusOfConvexity_nonneg (ε : ℝ) : 0 ≤ modulusOfConvexity E ε := by
  apply (le_modulusOfConvexity_iff E).2
  refine ⟨zero_le_one, fun x y hx hy _ ↦ ?_⟩
  linarith [norm_add_le x y]

/-- The modulus of convexity is at most one, including when there are no admissible pairs. -/
theorem modulusOfConvexity_le_one (ε : ℝ) : modulusOfConvexity E ε ≤ 1 :=
  ((le_modulusOfConvexity_iff E).1 le_rfl).1

/-- The modulus bounds the midpoint deficit of each separated pair in the unit ball. -/
theorem modulusOfConvexity_le {ε : ℝ} {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hxy : ε ≤ ‖x - y‖) : modulusOfConvexity E ε ≤ 1 - ‖x + y‖ / 2 :=
  ((le_modulusOfConvexity_iff E).1 le_rfl).2 x y hx hy hxy

/-- The modulus is monotone in the required separation. -/
theorem monotone_modulusOfConvexity : Monotone (modulusOfConvexity E) := by
  intro ε η hεη
  exact (le_modulusOfConvexity_iff E).2 ⟨modulusOfConvexity_le_one E ε,
    fun _ _ hx hy hxy ↦ modulusOfConvexity_le E hx hy (hεη.trans hxy)⟩

/-- Beyond the diameter of the unit ball, the modulus has its capped value one. -/
theorem modulusOfConvexity_eq_one_of_two_lt {ε : ℝ} (hε : 2 < ε) :
    modulusOfConvexity E ε = 1 := by
  refine le_antisymm (modulusOfConvexity_le_one E ε) ((le_modulusOfConvexity_iff E).2 ?_)
  refine ⟨le_rfl, fun x y hx hy hxy ↦ ?_⟩
  have := norm_sub_le x y
  linarith

/-- In the zero space, the modulus is one at every separation. -/
@[simp]
theorem modulusOfConvexity_eq_one_of_subsingleton [Subsingleton E] (ε : ℝ) :
    modulusOfConvexity E ε = 1 := by
  refine le_antisymm (modulusOfConvexity_le_one E ε) ((le_modulusOfConvexity_iff E).2 ?_)
  refine ⟨le_rfl, fun x y _ _ _ ↦ ?_⟩
  simp [Subsingleton.elim x 0, Subsingleton.elim y 0]

/-- The two-point inequality `‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2` bounds the
modulus of convexity below by `1 - √(1 - c * ε ^ 2 / 4)`. -/
theorem one_sub_sqrt_le_modulusOfConvexity {c ε : ℝ}
    (h : ∀ x y : E, ‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2) (hε : 0 ≤ ε) :
    1 - √(1 - c * ε ^ 2 / 4) ≤ modulusOfConvexity E ε := by
  refine (le_modulusOfConvexity_iff E).2
    ⟨by linarith [Real.sqrt_nonneg (1 - c * ε ^ 2 / 4)], fun u v hu hv huv ↦ ?_⟩
  -- Apply the inequality to the half-sum and half-difference, scaled by two.
  have huv' := h (u + v) (u - v)
  rw [show u + v + (u - v) = u + u by abel, show u + v - (u - v) = v + v by abel] at huv'
  have hu2 : ‖u + u‖ ≤ 2 := (norm_add_le u u).trans (by linarith)
  have hv2 : ‖v + v‖ ≤ 2 := (norm_add_le v v).trans (by linarith)
  have hs : ‖u + v‖ / 2 ≤ √(1 - c * ε ^ 2 / 4) := by
    refine Real.le_sqrt_of_sq_le ?_
    rcases le_or_gt 0 c with hc | hc
    · have : c * ε ^ 2 ≤ c * ‖u - v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε huv 2) hc
      nlinarith [norm_nonneg (u + u), norm_nonneg (v + v)]
    · have : ‖u + v‖ ≤ 2 := (norm_add_le u v).trans (by linarith)
      nlinarith [norm_nonneg (u + v)]
  linarith

/-- The two-point inequality `‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2` bounds the
modulus of convexity below by the quadratic `c * ε ^ 2 / 8`, as long as `c * ε ^ 2 ≤ 4`. -/
theorem mul_sq_div_eight_le_modulusOfConvexity {c ε : ℝ}
    (h : ∀ x y : E, ‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2) (hε : 0 ≤ ε)
    (hcε : c * ε ^ 2 ≤ 4) : c * ε ^ 2 / 8 ≤ modulusOfConvexity E ε := by
  refine le_trans ?_ (one_sub_sqrt_le_modulusOfConvexity E h hε)
  have : √(1 - c * ε ^ 2 / 4) ≤ 1 - c * ε ^ 2 / 8 :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith [sq_nonneg (c * ε ^ 2)]⟩
  linarith

variable [NormedSpace ℝ E]

/-- For separation at most two in a space with nonzero seminorm, the modulus is the
usual infimum over pairs in the closed unit ball, without the additional value one. -/
theorem modulusOfConvexity_eq_sInf [NontrivialTopology E] {ε : ℝ} (hε : ε ≤ 2) :
    modulusOfConvexity E ε =
      sInf {d | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ ε ≤ ‖x - y‖ ∧
        d = 1 - ‖x + y‖ / 2} := by
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  have hmem : (1 : ℝ) ∈ {d | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ ε ≤ ‖x - y‖ ∧
      d = 1 - ‖x + y‖ / 2} := by
    refine ⟨x, -x, hx.le, by simpa using hx.le, ?_, by simp⟩
    simpa only [sub_neg_eq_add, ← two_smul ℝ x, norm_smul,
      Real.norm_of_nonneg zero_le_two, hx, mul_one] using hε
  rw [modulusOfConvexity_def, insert_eq_of_mem hmem]

/-- In a space with nonzero seminorm, the modulus vanishes at nonpositive separations. -/
theorem modulusOfConvexity_eq_zero_of_nonpos [NontrivialTopology E] {ε : ℝ} (hε : ε ≤ 0) :
    modulusOfConvexity E ε = 0 := by
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  have h := modulusOfConvexity_le E hx.le hx.le (by simpa using hε : ε ≤ ‖x - x‖)
  rw [← two_smul ℝ x, norm_smul, Real.norm_of_nonneg zero_le_two, hx] at h
  exact le_antisymm (by linarith) (modulusOfConvexity_nonneg E ε)

/-- In a space with nonzero seminorm, the modulus at zero is zero. -/
@[simp]
theorem modulusOfConvexity_zero [NontrivialTopology E] : modulusOfConvexity E 0 = 0 :=
  modulusOfConvexity_eq_zero_of_nonpos E le_rfl

/-- Uniform convexity gives a strictly positive modulus at every positive separation. -/
theorem modulusOfConvexity_pos [UniformConvexSpace E] {ε : ℝ} (hε : 0 < ε) :
    0 < modulusOfConvexity E ε := by
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E hε
  apply lt_of_lt_of_le (lt_min zero_lt_one (half_pos hδ))
  apply (le_modulusOfConvexity_iff E).2
  refine ⟨min_le_left _ _, fun x y hx hy hxy ↦ ?_⟩
  have := h hx hy hxy
  have := min_le_right (1 : ℝ) (δ / 2)
  linarith

/-- A real seminormed space is uniformly convex exactly when its modulus is positive
at every positive separation. -/
theorem uniformConvexSpace_iff_modulusOfConvexity_pos :
    UniformConvexSpace E ↔ ∀ ε : ℝ, 0 < ε → 0 < modulusOfConvexity E ε := by
  refine ⟨fun _ _ hε ↦ modulusOfConvexity_pos E hε, fun h ↦ ⟨fun ε hε ↦ ?_⟩⟩
  refine ⟨2 * modulusOfConvexity E ε, mul_pos two_pos (h ε hε), fun x hx y hy hxy ↦ ?_⟩
  have := modulusOfConvexity_le E hx.le hy.le hxy
  linarith

end TauCeti

namespace LinearIsometry

variable {𝕜 E F : Type*} [Semiring 𝕜]
  [SeminormedAddCommGroup E] [Module 𝕜 E] [SeminormedAddCommGroup F] [Module 𝕜 F]

/-- Passing to a space containing an isometric linear copy can only decrease the modulus. -/
theorem modulusOfConvexity_le (f : E →ₗᵢ[𝕜] F) (ε : ℝ) :
    TauCeti.modulusOfConvexity F ε ≤ TauCeti.modulusOfConvexity E ε := by
  apply (TauCeti.le_modulusOfConvexity_iff E).2
  refine ⟨TauCeti.modulusOfConvexity_le_one F ε, fun x y hx hy hxy ↦ ?_⟩
  simpa only [← map_add, f.norm_map] using TauCeti.modulusOfConvexity_le F
    (by simpa using hx : ‖f x‖ ≤ 1) (by simpa using hy : ‖f y‖ ≤ 1)
    (by simpa only [← map_sub, f.norm_map] using hxy : ε ≤ ‖f x - f y‖)

end LinearIsometry

namespace LinearIsometryEquiv

variable {𝕜 E F : Type*} [Semiring 𝕜]
  [SeminormedAddCommGroup E] [Module 𝕜 E] [SeminormedAddCommGroup F] [Module 𝕜 F]

/-- Linearly isometric spaces have the same modulus of convexity. -/
theorem modulusOfConvexity_eq (f : E ≃ₗᵢ[𝕜] F) (ε : ℝ) :
    TauCeti.modulusOfConvexity E ε = TauCeti.modulusOfConvexity F ε :=
  le_antisymm (f.symm.toLinearIsometry.modulusOfConvexity_le ε)
    (f.toLinearIsometry.modulusOfConvexity_le ε)

end LinearIsometryEquiv
