/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.Dual.Basic

/-!
# Goldstine's theorem

**Goldstine's theorem** says that the canonical embedding of a normed space `E` into its bidual
maps the closed unit ball of `E` onto a weak-star dense subset of the closed unit ball of the
bidual. We prove it for every closed ball: the weak-star closure of the image of
`closedBall x r` under `NormedSpace.inclusionInDoubleDualWeak` is the closed ball of radius `r`
about the image of `x`. In particular `E` is weak-star dense in its bidual.

No completeness or separability is assumed, and seminormed spaces are allowed. Together with
Banach–Alaoglu (`WeakDual.isCompact_closedBall`), Goldstine's theorem relates weak compactness
of the unit ball of `E` to reflexivity of `E`.

## Main results

* `NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall`: Goldstine's theorem.
* `NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall_zero_one`: its unit-ball form.
* `NormedSpace.denseRange_inclusionInDoubleDualWeak`: `E` is weak-star dense in its bidual.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Theorem 2.6.26.
-/

public section

open Metric RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace NormedSpace

variable (𝕜 E)

/-- **Goldstine's theorem.** The weak-star closure of the image of the closed ball `closedBall x r`
under the canonical embedding into the bidual is the closed ball of radius `r` about the image
of `x`. -/
theorem closure_image_inclusionInDoubleDualWeak_closedBall (x : E) (r : ℝ) :
    closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall x r)) =
      WeakDual.toStrongDual ⁻¹' closedBall (inclusionInDoubleDual 𝕜 E x) r := by
  -- `WeakDual` carries no `IsScalarTower ℝ 𝕜` or `LocallyConvexSpace ℝ` instance; transfer them
  -- from the continuous dual and from the seminorms defining the weak-star topology, as needed
  -- for real Hahn–Banach separation. The real structure on `E` gives convexity of balls.
  let : IsScalarTower ℝ 𝕜 (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    inferInstanceAs (IsScalarTower ℝ 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
  let : LocallyConvexSpace ℝ (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    (WeakDual.withSeminorms 𝕜 (StrongDual 𝕜 E)).toLocallyConvexSpace
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  set S := inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall x r)
  have hS : S ⊆ WeakDual.toStrongDual ⁻¹' closedBall (inclusionInDoubleDual 𝕜 E x) r := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    -- The bidual's metric is not reducibly the one of its normed group, so name the type.
    rw [Set.mem_preimage, inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toStrongDual_toWeakDual,
      mem_closedBall_iff_norm (E := StrongDual 𝕜 (StrongDual 𝕜 E)),
      ← map_sub (inclusionInDoubleDual 𝕜 E) y x]
    exact (double_dual_bound 𝕜 E _).trans (mem_closedBall_iff_norm.1 hy)
  refine (closure_minimal hS (WeakDual.isClosed_closedBall _ _)).antisymm fun φ hφ ↦ ?_
  -- A point `φ` of the bidual ball outside the weak-star closure is separated from it by
  -- Hahn–Banach, through a weak-star continuous functional, which is evaluation at some `f` in
  -- the dual. `StrongDual.re_apply_add_mul_norm_le` bounds `re (f x) + r * ‖f‖` by the separating
  -- constant, while `φ` lying in the ball bounds `re (φ f)` by `re (f x) + r * ‖f‖`, which
  -- contradicts the separation.
  by_contra hφS
  have hconv : Convex ℝ S := by
    simp only [S, Set.image_image]
    exact (convex_closedBall x r).linear_image
      (((inclusionInDoubleDualWeak 𝕜 E).toLinearMap ∘ₗ
        (toWeakSpace 𝕜 E).toLinearMap).restrictScalars ℝ)
  obtain ⟨l, u, hl, hlφ⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hconv.closure isClosed_closure hφS
  -- Every weak-star continuous functional on the bidual is evaluation at a point of the dual.
  obtain ⟨f, hf⟩ := WeakDual.exists_forall_apply_eq_apply l
  have hfu : ∀ y ∈ closedBall x r, re (f y) ≤ u := fun y hy ↦ by
    have := (hl _ (subset_closure ⟨_, ⟨y, hy, rfl⟩, rfl⟩)).le
    rwa [hf, inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toWeakDual_apply, dual_def] at this
  have hfx := StrongDual.re_apply_add_mul_norm_le (dist_nonneg.trans hφ) hfu
  -- On the other hand `re (φ f) ≤ re (f x) + ‖φ - J x‖ * ‖f‖ ≤ re (f x) + r * ‖f‖`.
  have hφf : re (φ f) ≤ re (f x) + r * ‖f‖ := by
    have hφ' := (mem_closedBall_iff_norm (E := StrongDual 𝕜 (StrongDual 𝕜 E))).1 hφ
    have key := (re_le_norm _).trans
      (((WeakDual.toStrongDual φ - inclusionInDoubleDual 𝕜 E x).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right hφ' (norm_nonneg f)))
    rw [sub_apply, dual_def, WeakDual.toStrongDual_apply, map_sub] at key
    linarith
  rw [hf] at hlφ
  exact (hlφ.trans_le hφf).not_ge hfx

/-- **Goldstine's theorem**, unit-ball form: the closed unit ball of `E` has weak-star dense
image in the closed unit ball of its bidual. -/
theorem closure_image_inclusionInDoubleDualWeak_closedBall_zero_one :
    closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 1)) =
      WeakDual.toStrongDual ⁻¹' closedBall 0 1 := by
  simpa using closure_image_inclusionInDoubleDualWeak_closedBall 𝕜 E 0 1

/-- A normed space is weak-star dense in its bidual. -/
theorem denseRange_inclusionInDoubleDualWeak : DenseRange (inclusionInDoubleDualWeak 𝕜 E) := by
  intro φ
  refine closure_mono (Set.image_subset_range _ (toWeakSpace 𝕜 E '' closedBall 0
    ‖WeakDual.toStrongDual φ‖)) ?_
  rw [closure_image_inclusionInDoubleDualWeak_closedBall, map_zero]
  exact (mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))).2 le_rfl

end NormedSpace
