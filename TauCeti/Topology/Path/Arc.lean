/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Arcs: ranges of paths in Hausdorff spaces

The range of a path in a Hausdorff space is compact, hence closed, and the path traces a dense
part of it already on the open interval `(0, 1)`. When the path is injective, it is a closed
embedding of the unit interval, so its range is a closed one-dimensional disc whose boundary
sphere is the pair of endpoints.

## Main declarations

* `Path.closure_image_Ioo`: the closure of the set traced by a path on `(0, 1)` is its range.
* `Path.exists_homeomorph_range_closedBall`: the range of an injective path is homeomorphic to the
  closed unit ball of a one-dimensional real normed space, by a homeomorphism carrying the
  endpoints onto the unit sphere.
-/

public section

open Function Metric Module Set

namespace Path

variable {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X}

/-- The closure of the set traced by a path in a Hausdorff space on the open interval `(0, 1)` is
the whole range of the path. -/
theorem closure_image_Ioo (γ : Path x y) : closure (γ '' Ioo 0 1) = range γ := by
  refine (closure_minimal (image_subset_range _ _)
    (isCompact_range γ.continuous).isClosed).antisymm ?_
  have h : closure (Ioo 0 1 : Set unitInterval) = univ := by
    rw [closure_Ioo zero_ne_one, unitInterval.univ_eq_Icc]
  rw [← image_univ, ← h]
  exact image_closure_subset_closure_image γ.continuous

/-- **An arc is a closed one-dimensional disc.** The range of an injective path in a Hausdorff
space is homeomorphic to the closed unit ball of a one-dimensional real normed space, by a
homeomorphism carrying the two endpoints of the path onto the unit sphere. -/
theorem exists_homeomorph_range_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : Path x y} (hγ : Injective γ) (hE : finrank ℝ E = 1) :
    ∃ e : range γ ≃ₜ closedBall (0 : E) 1,
      ∀ z : range γ, (z : X) ∈ ({x, y} : Set X) ↔ ‖(e z : E)‖ = 1 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  -- `t ↦ 2 * t - 1` carries the unit interval onto `[-1, 1]`, the closed unit ball of `ℝ`.
  let e₀ : unitInterval ≃ₜ closedBall (0 : E) 1 :=
    ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm.trans
      (Homeomorph.setCongr (by rw [Real.closedBall_eq_Icc]; norm_num))).trans
      (TauCeti.closedBallHomeomorphOfFinrankEq (by rw [finrank_self, hE]))
  have he₀ (t : unitInterval) : ‖(e₀ t : E)‖ = 1 ↔ t = 0 ∨ t = 1 := by
    simp only [e₀, Homeomorph.trans_apply, TauCeti.coe_closedBallHomeomorphOfFinrankEq_apply,
      ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff]
    -- `Homeomorph.setCongr` does not move points.
    change ‖((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm t : ℝ)‖ = 1 ↔ _
    rw [iccHomeoI_symm_apply_coe, Real.norm_eq_abs, abs_eq zero_le_one]
    constructor
    · rintro (h | h)
      · exact Or.inr (Subtype.ext (show (t : ℝ) = 1 by linarith))
      · exact Or.inl (Subtype.ext (show (t : ℝ) = 0 by linarith))
    · rintro (rfl | rfl) <;> norm_num
  let h := (γ.continuous.isClosedEmbedding hγ).isEmbedding.toHomeomorph
  refine ⟨h.symm.trans e₀, fun z ↦ ?_⟩
  obtain ⟨t, rfl⟩ := h.surjective z
  rw [Homeomorph.trans_apply, Homeomorph.symm_apply_apply, he₀]
  -- The homeomorphism onto the range of the embedding `γ` is `γ`, by definition.
  change γ t ∈ ({x, y} : Set X) ↔ _
  have h0 : γ t = x ↔ t = 0 := (show γ t = x ↔ γ t = γ 0 by rw [Path.source]).trans hγ.eq_iff
  have h1 : γ t = y ↔ t = 1 := (show γ t = y ↔ γ t = γ 1 by rw [Path.target]).trans hγ.eq_iff
  rw [mem_insert_iff, mem_singleton_iff, h0, h1]

end Path

end
