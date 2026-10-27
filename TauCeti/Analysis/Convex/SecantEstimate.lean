/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import TauCeti.Analysis.Convex.StdSimplex

/-!
# The secant estimate on a simplex

Let `F : (α → ℝ) → E` be differentiable within the standard simplex, with derivative within `ε`
of a fixed linear map `A` at every point of the simplex. The *secant map* of `F` is the linear map
of barycentric coordinates `Fintype.linearCombination ℝ (fun a => F (Pi.single a 1))`, which
agrees with `F` at the vertices. This file proves that it differs from `A` by at most
`ε * ∑ a, |v a|` on every direction `v` of the simplex (every vector with coordinate sum zero), so
that a lower bound `c * ∑ a, |v a| ≤ ‖A v‖` on the directions passes to the secant map, weakened
by `ε`. Such a lower bound with `c > 0` exists whenever `A` is injective on the directions.

These estimates are how Whitehead and Munkres show that the secant map of a smooth triangulation
on a fine subdivision is again non-degenerate.

## Main results

* `TauCeti.norm_linearCombination_sub_le`: the secant estimate on a simplex.
* `TauCeti.mul_sum_abs_le_norm_linearCombination`: the secant map inherits a lower bound on the
  directions of the simplex from the nearby linear map.
* `TauCeti.exists_pos_mul_sum_abs_le_norm`: a linear map injective on the directions of the
  simplex has such a lower bound.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 9 (secant approximations).
-/

public section

open Set

namespace TauCeti

variable {α : Type*} [Fintype α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The secant estimate.** Let `F` be differentiable within the standard simplex with derivative
within `ε` of a linear map `A` everywhere on it. Then the linear map of barycentric coordinates
that agrees with `F` at the vertices differs from `A` by at most `ε * ∑ a, |v a|` on every
direction `v` of the simplex. -/
theorem norm_linearCombination_sub_le [DecidableEq α] {F : (α → ℝ) → E}
    {F' : (α → ℝ) → (α → ℝ) →L[ℝ] E} {A : (α → ℝ) →L[ℝ] E} {ε : ℝ}
    (hF : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
      HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (hA : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights, ‖F' y - A‖ ≤ ε)
    {v : α → ℝ} (hv : ∑ a, v a = 0) :
    ‖Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) v - A v‖ ≤ ε * ∑ a, |v a| := by
  set S := range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights
  cases isEmpty_or_nonempty α with
  | inl _ =>
    simp [Subsingleton.elim v 0]
  | inr h =>
    -- Compare every vertex with one fixed vertex `p` of the simplex.
    obtain ⟨a₀⟩ := h
    have hS : Convex ℝ S := Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ α
    have hvert (a : α) : Pi.single a 1 ∈ S :=
      ⟨.single a, by
        dsimp only
        rw [Convexity.StdSimplex.weights_single, Finsupp.single_eq_pi_single]⟩
    set p : α → ℝ := Pi.single a₀ 1
    -- The secant map minus `A`, on a direction, is a combination of the vertex errors.
    have hsplit : Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) v - A v =
        ∑ a, v a • (F (Pi.single a 1) - F p - A (Pi.single a 1 - p)) := by
      have hAv : A v = ∑ a, v a • A (Pi.single a 1) := by
        conv_lhs => rw [pi_eq_sum_univ' v]
        simp only [map_sum, map_smul]
      simp only [Fintype.linearCombination_apply, hAv, map_sub, smul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hv, zero_smul, sub_zero]
    rw [hsplit]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [norm_smul, Real.norm_eq_abs, mul_comm ε]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    -- Each vertex error is bounded by the mean value inequality, since the simplex has diameter
    -- at most one.
    have hp : p ∈ S := hvert a₀
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hF hA hS hp (hvert a)
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hA p hp)
    have hdist : ‖Pi.single a 1 - p‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact (Metric.dist_le_diam_of_mem
        (Convexity.StdSimplex.isBounded_range_toFun_comp_weights α) (hvert a) hp).trans
        (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall α)
    exact hmv.trans (mul_le_of_le_one_right hε hdist)

/-- A lower bound `c * ∑ a, |v a| ≤ ‖A v‖` at a direction `v` of the simplex passes, weakened by
`ε`, to the secant map of a map whose derivative is within `ε` of `A` on the simplex. -/
theorem mul_sum_abs_le_norm_linearCombination [DecidableEq α] {F : (α → ℝ) → E}
    {F' : (α → ℝ) → (α → ℝ) →L[ℝ] E} {A : (α → ℝ) →L[ℝ] E} {ε c : ℝ}
    (hF : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
      HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (hA : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights, ‖F' y - A‖ ≤ ε)
    {v : α → ℝ} (hv : ∑ a, v a = 0) (hc : c * ∑ a, |v a| ≤ ‖A v‖) :
    (c - ε) * ∑ a, |v a| ≤ ‖Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) v‖ := by
  have h := norm_linearCombination_sub_le hF hA hv
  have h' := norm_sub_norm_le (A v) (A v - Fintype.linearCombination ℝ
    (fun a => F (Pi.single a 1)) v)
  rw [sub_sub_cancel, norm_sub_rev] at h'
  linarith

/-- A linear map which is injective on the directions of the simplex is bounded below on them:
there is `c > 0` with `c * ∑ a, |v a| ≤ ‖A v‖` for every vector `v` with coordinate sum zero. -/
theorem exists_pos_mul_sum_abs_le_norm (A : (α → ℝ) →L[ℝ] E)
    (hA : ∀ v : α → ℝ, ∑ a, v a = 0 → A v = 0 → v = 0) :
    ∃ c > 0, ∀ v : α → ℝ, ∑ a, v a = 0 → c * ∑ a, |v a| ≤ ‖A v‖ := by
  -- Restricted to the directions of the simplex, `A` is injective, hence antilipschitz.
  let D := LinearMap.ker (Fintype.linearCombination ℝ fun _ : α => (1 : ℝ))
  have hmem {v : α → ℝ} : v ∈ D ↔ ∑ a, v a = 0 := by
    simp [D, Fintype.linearCombination_apply]
  have hker : LinearMap.ker ((A : (α → ℝ) →ₗ[ℝ] E) ∘ₗ D.subtype) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun w hw => Subtype.ext (hA w.1 (hmem.mp w.2) hw)
  obtain ⟨K, hK, hKA⟩ := ((A : (α → ℝ) →ₗ[ℝ] E) ∘ₗ D.subtype).exists_antilipschitzWith hker
  have hcard : (0 : ℝ) < (Fintype.card α + 1) * K := by positivity
  refine ⟨((Fintype.card α + 1) * K)⁻¹, inv_pos.mpr hcard, fun v hv => ?_⟩
  have hvA : ‖v‖ ≤ K * ‖A v‖ := by
    simpa using hKA.le_mul_norm_sub ⟨v, hmem.mpr hv⟩ 0
  have hsum : ∑ a, |v a| ≤ Fintype.card α * ‖v‖ := by
    simpa using Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => norm_le_pi_norm v a
  rw [inv_mul_le_iff₀ hcard]
  calc ∑ a, |v a| ≤ Fintype.card α * (K * ‖A v‖) := hsum.trans (by gcongr)
    _ ≤ (Fintype.card α + 1) * K * ‖A v‖ := by
      rw [← mul_assoc]
      gcongr
      linarith

end TauCeti
