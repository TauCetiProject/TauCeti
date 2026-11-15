/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Convex.StdSimplex

/-!
# The secant estimate on a simplex

Let `F : V → E` be differentiable within a convex set, with derivative within `ε` of a fixed
linear map `A` at every point of the set, and let `p` be finitely many points of the set at mutual
distance at most `d`. The *secant map* of `F` on the simplex spanned by `p` is the linear map of
barycentric coordinates `Fintype.linearCombination ℝ (fun b => F (p b))`, which agrees with `F` at
the vertices. This file proves that, on every direction `v` of the simplex (every coefficient
vector with sum zero), it differs from `A` applied to the corresponding combination of the points
by at most `ε * d * ∑ b, |v b|`. On the standard simplex itself (the points `Pi.single a 1`, at
mutual distance at most one) this says that a lower bound `c * ∑ a, |v a| ≤ ‖A v‖` on the
directions passes to the secant map, weakened by `ε`. Such a lower bound with `c > 0` exists
whenever `A` is injective on the directions, uniformly for a continuous family of such maps over a
compact set.

The derivative of a map within the standard simplex is only determined on the directions of the
simplex. A `C¹` map within the simplex nevertheless has a derivative within the simplex which
depends continuously on the point. Combining this with the estimates above gives the uniform
non-degeneracy of secant maps: if `F` has a continuous derivative within the standard simplex
which is injective on the directions, then for every `t > 0` there is `δ > 0` such that the secant
map of `F` on every simplex of size `d < δ` in the standard simplex which is `t`-fat at scale `d`
is injective on the directions.

These estimates are how Whitehead and Munkres show that the secant map of a smooth triangulation
on a fine subdivision is again non-degenerate.

## Main results

* `Convex.norm_linearCombination_sub_le`: the secant estimate on a simplex in a convex set.
* `IsCompact.exists_pos_norm_linearCombination_sub_le`: uniform first-order approximation on
  small fat simplices, with error relative to the norm of the geometric direction.
* `TauCeti.norm_linearCombination_sub_le`: the secant estimate on the standard simplex.
* `TauCeti.mul_sum_abs_le_norm_linearCombination`: the secant map inherits a lower bound on the
  directions of the simplex from the nearby linear map.
* `IsCompact.exists_pos_mul_sum_abs_le_norm`: a continuous family of linear maps injective on the
  directions of the simplex has such a lower bound, uniformly over a compact set.
* `ContinuousLinearMap.exists_pos_mul_sum_abs_le_norm`: the case of a single linear map.
* `HasFDerivWithinAt.apply_eq_of_sum_eq_zero`: derivatives within the standard simplex agree on
  its directions.
* `ContDiffOn.exists_continuousOn_hasFDerivWithinAt_stdSimplex`: a `C¹` map within the standard
  simplex has a continuous derivative within it.
* `TauCeti.exists_pos_forall_eq_zero_of_linearCombination_eq_zero`: uniform non-degeneracy of
  secant maps on small fat simplices.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 9 (secant approximations).
-/

public section

open Set

/-- **The secant estimate.** Let `F` be differentiable within a convex set `s`, with derivative
within `ε` of a linear map `A` everywhere on `s`, and let `p` be finitely many points of `s` at
mutual distance at most `d`. Then the combination of the values of `F` at these points, with
coefficients `v` summing to zero, differs from `A` applied to the same combination of the points
by at most `ε * d * ∑ b, |v b|`. -/
theorem Convex.norm_linearCombination_sub_le {V E β : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype β] {s : Set V}
    {F : V → E} {F' : V → V →L[ℝ] E} {A : V →L[ℝ] E} {ε d : ℝ}
    (hF : ∀ y ∈ s, HasFDerivWithinAt F (F' y) s y) (hA : ∀ y ∈ s, ‖F' y - A‖ ≤ ε)
    (hs : Convex ℝ s) {p : β → V} (hp : ∀ b, p b ∈ s) (hd : ∀ b b', ‖p b - p b'‖ ≤ d)
    {v : β → ℝ} (hv : ∑ b, v b = 0) :
    ‖Fintype.linearCombination ℝ (fun b => F (p b)) v - A (Fintype.linearCombination ℝ p v)‖ ≤
      ε * d * ∑ b, |v b| := by
  cases isEmpty_or_nonempty β with
  | inl _ =>
    simp [Subsingleton.elim v 0]
  | inr h =>
    -- Compare every point with one fixed point `p b₀`.
    obtain ⟨b₀⟩ := h
    -- The secant map minus `A`, on a direction, is a combination of the errors at the points.
    have hsplit : Fintype.linearCombination ℝ (fun b => F (p b)) v -
        A (Fintype.linearCombination ℝ p v) =
        ∑ b, v b • (F (p b) - F (p b₀) - A (p b - p b₀)) := by
      simp only [Fintype.linearCombination_apply, map_sum, map_smul, map_sub, smul_sub,
        Finset.sum_sub_distrib, ← Finset.sum_smul, hv, zero_smul, sub_zero]
    rw [hsplit]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [norm_smul, Real.norm_eq_abs, mul_comm (ε * d)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    -- Each error is bounded by the mean value inequality.
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hA _ (hp b₀))
    exact (hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hF hA (hp b₀) (hp b)).trans
      (mul_le_mul_of_nonneg_left (hd b b₀) hε)

/-- Secants of a map with continuous derivative on a compact convex set approximate that
derivative uniformly on small simplices of fixed positive fatness. The error is relative to the
norm of the geometric direction, and the derivative may be evaluated anywhere in the convex
hull of the vertices. The vertex type and the number of vertices are arbitrary. -/
theorem IsCompact.exists_pos_norm_linearCombination_sub_le
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set V}
    (hs : IsCompact s) (hconv : Convex ℝ s) {F : V → E} {F' : V → V →L[ℝ] E}
    (hF : ∀ y ∈ s, HasFDerivWithinAt F (F' y) s y) (hF' : ContinuousOn F' s)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ δ > 0, ∀ {β : Type*} [Fintype β] (p : β → V) (d : ℝ),
      (∀ b, p b ∈ s) → d < δ →
      (∀ b b', ‖p b - p b'‖ ≤ d) →
      (∀ v : β → ℝ, ∑ b, v b = 0 →
        t * d * ∑ b, |v b| ≤ ‖Fintype.linearCombination ℝ p v‖) →
      ∀ y ∈ convexHull ℝ (range p), ∀ v : β → ℝ, ∑ b, v b = 0 →
        ‖Fintype.linearCombination ℝ (fun b => F (p b)) v -
          F' y (Fintype.linearCombination ℝ p v)‖ ≤
            ε * ‖Fintype.linearCombination ℝ p v‖ := by
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp
    (hs.uniformContinuousOn_of_continuous hF') (ε * t) (mul_pos hε ht)
  refine ⟨δ, hδ, fun {β} _ p d hp hd hpd hfat y hy v hv => ?_⟩
  have hys : y ∈ s := (convexHull_min (range_subset_iff.mpr hp) hconv) hy
  have hpy (b : β) : ‖p b - y‖ ≤ d := by
    have hball : convexHull ℝ (range p) ⊆ Metric.closedBall (p b) d :=
      convexHull_min (range_subset_iff.mpr fun a => mem_closedBall_iff_norm.mpr (hpd a b))
        (convex_closedBall _ _)
    simpa only [mem_closedBall_iff_norm, norm_sub_rev] using hball hy
  have hbound : ∀ z ∈ s ∩ Metric.closedBall y d, ‖F' z - F' y‖ ≤ ε * t := by
    intro z hz
    rw [← dist_eq_norm]
    exact (hδF z hz.1 y hys ((Metric.mem_closedBall.mp hz.2).trans_lt hd)).le
  have hest := Convex.norm_linearCombination_sub_le
    (s := s ∩ Metric.closedBall y d)
    (fun z hz => (hF z hz.1).mono inter_subset_left) hbound
    (hconv.inter (convex_closedBall _ _))
    (fun b => ⟨hp b, mem_closedBall_iff_norm.mpr (hpy b)⟩) hpd hv
  exact hest.trans (by
    calc
      ε * t * d * ∑ b, |v b| = ε * (t * d * ∑ b, |v b|) := by ring
      _ ≤ ε * ‖Fintype.linearCombination ℝ p v‖ :=
        mul_le_mul_of_nonneg_left (hfat v hv) hε.le)

/-- A continuous family of linear maps, each injective on the directions of the simplex, is
bounded below on them uniformly over a compact set of parameters: there is `c > 0` with
`c * ∑ a, |v a| ≤ ‖A y v‖` for every `y ∈ s` and every vector `v` with coordinate sum zero. -/
theorem IsCompact.exists_pos_mul_sum_abs_le_norm {X α E : Type*} [TopologicalSpace X] [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set X} (hs : IsCompact s)
    {A : X → (α → ℝ) →L[ℝ] E} (hA : ContinuousOn A s)
    (hinj : ∀ y ∈ s, ∀ v : α → ℝ, ∑ a, v a = 0 → A y v = 0 → v = 0) :
    ∃ c > 0, ∀ y ∈ s, ∀ v : α → ℝ, ∑ a, v a = 0 → c * ∑ a, |v a| ≤ ‖A y v‖ := by
  -- The directions with `ℓ¹`-norm one form a compact set, on which `‖A y v‖` is positive.
  let W : Set (α → ℝ) := {v | ∑ a, v a = 0 ∧ ∑ a, |v a| = 1}
  have hW : IsCompact W := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const))
      (Metric.isBounded_closedBall (x := 0) (r := 1) |>.subset fun v hv => ?_)
    rw [mem_closedBall_zero_iff, ← hv.2]
    exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg (v a))).mpr
      fun a => Finset.single_le_sum (f := fun a => |v a|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ a)
  have hcont : ContinuousOn (fun q : X × (α → ℝ) => ‖A q.1 q.2‖) (s ×ˢ W) :=
    ((hA.comp continuousOn_fst mapsTo_fst_prod).clm_apply continuousOn_snd).norm
  obtain ⟨c, hc, hcW⟩ := (hs.prod hW).exists_forall_le' hcont (a := 0) fun q hq =>
    norm_pos_iff.mpr fun h0 => by
      have h1 := hq.2.2
      simp [hinj q.1 hq.1 q.2 hq.2.1 h0] at h1
  refine ⟨c, hc, fun y hy v hv => ?_⟩
  -- Rescale `v` to `ℓ¹`-norm one.
  rcases (Finset.sum_nonneg fun a _ => abs_nonneg (v a)).eq_or_lt with h0 | hr
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  have hmem : (∑ a, |v a|)⁻¹ • v ∈ W := by
    refine ⟨by simp [← Finset.mul_sum, hv], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hr, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hr.ne'
  have h := hcW (y, (∑ a, |v a|)⁻¹ • v) ⟨hy, hmem⟩
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at h
  rwa [le_inv_mul_iff₀ hr, mul_comm] at h

namespace TauCeti

variable {α : Type*} [Fintype α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The secant estimate on the standard simplex.** Let `F` be differentiable within the standard
simplex with derivative within `ε` of a linear map `A` everywhere on it. Then the linear map of
barycentric coordinates that agrees with `F` at the vertices differs from `A` by at most
`ε * ∑ a, |v a|` on every direction `v` of the simplex. -/
theorem norm_linearCombination_sub_le [DecidableEq α] {F : (α → ℝ) → E}
    {F' : (α → ℝ) → (α → ℝ) →L[ℝ] E} {A : (α → ℝ) →L[ℝ] E} {ε : ℝ}
    (hF : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
      HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (hA : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights, ‖F' y - A‖ ≤ ε)
    {v : α → ℝ} (hv : ∑ a, v a = 0) :
    ‖Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) v - A v‖ ≤ ε * ∑ a, |v a| := by
  set S := range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights
  have hvert (a : α) : Pi.single a 1 ∈ S :=
    ⟨.single a, by
      dsimp only
      rw [Convexity.StdSimplex.weights_single, Finsupp.single_eq_pi_single]⟩
  -- The vertices of the simplex are at mutual distance at most one.
  have hdist (a b : α) : ‖(Pi.single a 1 : α → ℝ) - Pi.single b 1‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem
      (Convexity.StdSimplex.isBounded_range_toFun_comp_weights α) (hvert a) (hvert b)).trans
      (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall α)
  have h := Convex.norm_linearCombination_sub_le hF hA
    (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ α) hvert hdist hv
  have hv' : Fintype.linearCombination ℝ (fun a => (Pi.single a 1 : α → ℝ)) v = v := by
    rw [Fintype.linearCombination_apply]
    exact (pi_eq_sum_univ' v).symm
  rwa [hv', mul_one] at h

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

end TauCeti

namespace ContinuousLinearMap

variable {α : Type*} [Fintype α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear map which is injective on the directions of the simplex is bounded below on them:
there is `c > 0` with `c * ∑ a, |v a| ≤ ‖A v‖` for every vector `v` with coordinate sum zero. -/
theorem exists_pos_mul_sum_abs_le_norm (A : (α → ℝ) →L[ℝ] E)
    (hA : ∀ v : α → ℝ, ∑ a, v a = 0 → A v = 0 → v = 0) :
    ∃ c > 0, ∀ v : α → ℝ, ∑ a, v a = 0 → c * ∑ a, |v a| ≤ ‖A v‖ := by
  obtain ⟨c, hc, h⟩ := isCompact_singleton.exists_pos_mul_sum_abs_le_norm
    (continuousOn_const (c := A) (s := {()})) fun _ _ => hA
  exact ⟨c, hc, h () rfl⟩

end ContinuousLinearMap

/-! ### Derivatives within the standard simplex -/

section Derivative

variable {α : Type*} [Fintype α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two derivatives of a map within the standard simplex, at a point of the simplex, agree on the
directions of the simplex, the vectors with coordinate sum zero. -/
theorem HasFDerivWithinAt.apply_eq_of_sum_eq_zero {F : (α → ℝ) → E} {f₁ f₂ : (α → ℝ) →L[ℝ] E}
    {y : α → ℝ}
    (h₁ : HasFDerivWithinAt F f₁ (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (h₂ : HasFDerivWithinAt F f₂ (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (hy : y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) {v : α → ℝ}
    (hv : ∑ a, v a = 0) : f₁ v = f₂ v := by
  classical
  set S := range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights
  -- The edge from `y` to every vertex is tangent to the simplex at `y`.
  have hedge (a : α) : f₁ (Pi.single a 1 - y) = f₂ (Pi.single a 1 - y) := by
    have hvert : Pi.single a 1 ∈ S :=
      ⟨.single a, by
        dsimp only
        rw [Convexity.StdSimplex.weights_single, Finsupp.single_eq_pi_single]⟩
    exact h₁.unique_on h₂ (mem_tangentConeAt_of_segment_subset
      ((Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ α).segment_subset hy hvert))
  -- A direction is the combination of these edges with its own coordinates as coefficients.
  have hv' : v = ∑ a, v a • (Pi.single a 1 - y) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hv, zero_smul, sub_zero]
    exact pi_eq_sum_univ' v
  rw [hv']
  simp only [map_sum, map_smul, hedge]

/-- **Continuous derivatives within the standard simplex.** A `C¹` map within the standard simplex
has a derivative within the simplex at every point of the simplex which depends continuously on
the point. Such derivatives are only determined on the directions of the simplex, so this is a
choice of derivative, not a statement about `fderivWithin`. -/
theorem ContDiffOn.exists_continuousOn_hasFDerivWithinAt_stdSimplex {F : (α → ℝ) → E}
    (hF : ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights)) :
    ∃ F' : (α → ℝ) → (α → ℝ) →L[ℝ] E,
      (∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
        HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y) ∧
      ContinuousOn F' (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) := by
  set S := range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights
  have hsum {z : α → ℝ} (hz : z ∈ S) : ∑ a, z a = 1 := by
    obtain ⟨t, rfl⟩ := hz
    exact t.total_of_fintype
  -- `P z` is the projection onto the directions of the simplex along `z`.
  let σ : (α → ℝ) →L[ℝ] ℝ := ∑ a, ContinuousLinearMap.proj a
  let P : (α → ℝ) → (α → ℝ) →L[ℝ] α → ℝ := fun z =>
    ContinuousLinearMap.id ℝ (α → ℝ) - ContinuousLinearMap.smulRightL ℝ (α → ℝ) (α → ℝ) σ z
  have hP (z v : α → ℝ) : P z v = v - (∑ a, v a) • z := by
    simp [P, σ, Finset.sum_smul]
  have hPdir {z : α → ℝ} (hz : z ∈ S) (v : α → ℝ) : ∑ a, P z v a = 0 := by
    simp [hP, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum hz]
  have hPcont : Continuous P :=
    continuous_const.sub (ContinuousLinearMap.smulRightL ℝ (α → ℝ) (α → ℝ) σ).continuous
  have hdiff := hF.differentiableOn one_ne_zero
  refine ⟨fun z => (fderivWithin ℝ F S z).comp (P z), fun y hy => ?_, fun y hy => ?_⟩
  · -- On the simplex, `P y` fixes every difference `x - y`, so the projected derivative is still a
    -- derivative within the simplex.
    refine HasFDerivWithinAt.of_isLittleO
      ((hdiff y hy).hasFDerivWithinAt.isLittleO.congr' ?_ (by rfl))
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxy : ∑ a, (x - y) a = 0 := by
      simp [Finset.sum_sub_distrib, hsum hx, hsum hy]
    simp only [ContinuousLinearMap.comp_apply, hP, hxy, zero_smul, sub_zero]
  · -- Near `y`, a continuous local derivative agrees with `fderivWithin` on the directions.
    obtain ⟨u, hu, -, f', hf', hf'c⟩ :=
      (contDiffOn_succ_iff_hasFDerivWithinAt (n := 0) (by simp)).mp (by simpa using hF) y hy
    rw [insert_eq_of_mem hy] at hu
    rw [contDiffOn_zero] at hf'c
    obtain ⟨U, hUo, hyU, hUu⟩ := mem_nhdsWithin.mp hu
    have heq : ∀ z ∈ S ∩ U, (fderivWithin ℝ F S z).comp (P z) = (f' z).comp (P z) := by
      rintro z ⟨hzS, hzU⟩
      have h₂ : HasFDerivWithinAt F (f' z) S z :=
        (hasFDerivWithinAt_inter (hUo.mem_nhds hzU)).mp
          ((hf' z (hUu ⟨hzU, hzS⟩)).mono fun x hx => hUu ⟨hx.2, hx.1⟩)
      ext1 v
      exact (hdiff z hzS).hasFDerivWithinAt.apply_eq_of_sum_eq_zero h₂ hzS (hPdir hzS v)
    have hcont : ContinuousWithinAt (fun z => (f' z).comp (P z)) S y :=
      ((hf'c y (mem_of_mem_nhdsWithin hy hu)).mono_of_mem_nhdsWithin hu).clm_comp
        hPcont.continuousWithinAt
    refine hcont.congr_of_eventuallyEq ?_ (heq y ⟨hy, hyU⟩)
    filter_upwards [inter_mem_nhdsWithin S (hUo.mem_nhds hyU)] with z hz using heq z hz

end Derivative

namespace TauCeti

variable {α : Type*} [Fintype α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniform non-degeneracy of secant maps.** Let `F` have a derivative `F'` within the standard
simplex which is continuous on the simplex and injective on its directions. For every `t > 0`
there is `δ > 0` with the following property. Let `p` be finitely many points of the simplex at
mutual distance at most `d`, where `0 < d < δ`, which are `t`-fat at scale `d`: every combination
of them with coefficients `v` summing to zero has norm at least `t * d * ∑ b, |v b|`. Then the
secant map of `F` on the simplex spanned by `p`, the linear map of barycentric coordinates sending
the vertices to the values `F (p b)`, is injective on the directions. -/
theorem exists_pos_forall_eq_zero_of_linearCombination_eq_zero {F : (α → ℝ) → E}
    {F' : (α → ℝ) → (α → ℝ) →L[ℝ] E}
    (hF : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
      HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (hF' : ContinuousOn F' (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights))
    (hinj : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
      ∀ v : α → ℝ, ∑ a, v a = 0 → F' y v = 0 → v = 0) {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, ∀ {β : Type*} [Fintype β] (p : β → α → ℝ) (d : ℝ),
      (∀ b, p b ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) → 0 < d → d < δ →
      (∀ b b', ‖p b - p b'‖ ≤ d) →
      (∀ v : β → ℝ, ∑ b, v b = 0 → t * d * ∑ b, |v b| ≤ ‖Fintype.linearCombination ℝ p v‖) →
      ∀ v : β → ℝ, ∑ b, v b = 0 → Fintype.linearCombination ℝ (fun b => F (p b)) v = 0 →
        v = 0 := by
  set S := range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights
  have hS : IsCompact S :=
    isCompact_range
      (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights (R := ℝ) α).continuous
  obtain ⟨c, hc, hcS⟩ := hS.exists_pos_mul_sum_abs_le_norm hF' hinj
  obtain ⟨δ, hδ, hδS⟩ := hS.exists_pos_norm_linearCombination_sub_le
    (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ α) hF hF' ht
    (half_pos hc)
  refine ⟨δ, hδ, fun {β} _ p d hp hd hdδ hpd hfat v hv hv0 => ?_⟩
  cases isEmpty_or_nonempty β with
  | inl _ =>
    exact Subsingleton.elim _ _
  | inr h =>
  obtain ⟨b₀⟩ := h
  have hest := hδS p d hp hdδ hpd hfat (p b₀)
    (subset_convexHull ℝ _ (mem_range_self b₀)) v hv
  rw [hv0, zero_sub, norm_neg] at hest
  -- The combination of the points is a direction of the simplex, so the lower bound applies.
  set w := Fintype.linearCombination ℝ p v
  have hw : ∑ a, w a = 0 := by
    have hsum (b : β) : ∑ a, p b a = 1 := by
      obtain ⟨s, hs⟩ := hp b
      rw [← hs]
      exact s.total_of_fintype
    simp only [w, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hsum, hv]
  have hnorm : ‖w‖ ≤ ∑ a, |w a| :=
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg (w a))).mpr
      fun a => Finset.single_le_sum (f := fun a => |w a|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ a)
  have hlow := hcS _ (hp b₀) w hw
  have hfat' := hfat v hv
  -- The relative error is less than the derivative lower bound, forcing the direction to
  -- vanish; positive fatness then forces every coefficient to vanish.
  have hsum0 : ∑ b, |v b| ≤ 0 := by
    have hpos : 0 < c * t * d := by positivity
    nlinarith
  funext b
  exact abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun b _ => abs_nonneg _).mp
    (le_antisymm hsum0 (Finset.sum_nonneg fun b _ => abs_nonneg _)) b (Finset.mem_univ b))

end TauCeti
