/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The coordinate simplex as a convex body

The coordinate simplex is the set of nonnegative coordinate vectors with total mass at most
one. Unlike the barycentric simplex, it is full dimensional: the missing mass is the
coordinate of its vertex at the origin. Its frontier consists of the points with a zero
coordinate or total mass one. This identifies the proper barycentric faces with a geometric
boundary, and allows Mathlib's convex-body rescaling theorem to identify that boundary with
a round sphere.

Reference: C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 2. The sphere identification uses Mathlib's
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall` by Yury Kudryashov.
-/

public section

open Set Metric Topology

namespace TauCeti

variable (ι : Type*) [Fintype ι]

/-- The full-dimensional simplex spanned by the origin and the coordinate unit vectors. -/
def coordinateSimplex : Set (ι → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- Membership in the coordinate simplex is nonnegativity and a bound on total mass. -/
@[simp]
theorem mem_coordinateSimplex (x : ι → ℝ) :
    x ∈ coordinateSimplex ι ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := (Iff.rfl)

/-- The coordinate simplex is convex. -/
theorem convex_coordinateSimplex : Convex ℝ (coordinateSimplex ι) := by
  have heq : coordinateSimplex ι =
      (⋂ i, {x : ι → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x
    simp
  rw [heq]
  refine (convex_iInter fun i =>
    convex_halfSpace_ge (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).isLinear 0).inter ?_
  simpa using convex_halfSpace_le
    (∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).isLinear 1

/-- The coordinate simplex is closed. -/
theorem isClosed_coordinateSimplex : IsClosed (coordinateSimplex ι) := by
  have heq : coordinateSimplex ι =
      (⋂ i, {x : ι → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x
    simp
  rw [heq]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

/-- Every coordinate of a point of the simplex lies in the unit interval. -/
theorem coordinateSimplex_subset_Icc : coordinateSimplex ι ⊆ Icc 0 1 := by
  intro x hx
  exact ⟨hx.1, fun i => (Finset.single_le_sum (fun j _ => hx.1 j)
    (Finset.mem_univ i)).trans hx.2⟩

/-- The coordinate simplex is compact, including in dimension zero. -/
theorem isCompact_coordinateSimplex : IsCompact (coordinateSimplex ι) :=
  isCompact_Icc.of_isClosed_subset (isClosed_coordinateSimplex ι)
    (coordinateSimplex_subset_Icc ι)

/-- The interior of the coordinate simplex consists of positive vectors with mass less than
one. -/
theorem interior_coordinateSimplex : interior (coordinateSimplex ι) =
    {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    simp [coordinateSimplex]
  | inr h =>
    let := h
    have heq : coordinateSimplex ι =
        (⋂ i, (fun x : ι → ℝ => x i) ⁻¹' Ici 0) ∩
          (fun x : ι → ℝ => ∑ i, x i) ⁻¹' Iic 1 := by
      ext x
      simp
    let S : (ι → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i
    have hS : Function.Surjective S := by
      classical
      intro r
      exact ⟨Pi.single (Classical.arbitrary ι) r, by simp [S]⟩
    rw [heq, interior_inter, interior_iInter_of_finite]
    have hi (i : ι) : interior ((fun x : ι → ℝ => x i) ⁻¹' Ici 0) =
        (fun x : ι → ℝ => x i) ⁻¹' Ioi 0 := by
      rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage
        (continuous_apply i), interior_Ici]
    simp_rw [hi]
    have hsum : interior ((fun x : ι → ℝ => ∑ i, x i) ⁻¹' Iic 1) =
        (fun x : ι → ℝ => ∑ i, x i) ⁻¹' Iio 1 := by
      have hcoe : (S : (ι → ℝ) → ℝ) = fun x => ∑ i, x i := by
        funext x
        simp [S]
      simpa only [hcoe, interior_Iic] using S.interior_preimage hS (Iic 1)
    rw [hsum]
    ext x
    simp

/-- A point lies on the frontier exactly when it is in the simplex and at least one of its
barycentric coordinates, including the missing mass, vanishes. -/
@[simp]
theorem mem_frontier_coordinateSimplex (x : ι → ℝ) :
    x ∈ frontier (coordinateSimplex ι) ↔
      ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1) ∧ ((∃ i, x i = 0) ∨ ∑ i, x i = 1) := by
  rw [frontier, (isClosed_coordinateSimplex ι).closure_eq, interior_coordinateSimplex]
  simp only [mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    by_cases hs : ∑ i, x i = 1
    · exact Or.inr hs
    · have hn : ¬∀ i, 0 < x i := fun hp => h ⟨hp, lt_of_le_of_ne hx.2 hs⟩
      obtain ⟨i, hi⟩ := not_forall.mp hn
      exact Or.inl ⟨i, le_antisymm (not_lt.mp hi) (hx.1 i)⟩
  · rintro ⟨hx, (⟨i, hi⟩ | hs)⟩
    · exact ⟨hx, fun h => by simpa [hi] using h.1 i⟩
    · exact ⟨hx, fun h => by simpa [hs] using h.2⟩

/-- The coordinate simplex has nonempty interior. -/
theorem nonempty_interior_coordinateSimplex : (interior (coordinateSimplex ι)).Nonempty := by
  rw [interior_coordinateSimplex]
  have hp : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  refine ⟨fun _ => (Fintype.card ι + 1 : ℝ)⁻¹, fun _ => inv_pos.mpr hp, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have he : (Fintype.card ι + 1 : ℝ) * (Fintype.card ι + 1 : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hp.ne'
  have hi := inv_pos.mpr hp
  nlinarith

/-- An ambient homeomorphism identifies the coordinate simplex, its interior and its
frontier with the Euclidean unit closed ball, open ball and sphere, respectively. -/
theorem exists_homeomorph_coordinateSimplex :
    ∃ e : (ι → ℝ) ≃ₜ EuclideanSpace ℝ ι,
      e '' coordinateSimplex ι = closedBall 0 1 ∧
      e '' interior (coordinateSimplex ι) = ball 0 1 ∧
      e '' frontier (coordinateSimplex ι) = sphere 0 1 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let s := e '' coordinateSimplex ι
  have hc : Convex ℝ s := (convex_coordinateSimplex ι).linear_image e.toLinearMap
  have hn : (interior s).Nonempty :=
    (e.toHomeomorph.image_interior _).symm ▸
      (nonempty_interior_coordinateSimplex ι).image _
  have hs : IsCompact s := (isCompact_coordinateSimplex ι).image e.continuous
  obtain ⟨h, hint, hcl, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hn hs.isBounded
  refine ⟨e.toHomeomorph.trans h, ?_, ?_, ?_⟩
  all_goals
    have hcoe : (e.toHomeomorph.trans h : (ι → ℝ) → EuclideanSpace ℝ ι) = h ∘ e := (rfl)
    rw [hcoe, image_comp]
  · rw [hs.isClosed.closure_eq] at hcl
    exact hcl
  · exact (congrArg (fun t => h '' t) (e.toHomeomorph.image_interior _)).trans hint
  · exact (congrArg (fun t => h '' t) (e.toHomeomorph.image_frontier _)).trans hfr

end TauCeti
