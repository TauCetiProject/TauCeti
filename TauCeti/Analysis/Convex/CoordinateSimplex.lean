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
a round sphere. Affine vertex swaps transport the neighbourhood of the origin to the
neighbourhoods of the other vertices.

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

section VertexSwap

variable {ι}

/-- The affine involution exchanging the origin vertex with the `j`th coordinate vertex
of the coordinate simplex. It replaces coordinate `j` by the missing barycentric mass. -/
noncomputable def coordinateSimplexVertexSwap (j : ι) : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) := by
  classical
  exact ContinuousAffineMap.const ℝ (ι → ℝ) (Pi.single j (1 : ℝ) : ι → ℝ) +
    (ContinuousLinearMap.pi fun i => if i = j then
      -(∑ k, (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ))
      else ContinuousLinearMap.proj i).toContinuousAffineMap

/-- The swapped coordinate is the missing mass; all other coordinates are unchanged. -/
theorem coordinateSimplexVertexSwap_apply [DecidableEq ι] (j : ι) (x : ι → ℝ) (i : ι) :
    coordinateSimplexVertexSwap j x i = if i = j then 1 - ∑ k, x k else x i := by
  classical
  by_cases h : i = j <;> simp [coordinateSimplexVertexSwap, h, sub_eq_add_neg]

/-- The total mass after a vertex swap is one minus the original swapped coordinate. -/
@[simp] theorem sum_coordinateSimplexVertexSwap (j : ι) (x : ι → ℝ) :
    ∑ i, coordinateSimplexVertexSwap j x i = 1 - x j := by
  classical
  have heq : coordinateSimplexVertexSwap j x = Function.update x j (1 - ∑ k, x k) := by
    ext i
    simp [coordinateSimplexVertexSwap_apply, Function.update_apply]
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ j)]
  rw [Finset.sdiff_singleton_eq_erase, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  ring

/-- Swapping a vertex with the origin twice is the identity on the ambient space. -/
@[simp] theorem coordinateSimplexVertexSwap_vertexSwap (j : ι) (x : ι → ℝ) :
    coordinateSimplexVertexSwap j (coordinateSimplexVertexSwap j x) = x := by
  classical
  ext i
  rw [coordinateSimplexVertexSwap_apply, sum_coordinateSimplexVertexSwap]
  by_cases h : i = j <;> simp [coordinateSimplexVertexSwap_apply, h]

/-- Vertex swapping preserves and reflects membership in the full coordinate simplex. -/
theorem coordinateSimplexVertexSwap_mem_iff (j : ι) (x : ι → ℝ) :
    coordinateSimplexVertexSwap j x ∈ coordinateSimplex ι ↔ x ∈ coordinateSimplex ι := by
  classical
  have hmap (y : ι → ℝ) (hy : y ∈ coordinateSimplex ι) :
      coordinateSimplexVertexSwap j y ∈ coordinateSimplex ι := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i = j
      · simp only [coordinateSimplexVertexSwap_apply, hi, ite_true]
        linarith [hy.2]
      · simpa [coordinateSimplexVertexSwap_apply, hi] using hy.1 i
    · rw [sum_coordinateSimplexVertexSwap]
      linarith [hy.1 j]
  exact ⟨fun h => by simpa using hmap _ h, hmap x⟩

/-- The ambient homeomorphism exchanging the origin and a coordinate vertex. -/
noncomputable def coordinateSimplexVertexSwapHomeomorph (j : ι) : (ι → ℝ) ≃ₜ (ι → ℝ) where
  toFun := coordinateSimplexVertexSwap j
  invFun := coordinateSimplexVertexSwap j
  left_inv := coordinateSimplexVertexSwap_vertexSwap j
  right_inv := coordinateSimplexVertexSwap_vertexSwap j
  continuous_toFun := (coordinateSimplexVertexSwap j).continuous
  continuous_invFun := (coordinateSimplexVertexSwap j).continuous

/-- Both directions of the vertex homeomorphism use the same affine involution. -/
@[simp] theorem coordinateSimplexVertexSwapHomeomorph_apply (j : ι) (x : ι → ℝ) :
    coordinateSimplexVertexSwapHomeomorph j x = coordinateSimplexVertexSwap j x := (rfl)

/-- The inverse vertex homeomorphism uses the same affine involution. -/
@[simp] theorem coordinateSimplexVertexSwapHomeomorph_symm_apply (j : ι) (x : ι → ℝ) :
    (coordinateSimplexVertexSwapHomeomorph j).symm x = coordinateSimplexVertexSwap j x := (rfl)

/-- A vertex swap preserves the geometric boundary of the coordinate simplex. -/
theorem coordinateSimplexVertexSwap_mem_frontier_iff (j : ι) (x : ι → ℝ) :
    coordinateSimplexVertexSwap j x ∈ frontier (coordinateSimplex ι) ↔
      x ∈ frontier (coordinateSimplex ι) := by
  have hs : (coordinateSimplexVertexSwapHomeomorph j) ⁻¹' coordinateSimplex ι =
      coordinateSimplex ι := Set.ext (coordinateSimplexVertexSwap_mem_iff j)
  have hf := (coordinateSimplexVertexSwapHomeomorph j).preimage_frontier (coordinateSimplex ι)
  rw [hs] at hf
  exact Set.ext_iff.mp hf x

end VertexSwap

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
