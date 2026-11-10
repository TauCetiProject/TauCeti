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

variable {ι} in
/-- Every point has positive missing mass `1 - ∑ i, x i` or a positive coordinate: its
barycentric coordinates, including the missing mass, sum to one. -/
theorem sum_lt_one_or_exists_pos (x : ι → ℝ) : ∑ i, x i < 1 ∨ ∃ j, 0 < x j := by
  by_contra! h
  linarith [Finset.sum_nonpos fun j (_ : j ∈ Finset.univ) => h.2 j]

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
@[simp] theorem coordinateSimplexVertexSwap_coordinateSimplexVertexSwap (j : ι) (x : ι → ℝ) :
    coordinateSimplexVertexSwap j (coordinateSimplexVertexSwap j x) = x := by
  classical
  ext i
  rw [coordinateSimplexVertexSwap_apply, sum_coordinateSimplexVertexSwap]
  by_cases h : i = j <;> simp [coordinateSimplexVertexSwap_apply, h]

/-- The vertex swap sends the origin to the chosen coordinate vertex. -/
@[simp] theorem coordinateSimplexVertexSwap_zero [DecidableEq ι] (j : ι) :
    coordinateSimplexVertexSwap j 0 = Pi.single j 1 := by
  ext i
  simp [coordinateSimplexVertexSwap_apply, Pi.single_apply]

/-- The vertex swap sends the chosen coordinate vertex to the origin. -/
@[simp] theorem coordinateSimplexVertexSwap_single [DecidableEq ι] (j : ι) :
    coordinateSimplexVertexSwap j (Pi.single j 1) = 0 := by
  rw [← coordinateSimplexVertexSwap_zero j,
    coordinateSimplexVertexSwap_coordinateSimplexVertexSwap]

/-- Vertex swapping preserves and reflects membership in the full coordinate simplex. -/
theorem coordinateSimplexVertexSwap_mem_iff (j : ι) (x : ι → ℝ) :
    coordinateSimplexVertexSwap j x ∈ coordinateSimplex ι ↔ x ∈ coordinateSimplex ι := by
  classical
  have hmap (y : ι → ℝ) (hy : y ∈ coordinateSimplex ι) :
      coordinateSimplexVertexSwap j y ∈ coordinateSimplex ι := by
    refine ⟨fun i => ?_, by linarith [hy.1 j, sum_coordinateSimplexVertexSwap j y]⟩
    rw [coordinateSimplexVertexSwap_apply]
    split_ifs
    · linarith [hy.2]
    · exact hy.1 i
  exact ⟨fun h => by simpa using hmap _ h, hmap x⟩

/-- The ambient homeomorphism exchanging the origin and a coordinate vertex. -/
noncomputable def coordinateSimplexVertexSwapHomeomorph (j : ι) : (ι → ℝ) ≃ₜ (ι → ℝ) where
  toFun := coordinateSimplexVertexSwap j
  invFun := coordinateSimplexVertexSwap j
  left_inv := coordinateSimplexVertexSwap_coordinateSimplexVertexSwap j
  right_inv := coordinateSimplexVertexSwap_coordinateSimplexVertexSwap j
  continuous_toFun := (coordinateSimplexVertexSwap j).continuous
  continuous_invFun := (coordinateSimplexVertexSwap j).continuous

/-- The vertex homeomorphism applies the affine vertex swap. -/
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

/-- Move a chart's vertex to the origin: `none` denotes the origin and `some j`
denotes the `j`th coordinate vertex. -/
noncomputable def coordinateSimplexChartSwap (v : Option ι) : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) :=
  v.elim (ContinuousAffineMap.id ℝ _) coordinateSimplexVertexSwap

/-- The origin chart leaves the ambient coordinates unchanged. -/
@[simp] theorem coordinateSimplexChartSwap_none (x : ι → ℝ) :
    coordinateSimplexChartSwap none x = x := (rfl)

/-- A coordinate-vertex chart swaps that vertex with the origin. -/
@[simp] theorem coordinateSimplexChartSwap_some (j : ι) (x : ι → ℝ) :
    coordinateSimplexChartSwap (some j) x = coordinateSimplexVertexSwap j x := (rfl)

/-- The chart vertex swap is an involution. -/
@[simp] theorem coordinateSimplexChartSwap_coordinateSimplexChartSwap (v : Option ι)
    (x : ι → ℝ) :
    coordinateSimplexChartSwap v (coordinateSimplexChartSwap v x) = x := by
  cases v <;> simp [coordinateSimplexChartSwap]

/-- A chart vertex swap preserves the coordinate simplex. -/
theorem coordinateSimplexChartSwap_mem_iff (v : Option ι) (x : ι → ℝ) :
    coordinateSimplexChartSwap v x ∈ coordinateSimplex ι ↔ x ∈ coordinateSimplex ι := by
  cases v with
  | none => rfl
  | some j => exact coordinateSimplexVertexSwap_mem_iff j x

/-- A chart vertex swap preserves the geometric boundary of the coordinate simplex. -/
theorem coordinateSimplexChartSwap_mem_frontier_iff (v : Option ι) (x : ι → ℝ) :
    coordinateSimplexChartSwap v x ∈ frontier (coordinateSimplex ι) ↔
      x ∈ frontier (coordinateSimplex ι) := by
  cases v with
  | none => rfl
  | some j => exact coordinateSimplexVertexSwap_mem_frontier_iff j x

end VertexSwap

/-- The coordinate simplex is convex. -/
theorem convex_coordinateSimplex : Convex ℝ (coordinateSimplex ι) := by
  rw [coordinateSimplex, ofPred_and, ofPred_forall]
  exact (convex_iInter fun i => convex_halfSpace_ge (LinearMap.proj i).isLinear 0).inter <| by
    simpa using convex_halfSpace_le (∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).isLinear 1

/-- The coordinate simplex is closed. -/
theorem isClosed_coordinateSimplex : IsClosed (coordinateSimplex ι) := by
  rw [coordinateSimplex, ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (by fun_prop) continuous_const)

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
  rcases isEmpty_or_nonempty ι with h | h
  · simp [coordinateSimplex]
  classical
  let S : (ι → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i
  have hS : Function.Surjective S := fun r => ⟨Pi.single (Classical.arbitrary ι) r, by simp [S]⟩
  have hsum : interior {x : ι → ℝ | ∑ i, x i ≤ 1} = {x | ∑ i, x i < 1} := by
    simpa [S, interior_Iic, preimage] using S.interior_preimage hS (Iic 1)
  have hi (i : ι) : interior {x : ι → ℝ | 0 ≤ x i} = {x | 0 < x i} := by
    simpa [interior_Ici, preimage] using
      ((isOpenMap_eval (X := fun _ : ι => ℝ) i).preimage_interior_eq_interior_preimage
        (continuous_apply i) (Ici 0)).symm
  rw [coordinateSimplex, ofPred_and, ofPred_forall, interior_inter, interior_iInter_of_finite, hsum,
    ofPred_and, ofPred_forall]
  simp_rw [hi]

/-- The points of the coordinate simplex whose coordinate sum is less than one form an open
set in its subtype topology. -/
theorem isOpen_setOf_sum_lt_one_coordinateSimplex :
    IsOpen {y : coordinateSimplex ι | ∑ i, y.1 i < 1} :=
  isOpen_lt (by fun_prop) continuous_const

/-- A point lies on the frontier exactly when it is in the simplex and at least one of its
barycentric coordinates, including the missing mass, vanishes. -/
@[simp]
theorem mem_frontier_coordinateSimplex (x : ι → ℝ) :
    x ∈ frontier (coordinateSimplex ι) ↔
      ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1) ∧ ((∃ i, x i = 0) ∨ ∑ i, x i = 1) := by
  rw [frontier, (isClosed_coordinateSimplex ι).closure_eq, interior_coordinateSimplex]
  simp only [mem_sdiff, mem_coordinateSimplex, mem_ofPred_eq, not_and_or, not_forall]
  exact and_congr_right fun hx => or_congr
    (exists_congr fun i => (hx.1 i).not_lt_iff_eq.trans eq_comm) hx.2.not_lt_iff_eq

/-- The coordinate simplex has nonempty interior. -/
theorem nonempty_interior_coordinateSimplex : (interior (coordinateSimplex ι)).Nonempty := by
  rw [interior_coordinateSimplex]
  refine ⟨fun _ => (Fintype.card ι + 1 : ℝ)⁻¹, fun _ => by positivity, ?_⟩
  simp [← div_eq_mul_inv, div_lt_one (by positivity : (0 : ℝ) < Fintype.card ι + 1)]

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
