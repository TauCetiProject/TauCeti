/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.CoordinateSimplex
public import TauCeti.Topology.PL.Orthant

/-!
# PL coordinates at a vertex of a simplex boundary

The part of the coordinate simplex boundary below its opposite facet is an open
neighbourhood of the vertex at the origin. Subtracting one coordinate from all the
others flattens this neighbourhood onto an open subset of a vector space one dimension
lower. The inverse adjoins zero and subtracts the minimum coordinate, using
`orthantLift`. Both maps have ambient piecewise-affine formulas, including at the vertex.

These polyhedral sphere charts provide PL coordinate maps for triangulated manifolds.
The model includes the
zero-dimensional boundary of a segment, whose vertex neighbourhood is a singleton.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Springer (1972), Chapters 1–2 (polyhedral local models).
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Flatten simplex boundary coordinates by subtracting the distinguished coordinate. -/
def coordinateSimplexBoundaryProjection : (Option ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (some i) : (Option ι → ℝ) →L[ℝ] ℝ) -
      ContinuousLinearMap.proj none

omit [Fintype ι] in
/-- Each flat coordinate is its original value minus the distinguished coordinate. -/
@[simp] theorem coordinateSimplexBoundaryProjection_apply (x : Option ι → ℝ) (i : ι) :
    coordinateSimplexBoundaryProjection x i = x (some i) - x none := (rfl)

/-- Lift flat coordinates to the nonnegative orthant boundary by minimum subtraction. -/
def coordinateSimplexBoundaryLift (y : ι → ℝ) : Option ι → ℝ :=
  Option.elim' (orthantLift y).2 (orthantLift y).1

/-- The lift uses the minimum-subtraction formula of `orthantLift`. -/
theorem coordinateSimplexBoundaryLift_def (y : ι → ℝ) :
    coordinateSimplexBoundaryLift y =
      let m := Finset.univ.inf' Finset.univ_nonempty (Option.elim' 0 y)
      Option.elim' (-m) (fun i => y i - m) := by
  simp only [coordinateSimplexBoundaryLift, orthantLift_def]

/-- The minimum-subtraction lift fixes the origin. -/
@[simp] theorem coordinateSimplexBoundaryLift_zero :
    coordinateSimplexBoundaryLift (0 : ι → ℝ) = 0 := by
  ext i
  cases i <;> simp [coordinateSimplexBoundaryLift]

/-- The lift is piecewise affine on the whole flat coordinate space. -/
theorem isPiecewiseAffineOn_coordinateSimplexBoundaryLift :
    IsPiecewiseAffineOn (coordinateSimplexBoundaryLift : (ι → ℝ) → (Option ι → ℝ)) univ := by
  let A : ((ι → ℝ) × ℝ) →L[ℝ] (Option ι → ℝ) :=
    ContinuousLinearMap.pi (Option.elim' (ContinuousLinearMap.snd ℝ _ _)
      (fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)))
  refine ((isPiecewiseAffineOn_continuousAffineMap A.toContinuousAffineMap univ).comp
    isPiecewiseAffineOn_orthantLift (mapsTo_univ _ _)).congr ?_
  intro y _
  funext i
  cases i <;> rfl

/-- Lifting and then flattening recovers the original flat coordinates. -/
@[simp] theorem coordinateSimplexBoundaryProjection_lift (y : ι → ℝ) :
    coordinateSimplexBoundaryProjection (coordinateSimplexBoundaryLift y) = y := by
  ext i
  simpa only [coordinateSimplexBoundaryProjection_apply, coordinateSimplexBoundaryLift,
    Option.elim'_some, Option.elim'_none, orthantProjection_apply] using
    congrFun (orthantProjection_orthantLift y) i

/-- Flattening and lifting recover a simplex boundary point below the opposite facet. -/
theorem coordinateSimplexBoundaryLift_projection {x : Option ι → ℝ}
    (hboundary : x ∈ frontier (coordinateSimplex (Option ι)))
    (hx : ∑ i, x i < 1) :
    coordinateSimplexBoundaryLift (coordinateSimplexBoundaryProjection x) = x := by
  obtain ⟨⟨hnonneg, _⟩, hz⟩ := (mem_frontier_coordinateSimplex (Option ι) x).mp hboundary
  have hz : ∃ i, x i = 0 := hz.resolve_right hx.ne
  have hp : ((fun i => x (some i)), x none) ∈
      frontier (Ici (0 : (ι → ℝ) × ℝ)) := by
    rw [mem_frontier_nonnegOrthant_iff]
    refine ⟨fun i => hnonneg (some i), hnonneg none, ?_⟩
    obtain ⟨i, hi⟩ := hz
    cases i with
    | none => exact Or.inl hi
    | some i => exact Or.inr ⟨i, hi⟩
  have he := orthantLift_orthantProjection hp
  have hproj : orthantProjection ((fun i => x (some i)), x none) =
      coordinateSimplexBoundaryProjection x := by
    ext i
    simp
  rw [hproj] at he
  funext i
  cases i with
  | none => exact congrArg Prod.snd he
  | some i => exact congrArg (fun p => p.1 i) he

/-- A lifted point lies on the simplex boundary whenever its total mass is less than one. -/
theorem coordinateSimplexBoundaryLift_mem_frontier {y : ι → ℝ}
    (hy : ∑ i, coordinateSimplexBoundaryLift y i < 1) :
    coordinateSimplexBoundaryLift y ∈ frontier (coordinateSimplex (Option ι)) := by
  obtain ⟨hnonneg, ht, hz⟩ := (mem_frontier_nonnegOrthant_iff _).mp
    (orthantLift_mem_frontier y)
  rw [mem_frontier_coordinateSimplex]
  refine ⟨⟨?_, hy.le⟩, Or.inl ?_⟩
  · intro i
    cases i with
    | none => exact ht
    | some i => exact hnonneg i
  · rcases hz with hz | ⟨i, hi⟩
    · exact ⟨none, hz⟩
    · exact ⟨some i, hi⟩

/-- The flat model is open: its lifted coordinate mass is strictly less than one. -/
theorem isOpen_coordinateSimplexBoundaryChartTarget :
    IsOpen {y : ι → ℝ | ∑ i, coordinateSimplexBoundaryLift y i < 1} := by
  have hcont := continuousOn_univ.mp
    (isPiecewiseAffineOn_coordinateSimplexBoundaryLift (ι := ι)).continuousOn
  exact isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).comp hcont)
    continuous_const

/-- The origin belongs to the flat chart target, including when there are no flat coordinates. -/
theorem zero_mem_coordinateSimplexBoundaryChartTarget :
    (0 : ι → ℝ) ∈ {y : ι → ℝ | ∑ i, coordinateSimplexBoundaryLift y i < 1} := by
  simp

end TauCeti
