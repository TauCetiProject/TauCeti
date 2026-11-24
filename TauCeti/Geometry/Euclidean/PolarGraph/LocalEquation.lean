/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# The minimal graph equation on the polar cover

A height on the polar cover solves the minimal graph equation if near each point of its domain
it agrees, through the planar projection, with a twice continuously differentiable Cartesian
height whose minimal graph operator vanishes at the projected point. Local agreement allows
different sheets to take different values over the same point of the plane. On any continuous
local section over an open domain the height is a classical solution, and translating sheets
preserves the equation.

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed
  genus in a 3-manifold IV*, Section 0.
* T. H. Colding and W. P. Minicozzi II, *A Course in Minimal Surfaces*, Section 1.9.
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti.PolarGraph

/-- The polar projection in the real orthonormal coordinates of the complex plane. -/
def planeProjection (p : PolarPoint) : EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr (projection p)

theorem planeProjection_def (p : PolarPoint) :
    planeProjection p = Complex.orthonormalBasisOneI.repr (projection p) := (rfl)

@[simp, grind =] theorem planeProjection_apply_zero (p : PolarPoint) :
    planeProjection p 0 = radius p * Real.cos (angle p) := by
  simp [planeProjection_def, Complex.orthonormalBasisOneI_repr_apply]

@[simp, grind =] theorem planeProjection_apply_one (p : PolarPoint) :
    planeProjection p 1 = radius p * Real.sin (angle p) := by
  simp [planeProjection_def, Complex.orthonormalBasisOneI_repr_apply]

/-- The Euclidean norm of the Cartesian projection is the polar radius. -/
@[simp, grind =] theorem norm_planeProjection (p : PolarPoint) :
    ‖planeProjection p‖ = radius p := by
  simp [planeProjection_def]

/-- The Cartesian projection is continuous on the polar cover. -/
@[fun_prop] theorem continuous_planeProjection : Continuous planeProjection := by
  apply (continuous_congr planeProjection_def).mpr
  exact Complex.orthonormalBasisOneI.repr.continuous.comp continuous_projection

@[simp, grind =] theorem planeProjection_deckShift (k : ℤ) (p : PolarPoint) :
    planeProjection (deckShift k p) = planeProjection p := by
  simp only [planeProjection_def, projection_deckShift]

/-- Around each point of the domain the height is the pullback of a twice continuously
differentiable Cartesian height satisfying the minimal graph equation at the projected point. -/
def IsMinimalHeightOn (u : PolarPoint → ℝ) (Ω : Set PolarPoint) : Prop :=
  ∀ p ∈ Ω, ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
    ContDiffAt ℝ 2 f (planeProjection p) ∧
    MinimalGraph.nondivergenceOperator f (planeProjection p) = 0 ∧
    u =ᶠ[𝓝 p] f ∘ planeProjection

/-- The local Cartesian germs characterizing a minimal height on the polar cover. -/
theorem isMinimalHeightOn_iff {u : PolarPoint → ℝ} {Ω : Set PolarPoint} :
    IsMinimalHeightOn u Ω ↔ ∀ p ∈ Ω, ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiffAt ℝ 2 f (planeProjection p) ∧
      MinimalGraph.nondivergenceOperator f (planeProjection p) = 0 ∧
      u =ᶠ[𝓝 p] f ∘ planeProjection := (Iff.rfl)

theorem IsMinimalHeightOn.mono {u : PolarPoint → ℝ} {Ω V : Set PolarPoint}
    (hu : IsMinimalHeightOn u Ω) (hV : V ⊆ Ω) : IsMinimalHeightOn u V :=
  isMinimalHeightOn_iff.mpr fun p hp ↦ isMinimalHeightOn_iff.mp hu p (hV hp)

/-- A continuous section of the projection reads a polar solution as a classical Cartesian
solution throughout its open domain. -/
theorem IsMinimalHeightOn.contDiffOn_comp_and_nondivergenceOperator_comp_eq_zero
    {u : PolarPoint → ℝ} {Ω : Set PolarPoint}
    (hu : IsMinimalHeightOn u Ω) {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsOpen s)
    {σ : EuclideanSpace ℝ (Fin 2) → PolarPoint} (hσ : ContinuousOn σ s)
    (hπ : ∀ x ∈ s, planeProjection (σ x) = x) (hΩ : MapsTo σ s Ω) :
    ContDiffOn ℝ 2 (u ∘ σ) s ∧ ∀ x ∈ s, MinimalGraph.nondivergenceOperator (u ∘ σ) x = 0 := by
  suffices H : ∀ x ∈ s, ContDiffAt ℝ 2 (u ∘ σ) x ∧ MinimalGraph.nondivergenceOperator (u ∘ σ) x = 0
    from ⟨fun x hx ↦ (H x hx).1.contDiffWithinAt, fun x hx ↦ (H x hx).2⟩
  intro x hx
  obtain ⟨f, hf, hPDE, he⟩ := isMinimalHeightOn_iff.mp hu _ (hΩ hx)
  rw [hπ x hx] at hf hPDE
  have hloc : u ∘ σ =ᶠ[𝓝 x] f := by
    filter_upwards [((hσ.continuousAt (hs.mem_nhds hx)).tendsto.eventually he),
      hs.mem_nhds hx] with y hy hys
    simpa only [Function.comp_apply, hπ y hys] using hy
  exact ⟨hf.congr_of_eventuallyEq hloc,
    (MinimalGraph.nondivergenceOperator_congr_of_eventuallyEq hloc).trans hPDE⟩

/-- Translating a polar minimal height to another sheet preserves its equation on the
preimage of its domain under the deck translation. -/
theorem IsMinimalHeightOn.comp_deckShift {u : PolarPoint → ℝ} {Ω : Set PolarPoint}
    (hu : IsMinimalHeightOn u Ω) (k : ℤ) :
    IsMinimalHeightOn (u ∘ deckShift k) (deckShift k ⁻¹' Ω) := by
  refine isMinimalHeightOn_iff.mpr ?_
  intro p hp
  obtain ⟨f, hf, hPDE, he⟩ := isMinimalHeightOn_iff.mp hu _ hp
  refine ⟨f, by simpa only [planeProjection_deckShift] using hf,
    by simpa only [planeProjection_deckShift] using hPDE, ?_⟩
  filter_upwards [(continuous_deckShift k).continuousAt.tendsto.eventually he] with q hq
  simpa only [Function.comp_apply, planeProjection_deckShift] using hq

end TauCeti.PolarGraph
