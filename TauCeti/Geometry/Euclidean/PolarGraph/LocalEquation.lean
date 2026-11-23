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

A height on the polar cover solves the minimal graph equation if it locally agrees with a
Cartesian solution through the planar projection. Local agreement allows different sheets to
take different values over the same point of the plane. On any continuous local section of the
projection the height is a classical solution, and translating sheets preserves the equation.
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

@[simp] theorem planeProjection_deckShift (k : ℤ) (p : PolarPoint) :
    planeProjection (deckShift k p) = planeProjection p := by
  simp only [planeProjection_def, projection_deckShift]

@[fun_prop] theorem continuous_deckShift (k : ℤ) : Continuous (deckShift k) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : PolarPoint ↦ (deckShift k p).val)
  rw [show (fun p : PolarPoint ↦ (deckShift k p).val) =
      fun p ↦ (p.val.1, p.val.2 + (k : ℝ) * (2 * Real.pi)) by
    funext p
    exact Prod.ext (by rw [← radius_def, radius_deckShift, radius_def])
      (by rw [← angle_def, angle_deckShift, angle_def])]
  fun_prop

/-- Around each point of the domain the height is the pullback of a twice continuously
differentiable Cartesian height satisfying the minimal graph equation at the projected point. -/
@[expose] def IsMinimalHeightOn (u : PolarPoint → ℝ) (Ω : Set PolarPoint) : Prop :=
  ∀ p ∈ Ω, ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
    ContDiffAt ℝ 2 f (planeProjection p) ∧
    MinimalGraph.nondivergenceOperator f (planeProjection p) = 0 ∧
    u =ᶠ[𝓝 p] f ∘ planeProjection

theorem IsMinimalHeightOn.mono {u : PolarPoint → ℝ} {Ω V : Set PolarPoint}
    (hu : IsMinimalHeightOn u Ω) (hV : V ⊆ Ω) : IsMinimalHeightOn u V :=
  fun p hp ↦ hu p (hV hp)

/-- A continuous section of the projection reads a polar solution as a classical Cartesian
solution throughout its open domain. -/
theorem IsMinimalHeightOn.in_chart {u : PolarPoint → ℝ} {Ω : Set PolarPoint}
    (hu : IsMinimalHeightOn u Ω) {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsOpen s)
    {σ : EuclideanSpace ℝ (Fin 2) → PolarPoint} (hσ : ContinuousOn σ s)
    (hπ : ∀ x ∈ s, planeProjection (σ x) = x) (hΩ : MapsTo σ s Ω) :
    ContDiffOn ℝ 2 (u ∘ σ) s ∧ ∀ x ∈ s, MinimalGraph.nondivergenceOperator (u ∘ σ) x = 0 := by
  suffices H : ∀ x ∈ s, ContDiffAt ℝ 2 (u ∘ σ) x ∧ MinimalGraph.nondivergenceOperator (u ∘ σ) x = 0
    from ⟨fun x hx ↦ (H x hx).1.contDiffWithinAt, fun x hx ↦ (H x hx).2⟩
  intro x hx
  obtain ⟨f, hf, hPDE, he⟩ := hu _ (hΩ hx)
  rw [hπ x hx] at hf hPDE
  have hloc : u ∘ σ =ᶠ[𝓝 x] f := by
    filter_upwards [((hσ.continuousAt (hs.mem_nhds hx)).tendsto.eventually he),
      hs.mem_nhds hx] with y hy hys
    simpa only [Function.comp_apply, hπ y hys] using hy
  exact ⟨hf.congr_of_eventuallyEq hloc,
    (MinimalGraph.nondivergenceOperator_congr_of_eventuallyEq hloc).trans hPDE⟩

/-- Translating a polar minimal height to another sheet preserves its equation on the
common domain of the two sheets. -/
theorem IsMinimalHeightOn.deckShift {u : PolarPoint → ℝ} {Ω : Set PolarPoint}
    (hu : IsMinimalHeightOn u Ω) (k : ℤ) :
    IsMinimalHeightOn (u ∘ deckShift k) (overlap Ω k) := by
  intro p hp
  obtain ⟨f, hf, hPDE, he⟩ := hu _ (mem_overlap_iff.mp hp).2
  refine ⟨f, by simpa only [planeProjection_deckShift] using hf,
    by simpa only [planeProjection_deckShift] using hPDE, ?_⟩
  filter_upwards [(continuous_deckShift k).continuousAt.tendsto.eventually he] with q hq
  simpa only [Function.comp_apply, planeProjection_deckShift] using hq

end TauCeti.PolarGraph
