/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Basic
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import Mathlib.Topology.Order.IntermediateValue
/-!
# Native Schottky sheet and boundary examples

The closed disc and its actual unit circle exercise full-sheet smoothness and the native boundary.
Finite-order and order-zero clients retain the endpoints of the embedding API. The open upper
half-plane gives a nonempty surface with empty boundary. Empty and disconnected inherited bordered
surfaces require no extra global hypotheses or componentwise choices.
-/

public section

noncomputable section
open Set Complex Filter Topology TopologicalSpace
open scoped Manifold ContDiff
open TauCeti
namespace TauCeti.Examples.SchottkyDouble

example : Manifold.IsSmoothEmbedding closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) ∞
    (DoubleAlong.inl (borderedInterior Complex.UnitClosedDisc : Set Complex.UnitClosedDisc)ᶜ) :=
  SchottkyDouble.isSmoothEmbedding_inl le_rfl

example : Manifold.IsSmoothEmbedding closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) 0
    (DoubleAlong.inr (borderedInterior Complex.UnitClosedDisc : Set Complex.UnitClosedDisc)ᶜ) :=
  SchottkyDouble.isSmoothEmbedding_inr bot_le

example (n : ℕ) : Manifold.IsSmoothEmbedding closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) n
    (DoubleAlong.inl (borderedInterior Complex.UnitClosedDisc : Set Complex.UnitClosedDisc)ᶜ) :=
  SchottkyDouble.isSmoothEmbedding_inl (by simp)

attribute [local instance] ClosedUpperHalfPlane.euclideanHalfSpaceChartedSpace
  ClosedUpperHalfPlane.isManifold_euclideanHalfSpace

example : Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
    (SchottkyDouble.boundaryInl (M := Complex.UnitClosedDisc)) :=
  SchottkyDouble.isSmoothEmbedding_boundaryInl le_rfl

example : Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) 0
    (SchottkyDouble.boundaryInl (M := Complex.UnitClosedDisc)) :=
  SchottkyDouble.isSmoothEmbedding_boundaryInl bot_le

example (p : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1) :
    ∃ q, SchottkyDouble.boundaryInl (M := Complex.UnitClosedDisc) q =
      DoubleAlong.inl (borderedInterior Complex.UnitClosedDisc : Set _)ᶜ p := by
  refine ⟨⟨p, (mem_boundary_euclideanHalfSpace_iff_notMem_borderedInterior p).2 ?_⟩, by simp⟩
  rw [Complex.UnitClosedDisc.mem_borderedInterior_iff]
  simp [hp]

example (z : Circle) :
    ∃ p : (𝓡∂ (1 + 1)).boundary Complex.UnitClosedDisc,
      SchottkyDouble.boundaryInl p = DoubleAlong.inl _
        (Complex.UnitClosedDisc.mk (z : ℂ) (by simp)) := by
  refine ⟨⟨Complex.UnitClosedDisc.mk (z : ℂ) (by simp),
    (mem_boundary_euclideanHalfSpace_iff_notMem_borderedInterior _).2 ?_⟩, by simp⟩
  rw [Complex.UnitClosedDisc.mem_borderedInterior_iff]
  simp

example (p : Complex.UnitClosedDisc) (hp : ‖(p : ℂ)‖ = 1)
    (v : TangentSpace closedUpperHalfPlaneModel p) :
    (v ∈ strictInwardTangentCone closedUpperHalfPlaneModel p ↔
      0 < (mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
        (DoubleAlong.inl (borderedInterior Complex.UnitClosedDisc : Set _)ᶜ) p v).im) ∧
    (v ∈ strictInwardTangentCone closedUpperHalfPlaneModel p ↔
      (mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
        (DoubleAlong.inr (borderedInterior Complex.UnitClosedDisc : Set _)ᶜ) p v).im < 0) := by
  have hb : p ∉ borderedInterior Complex.UnitClosedDisc := by
    rw [Complex.UnitClosedDisc.mem_borderedInterior_iff]
    simp [hp]
  exact ⟨SchottkyDouble.mem_strictInwardTangentCone_iff_im_mfderiv_inl_pos p hb v,
    SchottkyDouble.mem_strictInwardTangentCone_iff_im_mfderiv_inr_neg p hb v⟩

example : Nonempty (borderedInterior ClosedUpperHalfPlane) := by
  refine ⟨⟨⟨I, by simp⟩, ?_⟩⟩
  rw [mem_borderedInterior_iff_im_chartAt_pos]
  simp

example : IsEmpty ((𝓡∂ (1 + 1)).boundary (borderedInterior ClosedUpperHalfPlane)) := by
  constructor
  intro p
  have hp := (mem_boundary_euclideanHalfSpace_iff_notMem_borderedInterior (p : borderedInterior
    ClosedUpperHalfPlane)).1 p.property
  apply hp
  rw [mem_borderedInterior]
  exact closedUpperHalfPlaneModel.isInteriorPoint_iff_isInteriorPoint_val.2
    (mem_borderedInterior.mp p.val.property)

/-- The empty source has its unique topology. -/
local instance emptyTopology : TopologicalSpace Empty := ⊥

/-- The empty source carries the native empty bordered atlas. -/
local instance emptyChartedSpace : ChartedSpace ClosedUpperHalfPlane Empty :=
  ChartedSpace.empty _ _

/-- Compatibility of the empty bordered atlas is vacuous. -/
local instance emptyHasGroupoid : HasGroupoid Empty borderedHolomorphicGroupoid where
  compatible := by
    intro e e' he
    -- The locally installed empty atlas has definitionally no charts.
    change e ∈ (∅ : Set _) at he
    exact he.elim

example : Manifold.IsSmoothEmbedding closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) ∞
    (DoubleAlong.inl (borderedInterior Empty : Set Empty)ᶜ) :=
  SchottkyDouble.isSmoothEmbedding_inl le_rfl
/-- Two disjoint open regions of the closed upper half-plane, with their inherited atlas. -/
def separatedHalfPlanes : Opens ClosedUpperHalfPlane :=
  ⟨{z | (z : ℂ).re < -1 ∨ 1 < (z : ℂ).re},
    by
      -- The defining real-coordinate inequalities give the union of the two open regions.
      change IsOpen ({z : ClosedUpperHalfPlane | (z : ℂ).re < -1} ∪
        {z : ClosedUpperHalfPlane | 1 < (z : ℂ).re})
      exact (isOpen_lt (Complex.continuous_re.comp continuous_subtypeVal)
        continuous_const).union (isOpen_lt continuous_const
          (Complex.continuous_re.comp continuous_subtypeVal))⟩

example : Manifold.IsSmoothEmbedding closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) ∞
    (DoubleAlong.inl (borderedInterior separatedHalfPlanes : Set separatedHalfPlanes)ᶜ) :=
  SchottkyDouble.isSmoothEmbedding_inl le_rfl

example : ¬ PreconnectedSpace separatedHalfPlanes := by
  intro h
  -- These points belong to the two defining real-coordinate regions.
  let a : separatedHalfPlanes :=
    ⟨⟨-2, by simp⟩, by norm_num [separatedHalfPlanes]⟩
  let b : separatedHalfPlanes :=
    ⟨⟨2, by simp⟩, by norm_num [separatedHalfPlanes]⟩
  let f : separatedHalfPlanes → ℝ := fun z ↦ (z.val : ℂ).re
  have hf : Continuous f := Complex.continuous_re.comp
    (continuous_subtypeVal.comp continuous_subtypeVal)
  obtain ⟨x, _, hx⟩ := isPreconnected_univ.intermediate_value (a := a) (b := b)
    (mem_univ _) (mem_univ _) hf.continuousOn (show (0 : ℝ) ∈ Icc (f a) (f b) by
      constructor <;> norm_num [f, a, b])
  have hx' : ((x.val : ℂ).re) = 0 := by simpa only [f] using hx
  have hxmem := x.property
  -- Expand membership in the chosen open set to contradict the intermediate real coordinate.
  change (x.val : ℂ).re < -1 ∨ 1 < (x.val : ℂ).re at hxmem
  rcases hxmem with hxlt | hxgt <;> rw [hx'] at * <;> linarith
end TauCeti.Examples.SchottkyDouble
