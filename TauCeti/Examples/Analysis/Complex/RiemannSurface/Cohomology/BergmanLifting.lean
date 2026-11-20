/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Analysis.Complex.RiemannSurface.Cohomology.BergmanCochains

/-!
# Uniform Bergman lifting on compact complex curves

Native finite coordinate covers give five nested families on the Riemann sphere and on the
sum of two Riemann spheres. Duplicating each chart gives a constant coboundary that reads one
at an actual overlap containing infinity. One positive constant controls all middle cocycles
on each fixed family, including this nonzero coboundary and zero data. The empty original is
also an application of the uniform lifting theorem.
-/

public noncomputable section

open CategoryTheory Metric Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff ENNReal Topology OnePoint

universe w u
namespace TauCeti.Examples.BergmanLifting
open TauCeti.RiemannSurface.ChartBergman

variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]

namespace DiscCover
variable (D : DiscCover X)

/-- One constant lifts all cocycles, including the selected native coboundary. -/
theorem uniform_lift_selected [IsManifold 𝓘(ℂ) 1 X] :
    ∃ C > 0,
      (∀ ξ : cocycles₁ (e := D.chart₂) (W := D.level 3) 1
          (subset_source_of_le D.outer_source
          D.middle_le_outer),
        ∃ t : compatibleTriples (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source
          D.middle_le_outer D.inner_le_middle,
          middleProjection (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer
            D.inner_le_middle t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖) ∧
      ∃ t : compatibleTriples (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source
        D.middle_le_outer D.inner_le_middle,
        middleProjection (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer
          D.inner_le_middle t = D.constantCocycle ∧
        ‖t‖ ≤ C * ‖D.constantCocycle‖ := by
  exact D.uniform_lift.imp fun C h ↦ ⟨h.1, h.2, h.2 D.constantCocycle⟩

/-- One constant lifts all cocycles and the selected nonzero native coboundary. -/
theorem uniform_lift_constantCocycle [IsManifold 𝓘(ℂ) 1 X]
    (hne : D.constantCocycle ≠ 0) :
    ∃ C > 0,
      (∀ ξ : cocycles₁ (e := D.chart₂) (W := D.level 3) 1
          (subset_source_of_le D.outer_source
          D.middle_le_outer),
        ∃ t : compatibleTriples (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source
          D.middle_le_outer D.inner_le_middle,
          middleProjection (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer
            D.inner_le_middle t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖) ∧
      D.constantCocycle ≠ 0 ∧
      ∃ t : compatibleTriples (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source
        D.middle_le_outer D.inner_le_middle,
        middleProjection (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer
          D.inner_le_middle t = D.constantCocycle ∧
        ‖t‖ ≤ C * ‖D.constantCocycle‖ := by
  exact D.uniform_lift.imp fun C h ↦ ⟨h.1, h.2, hne, h.2 D.constantCocycle⟩

/-- Zero middle data has an actual zero native triple with the same geometric families. -/
theorem zero_lift [IsManifold 𝓘(ℂ) 1 X] :
    ∃ t : compatibleTriples (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer
      D.inner_le_middle,
      middleProjection (e := D.chart₂)
          (W := D.level 4) (W' := D.level 3) (W'' := D.inner)
          1 D.outer_source D.middle_le_outer
        D.inner_le_middle t = 0 ∧ ‖t‖ = 0 := by
  have h := D.uniform_lift
  rcases h with ⟨C, _, hL⟩
  have hz := hL 0
  rcases hz with ⟨t, ht, hn⟩
  have hn0 : ‖(0 : cocycles₁ (e := D.chart₂) (W := D.level 3) 1
      (subset_source_of_le D.outer_source D.middle_le_outer))‖ = 0 :=
    norm_zero (E := cocycles₁ (e := D.chart₂) (W := D.level 3) 1
      (subset_source_of_le D.outer_source D.middle_le_outer))
  rw [hn0, mul_zero] at hn
  exact ⟨t, ht, le_antisymm hn (norm_nonneg t)⟩

end DiscCover




section Curves
open TauCeti.RiemannSurface.ChartBergman

/-- Actual six-radius coordinate-cover data on the native Riemann sphere. -/
def sphereCover := chosenDiscCover (X := OnePoint ℂ)

/-- The selected native middle cocycle literally reads one at infinity. -/
theorem sphere_reading_one :
    ∃ i j, (∞ : OnePoint ℂ) ∈ sphereCover.level 3 i ⊓ sphereCover.level 3 j ∧
      BergmanSpace.representative (sphereCover.constantCocycle.val i j)
        (sphereCover.chart₂ i ∞) = 1 :=
  sphereCover.constantCocycle_reading_one ∞

/-- The concrete Riemann-sphere cocycle is genuinely nonzero as a native Bergman cocycle. -/
theorem sphere_cocycle_ne_zero : sphereCover.constantCocycle ≠ 0 := by
  intro h
  obtain ⟨i, j, hx, heval⟩ := sphere_reading_one
  have hξ : sphereCover.constantCocycle.val i j = 0 := by
    exact congrArg (fun ξ ↦ ξ.val i j) h
  have hmem := (sphereCover.chart₂ i).map_mem_imageOpens
    (sphereCover.outer_source i (sphereCover.middle_le_outer i hx.1)) hx
  rw [hξ, BergmanSpace.representative_zero hmem] at heval
  exact zero_ne_one heval

/-- One constant lifts all sphere cocycles and also the selected nonzero native coboundary. -/
theorem sphere_uniform_lift :
    ∃ C > 0,
      (∀ ξ : cocycles₁ (e := sphereCover.chart₂) (W := sphereCover.level 3) 1
          (subset_source_of_le sphereCover.outer_source
          sphereCover.middle_le_outer),
        ∃ t : compatibleTriples (e := sphereCover.chart₂)
          (W := sphereCover.level 4) (W' := sphereCover.level 3) (W'' := sphereCover.inner)
          1 sphereCover.outer_source
          sphereCover.middle_le_outer sphereCover.inner_le_middle,
          middleProjection (e := sphereCover.chart₂)
          (W := sphereCover.level 4) (W' := sphereCover.level 3) (W'' := sphereCover.inner)
          1 sphereCover.outer_source sphereCover.middle_le_outer
            sphereCover.inner_le_middle t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖) ∧
      sphereCover.constantCocycle ≠ 0 ∧
      ∃ t : compatibleTriples (e := sphereCover.chart₂)
          (W := sphereCover.level 4) (W' := sphereCover.level 3) (W'' := sphereCover.inner)
          1 sphereCover.outer_source
        sphereCover.middle_le_outer sphereCover.inner_le_middle,
        middleProjection (e := sphereCover.chart₂)
          (W := sphereCover.level 4) (W' := sphereCover.level 3) (W'' := sphereCover.inner)
          1 sphereCover.outer_source sphereCover.middle_le_outer
          sphereCover.inner_le_middle t = sphereCover.constantCocycle ∧
        ‖t‖ ≤ C * ‖sphereCover.constantCocycle‖ :=
  sphereCover.uniform_lift_constantCocycle sphere_cocycle_ne_zero

/-- Zero middle data has an actual zero native triple with the same geometric families. -/
theorem sphere_zero_lift :
    ∃ t : compatibleTriples (e := sphereCover.chart₂)
          (W := sphereCover.level 4) (W' := sphereCover.level 3) (W'' := sphereCover.inner)
          1 sphereCover.outer_source sphereCover.middle_le_outer
      sphereCover.inner_le_middle,
      middleProjection (e := sphereCover.chart₂)
          (W := sphereCover.level 4) (W' := sphereCover.level 3) (W'' := sphereCover.inner)
          1 sphereCover.outer_source sphereCover.middle_le_outer
        sphereCover.inner_le_middle t = 0 ∧ ‖t‖ = 0 := sphereCover.zero_lift

/-- The existing native empty complex charted-space structure. -/
local instance emptyChartedSpace : ChartedSpace ℂ PEmpty.{u + 1} :=
  ChartedSpace.empty ℂ PEmpty.{u + 1}

/-- Literal empty original: the same native cover construction and lifting theorem apply. -/
theorem empty_original_uniform_lift :
    ∃ C > 0, ∀ ξ : cocycles₁ 1 (subset_source_of_le
      (chosenDiscCover (X := PEmpty.{u + 1})).outer_source
      (chosenDiscCover (X := PEmpty.{u + 1})).middle_le_outer),
      ∃ t : compatibleTriples 1 (chosenDiscCover (X := PEmpty.{u + 1})).outer_source
        (chosenDiscCover (X := PEmpty.{u + 1})).middle_le_outer
        (chosenDiscCover (X := PEmpty.{u + 1})).inner_le_middle,
        middleProjection 1 (chosenDiscCover (X := PEmpty.{u + 1})).outer_source
          (chosenDiscCover (X := PEmpty.{u + 1})).middle_le_outer
          (chosenDiscCover (X := PEmpty.{u + 1})).inner_le_middle t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖ :=
  (chosenDiscCover (X := PEmpty.{u + 1})).uniform_lift

/-- Actual cover data on a disconnected union of two native compact closed curves. -/
def disconnectedCover := chosenDiscCover (X := (OnePoint ℂ) ⊕ (OnePoint ℂ))

/-- Both connected components have actual nonzero chart readings of the same native cocycle. -/
theorem disconnected_reading_one :
    (∃ i j, (Sum.inl ∞ : (OnePoint ℂ) ⊕ (OnePoint ℂ)) ∈
      disconnectedCover.level 3 i ⊓ disconnectedCover.level 3 j ∧
      BergmanSpace.representative (disconnectedCover.constantCocycle.val i j)
        (disconnectedCover.chart₂ i (Sum.inl ∞)) = 1) ∧
    (∃ i j, (Sum.inr ∞ : (OnePoint ℂ) ⊕ (OnePoint ℂ)) ∈
      disconnectedCover.level 3 i ⊓ disconnectedCover.level 3 j ∧
      BergmanSpace.representative (disconnectedCover.constantCocycle.val i j)
        (disconnectedCover.chart₂ i (Sum.inr ∞)) = 1) :=
  ⟨disconnectedCover.constantCocycle_reading_one _,
    disconnectedCover.constantCocycle_reading_one _⟩

/-- One constant controls every disconnected-curve cocycle and the selected native coboundary. -/
theorem disconnected_uniform_lift :
    ∃ C > 0,
      (∀ ξ : cocycles₁ (e := disconnectedCover.chart₂) (W := disconnectedCover.level 3) 1
          (subset_source_of_le disconnectedCover.outer_source
          disconnectedCover.middle_le_outer),
        ∃ t : compatibleTriples (e := disconnectedCover.chart₂)
          (W := disconnectedCover.level 4) (W' := disconnectedCover.level 3)
          (W'' := disconnectedCover.inner)
          1 disconnectedCover.outer_source
          disconnectedCover.middle_le_outer disconnectedCover.inner_le_middle,
          middleProjection (e := disconnectedCover.chart₂)
          (W := disconnectedCover.level 4) (W' := disconnectedCover.level 3)
          (W'' := disconnectedCover.inner)
          1 disconnectedCover.outer_source disconnectedCover.middle_le_outer
            disconnectedCover.inner_le_middle t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖) ∧
      ∃ t : compatibleTriples (e := disconnectedCover.chart₂)
          (W := disconnectedCover.level 4) (W' := disconnectedCover.level 3)
          (W'' := disconnectedCover.inner)
          1 disconnectedCover.outer_source
        disconnectedCover.middle_le_outer disconnectedCover.inner_le_middle,
        middleProjection (e := disconnectedCover.chart₂)
          (W := disconnectedCover.level 4) (W' := disconnectedCover.level 3)
          (W'' := disconnectedCover.inner)
          1 disconnectedCover.outer_source disconnectedCover.middle_le_outer
          disconnectedCover.inner_le_middle t = disconnectedCover.constantCocycle ∧
        ‖t‖ ≤ C * ‖disconnectedCover.constantCocycle‖ := by
  exact disconnectedCover.uniform_lift_selected

end Curves

end TauCeti.Examples.BergmanLifting
