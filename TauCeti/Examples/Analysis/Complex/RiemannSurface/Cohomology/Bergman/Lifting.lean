/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Cochains
public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Lifting
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

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

variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace DiscCover
variable (D : DiscCover X)

/-- The chosen five native families satisfy the complete uniform lifting conclusion. -/
theorem uniform_lift [IsManifold 𝓘(ℂ) 1 X] [T2Space X] :
    ∃ C > 0, ∀ ξ : D.cocycles,
      ∃ t : D.triples,
        D.proj t = ξ ∧
          ‖t‖ ≤ C * ‖ξ‖ := by
  have hcover : ⋃ i, ((D.chart₂ i).preimageBall (D.center₂ i) (D.radius₂ i) : Set X) =
      univ := by
    simpa only [Fin.val_zero, Nat.cast_zero, zero_add, level, one_mul] using
      D.iUnion_level_eq_univ 0
  have hcov : IsOpenCover fun i ↦
      (D.chart₂ i).preimageBall (D.center₂ i) (D.radius₂ i) :=
    IsOpenCover.of_sets (fun i ↦ ((D.chart₂ i).preimageBall (D.center₂ i)
      (D.radius₂ i)).isOpen) hcover
  exact exists_uniform_middle_lift_preimageBall D.chart₂ D.center₂ D.radius₂ 1
    (fun i ↦ IsManifold.subset_maximalAtlas (D.mem_atlas_chart₂ i))
    (fun i ↦ D.radius₂_pos i)
    (fun i ↦ D.closedBall_subset_target i (by norm_num : (5 : ℝ) ≤ 6)) hcov
    (fun _ _ ↦ mdifferentiableOn_const) (fun _ _ _ ↦ rfl)
    (fun _ _ _ _ _ ↦ one_mul 1)

end DiscCover

section Curves

/-- Actual six-radius coordinate-cover data on the native Riemann sphere. -/
def sphereCover := chosenDiscCover (X := OnePoint ℂ)

/-- The selected native middle cocycle literally reads one at infinity. -/
theorem sphere_exists_representative_eq_one :
    ∃ i j, (∞ : OnePoint ℂ) ∈ sphereCover.level 3 i ⊓ sphereCover.level 3 j ∧
      BergmanSpace.representative (sphereCover.constantCocycle.val i j)
        (sphereCover.chart₂ i ∞) = 1 :=
  sphereCover.exists_representative_constantCocycle_eq_one ∞

/-- The concrete Riemann-sphere cocycle is genuinely nonzero as a native Bergman cocycle. -/
theorem sphere_cocycle_ne_zero : sphereCover.constantCocycle ≠ 0 :=
  sphereCover.constantCocycle_ne_zero ∞

/-- One constant lifts all sphere cocycles and also the selected nonzero native coboundary. -/
theorem sphere_uniform_lift :
    ∃ C > 0,
      (∀ ξ : sphereCover.cocycles,
        ∃ t : sphereCover.triples,
          sphereCover.proj t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖) ∧
      sphereCover.constantCocycle ≠ 0 ∧
      ∃ t : sphereCover.triples,
        sphereCover.proj t = sphereCover.constantCocycle ∧
        ‖t‖ ≤ C * ‖sphereCover.constantCocycle‖ :=
  sphereCover.uniform_lift.imp fun _ h ↦
    ⟨h.1, h.2, sphere_cocycle_ne_zero, h.2 sphereCover.constantCocycle⟩

/-- Zero middle data is lifted by the uniform theorem on the actual geometric families. -/
theorem sphere_zero_lift :
    ∃ t : sphereCover.triples, sphereCover.proj t = 0 ∧ ‖t‖ = 0 :=
  (sphereCover.uniform_lift.choose_spec.2 0).imp fun t h ↦
    ⟨h.1, le_antisymm (h.2.trans_eq
      (mul_eq_zero_of_right _ (norm_zero (E := sphereCover.cocycles)))) (norm_nonneg t)⟩

/-- The existing native empty complex charted-space structure. -/
local instance emptyChartedSpace : ChartedSpace ℂ PEmpty.{u + 1} :=
  ChartedSpace.empty ℂ PEmpty.{u + 1}

/-- Actual finite coordinate-cover data for the literal empty manifold. -/
abbrev emptyCover : DiscCover PEmpty.{u + 1} := chosenDiscCover (X := PEmpty.{u + 1})

/-- Literal empty original: the same native cover construction and lifting theorem apply. -/
theorem empty_original_uniform_lift :
    ∃ C > 0, ∀ ξ : emptyCover.{u}.cocycles,
      ∃ t : emptyCover.{u}.triples, emptyCover.{u}.proj t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖ :=
  emptyCover.{u}.uniform_lift

/-- Actual cover data on a disconnected union of two native compact closed curves. -/
def disconnectedCover := chosenDiscCover (X := (OnePoint ℂ) ⊕ (OnePoint ℂ))

/-- Both connected components have actual nonzero chart readings of the same native cocycle. -/
theorem disconnected_exists_representative_eq_one :
    (∃ i j, (Sum.inl ∞ : (OnePoint ℂ) ⊕ (OnePoint ℂ)) ∈
      disconnectedCover.level 3 i ⊓ disconnectedCover.level 3 j ∧
      BergmanSpace.representative (disconnectedCover.constantCocycle.val i j)
        (disconnectedCover.chart₂ i (Sum.inl ∞)) = 1) ∧
    (∃ i j, (Sum.inr ∞ : (OnePoint ℂ) ⊕ (OnePoint ℂ)) ∈
      disconnectedCover.level 3 i ⊓ disconnectedCover.level 3 j ∧
      BergmanSpace.representative (disconnectedCover.constantCocycle.val i j)
        (disconnectedCover.chart₂ i (Sum.inr ∞)) = 1) :=
  ⟨disconnectedCover.exists_representative_constantCocycle_eq_one _,
    disconnectedCover.exists_representative_constantCocycle_eq_one _⟩

/-- One constant controls every disconnected-curve cocycle and the selected native coboundary. -/
theorem disconnected_uniform_lift :
    ∃ C > 0,
      (∀ ξ : disconnectedCover.cocycles,
        ∃ t : disconnectedCover.triples,
          disconnectedCover.proj t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖) ∧
      ∃ t : disconnectedCover.triples,
        disconnectedCover.proj t = disconnectedCover.constantCocycle ∧
        ‖t‖ ≤ C * ‖disconnectedCover.constantCocycle‖ :=
  disconnectedCover.uniform_lift.imp fun _ h ↦ ⟨h.1, h.2, h.2 disconnectedCover.constantCocycle⟩

end Curves

end TauCeti.Examples.BergmanLifting
