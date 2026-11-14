/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples

/-!
# Smooth unit groupoids

Given a `C^n` manifold `N`, the unit groupoid `Discrete N` inherits `C^n` manifold structures on
objects and total arrows by pulling charts back from `N` along
`TauCeti.UnitGroupoid.objectHomeomorph` and `TauCeti.UnitGroupoid.arrowHomeomorph`
(`Homeomorph.pullbackChartedSpace`). Under these charts, source and target are global `C^n`
diffeomorphisms (`TauCeti.UnitGroupoid.sourceDiffeomorph`), and in particular `C^n` local
diffeomorphisms (`TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
`TauCeti.UnitGroupoid.isLocalDiffeomorph_target`).

## Main declarations

* `TauCeti.UnitGroupoid.instChartedSpaceObjects`, `TauCeti.UnitGroupoid.instIsManifoldObjects`,
  and `TauCeti.UnitGroupoid.objectDiffeomorph`: `C^n` manifold structure on `Discrete N` and its
  coordinate diffeomorphism `Discrete N ≃ₘ^n⟮I, I⟯ N`.
* `TauCeti.UnitGroupoid.instChartedSpaceArrows`, `TauCeti.UnitGroupoid.instIsManifoldArrows`,
  and `TauCeti.UnitGroupoid.arrowDiffeomorph`: `C^n` manifold structure on
  `Quiver.Total (Discrete N)` and its coordinate diffeomorphism
  `Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ N`.
* `TauCeti.UnitGroupoid.sourceDiffeomorph`, `TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
  and `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`: the source diffeomorphism
  `Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ Discrete N` (with inverse the unit section) and local
  diffeomorphism of source and target.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace TauCeti.UnitGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- Objects of the unit groupoid `Discrete N` carry the charted-space structure pulled back from
`N`. -/
instance instChartedSpaceObjects : ChartedSpace H (Discrete N) :=
  (objectHomeomorph N).pullbackChartedSpace

/-- Objects of `Discrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Discrete N) :=
  (objectHomeomorph N).pullback_isManifold I n

/-- Forgetting the categorical wrapper on `Discrete N` as a `C^n` diffeomorphism. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] :
    Discrete N ≃ₘ^n⟮I, I⟯ N :=
  (objectHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : Discrete N) :
    objectDiffeomorph I n N x = x.as := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (objectDiffeomorph I n N).symm x = Discrete.mk x := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (objectDiffeomorph I n N).toHomeomorph = objectHomeomorph N := by
  simp [objectDiffeomorph]

/-- Total arrows of `Discrete N` carry the charted-space structure pulled back from `N` along
`arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (Discrete N)) :=
  (arrowHomeomorph N).pullbackChartedSpace

/-- Total arrows of `Discrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Quiver.Total (Discrete N)) :=
  (arrowHomeomorph N).pullback_isManifold I n

/-- The total-arrow space of `Discrete N` is `C^n` diffeomorphic to `N`. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] :
    Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ N :=
  (arrowHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem arrowDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (a : Quiver.Total (Discrete N)) :
    arrowDiffeomorph I n N a = a.left.as := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (arrowDiffeomorph I n N).symm x = ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩ := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (arrowDiffeomorph I n N).toHomeomorph = arrowHomeomorph N := by
  simp [arrowDiffeomorph]

/-- The source map of `Discrete N` as a global `C^n` diffeomorphism. -/
def sourceDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] :
    Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ Discrete N :=
  (arrowDiffeomorph I n N).trans (objectDiffeomorph I n N).symm

@[simp]
theorem coe_sourceDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(sourceDiffeomorph I n N) =
      (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) := by
  funext a
  simp [sourceDiffeomorph]

@[simp]
theorem coe_sourceDiffeomorph_symm (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(sourceDiffeomorph I n N).symm =
      fun x : Discrete N ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (Discrete N)) :=
  funext fun _ ↦ (sourceDiffeomorph I n N).injective (by simp)

/-- The source map of `Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) := by
  have h := (sourceDiffeomorph I n N).isLocalDiffeomorph
  rwa [coe_sourceDiffeomorph] at h

/-- The target map of `Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (Quiver.Total.right : Quiver.Total (Discrete N) → Discrete N) :=
  target_eq_source N ▸ isLocalDiffeomorph_source

end TauCeti.UnitGroupoid
