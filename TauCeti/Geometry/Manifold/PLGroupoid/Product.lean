/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PLGroupoid.Basic
public import TauCeti.Topology.PL.Product

/-!
# Products of PL manifolds

The product of two PL coordinate changes is a PL coordinate change for the product model
with corners. Consequently Mathlib's product atlas makes a product of PL manifolds a PL
manifold. This applies to models with boundary and corners as well as boundaryless models;
neither compactness nor finite-dimensionality is required.

The construction follows Mathlib's `contDiffGroupoid_prod` and `IsManifold.prod`, by
Sébastien Gouëzel, with the PL product calculus in place of differentiability.

Reference: C. Rourke and B. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapters 1–2.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}

/-- Products of invertible PL coordinate changes are invertible PL coordinate changes
in the product model with corners. -/
theorem PLGroupoid_prod {e : OpenPartialHomeomorph H H}
    {e' : OpenPartialHomeomorph H' H'} (he : e ∈ PLGroupoid I)
    (he' : e' ∈ PLGroupoid J) : e.prod e' ∈ PLGroupoid (I.prod J) := by
  obtain ⟨he, he_symm⟩ := (mem_PLGroupoid_iff I).mp he
  obtain ⟨he', he'_symm⟩ := (mem_PLGroupoid_iff J).mp he'
  rw [mem_PLGroupoid_iff]
  constructor
  · have hprod := he.prodMap he'
    rw [← I.image_eq, ← J.image_eq, prod_image_image_eq] at hprod
    rw [← (I.prod J).image_eq]
    exact hprod
  · have hprod := he_symm.prodMap he'_symm
    rw [← I.image_eq, ← J.image_eq, prod_image_image_eq] at hprod
    rw [← (I.prod J).image_eq]
    exact hprod

/-- The product atlas of two PL manifolds is a PL atlas for the product model with corners. -/
instance hasGroupoid_PLGroupoid_prod
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M (PLGroupoid I)]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] [HasGroupoid N (PLGroupoid J)] :
    HasGroupoid (M × N) (PLGroupoid (I.prod J)) where
  compatible := by
    rintro f g ⟨f₁, hf₁, f₂, hf₂, rfl⟩ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans]
    exact PLGroupoid_prod ((PLGroupoid I).compatible hf₁ hg₁)
      ((PLGroupoid J).compatible hf₂ hg₂)

end TauCeti
