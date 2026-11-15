/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars

/-!
# Restriction of scalars for Lie groups

Lie groups over compatible normed field extensions can be regarded over the smaller field,
with the same carrier, topology and charts, using the restricted boundaryless model.
The self-model specialization uses the usual smaller-field self-model directly.

## Main results

* `LieGroup.restrictScalars`: restriction of scalars for a boundaryless model and any regularity.
* `LieGroup.restrictScalars_self`: restriction of scalars for self-modelled Lie groups.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1, for complex Lie groups as real Lie groups.
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

variable (𝕜₀ : Type*) [NontriviallyNormedField 𝕜₀] [NormedAlgebra 𝕜₀ 𝕜]
  [NormedSpace 𝕜₀ E] [IsScalarTower 𝕜₀ 𝕜 E] [I.Boundaryless] {n : ℕ∞ω}

/-- A Lie group remains a Lie group after restricting scalars along a normed field extension.
The topology, carrier and charted space stay fixed; the model becomes `I.restrictScalars 𝕜₀`. -/
theorem LieGroup.restrictScalars [LieGroup I n G] : LieGroup (I.restrictScalars 𝕜₀) n G where
  toIsManifold := I.isManifold_restrictScalars 𝕜₀ inferInstance
  contMDiff_mul := by
    have h : ContMDiff (I.prod I) I n (fun p : G × G ↦ p.1 * p.2) := _root_.contMDiff_mul I n
    simpa only [ModelWithCorners.restrictScalars_prod] using h.restrictScalars 𝕜₀
  contMDiff_inv := by
    have h : ContMDiff I I n (fun g : G ↦ g⁻¹) := _root_.contMDiff_inv I n
    exact h.restrictScalars 𝕜₀

/-- A self-modelled Lie group remains a Lie group over the smaller field, using its usual
self-model and the same charts. -/
theorem LieGroup.restrictScalars_self {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [Group M] [LieGroup 𝓘(𝕜, E) n M] : LieGroup 𝓘(𝕜₀, E) n M := by
  have h := LieGroup.restrictScalars 𝕜₀ (I := 𝓘(𝕜, E)) (G := M) (n := n)
  rw [modelWithCornersSelf_restrictScalars] at h
  exact h
