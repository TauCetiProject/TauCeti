/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Projective
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Determinants of products and transposes on finite projective modules

The determinant `LinearMap.projectiveDet` of an endomorphism of a finite projective module is
computed through any splitting `π ∘ σ = id` off a free module of finite rank. Products of
splittings split products, and transposes of a splitting split the dual module, so:

* `LinearMap.projectiveDet_prodMap`: `det (f × g) = det f * det g`;
* `LinearMap.projectiveDet_dualMap`: `det fᵗ = det f`.

These extend `LinearMap.det_prodMap` and `LinearMap.det_dualMap` from free to projective modules.
-/

public section

open Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R M] [Module.Projective R M]

/-- **The determinant of a product** of endomorphisms of finite projective modules is the product
of the determinants. -/
theorem projectiveDet_prodMap [Module.Finite R N] [Module.Projective R N] (f : Module.End R M)
    (g : Module.End R N) : projectiveDet (f.prodMap g) = projectiveDet f * projectiveDet g := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨n', π', σ', -, -, h'⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  have hp : (π.prodMap π') ∘ₗ (σ.prodMap σ') = id := by
    rw [prodMap_comp, h, h', prodMap_id]
  rw [projectiveDet_eq_det_of_comp_eq_id _ _ hp, projectiveDet_eq_det_of_comp_eq_id π σ h,
    projectiveDet_eq_det_of_comp_eq_id π' σ' h', ← det_prodMap]
  congr 1

/-- **The determinant of the transpose** of an endomorphism of a finite projective module is its
determinant. -/
theorem projectiveDet_dualMap (f : Module.End R M) : projectiveDet f.dualMap = projectiveDet f := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hd : σ.dualMap ∘ₗ π.dualMap = id := by
    ext φ x
    simpa using congrArg φ (LinearMap.congr_fun h x)
  rw [projectiveDet_eq_det_of_comp_eq_id _ _ hd, projectiveDet_eq_det_of_comp_eq_id π σ h,
    ← det_dualMap (σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π))]
  congr 1
  refine LinearMap.ext fun φ ↦ LinearMap.ext fun x ↦ ?_
  simp

end LinearMap
