/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.IsManifold.Pi
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic

import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.Instances.AddCircle.Periodic

/-!
# Smoothness of the rotation torus action

The torus `(ℝ / 2πℤ)^ι` acts on `ℂ^ι` by `z_j ↦ exp(-i θ_j) z_j` (`TauCeti.torusRotation`). Read
in the real coordinates `z_j = q_j + i p_j`, the rotation by `θ` has coefficients `cos θ_j` and
`sin θ_j`, which are smooth functions on the circle (`Function.Periodic.contMDiff_lift`). So the
action map `(θ, z) ↦ exp(-i θ) z` is smooth on the product of the torus, with its product charts,
and `ℂ^ι` (`TauCeti.contMDiff_torusRotation_apply`). This is the smoothness of the torus action
needed to form quotients of invariant submanifolds of `ℂ^ι`, such as the level of the Delzant
construction, by subtori.
-/

public section

open Real
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The circle `ℝ / 2πℤ` of angles has positive period, so it is a smooth manifold. -/
local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- **The rotation torus acts smoothly.** The action map `(θ, z) ↦ exp(-i θ) z` of the torus
`(ℝ / 2πℤ)^ι` on `ℂ^ι`, in the real coordinates of `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, is
smooth for the product charts of the torus. -/
theorem contMDiff_torusRotation_apply {n : WithTop ℕ∞} :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) n
      (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        torusRotation p.1 p.2) := by
  -- The angle coefficients and the coordinates of `z` are smooth.
  have hcos (j : ι) : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) 𝓘(ℝ) n
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        cos_periodic.lift (p.1 j) :=
    (cos_periodic.contMDiff_lift contDiff_cos).comp (contMDiff_apply.comp contMDiff_fst)
  have hsin (j : ι) : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) 𝓘(ℝ) n
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        sin_periodic.lift (p.1 j) :=
    (sin_periodic.contMDiff_lift contDiff_sin).comp (contMDiff_apply.comp contMDiff_fst)
  have hq (j : ι) : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) 𝓘(ℝ) n
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦ p.2.1 j := by
    have hL := ((PiLp.proj 2 (fun _ : ι ↦ ℝ) j).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contMDiff (n := n)
    exact hL.comp contMDiff_snd
  have hp (j : ι) : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) 𝓘(ℝ) n
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦ p.2.2 j := by
    have hL := ((PiLp.proj 2 (fun _ : ι ↦ ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contMDiff (n := n)
    exact hL.comp contMDiff_snd
  -- Each coordinate of the rotation is a polynomial in these functions.
  set e := (PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ↦ ℝ).symm
  have h₁ : Prod.fst ∘ (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι ×
      EuclideanSpace ℝ ι) ↦ torusRotation p.1 p.2) = e ∘ fun p j ↦
        cos_periodic.lift (p.1 j) * p.2.1 j + sin_periodic.lift (p.1 j) * p.2.2 j := by
    funext p
    ext j
    simp [e, torusRotation_apply_fst]
  have h₂ : Prod.snd ∘ (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι ×
      EuclideanSpace ℝ ι) ↦ torusRotation p.1 p.2) = e ∘ fun p j ↦
        -(sin_periodic.lift (p.1 j) * p.2.1 j) + cos_periodic.lift (p.1 j) * p.2.2 j := by
    funext p
    ext j
    simp [e, torusRotation_apply_snd]
  refine (contMDiff_prod_module_iff _).2 ⟨?_, ?_⟩
  · rw [h₁]
    exact (e : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι).contMDiff.comp
      (contMDiff_pi_module_iff.2 fun j ↦ ((hcos j).mul (hq j)).add ((hsin j).mul (hp j)))
  · rw [h₂]
    exact (e : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι).contMDiff.comp
      (contMDiff_pi_module_iff.2 fun j ↦ ((hsin j).mul (hq j)).neg.add ((hcos j).mul (hp j)))

end TauCeti
