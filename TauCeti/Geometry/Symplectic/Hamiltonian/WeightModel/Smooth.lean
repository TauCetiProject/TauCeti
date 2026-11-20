/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle

import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smoothness of the rotation torus action

The rotation action `(θ, z) ↦ θ • z` of the torus `(ℝ / 2πℤ)^ι` on `ℂ^ι`
(`TauCeti.torusRotation`), with the torus a manifold modelled on `ℝ^ι`, is smooth: its
coefficients `cos θ_j` and `sin θ_j` are smooth on the circle
(`Function.Periodic.contMDiff_lift_iff`), and each coordinate of the rotated point is a polynomial
in these coefficients and the coordinates of `z`.

## Main results

* `TauCeti.contMDiff_torusRotation`: the rotation action of `(ℝ / 2πℤ)^ι` on `ℂ^ι` is smooth.
-/

public section

open Real
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- A map into `EuclideanSpace ℝ ι` is `C^n` when each of its coordinates is. -/
private theorem contMDiff_euclideanSpace_of_apply {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {n : ℕ∞ω} {g : M → EuclideanSpace ℝ ι}
    (h : ∀ j, ContMDiff I 𝓘(ℝ) n fun x ↦ g x j) : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ ι) n g :=
  ((EuclideanSpace.equiv ι ℝ).symm : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι).contMDiff.comp
    (contMDiff_pi_module_iff.2 h)

/-- The coefficients `cos θ_j` and `sin θ_j` of the rotation by `θ`, and the coordinates `z.1 j` and
`z.2 j` of the rotated point, are smooth functions of `(θ, z)`. -/
private theorem contMDiff_torusRotation_coefficients (j : ι) :
    let I := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          cos_periodic.lift (p.1 j)) ∧
      ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          sin_periodic.lift (p.1 j)) ∧
      ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          p.2.1 j) ∧
      ContMDiff I 𝓘(ℝ) ∞
        (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
          p.2.2 j) := by
  have hfst : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) 𝓘(ℝ) ∞
      fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ x.1 j :=
    ((EuclideanSpace.proj j : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contMDiff
  have hsnd : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) 𝓘(ℝ) ∞
      fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ x.2 j :=
    ((EuclideanSpace.proj j : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contMDiff
  exact ⟨(cos_periodic.contMDiff_lift_iff.2 contDiff_cos.contMDiff).comp
      (contMDiff_apply.comp contMDiff_fst),
    (sin_periodic.contMDiff_lift_iff.2 contDiff_sin.contMDiff).comp
      (contMDiff_apply.comp contMDiff_fst),
    hfst.comp contMDiff_snd, hsnd.comp contMDiff_snd⟩

/-- **The rotation action of the torus `(ℝ / 2πℤ)^ι` on `ℂ^ι` is smooth**, for the torus
modelled on `ℝ^ι`: the map `(θ, z) ↦ (z_j ↦ exp(-i θ_j) z_j)` is smooth. -/
theorem contMDiff_torusRotation :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        torusRotation p.1 p.2 := by
  have hpair : (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
      torusRotation p.1 p.2) = fun p ↦ ((torusRotation p.1 p.2).1, (torusRotation p.1 p.2).2) :=
    (rfl)
  rw [hpair]
  -- Each coordinate of the rotated point is a polynomial in smooth functions.
  refine ContMDiff.prodMk_space (contMDiff_euclideanSpace_of_apply fun j ↦ ?_)
    (contMDiff_euclideanSpace_of_apply fun j ↦ ?_) <;>
  obtain ⟨hcos, hsin, hfst, hsnd⟩ := contMDiff_torusRotation_coefficients (ι := ι) j
  · exact ((hcos.mul hfst).add (hsin.mul hsnd)).congr fun p ↦ torusRotation_apply_fst p.1 p.2 j
  · exact ((hsin.mul hfst).neg.add (hcos.mul hsnd)).congr fun p ↦ torusRotation_apply_snd p.1 p.2 j

end TauCeti
