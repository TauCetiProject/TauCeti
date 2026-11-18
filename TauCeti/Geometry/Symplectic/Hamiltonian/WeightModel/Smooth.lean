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

/-!
# Smoothness of the rotation torus action

The rotation `z_j ↦ exp(-i θ_j) z_j` of `ℂ^ι` by angles `θ ∈ (ℝ / 2πℤ)^ι`
(`TauCeti.torusRotation`) is jointly smooth in the angles and the point, for the smooth structure
of the torus `(ℝ / 2πℤ)^ι` as a finite product of circles
(`TauCeti.contMDiff_torusRotation`). In the real coordinates `z_j = q_j + i p_j` its entries are
products of the coordinates of the point with `cos θ_j` and `sin θ_j`, and the cosine and sine
descend to smooth functions on the circle (`Function.Periodic.contMDiff_lift_iff`).

This makes the rotation torus, and its closed subgroups, act smoothly on `ℂ^ι` and on the
invariant submanifolds of `ℂ^ι`, such as the levels used in Delzant's construction.
-/

public section

open Real
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

local instance weightModelSmoothTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- **The rotation torus acts smoothly.** The rotation `z_j ↦ exp(-i θ_j) z_j` of `ℂ^ι` is jointly
smooth in the angles `θ ∈ (ℝ / 2πℤ)^ι` and the point. -/
theorem contMDiff_torusRotation :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        torusRotation p.1 p.2 := by
  have hcos := cos_periodic.contMDiff_lift_iff.2 (contDiff_cos (n := ∞))
  have hsin := sin_periodic.contMDiff_lift_iff.2 (contDiff_sin (n := ∞))
  -- The angle `θ_j` and the coordinates `q_j`, `p_j` of the point are smooth.
  have hθ (j : ι) : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) 𝓘(ℝ) ∞
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦ p.1 j :=
    contMDiff_apply.comp contMDiff_fst
  have hq (j : ι) : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) 𝓘(ℝ) ∞
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦ p.2.1 j :=
    ((PiLp.proj 2 (fun _ : ι ↦ ℝ) j).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι)
      (EuclideanSpace ℝ ι))).contMDiff.comp contMDiff_snd
  have hp (j : ι) : ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) 𝓘(ℝ) ∞
      fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦ p.2.2 j :=
    ((PiLp.proj 2 (fun _ : ι ↦ ℝ) j).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι)
      (EuclideanSpace ℝ ι))).contMDiff.comp contMDiff_snd
  -- In coordinates, the rotation is built from `cos θ_j`, `sin θ_j`, `q_j` and `p_j`.
  have hfun : (fun p : (ι → AddCircle (2 * π)) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
      torusRotation p.1 p.2) = fun p ↦
      (WithLp.toLp 2 fun j ↦
          cos_periodic.lift (p.1 j) * p.2.1 j + sin_periodic.lift (p.1 j) * p.2.2 j,
        WithLp.toLp 2 fun j ↦
          -(sin_periodic.lift (p.1 j) * p.2.1 j) + cos_periodic.lift (p.1 j) * p.2.2 j) := by
    funext p
    ext j
    · exact torusRotation_apply_fst p.1 p.2 j
    · exact torusRotation_apply_snd p.1 p.2 j
  have htoLp := (PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ↦ ℝ).symm.contDiff.contMDiff (n := ∞)
  rw [hfun]
  refine ContMDiff.prodMk_space (htoLp.comp (contMDiff_pi_module_iff.2 fun j ↦ ?_))
    (htoLp.comp (contMDiff_pi_module_iff.2 fun j ↦ ?_))
  · exact ((hcos.comp (hθ j)).mul (hq j)).add ((hsin.comp (hθ j)).mul (hp j))
  · exact ((hsin.comp (hθ j)).mul (hq j)).neg.add ((hcos.comp (hθ j)).mul (hp j))

end TauCeti
