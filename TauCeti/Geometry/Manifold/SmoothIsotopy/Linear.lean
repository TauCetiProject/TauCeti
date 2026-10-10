/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.PositiveDeterminant
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Linear isotopies fixing the origin

A real linear map with positive determinant on a finite-dimensional normed space is smoothly
isotopic to the identity through linear automorphisms. The motion fixes the origin at every time.
This is the linear step in the disc theorem, before transporting and extending the isotopy in
an ambient manifold.

The smooth family comes from `ContinuousLinearMap.exists_contDiff_det_pos`, which uses
transvection generation and a positive diagonal factor.

Reference: M. Hirsch, *Differential Topology*, Chapter 4, §6, Theorem 6.6.
-/

public section

open Topology
open scoped Manifold ContDiff

namespace ContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A positive-determinant linear map is smoothly isotopic to the identity, fixing the origin
throughout the motion. The time slices are linear automorphisms. -/
theorem exists_smoothIsotopy_id (L : E ≃L[ℝ] E) (hL : 0 < L.toContinuousLinearMap.det) :
    ∃ F : TauCeti.SmoothIsotopy (ContMDiffMap.id (I := 𝓘(ℝ, E)) (M := E))
        L.toDiffeomorph.toContMDiffMap,
      (∀ t : unitInterval, F (t, 0) = 0) ∧
        ∀ t : unitInterval, ∃ A : E ≃L[ℝ] E, ∀ x, F (t, x) = A x := by
  obtain ⟨γ, hγ, hγ0, hγ1, hγdet⟩ := L.toContinuousLinearMap.exists_contDiff_det_pos hL
  have hs : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : unitInterval × E => γ p.1 p.2) :=
    (hγ.contMDiff.comp ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp
      contMDiff_fst)).clm_apply contMDiff_snd
  let F : TauCeti.SmoothIsotopy (ContMDiffMap.id (I := 𝓘(ℝ, E)) (M := E))
      L.toDiffeomorph.toContMDiffMap :=
    { toContMDiffMap := ⟨fun p => γ p.1 p.2, hs⟩
      map_zero_left := fun x => by simp [hγ0, ContMDiffMap.id]
      map_one_left := fun x => by simp [hγ1]
      isSmoothEmbedding := fun t => by
        let A := (γ t).toContinuousLinearEquivOfDetNeZero (hγdet t).ne'
        -- Compute the local time slice before applying the diffeomorphism criterion.
        dsimp only [ContMDiffMap.coeFn_mk]
        have hA : (A : E → E) = γ t := by
          funext x
          exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply _ _ x
        simpa only [ContinuousLinearEquiv.coe_toDiffeomorph, hA] using
          TauCeti.isSmoothEmbedding_diffeomorph A.toDiffeomorph }
  refine ⟨F, ?_, ?_⟩
  · intro t
    -- Evaluate the locally constructed motion before using linearity.
    exact (γ t).map_zero
  · intro t
    exact ⟨(γ t).toContinuousLinearEquivOfDetNeZero (hγdet t).ne', fun _ => rfl⟩

end ContinuousLinearEquiv
