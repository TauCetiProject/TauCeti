/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Pulling back continuous bilinear maps, and their quadratic maps

A continuous linear map `u : W →L[𝕜] V` pulls a continuous bilinear map `B` on `V` back to the
bilinear map `B (u ·) (u ·)` on `W`. This operation is itself continuous and linear in `B`
(`ContinuousLinearMap.pullbackBilinL`), so that it commutes with derivatives of families of
bilinear maps, such as the coordinate expressions of metrics. In particular, pulling back each
value of a continuous family of multilinear maps valued in bilinear maps, along `u` in every
argument, gives a continuous family
(`Continuous.pullbackBilinL_compContinuousMultilinearMap`).

The quadratic map `x ↦ B x x` of a continuous bilinear map is Lipschitz on every ball, with a
constant proportional to the radius: `‖B x x - B y y‖ ≤ ‖B‖ (‖x‖ + ‖y‖) ‖x - y‖`
(`ContinuousLinearMap.norm_apply_apply_sub_apply_apply_le`). This is the quadratic estimate on the
nonlinear terms of an equation that is quadratic in its unknown.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V W G : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pulling a continuous bilinear map back along a continuous linear map `u`,
`B ↦ B (u ·) (u ·)`, as a continuous linear map in `B`. -/
def pullbackBilinL (u : W →L[𝕜] V) : (V →L[𝕜] V →L[𝕜] G) →L[𝕜] W →L[𝕜] W →L[𝕜] G :=
  (compL 𝕜 W (V →L[𝕜] G) (W →L[𝕜] G) ((compL 𝕜 W V G).flip u)).comp
    ((compL 𝕜 W V (V →L[𝕜] G)).flip u)

@[simp]
theorem pullbackBilinL_apply (u : W →L[𝕜] V) (B : V →L[𝕜] V →L[𝕜] G) (v w : W) :
    pullbackBilinL u B v w = B (u v) (u w) :=
  (rfl)

/-- `pullbackBilinL u` precomposes a bilinear map with `u`, and then each of its values with `u`.
In this form it is visibly built from `u` by continuous linear operations, so that, for instance,
its regularity in `u` follows from that of the precomposition maps `compL`. -/
theorem pullbackBilinL_eq_comp (u : W →L[𝕜] V) :
    pullbackBilinL (G := G) u =
      (compL 𝕜 W (V →L[𝕜] G) (W →L[𝕜] G) ((compL 𝕜 W V G).flip u)).comp
        ((compL 𝕜 W V (V →L[𝕜] G)).flip u) :=
  (rfl)

/-- The quadratic map `x ↦ B x x` of a continuous bilinear map `B` satisfies
`‖B x x - B y y‖ ≤ ‖B‖ (‖x‖ + ‖y‖) ‖x - y‖`. -/
theorem norm_apply_apply_sub_apply_apply_le (B : V →L[𝕜] V →L[𝕜] G) (x y : V) :
    ‖B x x - B y y‖ ≤ ‖B‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have h : B x x - B y y = B x (x - y) + B (x - y) y := by
    simp only [map_sub, sub_apply]
    abel
  rw [h]
  calc ‖B x (x - y) + B (x - y) y‖ ≤ ‖B‖ * ‖x‖ * ‖x - y‖ + ‖B‖ * ‖x - y‖ * ‖y‖ :=
        (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))
    _ = ‖B‖ * (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

end ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V W G : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pulling back each value of a continuous family `f` of multilinear maps valued in bilinear
maps, both in its arguments and in its values, along a continuous linear map `u` gives a
continuous family. Applied to iterated derivatives of a family of bilinear forms, this is the
pullback of all their coordinate derivatives along `u`. -/
theorem Continuous.pullbackBilinL_compContinuousMultilinearMap {X ι : Type*} [TopologicalSpace X]
    {f : X → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ V) (V →L[𝕜] V →L[𝕜] G)} (hf : Continuous f)
    (u : W →L[𝕜] V) :
    Continuous fun x ↦ (ContinuousLinearMap.pullbackBilinL u).compContinuousMultilinearMap
      ((f x).compContinuousLinearMap fun _ ↦ u) :=
  ((ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ W) _ _
    (ContinuousLinearMap.pullbackBilinL u)).continuous.comp
    ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ u).continuous.comp hf) :)
