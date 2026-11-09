/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Pulling back continuous bilinear maps

A continuous linear map `u : W →L[𝕜] V` pulls a continuous bilinear map `B` on `V` back to the
bilinear map `B (u ·) (u ·)` on `W`. This operation is itself continuous and linear in `B`
(`ContinuousLinearMap.pullbackBilinL`), so that it commutes with derivatives of families of
bilinear maps, such as the coordinate expressions of metrics. In particular, pulling back each
value of a continuous family of multilinear maps valued in bilinear maps, along `u` in every
argument, gives a continuous family
(`Continuous.pullbackBilinL_compContinuousMultilinearMap`).

Pulling back along continuous linear equivalences keeps a bilinear map `B₀ : V →L V' →L G`
invertible as a map to the dual (`ContinuousLinearMap.IsInvertible.bilinearComp`), and it
conjugates the comparison operator `B₀⁻¹ ∘ B` of two such maps by the equivalence in the first
slot (`ContinuousLinearMap.inverse_bilinearComp_comp_bilinearComp`). This is how operators built
from a pair of bilinear forms, such as the Morse congruence of a form with a reference form,
transform under a linear change of coordinates.
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

section Invertible

variable {V' W' : Type*} [SeminormedAddCommGroup V'] [NormedSpace 𝕜 V']
  [SeminormedAddCommGroup W'] [NormedSpace 𝕜 W']

/-- Pulling a bilinear map that is invertible, as a map to the space of linear maps on its
second argument, back along continuous linear equivalences in both arguments keeps it
invertible. -/
theorem IsInvertible.bilinearComp {B₀ : V →L[𝕜] V' →L[𝕜] G} (hB₀ : B₀.IsInvertible)
    (e₁ : W ≃L[𝕜] V) (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).IsInvertible := by
  refine .of_inverse (g := (e₁.symm : V →L[𝕜] W) ∘L B₀.inverse ∘L
    (compL 𝕜 V' W' G).flip (e₂.symm : V' →L[𝕜] W')) ?_ ?_
  · ext φ x
    simp [hB₀.self_apply_inverse]
  · ext x
    have h : (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V') x).comp
        (e₂.symm : V' →L[𝕜] W') = B₀ (e₁ x) := by
      ext y
      simp
    simp [h, hB₀.inverse_apply_self]

/-- Pulling two bilinear maps back along continuous linear equivalences conjugates their
comparison operator `B₀⁻¹ ∘ B` by the equivalence `e₁` in the first argument. -/
theorem inverse_bilinearComp_comp_bilinearComp {B₀ : V →L[𝕜] V' →L[𝕜] G}
    (hB₀ : B₀.IsInvertible) (B : V →L[𝕜] V' →L[𝕜] G) (e₁ : W ≃L[𝕜] V) (e₂ : W' ≃L[𝕜] V') :
    (B₀.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V')).inverse ∘L
        B.bilinearComp (e₁ : W →L[𝕜] V) (e₂ : W' →L[𝕜] V') =
      (e₁.symm : V →L[𝕜] W) ∘L (B₀.inverse ∘L B) ∘L (e₁ : W →L[𝕜] V) := by
  ext w
  rw [comp_apply, (hB₀.bilinearComp e₁ e₂).inverse_apply_eq]
  ext w'
  simp [hB₀.self_apply_inverse]

end Invertible

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
