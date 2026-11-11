/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
/-!
# Coordinates of tangent sections along a map

This file records the coordinate reading of a tangent section along an arbitrary map in a fixed
tangent-bundle trivialization, its pointwise algebra laws, and its differentiability when the
section is differentiable as a map into the tangent bundle.

## Main definitions and results

* `TauCeti.Manifold.sectionCoordAlongMap`: the coordinate reading of a section along a map.
* `TauCeti.Manifold.mdifferentiableAt_sectionCoordAlongMap`: a section differentiable as a map
  into the tangent bundle has a differentiable coordinate reading near its base point.
-/

public section
open Set Filter Bundle
open scoped Manifold Topology
noncomputable section
namespace TauCeti.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
/-- Tangent coordinates of a section along an arbitrary map, in a fixed native trivialization. -/
def sectionCoordAlongMap (f : N → M) (V : ∀ x, TangentSpace I (f x)) (a : M) (x : N) : E :=
  (trivializationAt E (TangentSpace I) a).continuousLinearMapAt 𝕜 (f x) (V x)
/-- The defining formula for the coordinate reading of a section along a map. -/
theorem sectionCoordAlongMap_apply (f : N → M) (V : ∀ x, TangentSpace I (f x))
    (a : M) (x : N) :
    sectionCoordAlongMap f V a x =
      (trivializationAt E (TangentSpace I) a).continuousLinearMapAt 𝕜 (f x) (V x) := by
  unfold sectionCoordAlongMap
  rfl
/-- Coordinate reading along a map commutes with pointwise addition of sections. -/
theorem sectionCoordAlongMap_add (f : N → M) (V W : ∀ x, TangentSpace I (f x)) (a : M) :
    sectionCoordAlongMap f (fun x => V x + W x) a =
      sectionCoordAlongMap f V a + sectionCoordAlongMap f W a := by
  funext x
  simp only [sectionCoordAlongMap_apply, map_add, Pi.add_apply]
/-- Coordinate reading along a map commutes with multiplication by a scalar function. -/
theorem sectionCoordAlongMap_smul (f : N → M) (g : N → 𝕜) (V : ∀ x, TangentSpace I (f x))
    (a : M) :
    sectionCoordAlongMap f (fun x => g x • V x) a = g • sectionCoordAlongMap f V a := by
  funext x
  simp only [sectionCoordAlongMap_apply, map_smul, Pi.smul_apply']
/-- The zero section along a map has zero coordinate reading. -/
@[simp]
theorem sectionCoordAlongMap_zero (f : N → M) (a : M) :
    sectionCoordAlongMap f (fun x => (0 : TangentSpace I (f x))) a = 0 := by
  funext x
  simp only [sectionCoordAlongMap_apply, map_zero, Pi.zero_apply]
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
/-- A section along a map which is differentiable into the tangent bundle has a differentiable
coordinate reading in every tangent trivialization whose base set contains the image point. -/
theorem mdifferentiableAt_sectionCoordAlongMap
    {f : N → M} {V : ∀ x, TangentSpace I (f x)} {a : M} {x : N}
    (hV : MDifferentiableAt J I.tangent
      (fun y => TotalSpace.mk' E (f y) (V y)) x)
    (ha : f x ∈ (trivializationAt E (TangentSpace I) a).baseSet) :
    MDifferentiableAt J 𝓘(𝕜, E) (sectionCoordAlongMap f V a) x := by
  let e := trivializationAt E (TangentSpace I) a
  have h := hV.mdifferentiableWithinAt (s := univ)
  rw [e.mdifferentiableWithinAt_totalSpace_iff I] at h
  · obtain ⟨hf, hc⟩ := h
    have hbase : ∀ᶠ y in 𝓝 x, f y ∈ e.baseSet :=
      hf.continuousWithinAt.continuousAt univ_mem |>.preimage_mem_nhds
        (e.open_baseSet.mem_nhds ha)
    apply hc.mdifferentiableAt univ_mem |>.congr_of_eventuallyEq
    filter_upwards [hbase] with y hy
    rw [sectionCoordAlongMap_apply]
    exact e.continuousLinearMapAt_apply_of_mem 𝕜 hy (V y)
  · exact e.coe_mem_source.mpr ha
end TauCeti.Manifold
