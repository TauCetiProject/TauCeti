/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.Star
public import TauCeti.Topology.Category.TopCat.GlueData.PartialHomeomorph

/-!
# Gluing two manifolds along a partial diffeomorphism

Let `Φ : Y ⇀ X` be a `C^n` partial diffeomorphism between `C^n` manifolds modelled on the same
space, from an open subset of `Y` onto an open subset of `X`. Gluing `X` and `Y` along `Φ`
(`OpenPartialHomeomorph.glueData`) identifies each point `y` of the source of `Φ` with `Φ y`. This
is a star gluing along local diffeomorphisms, so it is a compatible gluing
(`PartialDiffeomorph.isCompatible_glueData`): the glued space is a `C^n` manifold for the glued
atlas, the canonical maps of `X` and `Y` into it are `C^n` local diffeomorphisms, hence
diffeomorphisms onto their open images, and a map out of the glued manifold is `C^m` exactly when
its composites with the canonical maps of `X` and of `Y` are. The glued manifold is Hausdorff
exactly when `X` and `Y` are and the graph of `Φ` on its source is closed
(`OpenPartialHomeomorph.t2Space_glueData_iff`).

The main example attaches a cylindrical end to a manifold. Let `X` be the interior of a manifold
with boundary `S`, modelled on `H × ℝ`, and let a collar of the boundary be a partial
diffeomorphism `Φ : S × ℝ ⇀ X` with source `S × (-∞, 0)`. Gluing along `Φ` continues the collar
coordinate to all of `ℝ`; the points outside `X` form the end `S × [0, ∞)`
(`OpenPartialHomeomorph.bijOn_glueInr_Ici`). For the backward Liouville flow of the boundary of a
Liouville domain `W`, the glued manifold is the underlying manifold `W ∪ (∂W × [0, ∞))` of the
completion of `W`.

## Main results

* `PartialDiffeomorph.isCompatible_glueData`: the gluing along a partial diffeomorphism is
  compatible.
* `PartialDiffeomorph.isManifold_glueData`: the glued space is a `C^n` manifold.
* `PartialDiffeomorph.isLocalDiffeomorph_glueInl`, `PartialDiffeomorph.isLocalDiffeomorph_glueInr`:
  the canonical maps are local diffeomorphisms.
* `PartialDiffeomorph.contMDiff_glueData_iff`: smoothness of maps out of the glued manifold.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  §2(a) (the completion of a Liouville domain).
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]

/-- The atlases of the two pieces of a gluing of `X` and `Y`. -/
noncomputable instance instChartedSpacePartialHomeomorphGluePiece :
    ∀ i, ChartedSpace H (partialHomeomorphGluePiece X Y i)
  | ⟨true⟩ => inferInstanceAs (ChartedSpace H X)
  | ⟨false⟩ => inferInstanceAs (ChartedSpace H Y)

/-- The two pieces of a gluing of `C^n` manifolds are `C^n` manifolds. -/
instance instIsManifoldPartialHomeomorphGluePiece [IsManifold I n X] [IsManifold I n Y] :
    ∀ i, IsManifold I n (partialHomeomorphGluePiece X Y i)
  | ⟨true⟩ => inferInstanceAs (IsManifold I n X)
  | ⟨false⟩ => inferInstanceAs (IsManifold I n Y)

end TauCeti

namespace PartialDiffeomorph

open TauCeti OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
  (Φ : PartialDiffeomorph I I Y X n)

/-- **The gluing along a partial diffeomorphism is compatible.** The piece `X` is attached to
itself by the identity and the piece `Y` by `Φ`, from its source onto its target, and both are
local diffeomorphisms. -/
theorem isCompatible_glueData :
    Φ.toOpenPartialHomeomorph.glueData.IsCompatible I n :=
  isCompatible_starGlueData fun
    | ⟨true⟩ => by
      -- The attaching map of `X` is the identity of `X`.
      have h : ⇑(Φ.toOpenPartialHomeomorph.glueMap ⟨true⟩) =
          ⇑(Diffeomorph.refl I (⊤ : Opens X) n) :=
        funext fun x ↦ Subtype.ext (coe_glueMap_true_apply _ x)
      rw [h]
      exact (Diffeomorph.refl I (⊤ : Opens X) n).isLocalDiffeomorph
    | ⟨false⟩ => by
      -- The attaching map of `Y` is `Φ` from its source onto its target.
      have h : ⇑(Φ.toOpenPartialHomeomorph.glueMap ⟨false⟩) =
          ⇑Φ.toDiffeomorphSourceTarget :=
        funext fun y ↦ Subtype.ext <| by
          rw [coe_glueMap_false_apply]
          exact (Φ.toDiffeomorphSourceTarget_apply_coe y).symm
      rw [h]
      exact Φ.toDiffeomorphSourceTarget.isLocalDiffeomorph

variable [IsManifold I n X] [IsManifold I n Y]

/-- **The gluing of two `C^n` manifolds along a partial diffeomorphism is a `C^n` manifold**, for
the glued atlas. -/
theorem isManifold_glueData :
    letI := Φ.toOpenPartialHomeomorph.glueData.chartedSpace H
    IsManifold I n Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued :=
  (isCompatible_glueData Φ).isManifold

/-- The canonical map of `X` into its gluing with `Y` along a partial diffeomorphism is a `C^n`
local diffeomorphism. -/
theorem isLocalDiffeomorph_glueInl :
    letI := Φ.toOpenPartialHomeomorph.glueData.chartedSpace H
    IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInl := by
  rw [coe_glueInl]
  exact (isCompatible_glueData Φ).isLocalDiffeomorph_ι ⟨true⟩

/-- The canonical map of `Y` into its gluing with `X` along a partial diffeomorphism is a `C^n`
local diffeomorphism. -/
theorem isLocalDiffeomorph_glueInr :
    letI := Φ.toOpenPartialHomeomorph.glueData.chartedSpace H
    IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInr := by
  rw [coe_glueInr]
  exact (isCompatible_glueData Φ).isLocalDiffeomorph_ι ⟨false⟩

/-- **Smooth maps out of a gluing.** A map out of the gluing of `X` and `Y` along a partial
diffeomorphism is `C^m`, for `m ≤ n`, exactly when its composites with the canonical maps of `X`
and of `Y` are. -/
theorem contMDiff_glueData_iff {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {m : ℕ∞ω} (hm : m ≤ n)
    (g : Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued → N) :
    letI := Φ.toOpenPartialHomeomorph.glueData.chartedSpace H
    ContMDiff I I' m g ↔
      ContMDiff I I' m (g ∘ Φ.toOpenPartialHomeomorph.glueInl) ∧
        ContMDiff I I' m (g ∘ Φ.toOpenPartialHomeomorph.glueInr) := by
  rw [(isCompatible_glueData Φ).contMDiff_iff hm, coe_glueInl, coe_glueInr]
  exact ⟨fun h ↦ ⟨h ⟨true⟩, h ⟨false⟩⟩, fun ⟨hX, hY⟩ ↦ fun | ⟨true⟩ => hX | ⟨false⟩ => hY⟩

end PartialDiffeomorph
