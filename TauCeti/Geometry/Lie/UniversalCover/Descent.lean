/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.UniversalCover

/-!
# Lie-map descent through a universal covering

The topological universal-cover descent equivalence identifies homomorphisms on a
path-connected Lie group with homomorphisms on its universal cover that kill the
projection kernel.  This file records the corresponding differential identity:
the Lie map of a descended homomorphism is obtained by composing the Lie map on
the cover with the inverse of the Lie-algebra equivalence induced by the
covering projection.

The result is the differential boundary used when an integrated homomorphism is
constructed on a simply connected cover and then descended through its kernel.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace H G]
  [LocallyPathConnectedSpace G] [PathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
  [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace H' K] [LieGroup I' ∞ K]

/-- The Lie map of a homomorphism descended from the universal cover is the
Lie map on the cover transported across the inverse differential of the
covering projection. -/
theorem lieMap_homEquivKerProjHom_symm
    (f : {g : UniversalCover (1 : G) →ₜ* K //
      ((projHom : UniversalCover (1 : G) →ₜ* G) :
        UniversalCover (1 : G) →* G).ker ≤ (g : UniversalCover (1 : G) →* K).ker}) :
    ContinuousMonoidHom.lieMap (I := I) (I' := I') (homEquivKerProjHom.symm f) =
      (ContinuousMonoidHom.lieMap (I := I) (I' := I') f.1).comp
        (lieEquivProjHom I G).symm.toLieHom := by
  let d : G →ₜ* K := homEquivKerProjHom.symm f
  let p : UniversalCover (1 : G) →ₜ* G := projHom
  have hcomp :
      ContinuousMonoidHom.lieMap (I := I) (I' := I') (d.comp p) =
        (ContinuousMonoidHom.lieMap (I := I) (I' := I') d).comp
          (ContinuousMonoidHom.lieMap (I := I) (I' := I) p) :=
    ContinuousMonoidHom.lieMap_comp (G := UniversalCover (1 : G)) (G' := G) (G'' := K)
      (I := I) (I' := I) (I'' := I') p d
  have hfun : d.comp p = f.1 := by
    dsimp [d, p]
    exact homEquivKerProjHom_symm_apply_comp f
  rw [hfun] at hcomp
  have hp : ContinuousMonoidHom.lieMap (I := I) (I' := I) p =
      (lieEquivProjHom I G).toLieHom := by
    dsimp [p]
    rw [ContinuousMonoidHom.lieMap_def]
    exact (lieEquivProjHom_toLieHom (I := I) (G := G)).symm
  rw [hp] at hcomp
  apply LieHom.ext
  intro Y
  simpa only [d, LieHom.comp_apply, LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply] using
    (congrArg (fun L ↦ L ((lieEquivProjHom I G).symm Y)) hcomp).symm

end TauCeti.UniversalCover
