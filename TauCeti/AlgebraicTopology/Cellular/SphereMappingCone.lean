/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Boundary
public import TauCeti.Topology.CWComplex.Classical.Sphere.MappingCone

/-!
# The attaching map of the top cell of `Sⁿ ∪_f Dⁿ⁺¹`

The CW complex `TauCeti.sphereMappingConeCWComplex h f` attaches an `(n + 1)`-cell to the sphere
`Sⁿ` along `f : Sⁿ → Sⁿ`, and its `n`-skeleton is `Sⁿ`
(`TauCeti.sphereMappingConeSkeletonHomeomorph`). This file shows that, read through that
identification, the attaching map `TauCeti.cellAttachingMap` of the `(n + 1)`-cell is `f`
(`TauCeti.cellAttachingMap_sphereMappingConeTopCell_apply`). This is the input the cellular
boundary formula `TauCeti.ι_cellularChainGroupIso_inv_comp_cellularDifferential` needs to compute
the differential of this complex in terms of `f`.

The mathematical source is Hatcher, *Algebraic Topology*, Chapter 0 (attaching cells) and
Section 2.2 (the cellular boundary formula).
-/

public section

noncomputable section

open CategoryTheory Metric Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1)
  (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, sphere (0 : EuclideanSpace ℝ ι) 1))

/-- The attaching map of the `(n + 1)`-cell of `Sⁿ ∪_f Dⁿ⁺¹` is `f`, read through the
identification `TauCeti.sphereMappingConeSkeletonHomeomorph` of the `n`-skeleton with `Sⁿ`. -/
@[simp]
theorem cellAttachingMap_sphereMappingConeTopCell_apply (x : TopCat.diskBoundary.{u} (n + 1)) :
    letI := sphereMappingConeCWComplex h f
    ConcreteCategory.hom (Y := TopCat.of (skeletonLT (sphereMappingCone f) ((n + 1 : ℕ) : ℕ∞)))
        (cellAttachingMap (sphereMappingConeTopCell h f)) x =
      sphereMappingConeSkeletonHomeomorph h f (f x.down) := by
  let _ := sphereMappingConeCWComplex h f
  apply Subtype.ext
  rw [coe_cellAttachingMap_apply, coe_diskHomeomorphClosedBall_apply]
  exact (map_sphereMappingConeTopCell_unitBallHomeomorph_coe_sphere h f x.down).trans
    (coe_sphereMappingConeSkeletonHomeomorph_apply h f _).symm

end TauCeti
