/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.AlgebraicTopology.UniversalCover.Group
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Descent

/-!
# Homomorphism descent from a universal covering group

Continuous homomorphisms from a path-connected topological group are exactly the continuous
homomorphisms from its universal covering group that kill the kernel of the covering projection.

## Main result

* `TauCeti.UniversalCover.homEquivKerProjHom` is the descent equivalence.
-/

public section

namespace TauCeti.UniversalCover

variable {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyPathConnectedSpace G] [PathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
  [Monoid K] [TopologicalSpace K]

/-- Continuous homomorphisms out of a path-connected group are equivalent to continuous
homomorphisms out of its universal cover that kill the projection kernel. -/
noncomputable def homEquivKerProjHom :
    (G →ₜ* K) ≃
      {f : UniversalCover (1 : G) →ₜ* K //
        ((projHom : UniversalCover (1 : G) →ₜ* G) :
          UniversalCover (1 : G) →* G).ker ≤ (f : UniversalCover (1 : G) →* K).ker} :=
  ContinuousMonoidHom.homEquivOfIsQuotientMap projHom <| by
    simpa only [coe_projHom] using
      (UniversalCover.isQuotientCoveringMap (x₀ := (1 : G))).toIsQuotientMap

/-- The universal-cover correspondence sends a homomorphism to its composition with the covering
projection. -/
@[simp]
theorem homEquivKerProjHom_apply_coe (f : G →ₜ* K) :
    ((homEquivKerProjHom f :
      {g : UniversalCover (1 : G) →ₜ* K //
        ((projHom : UniversalCover (1 : G) →ₜ* G) :
          UniversalCover (1 : G) →* G).ker ≤ (g : UniversalCover (1 : G) →* K).ker}) :
      UniversalCover (1 : G) →ₜ* K) = f.comp projHom := by
  rw [homEquivKerProjHom, ContinuousMonoidHom.homEquivOfIsQuotientMap_apply_coe]

/-- Descending a homomorphism from the universal cover and composing again with the covering
projection recovers the original homomorphism. -/
@[simp]
theorem homEquivKerProjHom_symm_apply_comp
    (f : {g : UniversalCover (1 : G) →ₜ* K //
      ((projHom : UniversalCover (1 : G) →ₜ* G) :
        UniversalCover (1 : G) →* G).ker ≤ (g : UniversalCover (1 : G) →* K).ker}) :
    (homEquivKerProjHom.symm f).comp projHom = f.1 := by
  have h := congrArg Subtype.val (homEquivKerProjHom.apply_symm_apply f)
  rw [homEquivKerProjHom_apply_coe] at h
  exact h

end TauCeti.UniversalCover
