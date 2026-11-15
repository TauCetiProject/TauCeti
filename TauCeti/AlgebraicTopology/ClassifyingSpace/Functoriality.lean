/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Strict functoriality of Milnor's classifying spaces

A group homomorphism induces a continuous map of classifying spaces by applying it to
the labels of the countable join and descending to orbits. These maps preserve the chosen
base points and respect identity homomorphisms and composition as equalities of continuous
maps. The total-space maps are equivariant, so the orbit projections commute with the induced
maps.

The representative formula `MonoidHom.classifyingSpaceMap_proj` characterizes the induced map
without unfolding the orbit space. Together with `classifyingSpace_continuousMap_ext`, it
also lets callers prove identities of induced maps on representatives.

Under the identifications `classifyingSpaceFundamentalGroupMulEquiv` of the fundamental groups
of the classifying spaces with the groups themselves, the map induced on fundamental groups is
the original homomorphism.

## Main definitions

* `MonoidHom.classifyingSpaceMap`: the continuous map induced by a group homomorphism.

## Main results

* `MonoidHom.classifyingSpaceMap_proj`: compatibility with the orbit projections.
* `MonoidHom.classifyingSpaceMap_basepoint`: preservation of the chosen base points.
* `MonoidHom.classifyingSpaceMap_id`, `MonoidHom.classifyingSpaceMap_comp`: strict functor laws.
* `MonoidHom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq`: the induced map on fundamental
  groups is the original homomorphism.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

namespace MonoidHom

open TauCeti

universe u v w

variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

/-- A group homomorphism induces a continuous map of Milnor classifying spaces by applying it
to the vertex labels of the countable join and passing to orbits. -/
def classifyingSpaceMap (φ : G →* H) : C(classifyingSpace G, classifyingSpace H) :=
  classifyingSpaceLift
    ((⟨classifyingSpaceProj H, continuous_classifyingSpaceProj H⟩ :
      C(universalGSpace H, classifyingSpace H)).comp φ.universalGSpaceMap)
    (fun g x => by simp)

/-- The induced map commutes with the orbit projections. -/
@[simp]
theorem classifyingSpaceMap_proj (φ : G →* H) (x : universalGSpace G) :
    φ.classifyingSpaceMap (classifyingSpaceProj G x) =
      classifyingSpaceProj H (φ.universalGSpaceMap x) :=
  classifyingSpaceLift_apply _ _ x

/-- The induced map preserves the chosen base point. -/
@[simp]
theorem classifyingSpaceMap_basepoint (φ : G →* H) :
    φ.classifyingSpaceMap (classifyingSpaceBasepoint G) = classifyingSpaceBasepoint H := by
  simpa only [universalGSpaceMap_basepoint, classifyingSpaceProj_universalGSpaceBasepoint]
    using φ.classifyingSpaceMap_proj (universalGSpaceBasepoint G)

/-- The identity homomorphism induces the identity continuous map. -/
@[simp]
theorem classifyingSpaceMap_id :
    (MonoidHom.id G).classifyingSpaceMap = ContinuousMap.id (classifyingSpace G) := by
  apply classifyingSpace_continuousMap_ext
  intro x
  simp

/-- Composition of group homomorphisms induces composition of continuous maps, strictly. -/
@[simp]
theorem classifyingSpaceMap_comp (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).classifyingSpaceMap = ψ.classifyingSpaceMap.comp φ.classifyingSpaceMap := by
  apply classifyingSpace_continuousMap_ext
  intro x
  simp

/-- **The induced map on fundamental groups is the homomorphism itself.** Under the
identifications `classifyingSpaceFundamentalGroupMulEquiv` of the fundamental groups of the
classifying spaces with `G` and `H`, the map induced by `φ.classifyingSpaceMap` on fundamental
groups at the base points is `φ`. -/
@[simp]
theorem classifyingSpaceFundamentalGroupMulEquiv_mapOfEq (φ : G →* H)
    (γ : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G)) :
    classifyingSpaceFundamentalGroupMulEquiv H
        (FundamentalGroup.mapOfEq φ.classifyingSpaceMap φ.classifyingSpaceMap_basepoint γ) =
      φ (classifyingSpaceFundamentalGroupMulEquiv G γ) := by
  -- The lift of the image loop is the image of the lift: the total-space map lies over
  -- `φ.classifyingSpaceMap`, so monodromy is natural for it.
  rw [classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff,
    IsCoveringMap.coe_monodromy_mapOfEq (isQuotientCoveringMap_classifyingSpaceProj G).isCoveringMap
      (isQuotientCoveringMap_classifyingSpaceProj H).isCoveringMap
      (g := φ.universalGSpaceMap) (funext fun x => (φ.classifyingSpaceMap_proj x).symm) _ γ
      ⟨universalGSpaceBasepoint G, classifyingSpaceProj_universalGSpaceBasepoint G⟩ _
      (universalGSpaceMap_basepoint φ),
    classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff.mp rfl]
  simp [← smul_universalGSpaceBasepoint]

end MonoidHom
