/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Basic

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

## Main definitions

* `MonoidHom.classifyingSpaceMap`: the continuous map induced by a group homomorphism.

## Main results

* `MonoidHom.classifyingSpaceMap_proj`: compatibility with the orbit projections.
* `MonoidHom.classifyingSpaceMap_basepoint`: preservation of the chosen base points.
* `MonoidHom.classifyingSpaceMap_id`, `MonoidHom.classifyingSpaceMap_comp`: strict functor laws.

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

end MonoidHom
