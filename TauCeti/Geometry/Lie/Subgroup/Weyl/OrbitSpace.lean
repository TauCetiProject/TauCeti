/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.OrbitSpace
public import TauCeti.Geometry.Lie.Subgroup.Weyl.AdjointOrbit
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The adjoint orbit space of a compact Lie group

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱 ⊆ 𝔤`, and let
`W = N(T) / T` be its Weyl group, acting on `𝔱` by the adjoint action
(`Subgroup.weylAdjointRepresentation`). This file identifies the space of adjoint orbits
`𝔤 / Ad G` with the orbit space `𝔱 / W`, as topological spaces. The orbit spaces are the
quotients by `Representation.orbitRel` of the adjoint representation of `G` on `𝔤` and of the
Weyl representation on `𝔱`, with the quotient topologies.

The inclusion `𝔱 → 𝔤` induces a map `𝔱 / W → 𝔤 / Ad G`. It is surjective because every adjoint
orbit meets `𝔱` (`TauCeti.Lie.IsMaximalTorus.exists_Ad_mem_lieSubalgebraOfSubgroup`), and injective
because two elements of `𝔱` in one adjoint orbit are related by the Weyl group
(`TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_iff`). Neither space need be
compact, so a continuous bijection between them need not be a homeomorphism. Instead, the map
`𝔱 → 𝔤 / Ad G` is proper: `𝔱` is a closed subspace of `𝔤`, and the orbit map of the compact
group `G` is proper (`Representation.isProperMap_orbitRel_mk`). The induced bijection
`𝔱 / W → 𝔤 / Ad G` is then continuous and closed, hence a homeomorphism. The adjoint orbit space
is Hausdorff (`TauCeti.Lie.t2Space_quotient_orbitRel_continuousAdjointRepresentation`).

No connectedness of `G` is needed. The restriction of the proper map `𝔱 → 𝔤 / Ad G` to a closed
subset of `𝔱` meeting every Weyl orbit exactly once is again proper and is bijective onto
`𝔤 / Ad G`. When `G` is connected, a closed Weyl chamber is such a subset; this is how adjoint
orbits are parametrized by a chamber.

## Main results

* `TauCeti.Lie.IsMaximalTorus.orbitRel_weylAdjointRepresentation_iff`: two elements of `𝔱` are in
  one Weyl orbit exactly when they are in one adjoint orbit.
* `TauCeti.Lie.IsMaximalTorus.isProperMap_orbitRel_mk_coe`: the map `𝔱 → 𝔤 / Ad G` is proper.
* `TauCeti.Lie.IsMaximalTorus.weylOrbitHomeomorph`: the homeomorphism `𝔱 / W ≃ₜ 𝔤 / Ad G`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Set Topology
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### The adjoint orbit space -/

section Compact

variable [CompactSpace G]

variable {T : Subgroup G} [IsMulCommutative T]

/-- **Weyl orbits are the traces of adjoint orbits on a torus Lie algebra.** Two elements of the
Lie algebra of a maximal torus `T` of a compact Lie group are in one orbit of the Weyl group
`N(T) / T` exactly when they are in one adjoint orbit of `G`. -/
theorem IsMaximalTorus.orbitRel_weylAdjointRepresentation_iff (hT : IsMaximalTorus T)
    (X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    (T.weylAdjointRepresentation (I := I)).orbitRel X Y ↔
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        (X : LeftInvariantDerivation I G) Y := by
  simp only [Representation.orbitRel_apply, ContRepresentation.toRepresentation_apply,
    continuousAdjointRepresentation_apply]
  exact hT.exists_weylAdjointRepresentation_eq_iff Y X

omit [IsMulCommutative T] in
/-- **The map from a torus Lie algebra to the adjoint orbit space is proper.** For a maximal torus
`T` of a compact Lie group `G`, the map `𝔱 → 𝔤 / Ad G` sending `X` to its adjoint orbit is
proper. -/
theorem IsMaximalTorus.isProperMap_orbitRel_mk_coe (hT : IsMaximalTorus T) :
    IsProperMap fun X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule ↦
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        (X : LeftInvariantDerivation I G) :=
  (Representation.isProperMap_orbitRel_mk _ continuous_continuousAdjointRepresentation_apply).comp
    (isClosed_lieSubalgebraOfSubgroup hT.isTorus.isClosed).isClosedEmbedding_subtypeVal.isProperMap

/-- The map `𝔱 / W → 𝔤 / Ad G` induced by the inclusion of the Lie algebra of a maximal torus. -/
private def IsMaximalTorus.weylOrbitMap (hT : IsMaximalTorus T) :
    Quotient (T.weylAdjointRepresentation (I := I)).orbitRel →
      Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel :=
  Quotient.map' (↑) fun X Y ↦ (hT.orbitRel_weylAdjointRepresentation_iff X Y).mp

/-- `weylOrbitMap` sends the Weyl orbit of `X ∈ 𝔱` to the adjoint orbit of `X`. -/
private theorem IsMaximalTorus.weylOrbitMap_mk (hT : IsMaximalTorus T)
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    hT.weylOrbitMap (Quotient.mk'' X) =
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        (X : LeftInvariantDerivation I G) :=
  Quotient.map'_mk'' _ _ X

private theorem IsMaximalTorus.bijective_weylOrbitMap (hT : IsMaximalTorus T) :
    Function.Bijective (hT.weylOrbitMap (I := I)) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · induction x using Quotient.inductionOn' with | h X => ?_
    induction y using Quotient.inductionOn' with | h Y => ?_
    rw [hT.weylOrbitMap_mk, hT.weylOrbitMap_mk] at hxy
    exact Quotient.sound' ((hT.orbitRel_weylAdjointRepresentation_iff X Y).mpr
      (Quotient.exact hxy))
  · induction y using Quotient.inductionOn' with | h X => ?_
    obtain ⟨g, hg⟩ := hT.exists_Ad_mem_lieSubalgebraOfSubgroup X
    refine ⟨Quotient.mk'' ⟨Ad (I := I) g X, hg⟩, (hT.weylOrbitMap_mk _).trans
      (Quotient.sound' ((Representation.orbitRel_apply _).mpr ⟨g, ?_⟩))⟩
    simp

/-- **The adjoint orbit space of a compact Lie group is the quotient of a torus Lie algebra by the
Weyl group.** For a maximal torus `T` of a compact Lie group `G`, the inclusion of its Lie algebra
`𝔱` into `𝔤` induces a homeomorphism `𝔱 / W ≃ₜ 𝔤 / Ad G` from the orbit space of the Weyl group
`W = N(T) / T` onto the adjoint orbit space. -/
def IsMaximalTorus.weylOrbitHomeomorph (hT : IsMaximalTorus T) :
    Quotient (T.weylAdjointRepresentation (I := I)).orbitRel ≃ₜ
      Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel :=
  (Equiv.ofBijective _ hT.bijective_weylOrbitMap).toHomeomorphOfContinuousClosed
    (continuous_subtypeVal.quotient_map' fun X Y ↦
      (hT.orbitRel_weylAdjointRepresentation_iff X Y).mp) fun C hC ↦ by
      -- The image of `C` is that of its preimage in `𝔱` under the proper map `𝔱 → 𝔤 / Ad G`.
      have hcomp : hT.weylOrbitMap (I := I) ∘ Quotient.mk'' =
          fun X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule ↦ Quotient.mk
            (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
            (X : LeftInvariantDerivation I G) :=
        funext hT.weylOrbitMap_mk
      rw [Equiv.coe_ofBijective, ← Quotient.mk''_surjective.image_preimage C, ← image_comp, hcomp]
      exact hT.isProperMap_orbitRel_mk_coe.isClosedMap _
        (hC.preimage continuous_quotient_mk')

/-- The homeomorphism `IsMaximalTorus.weylOrbitHomeomorph` sends the Weyl orbit of `X ∈ 𝔱` to the
adjoint orbit of `X`. -/
@[simp]
theorem IsMaximalTorus.weylOrbitHomeomorph_mk (hT : IsMaximalTorus T)
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    hT.weylOrbitHomeomorph (Quotient.mk _ X) =
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        (X : LeftInvariantDerivation I G) :=
  hT.weylOrbitMap_mk X

end Compact

end TauCeti.Lie
