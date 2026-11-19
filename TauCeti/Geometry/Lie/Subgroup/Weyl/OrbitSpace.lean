/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Weyl.AdjointOrbit
public import TauCeti.RepresentationTheory.OrbitSpace
public import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Geometry.Lie.Subgroup.Weyl.Finite
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
(`TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_iff`). Neither space is compact,
so a continuous bijection between them need not be a homeomorphism. Instead, the map `𝔱 → 𝔤 / Ad G`
is closed: `𝔱` is a closed subspace of `𝔤`, and the orbit map of the compact group `G` is closed
(`Representation.isClosedMap_orbitRel_mk`). Its fibres are single Weyl orbits, which are finite
because the Weyl group is finite (`TauCeti.Lie.IsMaximalTorus.finite_normalizerQuotient`), so this
map is proper. The induced bijection `𝔱 / W → 𝔤 / Ad G` is then continuous and closed, hence a
homeomorphism. The adjoint orbit space is Hausdorff, as the orbit space of a compact group acting
on a Hausdorff space.

No connectedness of `G` is needed. The restriction of the proper map `𝔱 → 𝔤 / Ad G` to a closed
subset of `𝔱` meeting every Weyl orbit exactly once, such as a closed Weyl chamber, is again proper
and is bijective onto `𝔤 / Ad G`; this is how adjoint orbits are parametrized by a chamber.

## Main results

* `TauCeti.Lie.IsMaximalTorus.orbitRel_weylAdjointRepresentation_iff`: two elements of `𝔱` are in
  one Weyl orbit exactly when they are in one adjoint orbit.
* `TauCeti.Lie.IsMaximalTorus.isProperMap_orbitRel_mk_coe`: the map `𝔱 → 𝔤 / Ad G` is proper.
* `TauCeti.Lie.IsMaximalTorus.weylOrbitHomeomorph`: the homeomorphism `𝔱 / W ≃ₜ 𝔤 / Ad G`.
* `TauCeti.Lie.t2Space_quotient_orbitRel_continuousAdjointRepresentation`: the adjoint orbit
  space of a compact Lie group is Hausdorff.

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

/-- The adjoint action `(g, X) ↦ Ad_g X`, read through the adjoint representation, is jointly
continuous. -/
private theorem continuous_continuousAdjointRepresentation_apply :
    Continuous fun p : G × LeftInvariantDerivation I G ↦
      ContRepresentation.toRepresentation ℝ G _ (continuousAdjointRepresentation (I := I) (G := G))
        p.1 p.2 := by
  simpa only [ContRepresentation.toRepresentation_apply, continuousAdjointRepresentation_apply]
    using (contMDiff_Ad_apply (I := I) (G := G)).continuous

/-! ### The adjoint orbit space -/

section Compact

variable [CompactSpace G]

/-- **The adjoint orbit space of a compact Lie group is Hausdorff.** -/
instance t2Space_quotient_orbitRel_continuousAdjointRepresentation :
    T2Space
      (Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel) :=
  Representation.t2Space_quotient_orbitRel _ continuous_continuousAdjointRepresentation_apply

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

/-- **The map from a torus Lie algebra to the adjoint orbit space is proper.** For a maximal torus
`T` of a compact Lie group `G`, the map `𝔱 → 𝔤 / Ad G` sending `X` to its adjoint orbit is
closed, since `𝔱` is closed in `𝔤` and the orbit map of the compact group `G` is closed, and its
fibres are single Weyl orbits, which are finite. -/
theorem IsMaximalTorus.isProperMap_orbitRel_mk_coe (hT : IsMaximalTorus T) :
    IsProperMap fun X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule ↦
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        (X : LeftInvariantDerivation I G) := by
  have := hT.finite_normalizerQuotient I
  have hι : IsClosedEmbedding
      ((↑) : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule → LeftInvariantDerivation I G) :=
    (isClosed_lieSubalgebraOfSubgroup hT.isTorus.isClosed).isClosedEmbedding_subtypeVal
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨continuous_quotient_mk'.comp hι.continuous,
      (Representation.isClosedMap_orbitRel_mk _
        continuous_continuousAdjointRepresentation_apply).comp hι.isClosedMap, fun y ↦ ?_⟩
  obtain hy | ⟨X₀, hX₀⟩ := (_ ⁻¹' {y}).eq_empty_or_nonempty
  · rw [hy]
    exact isCompact_empty
  -- A fibre that contains `X₀` lies in the Weyl orbit of `X₀`, which is finite.
  refine ((Set.finite_range fun w ↦ T.weylAdjointRepresentation (I := I) w X₀).subset
    fun X hX ↦ ?_).isCompact
  rw [mem_preimage, mem_singleton_iff, ← hX₀, Representation.orbitRel_mk_eq_mk_iff] at hX
  exact (Representation.orbitRel_apply _).mp
    ((hT.orbitRel_weylAdjointRepresentation_iff X X₀).mpr
      ((Representation.orbitRel_apply _).mpr hX))

/-- The map `𝔱 / W → 𝔤 / Ad G` induced by the inclusion of the Lie algebra of a maximal torus. -/
private def IsMaximalTorus.weylOrbitMap (hT : IsMaximalTorus T) :
    Quotient (T.weylAdjointRepresentation (I := I)).orbitRel →
      Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel :=
  Quotient.map' (↑) fun X Y ↦ (hT.orbitRel_weylAdjointRepresentation_iff X Y).mp

private theorem IsMaximalTorus.bijective_weylOrbitMap (hT : IsMaximalTorus T) :
    Function.Bijective (hT.weylOrbitMap (I := I)) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · induction x using Quotient.inductionOn' with | h X => ?_
    induction y using Quotient.inductionOn' with | h Y => ?_
    exact Quotient.sound' ((hT.orbitRel_weylAdjointRepresentation_iff X Y).mpr
      (Quotient.exact' hxy))
  · induction y using Quotient.inductionOn' with | h X => ?_
    obtain ⟨g, hg⟩ := hT.exists_Ad_mem_lieSubalgebraOfSubgroup X
    refine ⟨Quotient.mk'' ⟨Ad (I := I) g X, hg⟩,
      Quotient.sound' ((Representation.orbitRel_apply _).mpr ⟨g, ?_⟩)⟩
    simp

/-- **The adjoint orbit space of a compact Lie group is the quotient of a torus Lie algebra by the
Weyl group.** For a maximal torus `T` of a compact Lie group `G`, the inclusion of its Lie algebra
`𝔱` into `𝔤` induces a homeomorphism `𝔱 / W ≃ₜ 𝔤 / Ad G` from the orbit space of the Weyl group
`W = N(T) / T` onto the adjoint orbit space. -/
def IsMaximalTorus.weylOrbitHomeomorph (hT : IsMaximalTorus T) :
    Quotient (T.weylAdjointRepresentation (I := I)).orbitRel ≃ₜ
      Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel :=
  (Equiv.ofBijective _ hT.bijective_weylOrbitMap).toHomeomorphOfContinuousClosed
    (continuous_subtype_val.quotient_map' fun X Y ↦
      (hT.orbitRel_weylAdjointRepresentation_iff X Y).mp) fun C hC ↦ by
      -- The image of `C` is that of its preimage in `𝔱` under the proper map `𝔱 → 𝔤 / Ad G`.
      -- `Quotient.map'` computes on classes: `weylOrbitMap` sends the class of `X` to that of `X`.
      have hcomp : hT.weylOrbitMap (I := I) ∘ Quotient.mk'' =
          fun X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule ↦ Quotient.mk
            (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
            (X : LeftInvariantDerivation I G) :=
        rfl
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
        (X : LeftInvariantDerivation I G) := by
  simp [weylOrbitHomeomorph, weylOrbitMap]

end Compact

end TauCeti.Lie
