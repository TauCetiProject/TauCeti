/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.OrbitSpace
public import TauCeti.Geometry.Lie.Adjoint.Representation.OrbitSpace
public import TauCeti.Geometry.Lie.Subgroup.Weyl.AdjointOrbit
public import TauCeti.RepresentationTheory.InvariantForm
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.RepresentationTheory.Continuous.Basic
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The adjoint and coadjoint orbit spaces of a compact Lie group

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

The coadjoint orbit space `𝔤* / Ad* G`, the orbit space of the coadjoint representation on the dual
`𝔤* = Module.Dual ℝ 𝔤` of the tangent Lie algebra, is identified with `𝔱 / W` in the same way, once
`𝔱` is placed in `𝔤*` by a form. Let `B` be a form on `𝔤` invariant under the adjoint action with
trivial left radical, such as an invariant inner product
(`TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`). The injective linear
map `𝔱 → 𝔤*`, `X ↦ B (X, ·)`, intertwines the adjoint action with the coadjoint action:
`Ad*_g (B X) = B (Ad_g X)`.
So every coadjoint orbit meets its image, because every adjoint orbit meets `𝔱` and `B` is onto
`𝔤*` in finite dimension (`TauCeti.Lie.IsMaximalTorus.exists_coadjointRepresentation_apply_eq`),
and two covectors `B (X, ·)`, `B (Y, ·)` with `X, Y ∈ 𝔱` are in one coadjoint orbit exactly when
`X` and `Y` are in one Weyl orbit
(`TauCeti.Lie.IsMaximalTorus.orbitRel_coadjointRepresentation_iff`). With the module topology on
`𝔤*`, the map `𝔱 → 𝔤* / Ad* G` is proper, as an injective linear map out of a finite-dimensional
space followed by the orbit map of a compact group, so the induced bijection
`𝔱 / W → 𝔤* / Ad* G` is a homeomorphism. Here `𝔱` consists of left-invariant derivations, and is
placed in `𝔤` by evaluation at the identity
(`leftInvariantDerivationLieEquivGroupLieAlgebra`).

## Main results

* `TauCeti.Lie.IsMaximalTorus.orbitRel_weylAdjointRepresentation_iff`: two elements of `𝔱` are in
  one Weyl orbit exactly when they are in one adjoint orbit.
* `TauCeti.Lie.IsMaximalTorus.isProperMap_orbitRel_mk_coe`: the map `𝔱 → 𝔤 / Ad G` is proper.
* `TauCeti.Lie.IsMaximalTorus.weylOrbitHomeomorph`: the homeomorphism `𝔱 / W ≃ₜ 𝔤 / Ad G`.
* `TauCeti.Lie.IsMaximalTorus.exists_coadjointRepresentation_apply_eq`: every coadjoint orbit meets
  the image of `𝔱` under an invariant form.
* `TauCeti.Lie.IsMaximalTorus.orbitRel_coadjointRepresentation_iff`: two covectors `B (X, ·)` and
  `B (Y, ·)` with `X, Y ∈ 𝔱` are in one coadjoint orbit exactly when `X` and `Y` are in one Weyl
  orbit.
* `TauCeti.Lie.isProperMap_orbitRel_mk_coadjointRepresentation`: the map `𝔱 → 𝔤* / Ad* G` is
  proper.
* `TauCeti.Lie.IsMaximalTorus.weylCoadjointOrbitHomeomorph`: the homeomorphism
  `𝔱 / W ≃ₜ 𝔤* / Ad* G`.

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

/-! ### The coadjoint orbit space -/

section Coadjoint

local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- Evaluation at the identity, the Lie algebra isomorphism from left-invariant derivations to the
tangent Lie algebra `𝔤` on which the coadjoint representation is defined. -/
local notation "evalOne" => leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
  (BoundarylessManifold.isInteriorPoint (x := (1 : G)))

variable {T : Subgroup G} {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}

omit [T2Space G] [FiniteDimensional ℝ E] [LieGroup I ∞ G] in
/-- A form with trivial left radical is injective as a map `𝔤 → 𝔤*`. -/
private theorem injective_of_separatingLeft (hB' : LinearMap.SeparatingLeft B) :
    Function.Injective B :=
  LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hB')

omit [T2Space G] in
private theorem injective_apply_evalOne (hB' : LinearMap.SeparatingLeft B) :
    Function.Injective fun X : LeftInvariantDerivation I G ↦ B (evalOne X) :=
  (injective_of_separatingLeft hB').comp (evalOne).injective

/-- The linear map `𝔱 → 𝔤*`, `X ↦ B (X(1), ·)`, sending an element of the Lie algebra of `T` to
its covector for the form `B`. -/
private def torusCovector (T : Subgroup G) (B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)) :
    (lieSubalgebraOfSubgroup (I := I) T).toSubmodule →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G) :=
  B ∘ₗ (evalOne).toLinearEquiv.toLinearMap ∘ₗ
    (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.subtype

private theorem torusCovector_apply (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    torusCovector T B X = B (evalOne (X : LeftInvariantDerivation I G)) :=
  rfl

variable [CompactSpace G]

/-- **Every coadjoint orbit meets a torus Lie algebra.** Let `B` be an invariant form with trivial
left radical on the Lie algebra `𝔤` of a compact Lie group, and `T` a maximal torus with Lie algebra
`𝔱`. Then every covector `ν ∈ 𝔤*` is carried by the coadjoint action to the covector `B (X, ·)` of
some `X ∈ 𝔱`. -/
theorem IsMaximalTorus.exists_coadjointRepresentation_apply_eq (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hB' : LinearMap.SeparatingLeft B) (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    ∃ g : G, ∃ X ∈ lieSubalgebraOfSubgroup (I := I) T,
      coadjointRepresentation ℝ I G g ν = B (evalOne X) := by
  -- In finite dimension, a form with trivial left radical identifies `𝔤` with `𝔤*`.
  obtain ⟨Z, rfl⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := GroupLieAlgebra I G)).symm).mp
    (injective_of_separatingLeft hB') ν
  obtain ⟨X, rfl⟩ := (evalOne).surjective Z
  obtain ⟨g, hg⟩ := hT.exists_Ad_mem_lieSubalgebraOfSubgroup X
  exact ⟨g, _, hg, (Representation.orbitMap_mk _ _ g).symm.trans
    (orbitMap_coadjointRepresentation_bilinForm_mk hB X g)⟩

variable [IsMulCommutative T]

/-- **Coadjoint orbits through a torus Lie algebra are Weyl orbits.** Let `B` be an invariant form
with trivial left radical on the Lie algebra `𝔤` of a compact Lie group, and `T` a maximal torus
with Lie algebra `𝔱`. Two elements `X, Y ∈ 𝔱` are in one orbit of the Weyl group `N(T) / T` exactly
when their covectors `B (X, ·)` and `B (Y, ·)` are in one coadjoint orbit. -/
theorem IsMaximalTorus.orbitRel_coadjointRepresentation_iff (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hB' : LinearMap.SeparatingLeft B) (X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    (coadjointRepresentation ℝ I G).orbitRel (B (evalOne (X : LeftInvariantDerivation I G)))
        (B (evalOne (Y : LeftInvariantDerivation I G))) ↔
      (T.weylAdjointRepresentation (I := I)).orbitRel X Y := by
  rw [hT.orbitRel_weylAdjointRepresentation_iff, Representation.orbitRel_apply,
    Representation.orbitRel_apply]
  refine exists_congr fun g ↦ ?_
  rw [← Representation.orbitMap_mk, orbitMap_coadjointRepresentation_bilinForm_mk hB,
    ContRepresentation.toRepresentation_apply,
    continuousAdjointRepresentation_apply]
  exact (injective_apply_evalOne hB').eq_iff

/-- The map `𝔱 / W → 𝔤* / Ad* G` induced by `X ↦ B (X, ·)`. -/
private def IsMaximalTorus.weylCoadjointOrbitMap (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hB' : LinearMap.SeparatingLeft B) :
    Quotient (T.weylAdjointRepresentation (I := I)).orbitRel →
      Quotient (coadjointRepresentation ℝ I G).orbitRel :=
  Quotient.map' (torusCovector T B) fun X Y ↦
    (hT.orbitRel_coadjointRepresentation_iff hB hB' X Y).mpr

private theorem IsMaximalTorus.weylCoadjointOrbitMap_mk (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hB' : LinearMap.SeparatingLeft B) (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    hT.weylCoadjointOrbitMap hB hB' (Quotient.mk'' X) =
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel
        (B (evalOne (X : LeftInvariantDerivation I G))) :=
  (Quotient.map'_mk'' _ _ X).trans (congrArg _ (torusCovector_apply X))

private theorem IsMaximalTorus.bijective_weylCoadjointOrbitMap (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hB' : LinearMap.SeparatingLeft B) :
    Function.Bijective (hT.weylCoadjointOrbitMap hB hB') := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · induction x using Quotient.inductionOn' with | h X => ?_
    induction y using Quotient.inductionOn' with | h Y => ?_
    rw [hT.weylCoadjointOrbitMap_mk, hT.weylCoadjointOrbitMap_mk] at hxy
    exact Quotient.sound' ((hT.orbitRel_coadjointRepresentation_iff hB hB' X Y).mp
      (Quotient.exact hxy))
  · induction y using Quotient.inductionOn' with | h ν => ?_
    obtain ⟨g, X, hX, hgX⟩ := hT.exists_coadjointRepresentation_apply_eq hB hB' ν
    refine ⟨Quotient.mk'' ⟨X, hX⟩, (hT.weylCoadjointOrbitMap_mk hB hB' _).trans ?_⟩
    rw [← hgX, Representation.orbitRel_mk_apply]

variable [TopologicalSpace (Module.Dual ℝ (GroupLieAlgebra I G))]
  [IsModuleTopology ℝ (Module.Dual ℝ (GroupLieAlgebra I G))]

omit [IsMulCommutative T] in
/-- **The map from a subgroup Lie algebra to the coadjoint orbit space is proper.** For a subgroup
`T` of a compact Lie group with Lie algebra `𝔱`, and a form `B` with trivial left radical on the
Lie algebra `𝔤`, the map `𝔱 → 𝔤* / Ad* G` sending `X` to the coadjoint orbit of `B (X, ·)` is
proper, for the module topology on `𝔤*`. -/
theorem isProperMap_orbitRel_mk_coadjointRepresentation (hB' : LinearMap.SeparatingLeft B) :
    IsProperMap fun X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule ↦
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel
        (B (evalOne (X : LeftInvariantDerivation I G))) := by
  have := IsModuleTopology.isTopologicalAddGroup ℝ (Module.Dual ℝ (GroupLieAlgebra I G))
  have := ModuleTopology.t2Space (Module.finBasis ℝ (Module.Dual ℝ (GroupLieAlgebra I G)))
  -- An injective linear map out of the finite-dimensional space `𝔱` is a closed embedding.
  have hφ : IsClosedEmbedding (torusCovector (I := I) T B) :=
    LinearMap.isClosedEmbedding_of_injective <| LinearMap.ker_eq_bot.mpr fun X Y hXY ↦
      Subtype.val_injective <| injective_apply_evalOne hB' <| by
        rwa [torusCovector_apply, torusCovector_apply] at hXY
  simpa only [Function.comp_def, torusCovector_apply] using
    (Representation.isProperMap_orbitRel_mk _ continuous_coadjointRepresentation_apply).comp
      hφ.isProperMap

/-- **The coadjoint orbit space of a compact Lie group is the quotient of a torus Lie algebra by
the Weyl group.** Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱`, and
`B` an invariant form with trivial left radical on the Lie algebra `𝔤`, such as an invariant inner
product (`TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`). Then
`X ↦ B (X, ·)` induces a homeomorphism `𝔱 / W ≃ₜ 𝔤* / Ad* G` from the orbit space of the Weyl group
`W = N(T) / T` onto the coadjoint orbit space, for the module topology on `𝔤*`. -/
def IsMaximalTorus.weylCoadjointOrbitHomeomorph (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hB' : LinearMap.SeparatingLeft B) :
    Quotient (T.weylAdjointRepresentation (I := I)).orbitRel ≃ₜ
      Quotient (coadjointRepresentation ℝ I G).orbitRel :=
  have := IsModuleTopology.isTopologicalAddGroup ℝ (Module.Dual ℝ (GroupLieAlgebra I G))
  (Equiv.ofBijective _ (hT.bijective_weylCoadjointOrbitMap hB hB')).toHomeomorphOfContinuousClosed
    ((LinearMap.continuous_of_finiteDimensional (torusCovector T B)).quotient_map' fun X Y ↦
      (hT.orbitRel_coadjointRepresentation_iff hB hB' X Y).mpr) fun C hC ↦ by
      -- The image of `C` is that of its preimage in `𝔱` under the proper map `𝔱 → 𝔤* / Ad* G`.
      have hcomp : hT.weylCoadjointOrbitMap hB hB' ∘ Quotient.mk'' =
          fun X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule ↦ Quotient.mk
            (coadjointRepresentation ℝ I G).orbitRel
            (B (evalOne (X : LeftInvariantDerivation I G))) :=
        funext (hT.weylCoadjointOrbitMap_mk hB hB')
      rw [Equiv.coe_ofBijective, ← Quotient.mk''_surjective.image_preimage C, ← image_comp, hcomp]
      exact (isProperMap_orbitRel_mk_coadjointRepresentation hB').isClosedMap _
        (hC.preimage continuous_quotient_mk')

/-- The homeomorphism `IsMaximalTorus.weylCoadjointOrbitHomeomorph` sends the Weyl orbit of
`X ∈ 𝔱` to the coadjoint orbit of `B (X, ·)`. -/
@[simp]
theorem IsMaximalTorus.weylCoadjointOrbitHomeomorph_mk (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hB' : LinearMap.SeparatingLeft B) (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    hT.weylCoadjointOrbitHomeomorph hB hB' (Quotient.mk _ X) =
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel
        (B (evalOne (X : LeftInvariantDerivation I G))) :=
  hT.weylCoadjointOrbitMap_mk hB hB' X

end Coadjoint

end TauCeti.Lie
