/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat.Basic
import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
import TauCeti.AlgebraicTopology.EilenbergMacLane.PointedMaps

/-!
# Classification of pointed maps out of Milnor's classifying space

Since Milnor's classifying space `TauCeti.classifyingSpace G` is a well-pointed aspherical space
of CW type, the general classification of pointed maps out of well-pointed `K(G, 1)` spaces
(`TauCeti.IsAspherical.exists_mapOfEq`, `TauCeti.IsAspherical.homotopicRel_of_mapOfEq_eq`)
specializes to it:

* Every homomorphism `π₁(classifyingSpace G) →* π₁(Z, z)` into a space with vanishing homotopy
  groups from degree `2` on is induced by a pointed continuous map
  (`TauCeti.exists_mapOfEq_classifyingSpace`).
* Pointed maps `classifyingSpace G → Z` into a space whose homotopy groups vanish from degree `2`
  on at every point are determined up to homotopy relative to the base point by the homomorphism
  they induce on `π₁` (`TauCeti.homotopicRel_of_mapOfEq_eq_classifyingSpace`).
* Combined with strict functoriality (`MonoidHom.classifyingSpaceMap`), every pointed continuous map
  `classifyingSpace G → classifyingSpace H` is homotopic relative to the base point to
  `φ.classifyingSpaceMap` for a unique homomorphism `φ : G →* H`
  (`TauCeti.homotopicRel_classifyingSpaceMap_of_mapOfEq_eq`,
  `TauCeti.existsUnique_homotopicRel_classifyingSpaceMap`).

## Main results

* `TauCeti.exists_mapOfEq_classifyingSpace`: homomorphisms out of `π₁(classifyingSpace G)` are
  induced by pointed maps.
* `TauCeti.homotopicRel_of_mapOfEq_eq_classifyingSpace`: pointed maps out of `classifyingSpace G`
  are determined up to pointed homotopy by `π₁`.
* `TauCeti.homotopicRel_classifyingSpaceMap_of_mapOfEq_eq`: a pointed map
  `classifyingSpace G → classifyingSpace H` realizing `φ` on `π₁` is pointed homotopic to
  `φ.classifyingSpaceMap`.
* `TauCeti.existsUnique_homotopicRel_classifyingSpaceMap`: every pointed map
  `classifyingSpace G → classifyingSpace H` is pointed homotopic to `φ.classifyingSpaceMap` for a
  unique `φ : G →* H`.
* `TauCeti.fundamentalGroupFunctor_map_bijective_classifyingSpace`: pointed homotopy classes of
  maps out of `classifyingSpace G` into a space without higher homotopy groups are classified by
  `π₁`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B,
  Proposition 1B.9.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open scoped Topology Topology.Homotopy

universe u v

namespace TauCeti

/-- **Homomorphisms out of `π₁(classifyingSpace G)` are induced by pointed maps.** -/
theorem exists_mapOfEq_classifyingSpace (G : Type u) [Group G] {Z : Type u} [TopologicalSpace Z]
    {z : Z} (hZ : ∀ k, 2 ≤ k → Subsingleton (π_ k Z z))
    (fπ : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G) →*
      FundamentalGroup Z z) :
    ∃ (f : C(classifyingSpace G, Z)) (hf : f (classifyingSpaceBasepoint G) = z),
      FundamentalGroup.mapOfEq f hf = fπ :=
  (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.exists_mapOfEq
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G) hZ fπ

/-- **Pointed maps out of `classifyingSpace G` are determined up to pointed homotopy by `π₁`.** -/
theorem homotopicRel_of_mapOfEq_eq_classifyingSpace (G : Type u) [Group G] {Z : Type v}
    [TopologicalSpace Z] (hZ : ∀ (z : Z) (n : ℕ), Subsingleton (π_ (n + 2) Z z))
    {f g : C(classifyingSpace G, Z)} {z : Z}
    (hf : f (classifyingSpaceBasepoint G) = z) (hg : g (classifyingSpaceBasepoint G) = z)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {classifyingSpaceBasepoint G} :=
  (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.homotopicRel_of_mapOfEq_eq
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G) hZ hf hg hfg

/-- **Every pointed map `classifyingSpace G → classifyingSpace H` inducing `φ` is pointed homotopic
to `φ.classifyingSpaceMap`.** -/
theorem homotopicRel_classifyingSpaceMap_of_mapOfEq_eq {G : Type u} {H : Type v} [Group G]
    [Group H] (φ : G →* H) {f : C(classifyingSpace G, classifyingSpace H)}
    (hf : f (classifyingSpaceBasepoint G) = classifyingSpaceBasepoint H)
    (hfφ : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H (FundamentalGroup.mapOfEq f hf a) =
      φ (classifyingSpaceFundamentalGroupMulEquiv G a)) :
    f.HomotopicRel φ.classifyingSpaceMap {classifyingSpaceBasepoint G} :=
  homotopicRel_of_mapOfEq_eq_classifyingSpace G
    (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y) hf φ.classifyingSpaceMap_basepoint
    (MonoidHom.ext fun a ↦ (classifyingSpaceFundamentalGroupMulEquiv H).injective <| by
      rw [hfφ, φ.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq])

/-- **Pointed homotopy classes of maps `classifyingSpace G → classifyingSpace H` correspond
bijectively to group homomorphisms `G →* H`.** Every base-point-preserving continuous map between
Milnor classifying spaces is homotopic relative to the base point to `φ.classifyingSpaceMap` for a
unique homomorphism `φ : G →* H`. -/
theorem existsUnique_homotopicRel_classifyingSpaceMap {G : Type u} {H : Type v} [Group G]
    [Group H] (f : C(classifyingSpace G, classifyingSpace H))
    (hf : f (classifyingSpaceBasepoint G) = classifyingSpaceBasepoint H) :
    ∃! φ : G →* H, f.HomotopicRel φ.classifyingSpaceMap {classifyingSpaceBasepoint G} := by
  let φ : G →* H := (classifyingSpaceFundamentalGroupMulEquiv H).toMonoidHom.comp
    ((FundamentalGroup.mapOfEq f hf).comp
      (classifyingSpaceFundamentalGroupMulEquiv G).symm.toMonoidHom)
  refine ⟨φ, homotopicRel_classifyingSpaceMap_of_mapOfEq_eq φ hf fun a ↦ by
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply],
    fun ψ hψ ↦ MonoidHom.ext fun g ↦ ?_⟩
  have hEq := congrArg (fun k ↦ classifyingSpaceFundamentalGroupMulEquiv H
    (k ((classifyingSpaceFundamentalGroupMulEquiv G).symm g)))
    (FundamentalGroup.mapOfEq_eq_of_homotopicRel hf ψ.classifyingSpaceMap_basepoint rfl hψ)
  rw [ψ.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq,
    (classifyingSpaceFundamentalGroupMulEquiv G).apply_symm_apply] at hEq
  exact hEq.symm

/-- **Pointed maps out of Milnor's classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then pointed homotopy classes
`classifyingSpace G → Y` correspond bijectively to homomorphisms `π₁(classifyingSpace G) ⟶ π₁(Y)`.
-/
theorem fundamentalGroupFunctor_map_bijective_classifyingSpace (G : Type u) [Group G]
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj (classifyingSpaceFunctor.obj (GrpCat.of G)))
      (Y := PointedHomotopyCat.quotient.obj Y)) :=
  haveI : CWType (classifyingSpaceFunctor.obj (GrpCat.of G)).carrier :=
    inferInstanceAs (CWType (classifyingSpace G))
  IsAspherical.fundamentalGroupFunctor_map_bijective
    (X := classifyingSpaceFunctor.obj (GrpCat.of G))
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G) hY

end TauCeti
