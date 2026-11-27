/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
import TauCeti.AlgebraicTopology.ClassifyingSpace.HomotopyFunctor
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homotopic

/-!
# Pointed maps between Milnor classifying spaces

By Hatcher's Proposition 1B.9 for path-connected Hausdorff CW complexes
(`TauCeti.homotopicRel_of_mapOfEq_eq_of_cwComplex`), combined with strict functoriality
(`MonoidHom.classifyingSpaceMap`), every pointed continuous map
`classifyingSpace G → classifyingSpace H` between Milnor classifying spaces (in arbitrary
universes) is homotopic relative to the base point to `φ.classifyingSpaceMap` for a unique
homomorphism `φ : G →* H` (`TauCeti.homotopicRel_classifyingSpaceMap_of_mapOfEq_eq`,
`TauCeti.existsUnique_homotopicRel_classifyingSpaceMap`).

## Main results

* `TauCeti.homotopicRel_classifyingSpaceMap_of_mapOfEq_eq`: a pointed map
  `classifyingSpace G → classifyingSpace H` realizing `φ` on `π₁` is pointed homotopic to
  `φ.classifyingSpaceMap`.
* `TauCeti.existsUnique_homotopicRel_classifyingSpaceMap`: every pointed map
  `classifyingSpace G → classifyingSpace H` is pointed homotopic to `φ.classifyingSpaceMap` for a
  unique `φ : G →* H`.

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

/-- **Every pointed map `classifyingSpace G → classifyingSpace H` inducing `φ` is pointed homotopic
to `φ.classifyingSpaceMap`.** -/
theorem homotopicRel_classifyingSpaceMap_of_mapOfEq_eq {G : Type u} {H : Type v} [Group G]
    [Group H] (φ : G →* H) {f : C(classifyingSpace G, classifyingSpace H)}
    (hf : f (classifyingSpaceBasepoint G) = classifyingSpaceBasepoint H)
    (hfφ : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H (FundamentalGroup.mapOfEq f hf a) =
      φ (classifyingSpaceFundamentalGroupMulEquiv G a)) :
    f.HomotopicRel φ.classifyingSpaceMap {classifyingSpaceBasepoint G} :=
  have : PathConnectedSpace (classifyingSpace G) :=
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.pathConnectedSpace
  homotopicRel_of_mapOfEq_eq_of_cwComplex
    (fun n ↦ subsingleton_homotopyGroup_classifyingSpace H n (classifyingSpaceBasepoint H))
    hf φ.classifyingSpaceMap_basepoint
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

end TauCeti
