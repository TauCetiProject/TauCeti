/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Pinned

/-!
# Integral realization of the pinned type-B spin action

The toral closure of the independently pinned rational type-B action on the integral spin
lattice is the represented type-B spin carrier. The equality holds for the defining Hopf
ideals over `ℤ`, not just for points over fields. Consequently it identifies the integral
schemes and their matrix-valued points over every commutative ring.

The identification retains both signs of the numbered simple-root morphisms and the weight
torus. It supplies the integral realization needed when comparing this full-weight spin model
with other Chevalley models. It does not assert a comparison with the direct sum of fundamental
modules, or generation of all scheme points by root elements.

The proof uses `TypeBSpinCarrier.pinnedRep_ι_rootGenerator`: the pinned and native actions
have identical simple-root operators on the same lattice, hence identical integral
divided-power coactions. The torus uses the same spin weights in fundamental-weight coordinates.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open CategoryTheory
open _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (ht : (DynkinType.B (n + 1)).Valid)

/-- The pinned signed simple-root coordinate morphism is the native spin coordinate morphism,
including at the terminal short root. -/
theorem pinnedRootSubgroupCoordinateMap_eq (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    kostantRootSubgroupCoordinateMap
        ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n ht) k (isNilpotent_pinnedRep_rootGenerator n ht k)
        (latticeBasis n) =
      kostantRootSubgroupCoordinateMap typeBSimpleRootGeneratorFamily typeBSimpleCorootGenerator
        (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) k
        (isNilpotent_rep_rootGenerator n k) (latticeBasis n) := by
  apply kostantRootSubgroupCoordinateMap_eq_of_operator_eq
  exact pinnedRep_ι_rootGenerator n ht k

/-- The pinned spin toral closure has exactly the integral defining Hopf ideal of the
represented spin carrier. In particular this retains infinitesimal points in bad characteristic. -/
theorem pinnedToralDefiningIdeal_eq :
    kostantToralDefiningIdeal
        ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n ht) (isNilpotent_pinnedRep_rootGenerator n ht)
        (latticeBasis n) (basisWeight n) = definingIdeal n := by
  rw [definingIdeal_def]
  -- `erw` reduces the Dynkin rank when matching the pinned admissibility proofs.
  apply le_antisymm <;> erw [le_kostantToralDefiningIdeal_iff]
  · constructor
    · intro k
      rw [← pinnedRootSubgroupCoordinateMap_eq n ht k]
      exact kostantToralDefiningIdeal_toIdeal_le_root_ker _ _ _ _ _ _ _ _ k
    · exact kostantToralDefiningIdeal_toIdeal_le_torus_ker _ _ _ _ _ _ _ _
  · constructor
    · intro k
      rw [pinnedRootSubgroupCoordinateMap_eq n ht k]
      exact kostantToralDefiningIdeal_toIdeal_le_root_ker _ _ _ _ _ _ _ _ k
    · exact kostantToralDefiningIdeal_toIdeal_le_torus_ker _ _ _ _ _ _ _ _

/-- The integral scheme of the pinned spin action is the represented type-B spin carrier. -/
theorem pinnedToralGroupScheme_eq :
    kostantToralGroupScheme
        ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n ht) (isNilpotent_pinnedRep_rootGenerator n ht)
        (latticeBasis n) (basisWeight n) = groupScheme n := by
  rw [groupScheme_def]
  exact congrArg (CommHopfAlgCat.quotientSpec
    (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))) (pinnedToralDefiningIdeal_eq n ht)

/-- The integral realization preserves the closed immersion into the ambient general linear
group, so it changes no represented matrix. -/
@[simp]
theorem eqToHom_pinnedToralGroupScheme_comp_carrierι :
    eqToHom (pinnedToralGroupScheme_eq n ht) ≫ carrierι n =
      kostantToralGroupSchemeι
        ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n ht) (isNilpotent_pinnedRep_rootGenerator n ht)
        (latticeBasis n) (basisWeight n) := by
  -- The pinned and native indices differ only by reduction of the Dynkin rank.
  erw [carrierι_def, kostantToralGroupSchemeι_def, kostantToralGroupSchemeι_def]
  simp only [eqToHom_trans_assoc]
  rw [← Category.assoc]
  have hi := CommHopfAlgCat.eqToHom_comp_quotientSpecι _
    ((pinnedToralDefiningIdeal_eq n ht).trans (definingIdeal_def n))
  exact congrArg (fun f => f ≫ eqToHom (GeneralLinear.groupScheme_def ℤ (dimension n)).symm) hi

/-- The integral realization matches the positive and negative numbered simple-root morphisms. -/
@[simp]
theorem pinnedRootSubgroupToToral_comp_eqToHom (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    kostantRootSubgroupToToral
        ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n ht) (isNilpotent_pinnedRep_rootGenerator n ht)
        (latticeBasis n) (basisWeight n) k ≫ eqToHom (pinnedToralGroupScheme_eq n ht) =
      rootSubgroup n k := by
  apply (cancel_mono (carrierι n)).1
  -- Reduce the Dynkin rank when matching the pinned generator index.
  erw [Category.assoc, eqToHom_pinnedToralGroupScheme_comp_carrierι,
    kostantRootSubgroupToToral_comp_ι, rootSubgroup_comp_carrierι,
    kostantRootSubgroup_def, kostantRootSubgroup_def, pinnedRootSubgroupCoordinateMap_eq]

/-- The integral realization matches the full weight torus, with its original coordinates. -/
@[simp]
theorem pinnedWeightTorusToToral_comp_eqToHom :
    kostantWeightTorusToToral
        ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n ht) (isNilpotent_pinnedRep_rootGenerator n ht)
        (latticeBasis n) (basisWeight n) ≫ eqToHom (pinnedToralGroupScheme_eq n ht) =
      weightTorus n := by
  apply (cancel_mono (carrierι n)).1
  -- Reduce the Dynkin rank when matching the pinned torus index.
  erw [Category.assoc, eqToHom_pinnedToralGroupScheme_comp_carrierι,
    kostantWeightTorusToToral_comp_ι, weightTorus_comp_carrierι]
  rfl

/-- Over every commutative value ring the pinned and native spin points are the same subgroup
of the same general linear group, not merely abstractly isomorphic. -/
theorem pinnedToralPointsSubgroup_eq (A : Type*) [CommRing A] :
    kostantToralPointsSubgroup
        ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n ht) (isNilpotent_pinnedRep_rootGenerator n ht)
        (latticeBasis n) (basisWeight n) A = points n A := by
  -- Reduce the Dynkin rank inside the pinned admissibility proofs.
  erw [kostantToralPointsSubgroup_def, points_def, pinnedToralDefiningIdeal_eq]

end

end TauCeti.TypeBSpinCarrier
