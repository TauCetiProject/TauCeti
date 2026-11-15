/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Pinned
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.OperatorCongr

/-!
# Realizing the pinned type-D spin action on the integral carrier

The full spin action of the pinned rational type-D Lie algebra and the original Serre action
have exactly the same numbered raising and lowering operators on the exterior lattice.
Their integral toral defining ideals therefore coincide. This identifies the represented
spin group scheme, and its matrix-valued points over every commutative ring, with the toral
closure constructed from `TypeDSpinCarrier.pinnedRep` on that same lattice and weight basis.
Both signs of the root parametrizations are unchanged as scheme morphisms and as matrices.
The weight torus is unchanged as well: both constructions use the identical basis weights.

These are equalities inside the same general linear realization, not comparisons obtained by
choosing an abstract group isomorphism or testing only field-valued points. In particular,
they retain the integral scheme structure in characteristic two. They do not assert
faithfulness of the pinned Lie action, equality with a separately generated fibre, or a
comparison with the canonical full-weight Chevalley group.

The inputs are the native spin lattice and `TypeDSpinCarrier.pinnedRep_ι_rootGenerator`.
The passage from equality of operators to equality of integral defining ideals uses
`UniversalEnvelopingAlgebra.kostantToralDefiningIdeal_eq_of_operator_eq`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open _root_.TauCeti.UniversalEnvelopingAlgebra CategoryTheory

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-- The represented type-D spin ideal is exactly the integral toral ideal of the pinned Lie
algebra action, with the original exterior lattice, basis and fundamental-weight coordinates. -/
theorem definingIdeal_eq_pinned :
    definingIdeal n hn = kostantToralDefiningIdeal
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h
      (pinnedRep n hn) (lattice n).toAddSubgroup
      (pinnedRep_kostantForm_mem_lattice n hn)
      (isNilpotent_pinnedRep_rootGenerator n hn) (latticeBasis n) (basisWeight n) := by
  rw [definingIdeal_def]
  symm
  exact kostantToralDefiningIdeal_eq_of_operator_eq
    _ _ _ _ _ _ _ _ _ _ _ _ _ (pinnedRep_ι_rootGenerator n hn)

/-- The integral represented spin group scheme is the toral closure of the pinned spin action,
not merely a group with isomorphic field-valued points. -/
theorem groupScheme_eq_pinned :
    groupScheme n hn = kostantToralGroupScheme
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h
      (pinnedRep n hn) (lattice n).toAddSubgroup
      (pinnedRep_kostantForm_mem_lattice n hn)
      (isNilpotent_pinnedRep_rootGenerator n hn) (latticeBasis n) (basisWeight n) := by
  rw [groupScheme_def, definingIdeal_eq_pinned]

/-- The two constructions give the very same matrix subgroup over every commutative ring,
including rings with nilpotents and rings of characteristic two. -/
theorem points_eq_pinned (A : Type*) [CommRing A] :
    points n hn A = kostantToralPointsSubgroup
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h
      (pinnedRep n hn) (lattice n).toAddSubgroup
      (pinnedRep_kostantForm_mem_lattice n hn)
      (isNilpotent_pinnedRep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A := by
  -- The pinned signed-generator family uses the definitionally equal rank of D n.
  erw [kostantToralPointsSubgroup_def, ← definingIdeal_eq_pinned, points_def]

/-- Both signed simple-root morphisms into the ambient general linear scheme are the
exponentials of the pinned spin operators, with no change of parameter or basis. -/
theorem rootSubgroup_comp_carrierι_eq_pinned (i : Fin n ⊕ Fin n) :
    rootSubgroup n hn i ≫ carrierι n hn = kostantRootSubgroup
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h
      (pinnedRep n hn) (lattice n).toAddSubgroup
      (pinnedRep_kostantForm_mem_lattice n hn) i
      (isNilpotent_pinnedRep_rootGenerator n hn i) (latticeBasis n) := by
  -- Unfold the equal rank index types when comparing the two signed-root presentations.
  erw [rootSubgroup_comp_carrierι, kostantRootSubgroup_def, kostantRootSubgroup_def]
  congr 3
  apply congrArg Quiver.Hom.op
  exact kostantRootSubgroupCoordinateMap_eq_of_operator_eq
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pinnedRep_ι_rootGenerator n hn i).symm

/-- The matrix of each native signed root point is the pinned divided-power exponential over
any commutative value ring, with its original additive parameter. -/
theorem coe_rootSubgroupPoints_eq_pinned (i : Fin n ⊕ Fin n)
    (A : Type*) [CommRing A] (u : Multiplicative A) :
    (rootSubgroupPoints n hn i A u : Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      kostantRootSubgroupMatrix
        ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).rootGenerator
        ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h
        (pinnedRep n hn) (lattice n).toAddSubgroup
        (pinnedRep_kostantForm_mem_lattice n hn) i
        (isNilpotent_pinnedRep_rootGenerator n hn i) (latticeBasis n)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
  rw [coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pinnedRep_ι_rootGenerator n hn i).symm _

end

end TauCeti.TypeDSpinCarrier
