/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterKernel
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Reductive
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Commutative
import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Radical
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Solvable reductive groups are tori

A reductive group with solvable geometric points is a torus, over every field and in every
characteristic. The torus need not split over the ground field.

Pass to the geometric fibre `G` over an algebraic closure. It is smooth and connected, and it is
commutative by `TauCeti.reductiveCommHopfAlgProperty.isCocomm_of_geometricallySolvable`. For a
reduced connected commutative group, the unipotent radical is the closed unipotent Jordan factor,
whose rational points are exactly the unipotent points
(`TauCeti.HopfAlgebra.Point.mem_quotientPointsSubgroup_unipotentRadical_iff`). Reductivity makes
this radical trivial, so the unipotent part of every rational point of `G` is the identity: every
point is semisimple. The diagonalization criterion
`TauCeti.torusCommHopfAlgProperty_of_isSemisimplePoint` then identifies `G` as a split torus.

Consequently such a group is linearly reductive, and the common kernel of characters of its
geometric fibre is trivial.

## Main declarations

* `TauCeti.reductiveCommHopfAlgProperty.torus_of_geometricallySolvable`: a solvable reductive
  group is a torus.
* `TauCeti.reductiveCommHopfAlgProperty.linearlyReductive_of_geometricallySolvable`: a solvable
  reductive group is linearly reductive.
* `TauCeti.reductiveCommHopfAlgProperty.characterKernelIdeal_baseChange_eq_augmentation`: the
  characters of the geometric fibre of a solvable reductive group separate its points
  scheme-theoretically.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§4.7, 10.6 and 11.5.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.13 and Chapter 19.
-/

public section

open WithConv

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Every point of the geometric fibre of a solvable reductive group is semisimple, in every
characteristic. Semisimplicity is tested on all finite-dimensional representations of that
fibre. -/
private theorem isSemisimplePoint_geometricFiber_of_geometricallySolvable
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj)
    (g : WithConv
      ((FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) →ₐ[AlgebraicClosure k]
        AlgebraicClosure k)) :
    HopfAlgebra.IsSemisimplePoint g := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  have hG := hH.algebraicClosureBaseChange
  let _ : Algebra.Smooth K G := hG.smooth
  let _ : IsReduced G := isReduced_of_smooth K G
  let _ : _root_.Coalgebra.IsCocomm k H := hH.isCocomm_of_geometricallySolvable hsolv
  let _ : _root_.Coalgebra.IsCocomm K G := inferInstance
  rw [HopfAlgebra.isSemisimplePoint_iff_unipotentPart_eq_one]
  let v := HopfAlgebra.Point.unipotentPart K G K g
  have hv : HopfAlgebra.IsUnipotentPoint v := by
    rw [HopfAlgebra.isUnipotentPoint_def]
    exact fun M ↦ HopfAlgebra.Point.isUnipotent_pointsAction_unipotentPart K G K g M
  -- The unipotent radical of the commutative fibre consists of its unipotent points, and
  -- reductivity makes it the identity subgroup.
  rw [← HopfAlgebra.Point.mem_quotientPointsSubgroup_unipotentRadical_iff K G
    hG.geometricallyConnected, hG.unipotentRadicalDefiningIdeal_eq_augmentation] at hv
  exact CommHopfAlgCat.eq_one_of_mem_quotientPointsSubgroup_augmentation _ _ hv

/-- **A reductive group with solvable geometric points is a torus**, over every field and in
every characteristic. The torus need not split over the ground field. -/
theorem torus_of_geometricallySolvable
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj) :
    torusCommHopfAlgProperty k H := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  have hG := hH.algebraicClosureBaseChange
  let _ : Algebra.Smooth K G := hG.smooth
  let _ : IsReduced G := isReduced_of_smooth K G
  let _ : ConnectedSpace (PrimeSpectrum G) :=
    hH.geometricallyConnected.connectedSpace_algebraicClosureBaseChange
  let _ : _root_.Coalgebra.IsCocomm k H := hH.isCocomm_of_geometricallySolvable hsolv
  let _ : _root_.Coalgebra.IsCocomm K G := inferInstance
  have hT : torusCommHopfAlgProperty K G :=
    torusCommHopfAlgProperty_of_isSemisimplePoint G
      (hH.isSemisimplePoint_geometricFiber_of_geometricallySolvable hsolv)
  exact (torusCommHopfAlgProperty_iff k H).mpr
    ((splitTorusCommHopfAlgProperty_iff K G).mp (hT.split K G))

/-- A reductive group with solvable geometric points is linearly reductive, in every
characteristic and including when its torus does not split over the ground field. -/
theorem linearlyReductive_of_geometricallySolvable
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj) :
    linearlyReductiveCommHopfAlgProperty k H.obj :=
  (hH.torus_of_geometricallySolvable hsolv).linearlyReductive

/-- The common kernel of characters of the geometric fibre of a solvable reductive group is the
identity subgroup, scheme-theoretically and in every characteristic. -/
theorem characterKernelIdeal_baseChange_eq_augmentation
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj) :
    let G := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
    _root_.CommHopfAlgCat.characterKernelIdeal G.obj =
      HopfIdeal.augmentation (AlgebraicClosure k) G := by
  intro G
  let K := AlgebraicClosure k
  have hsplit : splitTorusCommHopfAlgProperty K G :=
    (splitTorusCommHopfAlgProperty_iff K G).mpr
      ((torusCommHopfAlgProperty_iff k H).mp (hH.torus_of_geometricallySolvable hsolv))
  -- The split fibre is spanned by its characters, so evaluation of characters is surjective.
  have hspan := (DiagonalizableGroup.groupLikeSpannedProperty_iff K G).mp
    (hsplit.groupLikeSpanned K G)
  rw [_root_.CommHopfAlgCat.characterKernelIdeal_def]
  exact CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective _
    ((GroupLike.liftGroupLikeBialgHom_surjective_iff_groupLikeSetSpan_eq_top K G).mpr hspan)

end TauCeti.reductiveCommHopfAlgProperty
