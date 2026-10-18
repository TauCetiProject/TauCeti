/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Solvable.CharacterKernel
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Reductive
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Commutative
import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Connected

/-!
# Solvable reductive groups in characteristic zero are tori

The common kernel of characters of the geometric fibre of a solvable reductive group is
trivial in characteristic zero. Indeed, Lie--Kolchin makes this normal subgroup unipotent,
Cartier's theorem makes it smooth, and characteristic-zero unipotent groups are connected.
Reductivity therefore eliminates it. Every unipotent point lies in this kernel, so every point
of the geometric fibre is semisimple.

The commutativity theorem for solvable reductive groups and the diagonalization criterion
`TauCeti.torusCommHopfAlgProperty_of_isSemisimplePoint` then identify the group as a torus,
so it is linearly reductive. This applies to non-split groups over arbitrary characteristic-zero
fields. The character kernel and its unipotence theorem are those of
`CommHopfAlgCat.characterKernelIdeal` and
`TauCeti.CommHopfAlgCat.geometricallyUnipotentPointsCommHopfAlgProperty_characterKernelIdeal`.

## References

* A. Borel, *Linear Algebraic Groups*, §§10--11.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 14 and 19.
-/

public section

open WithConv

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- In characteristic zero, the common kernel of characters of the geometric fibre of a
solvable reductive group is the identity subgroup, scheme-theoretically. -/
theorem characterKernelIdeal_baseChange_eq_augmentation
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj) :
    let G := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
    _root_.CommHopfAlgCat.characterKernelIdeal G.obj =
      HopfIdeal.augmentation (AlgebraicClosure k) G := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let I := _root_.CommHopfAlgCat.characterKernelIdeal G.obj
  let Q := FiniteTypeCommHopfAlgCat.quotient G I
  let _ : IsReduced G := HopfAlgebra.isReduced_of_charZero K G
  let _ : ConnectedSpace (PrimeSpectrum G) :=
    hH.geometricallyConnected.connectedSpace_algebraicClosureBaseChange
  let _ : Group.IsSolvable (WithConv (H →ₐ[k] K)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff k H.obj).mp hsolv
  let e := (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := K)).symm
  let _ : Group.IsSolvable (WithConv (G →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hU : smoothUnipotentCommHopfAlgProperty K Q := by
    rw [smoothUnipotentCommHopfAlgProperty_iff]
    exact ⟨(smoothCommHopfAlgProperty_iff Q.obj).mp
      (smoothCommHopfAlgProperty_of_charZero K Q.obj),
      (geometricallyUnipotentPointsCommHopfAlgProperty_iff K Q.obj).mp
        (CommHopfAlgCat.geometricallyUnipotentPointsCommHopfAlgProperty_characterKernelIdeal
          (k := K) (H := G))⟩
  exact hH.eq_augmentation I (_root_.CommHopfAlgCat.isNormal_characterKernelIdeal G.obj)
    hU.geometricallyConnected hU

/-- Every point of the geometric fibre of a solvable reductive group in characteristic zero is
semisimple. Semisimplicity is tested on all finite-dimensional representations of that fibre. -/
private theorem isSemisimplePoint_geometricFiber_of_geometricallySolvable
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj)
    (g : WithConv
      ((FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) →ₐ[AlgebraicClosure k]
        AlgebraicClosure k)) :
    HopfAlgebra.IsSemisimplePoint g := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  rw [HopfAlgebra.isSemisimplePoint_iff_unipotentPart_eq_one]
  let v := HopfAlgebra.Point.unipotentPart K G K g
  have hv : HopfAlgebra.IsUnipotentPoint v := by
    rw [HopfAlgebra.isUnipotentPoint_def]
    exact fun M ↦ HopfAlgebra.Point.isUnipotent_pointsAction_unipotentPart K G K g M
  have hker := (_root_.CommHopfAlgCat.characterKernelIdeal_toIdeal_le_ker_iff
    G.obj v.ofConv).mpr hv.apply_groupLike_eq_one
  rw [hH.characterKernelIdeal_baseChange_eq_augmentation hsolv] at hker
  apply ofConv_injective
  apply AlgHom.ext
  intro x
  exact AlgHom.apply_eq_counit_of_augmentation_le_ker v.ofConv hker x

/-- A reductive group with solvable geometric points over a characteristic-zero field is a
torus. The torus need not split over the ground field. -/
theorem torus_of_geometricallySolvable
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj) :
    torusCommHopfAlgProperty k H := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let _ : IsReduced G := HopfAlgebra.isReduced_of_charZero K G
  let _ : ConnectedSpace (PrimeSpectrum G) :=
    hH.geometricallyConnected.connectedSpace_algebraicClosureBaseChange
  let _ : _root_.Coalgebra.IsCocomm k H := hH.isCocomm_of_geometricallySolvable hsolv
  let _ : _root_.Coalgebra.IsCocomm K G := inferInstance
  have hT : torusCommHopfAlgProperty K G :=
    torusCommHopfAlgProperty_of_isSemisimplePoint G
      (hH.isSemisimplePoint_geometricFiber_of_geometricallySolvable hsolv)
  exact (torusCommHopfAlgProperty_iff k H).mpr
    ((splitTorusCommHopfAlgProperty_iff K G).mp (hT.split K G))

/-- A reductive group with solvable geometric points is linearly reductive in characteristic
zero, including when its torus does not split over the ground field. -/
theorem linearlyReductive_of_geometricallySolvable
    (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj) :
    linearlyReductiveCommHopfAlgProperty k H.obj :=
  (hH.torus_of_geometricallySolvable hsolv).linearlyReductive

end TauCeti.reductiveCommHopfAlgProperty
