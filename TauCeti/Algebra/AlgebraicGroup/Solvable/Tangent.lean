/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Lie
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Tangent
import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Lie algebras of solvable affine groups

A geometrically reduced, geometrically connected finite-type affine group with solvable
geometric points has solvable Lie algebra, in every characteristic. Over an algebraically
closed field, Lie--Kolchin embeds the group into an upper triangular general linear group.
The differential is injective and the upper triangular tangent Lie algebra is solvable.
Scalar extension and faithful-flat descent of Lie solvability give the general field case.

In characteristic zero this completes the equivalence between geometric solvability of a
geometrically connected group and solvability of its Lie algebra. The reverse implication
is `geometricallySolvablePointsCommHopfAlgProperty.of_geometricallyConnected_of_isSolvable_lie`.
This comparison is used when relating solvable group radicals to Lie-algebra radicals.

Reducedness is essential in positive characteristic: geometric points alone do not detect
infinitesimal groups. Connectedness is essential for the characteristic-zero converse,
since a finite group has zero Lie algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 16.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

/-- Over an algebraically closed field, a reduced connected affine group of finite type with
solvable rational points has solvable Lie algebra, in every characteristic. -/
theorem isSolvable_lieAlgebra_of_isSolvable_points
    {k : Type u} [Field k] [IsAlgClosed k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    [Group.IsSolvable (WithConv (H →ₐ[k] k))] :
    LieAlgebra.IsSolvable (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  obtain ⟨n, f, hf⟩ := exists_upperTriangular_surjective_of_weight_vectors
    (k := k) (H := H) fun _ _ _ _ _ _ ↦
      Comodule.hasNonzeroWeightVector_of_isSolvable (k := k) (H := H)
  exact Function.Injective.lieAlgebra_isSolvable (R := k)
    (f := derivationCompLieHom (B := k) f.hom)
    (derivationCompLieHom_injective_of_surjective (B := k) f.hom hf)

/-- The Lie algebra of a geometrically reduced and geometrically connected solvable affine
group of finite type is solvable, over every field. -/
theorem geometricallySolvablePointsCommHopfAlgProperty.isSolvable_lieAlgebra
    {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [Algebra.IsGeometricallyReduced k H]
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    LieAlgebra.IsSolvable (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let K := AlgebraicClosure k
  let HK := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let _ : ConnectedSpace (PrimeSpectrum HK) := hconn.connectedSpace_algebraicClosureBaseChange
  let _ : IsReduced HK := inferInstance
  let _ : Group.IsSolvable (WithConv (H →ₐ[k] K)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff k H.obj).mp hsolv
  let e := (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := K)).symm
  let _ : Group.IsSolvable (WithConv (HK →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hHK := isSolvable_lieAlgebra_of_isSolvable_points (H := HK)
  let eLie := Derivation.tangentScalarExtensionLieEquiv.trans
    (tangentBaseChangeLieEquiv (R := k) (K := K) (H := H))
  have htensor := (LieAlgebra.solvable_iff_equiv_solvable eLie).mpr hHK
  have hdual := (LieAlgebra.isSolvable_tensorProduct_iff
    (R := k) (A := K) (L := Module.Dual k (Bialgebra.CotangentSpace k H))).mp htensor
  exact (LieAlgebra.solvable_iff_equiv_solvable Derivation.cotangentDualLieEquiv).mp hdual

/-- A geometrically connected finite-type affine group in characteristic zero is geometrically
solvable exactly when its Lie algebra is solvable. Smoothness follows from Cartier's theorem. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_iff_isSolvable_lieAlgebra
    {k : Type u} [Field k] [CharZero k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hconn : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    geometricallySolvablePointsCommHopfAlgProperty k H.obj ↔
      LieAlgebra.IsSolvable (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let _ : Algebra.Smooth k H :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H.obj)
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  constructor
  · exact fun hsolv ↦ hsolv.isSolvable_lieAlgebra hconn
  · intro hlie
    let _ := hlie
    exact geometricallySolvablePointsCommHopfAlgProperty.of_geometricallyConnected_of_isSolvable_lie
      hconn

end

end TauCeti
