/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Geometric unipotence under base change

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field `k`. For every
field extension `K / k`, the scalar extension `K ⊗[k] H` is smooth unipotent if and only if `H` is
smooth unipotent.

In the forward direction, choose a faithful finite-dimensional `H`-comodule and extend it to `K`.
Its coordinate morphism remains surjective, hence the extended comodule is faithful. The universal
coefficient matrix of the extended comodule is obtained from the original one by scalar extension.
Its characteristic polynomial therefore remains a power of `X - 1`, and the faithful-representation
criterion detects unipotence of every geometric point of the base-changed group.

In the reverse direction, smoothness descends by faithfully flat descent for smooth algebras. For
each finite-dimensional `H`-comodule, the base-changed comodule over the smooth (hence reduced)
Hopf algebra `K ⊗[k] H` has universal coefficient matrix whose characteristic polynomial is a power
of `X - 1`. Since `H → K ⊗[k] H` is injective, the same characteristic-polynomial identity holds
over `k`, which makes every geometric point of `H` act unipotently on the comodule.

## Main declarations

* `TauCeti.smoothUnipotentCommHopfAlgProperty.baseChange`: smooth geometric unipotence is
  preserved by arbitrary field extension.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.of_baseChange`: smooth geometric unipotence
  descends along arbitrary field extension.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.baseChange_iff`: smooth geometric unipotence is
  invariant under arbitrary field extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 14.5.
* A. Borel, *Linear Algebraic Groups*, Section 15.4.
-/

public section

open CategoryTheory Module WithConv
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

open geometricallyUnipotentPointsCommHopfAlgProperty

namespace smoothUnipotentCommHopfAlgProperty

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Smooth geometric unipotence is preserved by arbitrary extension of the ground field. -/
theorem baseChange (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : smoothUnipotentCommHopfAlgProperty k H) :
    smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  have hH' := (smoothUnipotentCommHopfAlgProperty_iff k H).mp hH
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨@Algebra.Smooth.baseChange k _ H K _ _ _ _ hH'.1, ?_⟩
  obtain ⟨M, d, b, hb⟩ := Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom
    (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Free k M := Module.Free.of_basis b
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hM : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).2 hb
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  let bK := b.baseChange K
  let _ : Module.Free K (K ⊗[k] M) := Module.Free.of_basis bK
  let _ : Module.Finite K (K ⊗[k] M) := Module.Finite.of_basis bK
  let MK : FGComoduleCat.{u, u, u} K (K ⊗[k] H) :=
    FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M)
  let _ : Algebra.Smooth k H := hH'.1
  let _ : IsReduced H := isReduced_of_smooth k H
  have hgeom : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj := by
    rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
    exact hH'.2
  have hC : (Comodule.coefficientMatrix (C := H) b).charpoly =
      ((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map
        (algebraMap k H) := by
    simpa only using
      (geometricallyUnipotentPointsCommHopfAlgProperty.coefficientMatrix_charpoly_eq
        hgeom (FGComoduleCat.of (R := k) (C := H) M) b)
  have hCK : (Comodule.coefficientMatrix (C := K ⊗[k] H) bK).charpoly =
      ((Polynomial.X - (1 : Polynomial K)) ^ Module.finrank K (K ⊗[k] M)).map
        (algebraMap K (K ⊗[k] H)) := by
    rw [Comodule.coefficientMatrix_baseChange]
    let f : H →+* K ⊗[k] H :=
      (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H).toRingHom
    have hmatrix : (Comodule.coefficientMatrix (C := H) b).map
          ((TensorProduct.mk k K H) 1) =
        (Comodule.coefficientMatrix (C := H) b).map f := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply]
      rw [TensorProduct.mk_apply]
      exact (Algebra.TensorProduct.includeRight_apply _).symm
    rw [hmatrix, Matrix.charpoly_map, hC]
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Module.finrank_baseChange]
  intro g
  apply (HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    MK (Comodule.IsFaithful.baseChange (K := K) hM) g).2
  exact Comodule.isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq g bK hCK

/-- Smooth geometric unipotence descends along an arbitrary extension of the ground field. -/
theorem of_baseChange (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    smoothUnipotentCommHopfAlgProperty k H := by
  have hH' := (smoothUnipotentCommHopfAlgProperty_iff K _).mp hH
  let _ : Algebra.Smooth K (K ⊗[k] H.obj) := hH'.1
  let _ : IsReduced (K ⊗[k] H.obj) := isReduced_of_smooth K (K ⊗[k] H.obj)
  have hsmooth : Algebra.Smooth k H :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj) K
  have hgeomK : geometricallyUnipotentPointsCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H).obj := by
    rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
    exact hH'.2
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨hsmooth, fun g ↦ (HopfAlgebra.isUnipotentPoint_def g).mpr fun M ↦ ?_⟩
  let b := Module.finBasis k M
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  let bK := b.baseChange K
  let MK : FGComoduleCat.{u, u, u} K (K ⊗[k] H.obj) :=
    FGComoduleCat.of (R := K) (C := K ⊗[k] H.obj) (K ⊗[k] M)
  have hCK : (Comodule.coefficientMatrix (C := K ⊗[k] H.obj) bK).charpoly =
      ((Polynomial.X - (1 : Polynomial K)) ^ Module.finrank K (K ⊗[k] M)).map
        (algebraMap K (K ⊗[k] H.obj)) := by
    simpa only using
      (geometricallyUnipotentPointsCommHopfAlgProperty.coefficientMatrix_charpoly_eq
        hgeomK MK bK)
  let f : H.obj →+* K ⊗[k] H.obj :=
    (Algebra.TensorProduct.includeRight : H.obj →ₐ[k] K ⊗[k] H.obj).toRingHom
  have hC : (Comodule.coefficientMatrix (C := H.obj) b).charpoly =
      ((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map (algebraMap k H.obj) := by
    apply Polynomial.map_injective f
      (Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective)
    have hmatrix : (Comodule.coefficientMatrix (C := H.obj) b).map
          ((TensorProduct.mk k K H.obj) 1) =
        (Comodule.coefficientMatrix (C := H.obj) b).map f := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, TensorProduct.mk_apply]
      exact (Algebra.TensorProduct.includeRight_apply _).symm
    rw [← Matrix.charpoly_map, ← hmatrix, ← Comodule.coefficientMatrix_baseChange, hCK]
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Module.finrank_baseChange]
  exact Comodule.isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq g b hC

/-- Smooth geometric unipotence is invariant under arbitrary extension of the ground field. -/
theorem baseChange_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      smoothUnipotentCommHopfAlgProperty k H :=
  ⟨of_baseChange H, baseChange H⟩

end smoothUnipotentCommHopfAlgProperty

end

end TauCeti
