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

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field `k`, and let
`K / k` be an arbitrary field extension. Smooth geometric unipotence of `H` is both preserved and
reflected by passing to the scalar extension `K ⊗[k] H`.

Choose a faithful finite-dimensional `H`-comodule and extend it to `K`. Its coordinate morphism
remains surjective, hence the extended comodule is faithful, while smoothness is preserved by base
change and reflected by faithfully flat scalar extension. The universal coefficient matrix of the
extended comodule is obtained from the original one along the injective inclusion
`H → K ⊗[k] H`. Its characteristic polynomial is therefore a power of `X - 1` over `K ⊗[k] H`
if and only if the original characteristic polynomial is a power of `X - 1` over `H`, and the
faithful-representation criterion detects unipotence of geometric points on both sides.

## Main declarations

* `TauCeti.smoothUnipotentCommHopfAlgProperty.baseChange`: smooth geometric unipotence is
  preserved by arbitrary field extension.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.of_baseChange`: smooth geometric unipotence is
  reflected by arbitrary field extension.
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

/-- Along a field extension `K / k`, the universal coefficient matrix of a scalar-extended
finite-dimensional comodule has unipotent characteristic polynomial `(X - 1) ^ d` if and only if
the original universal coefficient matrix does. -/
private theorem coefficientMatrix_baseChange_charpoly_eq_iff
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
    {d : Type*} [Fintype d] [DecidableEq d] (b : Module.Basis d k M) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
    (Comodule.coefficientMatrix (C := K ⊗[k] H) (b.baseChange K)).charpoly =
        ((Polynomial.X - (1 : Polynomial K)) ^ Module.finrank K (K ⊗[k] M)).map
          (algebraMap K (K ⊗[k] H)) ↔
      (Comodule.coefficientMatrix (C := H) b).charpoly =
        ((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map (algebraMap k H) := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  let f : H →+* K ⊗[k] H :=
    (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H).toRingHom
  have hmatrix : Comodule.coefficientMatrix (C := K ⊗[k] H) (b.baseChange K) =
      (Comodule.coefficientMatrix (C := H) b).map f := by
    rw [Comodule.coefficientMatrix_baseChange]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, TensorProduct.mk_apply]
    exact (Algebra.TensorProduct.includeRight_apply _).symm
  rw [← (Polynomial.map_injective f
    (Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective)).eq_iff,
    hmatrix, Matrix.charpoly_map]
  have hrhs :
      (((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map (algebraMap k H)).map f =
        ((Polynomial.X - (1 : Polynomial K)) ^ Module.finrank K (K ⊗[k] M)).map
          (algebraMap K (K ⊗[k] H)) := by
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Module.finrank_baseChange]
  rw [hrhs]

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
  let _ : Algebra.Smooth k H := hH'.1
  let _ : IsReduced H := isReduced_of_smooth k H
  have hCK : (Comodule.coefficientMatrix (C := K ⊗[k] H) bK).charpoly =
      ((Polynomial.X - (1 : Polynomial K)) ^ Module.finrank K (K ⊗[k] M)).map
        (algebraMap K (K ⊗[k] H)) := by
    rw [coefficientMatrix_baseChange_charpoly_eq_iff (K := K) b]
    simpa only using
      (geometricallyUnipotentPointsCommHopfAlgProperty.coefficientMatrix_charpoly_eq
        ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k H.obj).mpr hH'.2)
        (FGComoduleCat.of (R := k) (C := H) M) b)
  intro g
  apply (HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M))
    (Comodule.IsFaithful.baseChange (K := K) hM) g).2
  exact Comodule.isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq g bK hCK

/-- Smooth geometric unipotence is reflected by arbitrary extension of the ground field. -/
theorem of_baseChange (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    smoothUnipotentCommHopfAlgProperty k H := by
  have hH' := (smoothUnipotentCommHopfAlgProperty_iff K
    (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)).mp hH
  let _ : Algebra.Smooth K (K ⊗[k] H.obj) := by
    simpa only [FiniteTypeCommHopfAlgCat.baseChange, CommHopfAlgCat.baseChange,
      _root_.CommHopfAlgCat.coe_of] using hH'.1
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj) K, ?_⟩
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
  let _ : IsReduced (K ⊗[k] H.obj) := isReduced_of_smooth K (K ⊗[k] H.obj)
  have hC : (Comodule.coefficientMatrix (C := H) b).charpoly =
      ((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map (algebraMap k H) := by
    rw [← coefficientMatrix_baseChange_charpoly_eq_iff (K := K) b]
    simpa only using
      (geometricallyUnipotentPointsCommHopfAlgProperty.coefficientMatrix_charpoly_eq
        ((geometricallyUnipotentPointsCommHopfAlgProperty_iff K _).mpr hH'.2)
        (FGComoduleCat.of (R := K) (C := K ⊗[k] H.obj) (K ⊗[k] M)) bK)
  intro g
  apply (HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    (FGComoduleCat.of (R := k) (C := H) M) hM g).2
  exact Comodule.isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq g b hC

-- The defining simp lemma `smoothUnipotentCommHopfAlgProperty_iff` already simplifies the left-hand
-- side, so adding `baseChange_iff` to the simp set would violate `simpNF`.
/-- Smooth geometric unipotence of a finite-type affine group is invariant under arbitrary
extension of the ground field. -/
theorem baseChange_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      smoothUnipotentCommHopfAlgProperty k H :=
  ⟨of_baseChange H, baseChange H⟩

end smoothUnipotentCommHopfAlgProperty

end

end TauCeti
