/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal

/-!
# The centralizer of the diagonal torus in the general linear group

Over every commutative ring `R`, the scheme-theoretic centralizer of the diagonal torus `T` of
`GL_n` is `T` itself. In Hopf coordinates, the centralizer ideal
`BialgHom.centralizerHopfIdeal` of the diagonal-torus coordinate morphism is the diagonal-torus
defining ideal.

The statement is about the closed subgroup scheme, not only about its points over a field. It
holds over every base ring, including `𝔽₂`, where the group of rational diagonal matrices is
trivial and its centralizer in `GL_n(𝔽₂)` is everything.

The generic quotient of the normalizer of a diagonalizable subgroup by its centralizer, in
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Quotient`, is therefore the
quotient of the normalizer of the diagonal torus of `GL_n` by the torus itself.

## Main declaration

* `TauCeti.GeneralLinear.centralizerHopfIdeal_diagonalTorusCoordinateMap`: **the centralizer of
  the diagonal torus of `GL_n` is the diagonal torus.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §16.1.
* SGA 3, Exposé XI, on centralizers of diagonalizable subgroups.
-/

public section

open TensorProduct WithConv

namespace TauCeti.GeneralLinear

universe u w

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A point of `GL_n` killing the centralizer ideal of the diagonal torus is a diagonal matrix,
over every base ring and every value algebra. The public form of this statement is
`centralizerHopfIdeal_diagonalTorusCoordinateMap`. -/
private theorem isDiag_pointsMulEquiv_of_centralizerHopfIdeal_le_ker
    {A : Type w} [CommRing A] [Algebra R A]
    {g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)}
    (hg : (BialgHom.centralizerHopfIdeal
        (diagonalTorusCoordinateMap (R := R) (N := n)).hom).toIdeal ≤ RingHom.ker g.ofConv) :
    ((pointsMulEquiv n g : Matrix.GeneralLinearGroup (Fin n) A) :
      Matrix (Fin n) (Fin n) A).IsDiag := by
  -- Such a point commutes with the universal point of the diagonal torus over the extension
  -- `A ⊗[R] R[ℤⁿ]` of its value algebra. The diagonal entries of that universal point are
  -- distinct basis elements of the Laurent coordinate ring, so comparing coefficients at the
  -- coordinate characters forces every off-diagonal entry to vanish.
  intro i j hij
  let X := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)
  let B := A ⊗[R] MonoidAlgebra R X
  let e : Fin n → X := fun a ↦ Multiplicative.ofAdd (Finsupp.single (ULift.up a) 1)
  let u : WithConv (MonoidAlgebra R X →ₐ[R] B) := toConv Algebra.TensorProduct.includeRight
  have hcomm := (BialgHom.centralizerHopfIdeal_le_ker_iff_commute_of_injective
    (diagonalTorusCoordinateMap (R := R) (N := n)).hom g (AlgHom.id R B)
    Function.injective_id).mp hg
  rw [AlgHom.id_comp, AlgHom.id_comp] at hcomm
  -- The universal diagonal-torus point is the diagonal matrix of the coordinate characters.
  have hD : ((pointsMulEquiv n (BialgHom.mapDomain
        (diagonalTorusCoordinateMap (R := R) (N := n)).hom u) :
        Matrix.GeneralLinearGroup (Fin n) B) : Matrix (Fin n) (Fin n) B) =
      Matrix.diagonal fun a ↦ (1 : A) ⊗ₜ[R] MonoidAlgebra.single (e a) (1 : R) := by
    ext a b
    rw [pointsMulEquiv_apply, pointToGeneralLinear_apply, BialgHom.mapDomain_apply,
      ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom, diagonalTorusCoordinateMap_X,
      Matrix.diagonal_apply]
    split_ifs
    · exact Algebra.TensorProduct.includeRight_apply _
    · simp
  -- The point itself, viewed over `B`, has entries `m ⊗ 1`.
  have hM : ((pointsMulEquiv n (AlgHom.mapValue
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] B) g) :
        Matrix.GeneralLinearGroup (Fin n) B) : Matrix (Fin n) (Fin n) B) i j =
      (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) i j ⊗ₜ[R] (1 : MonoidAlgebra R X) := by
    rw [pointsMulEquiv_mapValue]
    simp only [Matrix.GeneralLinearGroup.map_apply, AlgHom.coe_toRingHom]
    exact Algebra.TensorProduct.includeLeft_apply _
  have hentry := congrArg (fun h ↦ ((pointsMulEquiv n h : Matrix.GeneralLinearGroup (Fin n) B) :
    Matrix (Fin n) (Fin n) B) i j) hcomm.eq
  simp only [map_mul, Units.val_mul] at hentry
  rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, hM, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul, mul_one] at hentry
  -- Read off the coefficient at the `i`-th coordinate character.
  have hcoeff := congrArg
    (LinearMap.tensorComponent (R := R) (M := A) (Comodule.monoidCoeff R X (e i))) hentry
  have he : e j ≠ e i := fun h ↦ hij
    (ULift.up_injective (Finsupp.single_left_injective one_ne_zero
      (Multiplicative.ofAdd.injective h))).symm
  simpa [MonoidAlgebra.coeff_single, he] using hcoeff.symm

/-- **The centralizer of the diagonal torus of `GL_n` is the diagonal torus**, as closed subgroup
schemes over an arbitrary commutative ring. In coordinates, the centralizer ideal of the
diagonal-torus coordinate morphism equals the diagonal-torus defining ideal. -/
theorem centralizerHopfIdeal_diagonalTorusCoordinateMap :
    BialgHom.centralizerHopfIdeal (diagonalTorusCoordinateMap (R := R) (N := n)).hom =
      diagonalTorusDefiningIdeal R n := by
  -- The centralizer contains the torus; conversely, the quotient by the centralizer ideal is a
  -- diagonal point, so it kills the diagonal-torus ideal.
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rw [diagonalTorusDefiningIdeal_eq_ker]
    exact BialgHom.centralizerHopfIdeal_le_kerOfSurjective _
      (diagonalTorusCoordinateMap_surjective R n)
  let C := BialgHom.centralizerHopfIdeal (diagonalTorusCoordinateMap (R := R) (N := n)).hom
  -- The quotient map by the centralizer ideal is a point killing that ideal, hence diagonal.
  let g : WithConv (coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n ⧸ C.toIdeal) :=
    toConv (Ideal.Quotient.mkₐ R C.toIdeal)
  have hg : C.toIdeal ≤ RingHom.ker g.ofConv := fun y hy ↦ by
    rw [RingHom.mem_ker, ofConv_toConv, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hy
  let A := coordinateHopfAlgebra R n ⧸ C.toIdeal
  have hmem : g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R n)
      (diagonalTorusDefiningIdeal R n) (CommAlgCat.of R A) :=
    (mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff R n A g).mpr
      (isDiag_pointsMulEquiv_of_centralizerHopfIdeal_le_ker (A := A) hg)
  have hx0 :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ (CommAlgCat.of R A) g).mp hmem x hx
  rw [ofConv_toConv, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hx0
  exact HopfIdeal.mem_toIdeal.mp hx0

end TauCeti.GeneralLinear
