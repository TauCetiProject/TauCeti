/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.LinearAlgebra.Matrix.Charpoly.Laurent

/-!
# Unipotence of the dynamic unipotent subgroup

For a cocharacter `l : 𝔾ₘ → G`, the dynamic subgroup `U(l)` consists of the points whose
conjugates by `l(t)` extend to `t = 0` with limit one. This file proves that these points are
unipotent in the representation-theoretic sense: they act unipotently in every finite-dimensional
comodule.

The proof applies a representation to the extending polynomial family. Over the Laurent
polynomials the family is conjugate to the original action, so its characteristic polynomial is
constant. At the origin the family is the identity, hence that constant is `(X - 1) ^ n`.

## Main declarations

* `TauCeti.Cocharacter.isUnipotentPoint_of_mem_unipotent`: every point of the dynamic unipotent
  subgroup is a unipotent point.
* `TauCeti.Cocharacter.isUnipotentPoint_quotient_of_le_unipotent`: every point of a Hopf-ideal
  quotient whose cut-out subgroup lies in a dynamic unipotent subgroup is unipotent.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.

This proves the pointwise unipotence assertion implicit in the dynamic route to parabolic and Levi
subgroups, using the representation-theoretic definition of unipotence.
-/

public section

open Module Polynomial WithConv
open scoped TensorProduct

namespace TauCeti.Cocharacter

universe u v w

noncomputable section

variable {R : Type u} {H : Type v} {A : Type w}
variable [Field R] [Semiring H] [_root_.HopfAlgebra R H]
variable [CommRing A] [Algebra R A]

private theorem charpoly_conjugate {B : Type w} [CommRing B] [Algebra R B]
    (M : FGComoduleCat.{u, v, u} R H) (x y : WithConv (H →ₐ[R] B)) :
    (Comodule.endOfPoint M (x * y * x⁻¹).ofConv).charpoly =
      (Comodule.endOfPoint M y.ofConv).charpoly := by
  have hEnd : Comodule.endOfPoint M (x * y * x⁻¹).ofConv =
      (Comodule.pointsAction M x).conj (Comodule.endOfPoint M y.ofConv) := by
    rw [← Comodule.pointsAction_toLinearMap M]
    ext z
    simp [LinearEquiv.conj_apply, Comodule.pointsAction_toLinearMap]
  rw [hEnd, LinearEquiv.charpoly_conj]

/-- Over the Laurent polynomials, the coefficient matrix of the extension of the conjugate of `g`
has the same characteristic polynomial as that of the constant matrix of `g`. -/
private theorem charpoly_map_toLaurent_extend_coefficientMatrix
    (l : H →ₐc[R] LaurentPolynomial R) {g : WithConv (H →ₐ[R] A)} (hgP : g ∈ parabolic A l)
    (M : FGComoduleCat.{u, v, u} R H) :
    let b := Module.Free.chooseBasis R M
    let C := Comodule.coefficientMatrix (C := H) b
    ((C.map (extend A l ⟨g, hgP⟩).ofConv).map Polynomial.toLaurent).charpoly =
      ((C.map g.ofConv).map LaurentPolynomial.C).charpoly := by
  intro b C
  let f := IsScalarTower.toAlgHom R A (LaurentPolynomial A)
  have hf : (f : A →+* LaurentPolynomial A) = LaurentPolynomial.C := by
    apply RingHom.ext
    intro a
    exact (LaurentPolynomial.C_eq_algebraMap a).symm
  have hLaurentMatrix :
      (C.map (extend A l ⟨g, hgP⟩).ofConv).map Polynomial.toLaurent =
        C.map (conjugate A l g).ofConv := by
    calc
      _ = C.map (ofPolyPoint A (extend A l ⟨g, hgP⟩)).ofConv := by
        ext i j
        simp [C, ofPolyPoint_apply, Matrix.map_apply]
      _ = C.map (conjugate A l g).ofConv := by rw [ofPolyPoint_extend]
  calc
    _ = (C.map (conjugate A l g).ofConv).charpoly := congrArg Matrix.charpoly hLaurentMatrix
    _ = (Comodule.endOfPoint M (conjugate A l g).ofConv).charpoly := by
      rw [← Comodule.toMatrix_endOfPoint b, LinearMap.charpoly_toMatrix]
    _ = (Comodule.endOfPoint M (constPoint A g).ofConv).charpoly := by
      rw [conjugate_apply, charpoly_conjugate]
    _ = (Comodule.endOfPoint M (f.comp g.ofConv)).charpoly := by rw [constPoint_apply]
    _ = (Comodule.endOfPoint M g.ofConv).charpoly.map f :=
      Comodule.charpoly_endOfPoint_comp g.ofConv f
    _ = (C.map g.ofConv).charpoly.map LaurentPolynomial.C := by
      rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint M g.ofConv) (b.baseChange A),
        Comodule.toMatrix_endOfPoint, hf]
    _ = _ := by rw [Matrix.charpoly_map]

/-- Every point of the dynamic unipotent subgroup attached to a cocharacter is unipotent in
every finite-dimensional representation. -/
theorem isUnipotentPoint_of_mem_unipotent
    (l : H →ₐc[R] LaurentPolynomial R) {g : WithConv (H →ₐ[R] A)}
    (hg : g ∈ unipotent A l) : HopfAlgebra.IsUnipotentPoint g := by
  rw [HopfAlgebra.isUnipotentPoint_def]
  intro M
  obtain ⟨hgP, hlimit⟩ := mem_unipotent_iff.mp hg
  let E := extend A l ⟨g, hgP⟩
  let b := Module.Free.chooseBasis R M
  let C := Comodule.coefficientMatrix (C := H) b
  have hzeroPoint : evalZeroPoint A E = 1 := by
    simpa only [E, limit_apply] using hlimit
  have hzeroMatrix : (C.map E.ofConv).map (Polynomial.evalRingHom (0 : A)) = 1 := by
    calc
      (C.map E.ofConv).map (Polynomial.evalRingHom (0 : A)) =
          C.map (evalZeroPoint A E).ofConv := by
        ext i j
        simp [C, evalZeroPoint_apply, Matrix.map_apply]
      _ = C.map (1 : WithConv (H →ₐ[R] A)).ofConv := by rw [hzeroPoint]
      _ = 1 := by
        rw [← Comodule.toMatrix_endOfPoint b]
        simp
  have hGCharpoly := Matrix.charpoly_eq_charpoly_one_of_map_toLaurent (C.map E.ofConv)
    (C.map g.ofConv)
    hzeroMatrix (charpoly_map_toLaurent_extend_coefficientMatrix l hgP M)
  have hEndCharpoly :
      (Comodule.endOfPoint M g.ofConv).charpoly =
        (Polynomial.X - 1) ^ Fintype.card (Module.Free.ChooseBasisIndex R M) := by
    rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint M g.ofConv) (b.baseChange A),
      Comodule.toMatrix_endOfPoint, hGCharpoly, Matrix.charpoly_one]
  exact LinearMap.GeneralLinearGroup.isUnipotent_of_charpoly_eq _
    ((Comodule.pointsAction_toLinearMap M g).symm ▸ hEndCharpoly)

/-- Every point of a Hopf-ideal quotient is unipotent when its ambient cut-out subgroup lies in a
dynamic unipotent subgroup. -/
theorem isUnipotentPoint_quotient_of_le_unipotent
    (B : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R B)
    (l : B →ₐc[R] LaurentPolynomial R) (L : Type u)
    [Field L] [Algebra R L] [PerfectField L]
    (hI : CommHopfAlgCat.quotientPointsSubgroup B I (CommAlgCat.of R L) ≤
      unipotent (CommAlgCat.of R L) l)
    (g : HopfAlgebra.points (R := R) (H := CommHopfAlgCat.quotient B I)
      (CommAlgCat.of R L)) :
    HopfAlgebra.IsUnipotentPoint g := by
  apply (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective
    (CommHopfAlgCat.mkQuotient B I).hom
    (CommHopfAlgCat.mkQuotient_surjective B I) g).mp
  rw [← CommHopfAlgCat.quotientPointsHom_apply]
  exact isUnipotentPoint_of_mem_unipotent l
    (hI (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup B I
      (CommAlgCat.of R L) g))

end

end TauCeti.Cocharacter
