/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Base change of the orthogonal group scheme of a quadratic form

For a morphism of commutative rings `R → K` and a quadratic form `q` on `Rⁿ`, scalar extension
of the coordinate Hopf algebra of `O(q)` (`TauCeti.QuadraticOrthogonal.groupScheme`) is the
coordinate Hopf algebra of `O(q_K)`, for `q_K` the form on `Kⁿ` with the same coefficients
(`QuadraticForm.baseChangeForm q K`). Nothing assumes `2` invertible.

The coefficient matrix of `q_K` is that of `q` read in `K`
(`QuadraticForm.coefficientMatrix_baseChangeForm`), since the coefficient matrix is upper
triangular. The general-linear base-change isomorphism `K ⊗[R] O(GLₙ, R) ≅ O(GLₙ, K)` carries
the generic matrix to the generic matrix, so it carries each scalar-extended entry of the relation
matrix `Xᵀ M X - M` to the corresponding entry over `K`, the relation set onto the relation set,
and the base-changed defining Hopf ideal onto the defining Hopf ideal over `K`; the general
base-change theorem for Hopf-ideal quotients then gives the isomorphism, as for
`TauCeti.Symplectic.coordinateHopfAlgebraBaseChangeIso`. The group-scheme base change follows
`TauCeti.ConstantForm.groupSchemeBaseChangeIso`.

## Main declarations

* `TauCeti.QuadraticOrthogonal.map_baseChangeHopfIdeal_definingHopfIdeal`: transport of the
  defining Hopf ideal along the general-linear base-change isomorphism.
* `TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraBaseChangeIso`: base change of the
  coordinate Hopf algebra of `O(q)` is that of `O(q')` for any form `q'` over `K` with the
  coefficients of `q`, in particular `q' = q_K`
  (`TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraBaseChangeIsoBaseChangeForm`).
* `TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraBaseChangeIso_hom_tmul_mkQuotient`: its value
  on a pure tensor of a class of a general-linear function.
* `TauCeti.QuadraticOrthogonal.groupSchemeBaseChangeIso`: base change of the group scheme `O(q)`,
  compatible with the inclusions into `GLₙ` (`map_inclusion_comp_groupSchemeBaseChangeIso_hom`).

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.1, for the orthogonal group scheme of a
  quadratic space over a ring, in every characteristic.
* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct
open QuadraticForm (coefficientMatrix baseChangeForm)

namespace TauCeti.QuadraticOrthogonal

universe u v

section Coordinate

variable {R : Type u} {K : Type max u v} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}
variable {q : QuadraticForm R (Fin n → R)} {q' : QuadraticForm K (Fin n → K)}

variable (R K n) in
/-- The ring morphism `x ↦ e (1 ⊗ x)` from `O(GLₙ, R)` to `O(GLₙ, K)`, for `e` the general-linear
base-change isomorphism `K ⊗[R] O(GLₙ, R) ≅ O(GLₙ, K)`. -/
private noncomputable def oneTmulBaseChange :
    GeneralLinear.coordinateHopfAlgebra R n →+* GeneralLinear.coordinateHopfAlgebra K n :=
  (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom.toAlgHom.toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom

/-- The morphism `oneTmulBaseChange R K n` sends `x` to `e (1 ⊗ x)`. -/
private theorem oneTmulBaseChange_apply (x : GeneralLinear.coordinateHopfAlgebra R n) :
    oneTmulBaseChange R K n x =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x) :=
  rfl

/-- The general-linear base-change isomorphism carries each scalar-extended entry of the relation
matrix `Xᵀ M X - M` of `q` to the corresponding entry for `q'`, when the coefficients of `q` map
to those of `q'`. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) (i j : Fin n) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
        (1 ⊗ₜ[R] relationMatrix R n q i j) =
      relationMatrix K n q' i j := by
  have hgeneric :
      (GeneralLinear.genericMatrix R n).map (oneTmulBaseChange R K n) =
        GeneralLinear.genericMatrix K n :=
    Matrix.ext (GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_genericMatrix R K n)
  have hform : ((coefficientMatrix q (Pi.basisFun R (Fin n))).map
        (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n))).map (oneTmulBaseChange R K n) =
      (coefficientMatrix q' (Pi.basisFun K (Fin n))).map
        (algebraMap K (GeneralLinear.coordinateHopfAlgebra K n)) := by
    rw [← hq, Matrix.map_map, Matrix.map_map]
    congr 1
    funext r
    rw [Function.comp_apply, Function.comp_apply, oneTmulBaseChange_apply,
      ← Algebra.TensorProduct.includeRight_apply, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R K, AlgHomClass.commutes]
  have hmatrix : (relationMatrix R n q).map (oneTmulBaseChange R K n) = relationMatrix K n q' := by
    rw [relationMatrix_def, relationMatrix_def,
      Matrix.map_sub _ (map_sub (oneTmulBaseChange R K n)), Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, hgeneric, hform]
  exact congrFun (congrFun hmatrix i) j

/-- The general-linear base-change isomorphism carries the scalar-extended relation set of `q`
onto the relation set of `q'`, when the coefficients of `q` map to those of `q'`. -/
theorem image_relationSet_baseChange
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    (fun x : GeneralLinear.coordinateHopfAlgebra R n ↦
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x)) ''
        relationSet R n q =
      relationSet K n q' := by
  have hmatrix : (relationMatrix R n q).map (oneTmulBaseChange R K n) = relationMatrix K n q' :=
    Matrix.ext fun i j => by
      rw [Matrix.map_apply, oneTmulBaseChange_apply,
        coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix hq]
  have hfun : (fun x : GeneralLinear.coordinateHopfAlgebra R n ↦
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x)) =
        oneTmulBaseChange R K n :=
    funext fun x => (oneTmulBaseChange_apply x).symm
  rw [hfun, relationSet_def, relationSet_def, ← hmatrix, Matrix.image_altRelationSet]

/-- The general-linear base-change isomorphism carries the base-changed defining Hopf ideal of
`O(q)` onto the defining Hopf ideal of `O(q')`, when the coefficients of `q` map to those of
`q'`. -/
theorem map_baseChangeHopfIdeal_definingHopfIdeal
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R n q)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom =
      definingHopfIdeal K n q' :=
  CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R n q) (definingHopfIdeal K n q')
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (definingHopfIdeal_toIdeal R n q) (definingHopfIdeal_toIdeal K n q')
    (image_relationSet_baseChange hq)

/-- **Base change of `O(q)`.** If the coefficients of `q` map to those of `q'` along `R → K`, the
scalar extension of the coordinate Hopf algebra of `O(q)` is the coordinate Hopf algebra of
`O(q')`. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n q) ≅
      coordinateHopfAlgebra K n q' :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (definingHopfIdeal R n q) (definingHopfIdeal K n q')
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal hq)

/-- The base-change isomorphism of `O(q)` is compatible with the quotient morphisms from the
general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_hom
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
          (definingHopfIdeal R n q)) ≫
        (coordinateHopfAlgebraBaseChangeIso hq).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom ≫
        CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra K n)
          (definingHopfIdeal K n q') :=
  CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (definingHopfIdeal R n q) (definingHopfIdeal K n q')
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal hq)

/-- On a pure tensor of a class of a general-linear function, the base-change isomorphism of
`O(q)` is the general-linear isomorphism followed by the quotient map. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_tmul_mkQuotient
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n)))
    (s : K) (x : GeneralLinear.coordinateHopfAlgebra R n) :
    (coordinateHopfAlgebraBaseChangeIso hq).hom.hom
        (s ⊗ₜ[R] (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
          (definingHopfIdeal R n q)).hom x) =
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra K n)
          (definingHopfIdeal K n q')).hom
        ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (s ⊗ₜ[R] x)) := by
  have h := congrArg (fun f ↦ f.hom (s ⊗ₜ[R] x))
    (baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_hom hq)
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply,
    CommHopfAlgCat.baseChangeMap_apply_tmul] at h
  exact h

variable (q K) in
/-- **Base change of `O(q)` to `O(q_K)`**: the scalar extension of the coordinate Hopf algebra of
`O(q)` along `R → K` is the coordinate Hopf algebra of `O(q_K)`, for `q_K` the form with the
coefficients of `q`. -/
noncomputable def coordinateHopfAlgebraBaseChangeIsoBaseChangeForm :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n q) ≅
      coordinateHopfAlgebra K n (baseChangeForm q K) :=
  coordinateHopfAlgebraBaseChangeIso (QuadraticForm.coefficientMatrix_baseChangeForm q K).symm

variable (q K) in
/-- The base-change isomorphism to `O(q_K)` is the general base-change isomorphism for `q' = q_K`,
so the compatibility lemmas for `coordinateHopfAlgebraBaseChangeIso` apply to it. -/
theorem coordinateHopfAlgebraBaseChangeIsoBaseChangeForm_def :
    coordinateHopfAlgebraBaseChangeIsoBaseChangeForm K q =
      coordinateHopfAlgebraBaseChangeIso
        (QuadraticForm.coefficientMatrix_baseChangeForm q K).symm :=
  (rfl)

/-- The inverse base-change isomorphism of `O(q)` is compatible with the quotient morphisms from
the general-linear coordinate Hopf algebras. -/
@[reassoc]
theorem mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_inv
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra K n)
          (definingHopfIdeal K n q') ≫ (coordinateHopfAlgebraBaseChangeIso hq).inv =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
            (definingHopfIdeal R n q)) :=
  CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIsoOfMapEq_inv _ _ _ _

end Coordinate

/-! ### Base change of the group scheme -/

section GroupScheme

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}
variable {q : QuadraticForm R (Fin n → R)} {q' : QuadraticForm K (Fin n → K)}

/-- **Base change of the group scheme `O(q)`.** If the coefficients of `q` map to those of `q'`
along `R → K`, the base change of `O(q)` to `K` is `O(q')`: the Hopf-ideal base-change comparison
of `GLₙ` at the defining Hopf ideals. -/
noncomputable def groupSchemeBaseChangeIso
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj
        (groupScheme R n q) ≅ groupScheme K n q' :=
  GeneralLinear.hopfIdealBaseChangeIso R K n (definingHopfIdeal R n q) (definingHopfIdeal K n q')
    (coordinateHopfAlgebraBaseChangeIso hq).symm

/-- The base-change isomorphism of `O(q)` is the Hopf-ideal base-change comparison of `GLₙ` for
the inverse base-change isomorphism of coordinate Hopf algebras. -/
theorem groupSchemeBaseChangeIso_def
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    groupSchemeBaseChangeIso hq =
      GeneralLinear.hopfIdealBaseChangeIso R K n (definingHopfIdeal R n q)
        (definingHopfIdeal K n q') (coordinateHopfAlgebraBaseChangeIso hq).symm :=
  (rfl)

/-- **Base change of `O(q)` is compatible with the inclusions.** Along the base-change
isomorphisms, the base change of the inclusion of `O(q)` into `GLₙ` is the inclusion of
`O(q')`. -/
@[reassoc]
theorem map_inclusion_comp_groupSchemeBaseChangeIso_hom
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.map
          (inclusion R n q) ≫ (GeneralLinear.groupSchemeBaseChangeIso R K n).hom =
      (groupSchemeBaseChangeIso hq).hom ≫ inclusion K n q' := by
  rw [inclusion_def, inclusion_def, groupSchemeBaseChangeIso_def]
  exact GeneralLinear.map_hopfIdealInclusion_comp_groupSchemeBaseChangeIso R K n _ _
    (coordinateHopfAlgebraBaseChangeIso hq).symm
    (mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_inv hq)

end GroupScheme

end TauCeti.QuadraticOrthogonal
