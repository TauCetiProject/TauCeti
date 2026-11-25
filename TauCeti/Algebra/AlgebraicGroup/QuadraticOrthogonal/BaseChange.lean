/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic
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
`TauCeti.Symplectic.coordinateHopfAlgebraBaseChangeIso`.

## Main declarations

* `QuadraticForm.coefficientMatrix_baseChangeForm`: the coefficient matrix of `q_K` is that of `q`
  read in `K`.
* `TauCeti.QuadraticOrthogonal.map_baseChangeHopfIdeal_definingHopfIdeal`: transport of the
  defining Hopf ideal along the general-linear base-change isomorphism.
* `TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraBaseChangeIso`: base change of the
  coordinate Hopf algebra of `O(q)` is that of `O(q')` for any form `q'` over `K` with the
  coefficients of `q`, in particular `q' = q_K`
  (`TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraBaseChangeIsoBaseChangeForm`).

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.1, for the orthogonal group scheme of a
  quadratic space over a ring, in every characteristic.
* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
-/

public section

open CategoryTheory Matrix
open scoped TensorProduct
open QuadraticForm (coefficientMatrix baseChangeForm baseChangeForm_apply)

namespace QuadraticForm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The coefficients of `q_K` are those of `q`.** The coefficient matrix of the form `q_K` on
`Kⁿ` with the coefficients of `q` is the coefficient matrix of `q` read in `K`. -/
theorem coefficientMatrix_baseChangeForm (q : QuadraticForm R (Fin n → R)) (K : Type*)
    [CommRing K] [Algebra R K] :
    coefficientMatrix (baseChangeForm q K) (Pi.basisFun K (Fin n)) =
      (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) := by
  classical
  have hlow : ∀ i j, j < i → coefficientMatrix q (Pi.basisFun R (Fin n)) i j = 0 :=
    fun i j hji ↦ by
      simp [coefficientMatrix_apply, ne_of_gt hji, not_lt.mpr hji.le]
  have hsingle (i j : Fin n) : (Pi.single i 1 : Fin n → K) ⬝ᵥ
      ((coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) *ᵥ Pi.single j 1) =
        algebraMap R K (coefficientMatrix q (Pi.basisFun R (Fin n)) i j) := by
    simp
  ext i j
  rw [coefficientMatrix_apply]
  split_ifs with hij hlt
  · subst hij
    rw [Pi.basisFun_apply, baseChangeForm_apply, hsingle, Matrix.map_apply]
  · rw [QuadraticMap.polar, Pi.basisFun_apply, Pi.basisFun_apply, baseChangeForm_apply,
      baseChangeForm_apply, baseChangeForm_apply, mulVec_add, dotProduct_add, add_dotProduct,
      add_dotProduct, hsingle, hsingle, hsingle, hsingle, hlow j i hlt, map_zero,
      Matrix.map_apply]
    ring
  · rw [Matrix.map_apply, hlow i j (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)), map_zero]

end QuadraticForm

namespace TauCeti.QuadraticOrthogonal

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (n : ℕ)

/-- The `R`-algebra structure obtained by restricting the coordinate algebra over `K`. -/
noncomputable local instance : Algebra R (GeneralLinear.coordinateHopfAlgebra K n) :=
  Algebra.compHom _ (algebraMap R K)

/-- The coordinate algebra over `K` is a scalar tower over `R → K`. -/
local instance : IsScalarTower R K (GeneralLinear.coordinateHopfAlgebra K n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The restriction of the general-linear base-change isomorphism to the original coordinate
Hopf algebra. -/
private noncomputable def baseChangeAlgHom :
    GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] GeneralLinear.coordinateHopfAlgebra K n :=
  ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom.toAlgHom.restrictScalars
      R).comp
    (Algebra.TensorProduct.includeRight :
      GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] K ⊗[R] GeneralLinear.coordinateHopfAlgebra R n)

/-- Applying the restricted base-change map is applying the ambient isomorphism to a scalar pure
tensor. -/
private theorem baseChangeAlgHom_apply (x : GeneralLinear.coordinateHopfAlgebra R n) :
    baseChangeAlgHom R K n x =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x) := by
  simp only [baseChangeAlgHom, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.coe_restrictScalars', BialgHom.coe_toAlgHom]

variable {R K n}
variable {q : QuadraticForm R (Fin n → R)} {q' : QuadraticForm K (Fin n → K)}

/-- The general-linear base-change isomorphism carries each scalar-extended entry of the relation
matrix `Xᵀ M X - M` of `q` to the corresponding entry for `q'`, when the coefficients of `q` map
to those of `q'`. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix
    (hq : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q' (Pi.basisFun K (Fin n))) (i j : Fin n) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
        (1 ⊗ₜ[R] relationMatrix R n q i j) =
      relationMatrix K n q' i j := by
  rw [← baseChangeAlgHom_apply R K n]
  have hgeneric : (GeneralLinear.genericMatrix R n).map (baseChangeAlgHom R K n) =
      GeneralLinear.genericMatrix K n := by
    simpa only [baseChangeAlgHom] using
      GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_genericMatrix R K n
  have hform : (coefficientMatrix q (Pi.basisFun R (Fin n))).map
        (algebraMap R (GeneralLinear.coordinateHopfAlgebra K n)) =
      (coefficientMatrix q' (Pi.basisFun K (Fin n))).map
        (algebraMap K (GeneralLinear.coordinateHopfAlgebra K n)) := by
    rw [← hq, Matrix.map_map, IsScalarTower.algebraMap_eq R K, RingHom.coe_comp]
  have hmatrix := relationMatrix_map R n q (baseChangeAlgHom R K n)
  rw [hgeneric, hform, ← relationMatrix_def K n q'] at hmatrix
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
  have hrel := coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix hq
  have hsum (i j : Fin n) :
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
          (1 ⊗ₜ[R] (relationMatrix R n q i j + relationMatrix R n q j i)) =
        relationMatrix K n q' i j + relationMatrix K n q' j i := by
    rw [TensorProduct.tmul_add, map_add, hrel, hrel]
  rw [relationSet_def, relationSet_def, Set.image_union, ← Set.range_comp, ← Set.range_comp]
  congr 1
  · exact congrArg Set.range (funext fun i ↦ hrel i i)
  · exact congrArg Set.range (funext fun ij ↦ hsum ij.1 ij.2)

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

variable (q K) in
/-- **Base change of `O(q)` to `O(q_K)`**: the scalar extension of the coordinate Hopf algebra of
`O(q)` along `R → K` is the coordinate Hopf algebra of `O(q_K)`, for `q_K` the form with the
coefficients of `q`. -/
noncomputable abbrev coordinateHopfAlgebraBaseChangeIsoBaseChangeForm :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n q) ≅
      coordinateHopfAlgebra K n (baseChangeForm q K) :=
  coordinateHopfAlgebraBaseChangeIso (QuadraticForm.coefficientMatrix_baseChangeForm q K).symm

end TauCeti.QuadraticOrthogonal
