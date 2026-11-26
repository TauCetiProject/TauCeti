/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Base change of constant-form subgroup schemes

For a morphism of commutative rings `R → K` and constant forms `C` over `R` and `C'` over `K`
with `C.map (algebraMap R K) = C'`, the general-linear base-change isomorphism
`K ⊗[R] O(GLₙ, R) ≅ O(GLₙ, K)` carries each scalar-extended entry of `X C Xᵀ - C` to the
corresponding entry of `X C' Xᵀ - C'`. Hence it carries the scalar-extended relation set onto
the relation set over `K`, and the base-changed defining Hopf ideal of `C` onto the defining
Hopf ideal of `C'`.

From this transport of the defining Hopf ideal, the file builds the base-change isomorphism
from the scalar extension of the coordinate Hopf algebra of the subgroup scheme preserving `C` to
that of the subgroup scheme preserving `C'`, compatibly with the quotient maps from `O(GLₙ)`.
Its scheme-side form, the instance of `TauCeti.GeneralLinear.hopfIdealBaseChangeIso` at the
defining Hopf ideals, identifies the base change of the subgroup scheme preserving `C` with the
subgroup scheme preserving `C'`, compatibly with the inclusions into `GLₙ`.

## Main declarations

* `TauCeti.ConstantForm.coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix`: transport of a
  single relation.
* `TauCeti.ConstantForm.image_relationSet_baseChange`: transport of the relation set.
* `TauCeti.ConstantForm.map_baseChangeHopfIdeal_definingHopfIdeal`: transport of the defining
  Hopf ideal.
* `TauCeti.ConstantForm.coordinateHopfAlgebraBaseChangeIso`: base change of the coordinate Hopf
  algebra of the subgroup scheme preserving `C`, compatibly with the quotient maps from `O(GLₙ)`.
* `TauCeti.ConstantForm.groupSchemeBaseChangeIso`: base change of the subgroup scheme preserving
  `C`.
* `TauCeti.ConstantForm.map_inclusion_comp_groupSchemeBaseChangeIso_hom`: compatibility with the
  inclusions into `GLₙ` and `TauCeti.GeneralLinear.groupSchemeBaseChangeIso`.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags [01JO](https://stacks.math.columbia.edu/tag/01JO) and
  [022W](https://stacks.math.columbia.edu/tag/022W).

The symplectic base-change isomorphism `TauCeti.Symplectic.coordinateHopfAlgebraBaseChangeIso`
is the specialization of this one to `Jₘ`.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct

namespace TauCeti.ConstantForm

universe u v

section Coordinate

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
variable {C : Matrix (Fin n) (Fin n) R} {C' : Matrix (Fin n) (Fin n) K}

/-- The general-linear base-change isomorphism carries each scalar-extended entry of
`X C Xᵀ - C` to the corresponding entry of `X C' Xᵀ - C'`, when `C` maps to `C'`. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix
    (hC : C.map (algebraMap R K) = C') (i j : Fin n) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
        (1 ⊗ₜ[R] relationMatrix R n C i j) =
      relationMatrix K n C' i j := by
  rw [← baseChangeAlgHom_apply R K n]
  have hgeneric : (GeneralLinear.genericMatrix R n).map (baseChangeAlgHom R K n) =
      GeneralLinear.genericMatrix K n := by
    simpa only [baseChangeAlgHom] using
      GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_genericMatrix R K n
  have hform : C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra K n)) =
      C'.map (algebraMap K (GeneralLinear.coordinateHopfAlgebra K n)) := by
    rw [← hC, Matrix.map_map, IsScalarTower.algebraMap_eq R K, RingHom.coe_comp]
  have hmatrix := relationMatrix_map R n C (baseChangeAlgHom R K n)
  rw [hgeneric, hform] at hmatrix
  rw [← relationMatrix_def K n C'] at hmatrix
  exact congrFun (congrFun hmatrix i) j

/-- The general-linear base-change isomorphism carries the scalar-extended relation set of `C`
onto the relation set of `C'`, when `C` maps to `C'`. -/
theorem image_relationSet_baseChange (hC : C.map (algebraMap R K) = C') :
    (fun x : GeneralLinear.coordinateHopfAlgebra R n ↦
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x)) ''
        relationSet R n C =
      relationSet K n C' := by
  ext x
  constructor
  · rintro ⟨_, hy, rfl⟩
    obtain ⟨i, j, rfl⟩ := (mem_relationSet_iff R n C).mp hy
    dsimp only
    rw [coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix hC i j]
    exact relationMatrix_mem_relationSet K n C' i j
  · intro hx
    obtain ⟨i, j, rfl⟩ := (mem_relationSet_iff K n C').mp hx
    exact ⟨relationMatrix R n C i j, relationMatrix_mem_relationSet R n C i j,
      coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix hC i j⟩

/-- The general-linear base-change isomorphism carries the base-changed defining Hopf ideal of
`C` onto the defining Hopf ideal of `C'`, when `C` maps to `C'`. -/
theorem map_baseChangeHopfIdeal_definingHopfIdeal (hC : C.map (algebraMap R K) = C') :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R n C)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom =
      definingHopfIdeal K n C' :=
  CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R n C) (definingHopfIdeal K n C')
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (definingHopfIdeal_toIdeal R n C) (definingHopfIdeal_toIdeal K n C')
    (image_relationSet_baseChange hC)

/-- **Base change of the coordinate Hopf algebra of a constant-form subgroup scheme.** If `C` maps
to `C'` over `K`, scalar extension of the coordinate Hopf algebra of the subgroup scheme preserving
`C` is that of the subgroup scheme preserving `C'`. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso (hC : C.map (algebraMap R K) = C') :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n C) ≅
      coordinateHopfAlgebra K n C' :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq (definingHopfIdeal R n C) (definingHopfIdeal K n C')
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal hC)

/-- The base-change isomorphism is compatible with the quotient maps from `O(GLₙ)`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom
    (hC : C.map (algebraMap R K) = C') :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n C) ≫
        (coordinateHopfAlgebraBaseChangeIso hC).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom ≫ coordinateMap K n C' := by
  rw [coordinateMap_def, coordinateMap_def, coordinateHopfAlgebraBaseChangeIso]
  exact CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom _ _ _ _

/-- The inverse base-change isomorphism is compatible with the quotient maps from `O(GLₙ)`. -/
@[reassoc]
theorem coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv
    (hC : C.map (algebraMap R K) = C') :
    coordinateMap K n C' ≫ (coordinateHopfAlgebraBaseChangeIso hC).inv =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n C) := by
  rw [coordinateMap_def, coordinateMap_def, coordinateHopfAlgebraBaseChangeIso]
  exact CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIsoOfMapEq_inv _ _ _ _

end Coordinate

/-! ### Base change of the subgroup scheme -/

section GroupScheme

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}
variable {C : Matrix (Fin n) (Fin n) R} {C' : Matrix (Fin n) (Fin n) K}

/-- **Base change of a constant-form subgroup scheme.** If `C` maps to `C'` over `K`, the base
change to `K` of the subgroup scheme of `GLₙ` preserving `C` is the subgroup scheme preserving
`C'`: the Hopf-ideal base-change comparison of `GLₙ` at the defining Hopf ideals. -/
noncomputable def groupSchemeBaseChangeIso (hC : C.map (algebraMap R K) = C') :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj
        (groupScheme R n C) ≅ groupScheme K n C' :=
  GeneralLinear.hopfIdealBaseChangeIso R K n (definingHopfIdeal R n C) (definingHopfIdeal K n C')
    (coordinateHopfAlgebraBaseChangeIso hC).symm

/-- The base-change isomorphism is the Hopf-ideal base-change comparison of `GLₙ` for the inverse
base-change isomorphism of coordinate Hopf algebras. -/
theorem groupSchemeBaseChangeIso_def (hC : C.map (algebraMap R K) = C') :
    groupSchemeBaseChangeIso hC =
      GeneralLinear.hopfIdealBaseChangeIso R K n (definingHopfIdeal R n C)
        (definingHopfIdeal K n C') (coordinateHopfAlgebraBaseChangeIso hC).symm :=
  (rfl)

/-- **Base change of a constant-form subgroup scheme is compatible with the inclusions.** Along
the base-change isomorphisms, the base change of the inclusion of the subgroup scheme preserving
`C` into `GLₙ` is the inclusion of the subgroup scheme preserving `C'`. -/
@[reassoc]
theorem map_inclusion_comp_groupSchemeBaseChangeIso_hom (hC : C.map (algebraMap R K) = C') :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.map
          (inclusion R n C) ≫ (GeneralLinear.groupSchemeBaseChangeIso R K n).hom =
      (groupSchemeBaseChangeIso hC).hom ≫ inclusion K n C' := by
  have he := coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv hC
  rw [coordinateMap_def, coordinateMap_def] at he
  rw [inclusion_def, inclusion_def, groupSchemeBaseChangeIso_def]
  exact GeneralLinear.map_hopfIdealInclusion_comp_groupSchemeBaseChangeIso R K n _ _ _ he

end GroupScheme

end TauCeti.ConstantForm
