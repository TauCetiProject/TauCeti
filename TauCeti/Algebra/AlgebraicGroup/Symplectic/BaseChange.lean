/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic

/-!
# Base change of the symplectic group

For a morphism of commutative rings `R → K`, scalar extension of the coordinate Hopf algebra
of `Sp₂ₘ` is canonically the coordinate Hopf algebra constructed directly over `K`.

Since `Sp₂ₘ` is the subgroup scheme of `GL (m + m)` preserving the constant form `Jₘ`, and `Jₘ`
over `R` maps to `Jₘ` over `K`, everything here specializes the base change of constant-form
subgroup schemes (`TauCeti.ConstantForm.coordinateHopfAlgebraBaseChangeIso`).

## Main declarations

* `TauCeti.Symplectic.coordinateHopfAlgebraBaseChangeIso`: base change of the coordinate Hopf
  algebra of `Sp₂ₘ`.
* `TauCeti.Symplectic.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom`:
  compatibility with the quotient coordinate morphisms from `O(GL (m + m))`.
* `TauCeti.Symplectic.finiteTypeCoordinateHopfAlgebraBaseChangeIso`: the finite-type form of the
  same isomorphism.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags [01JO](https://stacks.math.columbia.edu/tag/01JO) and
  [022W](https://stacks.math.columbia.edu/tag/022W).
-/

public section

open CategoryTheory Matrix
open scoped TensorProduct

namespace TauCeti.Symplectic

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (m : ℕ)

/-- The general-linear base-change isomorphism carries each scalar-extended symplectic relation
to the corresponding relation over the new base. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix (i j : Fin (m + m)) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom
        (1 ⊗ₜ[R] relationMatrix R m i j) =
      relationMatrix K m i j :=
  ConstantForm.coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix
    (JFin_map m (algebraMap R K)) i j

/-- The general-linear base-change isomorphism carries the base-changed symplectic defining Hopf
ideal onto the symplectic defining Hopf ideal over the new base. -/
theorem map_baseChangeHopfIdeal_definingHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R m)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom =
      definingHopfIdeal K m :=
  ConstantForm.map_baseChangeHopfIdeal_definingHopfIdeal (JFin_map m (algebraMap R K))

/-- Base change of the symplectic coordinate Hopf algebra is canonically the symplectic
coordinate Hopf algebra over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R m) ≅
      coordinateHopfAlgebra K m :=
  ConstantForm.coordinateHopfAlgebraBaseChangeIso (JFin_map m (algebraMap R K))

/-- The symplectic base-change isomorphism is compatible with the quotient coordinate morphisms
from the corresponding general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R m) ≫
        (coordinateHopfAlgebraBaseChangeIso R K m).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom ≫
        coordinateMap K m :=
  ConstantForm.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom _

/-- On a pure tensor of a restricted general-linear function, the symplectic base-change
isomorphism is the general-linear isomorphism followed by restriction. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap
    (s : K) (x : GeneralLinear.coordinateHopfAlgebra R (m + m)) :
    (coordinateHopfAlgebraBaseChangeIso R K m).hom.hom
        (s ⊗ₜ[R] (coordinateMap R m).hom x) =
      (coordinateMap K m).hom
        ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom
          (s ⊗ₜ[R] x)) := by
  have h := congrArg (fun f ↦ f.hom (s ⊗ₜ[R] x))
    (baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom R K m)
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply,
    CommHopfAlgCat.baseChangeMap_apply_tmul] at h
  exact h

/-- The finite-type coordinate Hopf algebra of `Sp₂ₘ` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R m) ≅
      finiteTypeCoordinateHopfAlgebra K m :=
  FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso
    (finiteTypeCoordinateHopfAlgebra_obj R m)
    (finiteTypeCoordinateHopfAlgebra_obj K m)
    (coordinateHopfAlgebraBaseChangeIso R K m)

/-- The underlying commutative-Hopf-algebra morphism of the finite-type base-change isomorphism
is the coordinate-Hopf-algebra base-change isomorphism, with the object equalities made explicit.
-/
@[simp]
theorem finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom :
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso R K m).hom.hom =
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
          (finiteTypeCoordinateHopfAlgebra_obj R m)) ≪≫
        coordinateHopfAlgebraBaseChangeIso R K m ≪≫
        eqToIso
          (finiteTypeCoordinateHopfAlgebra_obj K m).symm).hom := by
  exact FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso_hom
    (finiteTypeCoordinateHopfAlgebra_obj R m)
    (finiteTypeCoordinateHopfAlgebra_obj K m)
    (coordinateHopfAlgebraBaseChangeIso R K m)

end TauCeti.Symplectic
