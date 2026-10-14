/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange

/-!
# Base change of the standard symplectic isotropic flag subgroup

For any homomorphism of commutative rings `R → K`, the scalar extension of the coordinate
Hopf algebra of the standard complete isotropic flag stabilizer in `Sp₂ₘ` is canonically
the coordinate Hopf algebra of that stabilizer over `K`. The comparison commutes with
coordinate restriction from the symplectic group. Thus geometric fibers of the flag
subgroup can be studied using its explicit matrix presentation over the residue field.
The induced point equivalence preserves the flag-preserving symplectic matrix over every
commutative value algebra.

The defining equations are the matrix entries below the diagonal in the self-dual flag
order. Transporting these equations uses the general-linear and symplectic base-change
comparisons; the quotient construction uses `CommHopfAlgCat.quotientBaseChangeIsoOfMapEq`.
The defining-ideal proof follows
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Borel`; the matrix-point
interface follows `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.BaseChange`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6 (symplectic groups and isotropic flags).
* B. Conrad, *Reductive Group Schemes* (2014), §5.1 (Borel subgroups over a base).
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.Symplectic.IsotropicFlag

universe u v w

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (m : ℕ)

/-- The symplectic base-change comparison carries the scalar-extended flag ideal onto
the flag ideal over the new base, including nonflat changes of base. -/
-- Use `rw` with explicit base rings: the `max` universe prevents reliable `simp` matching.
theorem map_baseChangeHopfIdeal_definingHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R m)).map
        (Symplectic.coordinateHopfAlgebraBaseChangeIso R K m).hom.hom =
      definingHopfIdeal K m := by
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R m) (definingHopfIdeal K m)
    (Symplectic.coordinateHopfAlgebraBaseChangeIso R K m)
    (definingHopfIdeal_toIdeal R m) (definingHopfIdeal_toIdeal K m) ?_
  rw [Set.image_image]
  ext x
  simp only [Set.mem_image,
    Symplectic.coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap R K m,
    GeneralLinear.mem_weightParabolicRelationSet_iff]
  constructor
  · rintro ⟨y, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, j, hij, rfl⟩,
      by rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X]⟩
  · rintro ⟨y, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, j, hij, rfl⟩,
      by rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X]⟩

/-- Scalar extension of the flag subgroup's coordinate Hopf algebra is the flag coordinate
Hopf algebra over the new base. No flatness, field, or characteristic hypothesis is needed. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R m) ≅
      coordinateHopfAlgebra K m :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (definingHopfIdeal R m) (definingHopfIdeal K m)
    (Symplectic.coordinateHopfAlgebraBaseChangeIso R K m)
    (map_baseChangeHopfIdeal_definingHopfIdeal R K m)

/-- Base change of the flag restriction agrees with restriction over the new base under
the canonical symplectic and flag comparisons. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R m) ≫
        (coordinateHopfAlgebraBaseChangeIso R K m).hom =
      (Symplectic.coordinateHopfAlgebraBaseChangeIso R K m).hom ≫ coordinateMap K m :=
  CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (definingHopfIdeal R m) (definingHopfIdeal K m)
    (Symplectic.coordinateHopfAlgebraBaseChangeIso R K m)
    (map_baseChangeHopfIdeal_definingHopfIdeal R K m)

/-- On a pure tensor of a restricted symplectic function, the flag comparison is the
ambient symplectic comparison followed by restriction. -/
theorem coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap
    (s : K) (x : Symplectic.coordinateHopfAlgebra R m) :
    (coordinateHopfAlgebraBaseChangeIso R K m).hom.hom
        (s ⊗ₜ[R] (coordinateMap R m).hom x) =
      (coordinateMap K m).hom
        ((Symplectic.coordinateHopfAlgebraBaseChangeIso R K m).hom.hom (s ⊗ₜ[R] x)) := by
  have h := congrArg (fun f ↦ f.hom (s ⊗ₜ[R] x))
    (baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom R K m)
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply,
    CommHopfAlgCat.baseChangeMap_apply_tmul] at h
  exact h

/-- The flag base-change point equivalence preserves the flag-preserving symplectic matrix
over every commutative value algebra. -/
theorem pointsMulEquiv_baseChangeIsoPointsMulEquiv
    (A : CommAlgCat.{w} K)
    (q : HopfAlgebra.points (R := K) (H := coordinateHopfAlgebra K m) A) :
    pointsMulEquiv R m
        (A := TauCeti.CommAlgCat.restrictScalarsObj (algebraMap R K) A)
        (CommHopfAlgCat.baseChangeIsoPointsMulEquiv
          (coordinateHopfAlgebraBaseChangeIso R K m).symm A q) =
      pointsMulEquiv K m (A := A) q := by
  apply Subtype.ext
  apply Subtype.ext
  rw [← pointsMulEquiv_coe, ← pointsMulEquiv_coe,
    ← Symplectic.pointsMulEquiv_coe, ← Symplectic.pointsMulEquiv_coe]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply]
  rw [CommHopfAlgCat.quotientPointsHom_apply, CommHopfAlgCat.quotientPointsHom_apply,
    CommHopfAlgCat.quotientPointsHom_apply, CommHopfAlgCat.quotientPointsHom_apply]
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  rw [CommHopfAlgCat.baseChangeIsoPointsMulEquiv_apply_apply]
  simp only [Iso.symm_inv]
  rw [← Symplectic.coordinateMap_def R m, ← Symplectic.coordinateMap_def K m,
    coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap,
    Symplectic.coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap,
    GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X]

end TauCeti.Symplectic.IsotropicFlag
