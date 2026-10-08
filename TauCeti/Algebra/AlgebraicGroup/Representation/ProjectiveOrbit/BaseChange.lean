/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
public import TauCeti.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Scalar extension of projective orbit morphisms

Extending the coefficient Hopf algebra and its comodule along `R → S` preserves the
projective orbit morphism of a unimodular vector. The comparison uses the canonical
identification of the scalar-extended dual with the dual of the scalar-extended module.
The result compares scheme morphisms, including their structure-sheaf maps, and applies
to nonreduced groups and value rings. It is the compatibility needed to transport
projective realizations of homogeneous spaces across extensions of the base field.

The coordinate calculation uses `Comodule.matrixCoefficient_baseChange_tmul`.
The projective comparison uses `TauCeti.Module.Dual.baseChangeEvaluationEquiv`,
`Proj.symmetricAlgebraScalarTensorIso`, and `Proj.baseChangeProjection`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

section Coordinates

variable {R : Type u} {S : Type v} {H : Type w} {M : Type x}
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring H] [Bialgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- After the canonical symmetric-algebra and dual comparisons, orbit coordinates are
exactly the scalar extension of the original coordinate map. -/
@[simp]
theorem orbitCoordinates_baseChange (m : M) :
    letI := Comodule.baseChange (R := R) (H := H) (M := M) S
    ((orbitCoordinates (H := S ⊗[R] H) (1 ⊗ₜ[R] m)).comp
      (SymmetricAlgebra.map S (Module.Dual.baseChangeEvaluation (R := R) (M := M)))).comp
        (SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toAlgHom =
      Algebra.TensorProduct.map (AlgHom.id S S) (orbitCoordinates (H := H) m) := by
  let := Comodule.baseChange (R := R) (H := H) (M := M) S
  apply Algebra.TensorProduct.ext
  · ext
  · ext φ
    simp [orbitCoordinates_ι]

end Coordinates

section Scheme

variable {R S H M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing H] [HopfAlgebra R H] [AddCommMonoid M] [Module R M] [Comodule R H M]
  [Module.Finite R M] [Module.Projective R M]

/-- Projection of the scalar-extended projective orbit morphism to the original projective
space is the original orbit morphism pulled back along the group coefficient projection.
No flatness assumption on `S` is needed for this equality. -/
@[reassoc]
theorem projectiveOrbitMap_baseChange (m : M) (hm : Module.IsUnimodular R m) :
    letI := Comodule.baseChange (R := R) (H := H) (M := M) S
    projectiveOrbitMap (H := S ⊗[R] H) (1 ⊗ₜ[R] m)
        hm.one_tmul ≫
      (Proj.symmetricAlgebraMapIso S
        (Module.Dual.baseChangeEvaluationEquiv (R := R) (A := S) (M := M))).hom ≫
      (Proj.symmetricAlgebraScalarTensorIso R S (Module.Dual R M)).hom ≫
      Proj.baseChangeProjection (SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)) S =
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      projectiveOrbitMap (H := H) m hm := by
  let := Comodule.baseChange (R := R) (H := H) (M := M) S
  simp only [Proj.symmetricAlgebraMapIso_hom, Proj.symmetricAlgebraScalarTensorIso_hom,
    Proj.baseChangeProjection_def, projectiveOrbitMap_def]
  simp only [← Category.assoc, Proj.fromOfGlobalSections_map,
    Proj.fromOfGlobalSections_naturality]
  congr 1
  apply RingHom.ext
  intro s
  have hnat := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := H)).toRingHom))
  have hcoord := AlgHom.congr_fun (orbitCoordinates_baseChange (S := S) (H := H) m)
    (1 ⊗ₜ[R] s)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hnat ⊢
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at hcoord
  have h := DFunLike.congr_fun hnat (orbitCoordinates (H := H) m s)
  simp only [RingHom.comp_apply] at h
  rw [← h]
  congr 1
  -- Convert the dual equivalence to its characteristic evaluation map before
  -- identifying the underlying functions of the bundled graded maps.
  have he : (Module.Dual.baseChangeEvaluationEquiv (R := R) (A := S) (M := M)).toLinearMap =
      Module.Dual.baseChangeEvaluation := by
    ext x
    simp
  simp only [GradedRingHom.coe_toRingHom, SymmetricAlgebra.gradedMap_apply,
    TauCeti.GradedAlgebra.baseChangeMap_apply, he]
  erw [TensorProduct.scalarTensorGradedAlgHom_apply]
  exact hcoord

end Scheme

end TauCeti.Comodule
