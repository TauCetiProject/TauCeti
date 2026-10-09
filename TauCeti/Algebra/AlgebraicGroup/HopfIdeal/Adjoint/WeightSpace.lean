/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Adjoint weights of a closed subgroup with a weight torus

A torus map to a closed subgroup of `GLₙ` whose ambient map is diagonal with weights `w`
acts on tangent-matrix entry `(i,j)` through `w i - w j`. Testing the universal torus
point detects exactly the entries allowed in an adjoint weight space. The derivation
criterion needs no smoothness assumption; the comodule criterion assumes that the
augmentation cotangent module is finite projective.

The argument factors the matrix computations of
`TauCeti.SpecialLinear.adDerivation_universalDiagonalTorus_eq_iff` and its comodule
criterion through the injective closed-subgroup differential. This supplies the common
entrywise criterion used in classical pinnings.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u

noncomputable section

variable {R : Type u} [CommRing R] {n : ℕ} {σ : Type u} [Fintype σ]
variable (I : HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n))
variable (w : Fin n → σ → ℤ)
variable (π : (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) →ₐc[R]
  MonoidAlgebra R (Multiplicative (σ →₀ ℤ)))
variable (hπ : π.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) =
  (GeneralLinear.weightTorusCoordinateMap w).hom)

include hπ

private theorem ambientCounitPoint_weightTorus {B : Type*} [CommRing B] [Algebra R B]
    (s : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] B)) :
    GeneralLinear.counitPointsMulEquiv n
      (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
        (GeneralLinear.coordinateHopfAlgebra R n) B)
        (Bialgebra.Quotient.mkBialgHom I.toIdeal)
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B
          (toConv (s.ofConv.comp π.toAlgHom)))) =
      diagGL (fun i => DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (w i))) := by
  rw [GeneralLinear.counitPointsMulEquiv_eq_pointsMulEquiv]
  have hpoint :
      AlgHom.mapValue
          (Bialgebra.CounitAlgebra.algEquivSelf R
            (GeneralLinear.coordinateHopfAlgebra R n) B).toAlgHom
          (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
            (GeneralLinear.coordinateHopfAlgebra R n) B)
            (Bialgebra.Quotient.mkBialgHom I.toIdeal)
            (Derivation.pointInCounitAlgebra
              (H := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B
              (toConv (s.ofConv.comp π.toAlgHom)))) =
        toConv (s.ofConv.comp (GeneralLinear.weightTorusCoordinateMap w).hom.toAlgHom) := by
    apply WithConv.ofConv_injective
    ext x
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    -- `mapDomain` returns the ambient-indexed counit algebra, while the point uses
    -- the quotient-indexed one. The application rules erase these coefficient indexings.
    erw [Bialgebra.CounitAlgebra.algEquivSelf_apply, AlgHom.mapDomain_apply_apply,
      Derivation.pointInCounitAlgebra_apply]
    rw [ofConv_toConv, AlgHom.comp_apply]
    exact congrArg s.ofConv (BialgHom.congr_fun hπ x)
  rw [hpoint]
  have hdiag := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap w
    (CommAlgCat.of R B) s
  -- The categorical point uses `CommAlgCat.of R B`; expose its algebra-hom presentation.
  erw [CommHopfAlgCat.mapPointsFunctor_app_apply] at hdiag
  simpa only [SplitTorus.charOfPoint_weightCharacter] using hdiag

/-- A weight-torus point scales each entry of the ambient tangent matrix of a closed
subgroup by the difference of its two standard weights. -/
theorem tangentMatrix_adDerivation_weightTorus_apply
    {B : Type*} [CommRing B] [Algebra R B]
    (s : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] B))
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B))
    (i j : Fin n) :
    GeneralLinear.tangentMatrix n (quotientLieHom I
      (Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B
          (toConv (s.ofConv.comp π.toAlgHom))) d)) i j =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (w i - w j)) : B) *
        GeneralLinear.tangentMatrix n (quotientLieHom I d) i j := by
  rw [quotientLieHom_adDerivation,
    GeneralLinear.tangentMatrix_adDerivation_apply_of_diagGL
      (ambientCounitPoint_weightTorus I w π hπ s)]
  rw [SplitTorus.charOfPoint_weightCharacter, SplitTorus.charOfPoint_weightCharacter,
    SplitTorus.charOfPoint_weightCharacter, torusCharacter_sub, div_eq_mul_inv, Units.val_mul]
  ring

/-- At the universal weight-torus point, a closed-subgroup tangent-matrix entry is
multiplied by its integral character in the group-algebra basis. -/
theorem tangentMatrix_adDerivation_universalWeightTorus_apply
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) R))
    (i j : Fin n) :
    GeneralLinear.tangentMatrix n (quotientLieHom I
      (Derivation.adDerivation (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
        (Derivation.pointInCounitAlgebra
          (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
          (toConv π.toAlgHom)) (Derivation.mapValue (Algebra.ofId R _) d))) i j =
      MonoidAlgebra.single (SplitTorus.weightCharacter (w i - w j))
        (GeneralLinear.tangentMatrix n (quotientLieHom I d) i j) := by
  have h := tangentMatrix_adDerivation_weightTorus_apply I w π hπ
    (toConv (AlgHom.id R _)) (Derivation.mapValue (Algebra.ofId R _) d) i j
  rw [ofConv_toConv, AlgHom.id_comp] at h
  rw [h, quotientLieHom_mapValue, GeneralLinear.tangentMatrix_mapValue, Matrix.map_apply,
    DiagonalizableGroup.charOfPoint_apply_coe, AlgHom.id_apply, Algebra.ofId_apply]
  rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]

/-- A closed-subgroup tangent vector is an eigenvector at the universal weight-torus
point exactly when entries of every other character vanish. -/
theorem adDerivation_universalWeightTorus_eq_iff
    (α : Multiplicative (σ →₀ ℤ))
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) R)) :
    Derivation.adDerivation (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
        (Derivation.pointInCounitAlgebra
          (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
          (toConv π.toAlgHom)) (Derivation.mapValue (Algebra.ofId R _) d) =
      MonoidAlgebra.single α (1 : R) • Derivation.mapValue (Algebra.ofId R _) d ↔
      ∀ i j : Fin n, SplitTorus.weightCharacter (w i - w j) ≠ α →
        GeneralLinear.tangentMatrix n (quotientLieHom I d) i j = 0 := by
  let K := MonoidAlgebra R (Multiplicative (σ →₀ ℤ))
  have hentry (i j : Fin n) :
      GeneralLinear.tangentMatrix n (quotientLieHom I
        (MonoidAlgebra.single α (1 : R) • Derivation.mapValue (Algebra.ofId R K) d)) i j =
        MonoidAlgebra.single α (GeneralLinear.tangentMatrix n (quotientLieHom I d) i j) := by
    rw [map_smul, map_smul, Matrix.smul_apply, smul_eq_mul,
      quotientLieHom_mapValue, GeneralLinear.tangentMatrix_mapValue, Matrix.map_apply,
      Algebra.ofId_apply]
    rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]
  constructor
  · intro h i j hij
    have he := congrArg (fun e => GeneralLinear.tangentMatrix n (quotientLieHom I e) i j) h
    rw [tangentMatrix_adDerivation_universalWeightTorus_apply I w π hπ, hentry] at he
    by_contra hne
    exact hij (MonoidAlgebra.single_left_injective hne he)
  · intro h
    apply quotientLieHom_injective I
    apply (GeneralLinear.tangentLinearEquivMatrix (R := R) (B := K) n).injective
    rw [GeneralLinear.tangentLinearEquivMatrix_apply,
      GeneralLinear.tangentLinearEquivMatrix_apply]
    ext i j
    rw [tangentMatrix_adDerivation_universalWeightTorus_apply I w π hπ, hentry]
    by_cases hij : SplitTorus.weightCharacter (w i - w j) = α
    · rw [hij]
    · simp [h i j hij]

variable [Module.Finite R
  (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))]

/-- For a closed subgroup with a weight-torus factorization, membership in the actual
adjoint comodule weight space is equivalent to vanishing of entries of every other weight. -/
theorem mem_adjointWeightSpace_iff_of_weightTorus
    (α : Multiplicative (σ →₀ ℤ))
    (x : Module.Dual R
      (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))) :
    x ∈ Derivation.adjointWeightSpace π α ↔
      ∀ i j : Fin n, SplitTorus.weightCharacter (w i - w j) ≠ α →
        GeneralLinear.tangentMatrix n
          (quotientLieHom I (Derivation.cotangentLinearEquiv (B := R) x)) i j = 0 := by
  rw [Derivation.mem_adjointWeightSpace_iff_universalPointAction]
  let K := MonoidAlgebra R (Multiplicative (σ →₀ ℤ))
  rw [← (Derivation.tangentScalarExtensionEquiv
    (R := R) (A := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) (B := K)).injective.eq_iff]
  rw [Derivation.tangentScalarExtensionEquiv_adjointAction (CommAlgCat.of R K)
      (toConv π.toAlgHom), Derivation.tangentScalarExtensionEquiv_tmul, one_smul,
    Derivation.tangentScalarExtensionEquiv_tmul,
    adDerivation_universalWeightTorus_eq_iff I w π hπ]

end

end TauCeti.HopfIdeal
