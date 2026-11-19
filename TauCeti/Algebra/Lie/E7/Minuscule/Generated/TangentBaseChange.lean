/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.BaseChangeMap
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Naturality

/-!
# Restriction of generated E₇ tangent vectors under arbitrary base change

For every algebra of commutative rings `R → S`, the coordinate comparison induces an injective
`S`-linear Lie map from the tangent algebra generated over `S` to the `S`-valued tangent algebra
of the group generated over `R`. Its ambient matrix is unchanged. Consequently it sends each
normalized root vector, Cartan bracket, and simple-coroot differential to the coefficient
extension of its counterpart over `R`.

These identities apply to integral reduction in every characteristic, without a freeness or
nontriviality assumption. They give compatibility of the numbered candidate pinning vectors
across fibers; they do not assert that the entire generated group commutes with arbitrary base
change or identify its Lie algebra with the full Serre presentation.

## Main declarations

* `TauCeti.E7Minuscule.generatedTangentRestriction`: the injective coefficient-valued Lie map.
* `TauCeti.E7Minuscule.tangentMatrix_generatedTangentRestriction`: its ambient matrix formula.
* `TauCeti.E7Minuscule.generatedTangentRestriction_generatedRootVector`: root normalization.
* `TauCeti.E7Minuscule.generatedTangentRestriction_generatedCartanVector`: Cartan normalization.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.E7Minuscule

universe u

noncomputable section

attribute [local instance high] Algebra.toModule

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Restriction from the newly generated tangent algebra to coefficient-valued tangent vectors
of the original generated group. The coefficient ring of this Lie map is `S`. -/
def generatedTangentRestriction :
    Derivation S (generatedCoordinateHopfAlgebra S)
        (Bialgebra.CounitAlgebra S (generatedCoordinateHopfAlgebra S) S) →ₗ⁅S⁆
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) S) :=
  (tangentBaseChangeLieEquiv (R := R) (K := S)
    (H := generatedCoordinateHopfAlgebra R)).symm.toLieHom.comp
      (derivationCompLieHom (B := S) (generatedCoordinateBaseChangeMap R S).hom)

/-- Restriction is injective because the coordinate comparison is surjective. -/
theorem generatedTangentRestriction_injective :
    Function.Injective (generatedTangentRestriction R S) :=
  (tangentBaseChangeLieEquiv (R := R) (K := S)
    (H := generatedCoordinateHopfAlgebra R)).symm.injective.comp
      (derivationCompLieHom_injective_of_surjective _
        (generatedCoordinateBaseChangeMap_surjective R S))

/-- Restriction evaluates on the scalar extension of an original coordinate. -/
theorem generatedTangentRestriction_apply
    (d : Derivation S (generatedCoordinateHopfAlgebra S)
      (Bialgebra.CounitAlgebra S (generatedCoordinateHopfAlgebra S) S))
    (x : generatedCoordinateHopfAlgebra R) :
    Bialgebra.CounitAlgebra.algEquivSelf R (generatedCoordinateHopfAlgebra R) S
        (generatedTangentRestriction R S d x) =
      Bialgebra.CounitAlgebra.algEquivSelf S (generatedCoordinateHopfAlgebra S) S
        (d ((generatedCoordinateBaseChangeMap R S).hom (1 ⊗ₜ[R] x))) := by
  simp only [generatedTangentRestriction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    tangentBaseChangeLieEquiv_symm_apply, AlgEquiv.apply_symm_apply,
    derivationCompLieHom_apply, algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom]

/-- The tangent restriction preserves every entry of the ambient minuscule matrix. -/
theorem tangentMatrix_generatedTangentRestriction
    (d : Derivation S (generatedCoordinateHopfAlgebra S)
      (Bialgebra.CounitAlgebra S (generatedCoordinateHopfAlgebra S) S)) :
    GeneralLinear.tangentMatrix 56
        (derivationComp (B := S) (generatedCoordinateMap R).hom
          (generatedTangentRestriction R S d)) =
      GeneralLinear.tangentMatrix 56
        (derivationComp (B := S) (generatedCoordinateMap S).hom d) := by
  ext i j
  rw [GeneralLinear.tangentMatrix_apply, GeneralLinear.tangentMatrix_apply,
    algEquivSelf_derivationComp_apply, algEquivSelf_derivationComp_apply,
    generatedTangentRestriction_apply]
  have h := congrArg (fun f ↦ f.hom
    (1 ⊗ₜ[R] GeneralLinear.coordinateHopfAlgebraAlgEquiv R 56
      (GeneralLinear.coordinateRingMap R 56 (MvPolynomial.X (i, j)))))
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateBaseChangeMap R S)
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    CommHopfAlgCat.baseChangeMap_apply_tmul.{u, u, u}] at h
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_one_tmul_X R S 56 i j] at h
  simp only [BialgHom.coe_toAlgHom]
  exact congrArg (fun x ↦ Bialgebra.CounitAlgebra.algEquivSelf S
    (generatedCoordinateHopfAlgebra S) S (d x)) h

private theorem derivationComp_generatedCoordinateMap_mapValue
    (d : Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R)) :
    derivationComp (B := S) (generatedCoordinateMap R).hom
        (Derivation.mapValue (Algebra.ofId R S) d) =
      Derivation.mapValue (Algebra.ofId R S)
        (derivationComp (B := R) (generatedCoordinateMap R).hom d) := by
  ext x
  apply (Bialgebra.CounitAlgebra.algEquivSelf R
    (GeneralLinear.coordinateHopfAlgebra R 56) S).injective
  rw [algEquivSelf_derivationComp_apply, Derivation.mapValue_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_map, Derivation.mapValue_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_map, algEquivSelf_derivationComp_apply]

/-- A numbered root vector restricts to the coefficient extension of the original normalized
root vector. This includes integral reduction in characteristics two and three. -/
@[simp]
theorem generatedTangentRestriction_generatedRootVector (k : Fin 7 ⊕ Fin 7) :
    generatedTangentRestriction R S (generatedRootVector S k) =
      Derivation.lieMapValue (Algebra.ofId R S) (generatedRootVector R k) := by
  apply derivationComp_injective_of_surjective (generatedCoordinateMap R).hom
    (generatedCoordinateMap_surjective R)
  apply (GeneralLinear.tangentLinearEquivMatrix (R := R) (B := S) 56).injective
  simp only [GeneralLinear.tangentLinearEquivMatrix_apply]
  have hvalue : Derivation.lieMapValue (Algebra.ofId R S) (generatedRootVector R k) =
      Derivation.mapValue (Algebra.ofId R S) (generatedRootVector R k) :=
    DFunLike.congr_fun (Derivation.lieMapValue_toLinearMap (Algebra.ofId R S)) _
  rw [tangentMatrix_generatedTangentRestriction, hvalue,
    derivationComp_generatedCoordinateMap_mapValue, GeneralLinear.tangentMatrix_mapValue,
    tangentMatrix_generatedRootVector, tangentMatrix_generatedRootVector]
  ext i j
  simp only [Matrix.map_apply, map_intCast]

/-- Restriction preserves the Cartan vector with the positive-then-negative bracket convention. -/
@[simp]
theorem generatedTangentRestriction_generatedCartanVector (i : Fin 7) :
    generatedTangentRestriction R S (generatedCartanVector S i) =
      Derivation.lieMapValue (Algebra.ofId R S) (generatedCartanVector R i) := by
  rw [generatedCartanVector_def S i, generatedCartanVector_def R i, LieHom.map_lie,
    LieHom.map_lie, generatedTangentRestriction_generatedRootVector,
    generatedTangentRestriction_generatedRootVector]

/-- Restriction sends the normalized simple-coroot differential over `S` to the coefficient
extension of the corresponding differential over `R`. -/
theorem generatedTangentRestriction_corootDifferential (i : Fin 7) :
    generatedTangentRestriction R S
        (derivationComp (generatedCorootCocharacter S i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : S))) =
      Derivation.lieMapValue (Algebra.ofId R S)
        (derivationComp (generatedCorootCocharacter R i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R))) := by
  rw [← generatedCartanVector_eq_derivationComp_generatedCorootCocharacter S i,
    ← generatedCartanVector_eq_derivationComp_generatedCorootCocharacter R i,
    generatedTangentRestriction_generatedCartanVector]

end

end TauCeti.E7Minuscule
