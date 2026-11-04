/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Root.Differential

/-!
# Simple-coroot differentials of the integral Geck carrier

The coordinate cocharacters of the Geck weight torus are the simple coroots of the named
simply connected root datum. Their differentials are the brackets of the normalized positive
and negative simple-root vectors, with values in every commutative ring. In particular the
toral tangent image is spanned by these opposite-root brackets. No smoothness or cotangent
projectivity hypothesis is used.

The integral matrix calculation follows from the rational Geck sl₂ triples by injectivity of
`ℤ → ℚ`, so it retains the normalization in bad characteristic and over nonreduced rings.
The weight-torus parametrization need not be an immersion for an arbitrary diagram; no
independence of these differentials, torus maximality, or identification of the carrier with
an independently pinned simply connected group is asserted.

## Main results

* `TauCeti.DynkinType.geckCorootCocharacter_eq_cocharacter_coroot_simpleIndex` identifies the
  cocharacters with the Bourbaki-numbered simple coroots.
* `TauCeti.DynkinType.lie_geckRootVector_eq_derivationComp_geckCorootCocharacter` identifies
  their differentials with the normalized opposite-root brackets.
* `TauCeti.DynkinType.range_derivationCompLieHom_geckWeightTorusIntegralCoordinateMap_eq_span`
  identifies the toral tangent image.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233–3247.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.

The cocharacter and tangent-image interface follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`; the root vectors are those of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Root.Differential`.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- The coordinate cocharacter of the integral Geck weight torus at a Bourbaki simple coroot. -/
def geckCorootCocharacter (i : Fin t.rank) :
    t.geckCoordinateHopfAlgebra ht →ₐc[ℤ] LaurentPolynomial ℤ :=
  (t.geckWeightTorusIntegralCoordinateMap ht).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The cocharacter evaluates the corresponding fundamental-weight coordinate. -/
theorem geckCorootCocharacter_def (i : Fin t.rank) :
    t.geckCorootCocharacter ht i =
      (t.geckWeightTorusIntegralCoordinateMap ht).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter is the named simple coroot of the simply connected root datum. -/
theorem geckCorootCocharacter_eq_cocharacter_coroot_simpleIndex (i : Fin t.rank) :
    t.geckCorootCocharacter ht i =
      (t.geckWeightTorusIntegralCoordinateMap ht).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          ((t.simplyConnectedRootDatum ht).coroot (t.simpleIndex ht i))) := by
  rw [geckCorootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  rw [coroot_simpleIndex]
  ext j
  simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

variable {B : Type*} [CommRing B]

/-- The simple-coroot differential is the diagonal matrix of the Geck weights evaluated on
that coroot, multiplied by the multiplicative tangent parameter. -/
-- Match before simplification changes the inherited integer module of the coefficient algebra.
@[simp↓]
theorem tangentMatrix_derivationComp_geckCorootCocharacter (i : Fin t.rank)
    (d : Derivation ℤ (LaurentPolynomial ℤ)
      (Bialgebra.CounitAlgebra ℤ (LaurentPolynomial ℤ) B)) :
    GeneralLinear.tangentMatrix (t.geckDim ht)
        (HopfIdeal.quotientLieHom (B := B) (t.geckDefiningIdeal ht)
          (derivationComp (t.geckCorootCocharacter ht i) d)) =
      Matrix.diagonal (fun a ↦ t.geckWeightFin ht a i •
        MultiplicativeGroup.tangentLinearEquiv d) := by
  rw [HopfIdeal.quotientLieHom_apply, geckCorootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _
      (t.geckWeightTorusIntegralCoordinateMap_hom_comp_mkBialgHom ht)]
  simp

/-- The bracket of the normalized opposite simple-root vectors is the differential of the
actual simple-coroot cocharacter, over every commutative value ring. -/
theorem lie_geckRootVector_eq_derivationComp_geckCorootCocharacter (i : Fin t.rank) :
    ⁅t.geckRootVector ht (B := B) (.inl i), t.geckRootVector ht (B := B) (.inr i)⁆ =
      derivationComp (t.geckCorootCocharacter ht i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) := by
  apply HopfIdeal.quotientLieHom_injective (t.geckDefiningIdeal ht)
  apply (GeneralLinear.tangentLinearEquivMatrix (R := ℤ) (B := B) (t.geckDim ht)).injective
  rw [GeneralLinear.tangentLinearEquivMatrix_apply,
    GeneralLinear.tangentLinearEquivMatrix_apply,
    tangentMatrix_derivationComp_geckCorootCocharacter]
  simp only [LieHom.map_lie, GeneralLinear.tangentMatrix_lie, tangentMatrix_geckRootVector,
    LinearEquiv.apply_symm_apply]
  have h := congrArg (fun M ↦ M.map (Int.castRingHom B)) (t.lie_geckRootIntMatrix ht i)
  simp only [Ring.lie_def, Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.diagonal_map (map_zero _)] at h
  simpa only [Ring.lie_def, Int.coe_castRingHom, Function.comp_def, zsmul_one] using h

/-- The tangent image of the integral Geck weight torus is spanned by the brackets of the
numbered opposite-root vectors. This does not assume injectivity of its differential. -/
theorem range_derivationCompLieHom_geckWeightTorusIntegralCoordinateMap_eq_span :
    LinearMap.range (derivationCompLieHom (B := B)
        (t.geckWeightTorusIntegralCoordinateMap ht).hom).toLinearMap =
      Submodule.span B (Set.range (fun i : Fin t.rank ↦
        ⁅t.geckRootVector ht (B := B) (.inl i), t.geckRootVector ht (B := B) (.inr i)⁆)) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [lie_geckRootVector_eq_derivationComp_geckCorootCocharacter,
    geckCorootCocharacter_def, derivationCompLieHom_apply]

end

end TauCeti.DynkinType
