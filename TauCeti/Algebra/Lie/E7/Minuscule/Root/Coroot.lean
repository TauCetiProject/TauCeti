/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent.Map
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.Lie.E7.Minuscule.Basic
public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Coordinates
public import TauCeti.Algebra.Lie.Matrix.IntegralCast

/-!
# Carrier-independent E₇ coroot differentials

The weight torus determines the simple-coroot matrices in the minuscule representation.
For any represented bialgebra through which this torus factors, its coordinate cocharacters
have those same differentials. An injective tangent realization therefore identifies them
with any vectors having the prescribed Cartan matrices. The integral and generated E₇
carriers both use these calculations.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

public section

namespace TauCeti.E7Minuscule

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {R : Type*} [CommRing R]

/-- The integral Cartan matrix is the diagonal of the simple-coroot weight pairings. -/
theorem cartanMatrix_map_intCast_eq_diagonal_coroot' (ht : DynkinType.E7.Valid) (i : Fin 7) :
    (cartanMatrix i).map (Int.cast : ℤ → R) = Matrix.diagonal fun a ↦
      ((DynkinType.E7.simplyConnectedRootDatum ht).coroot'
        (DynkinType.E7.simpleIndex ht i) (DynkinType.e7MinusculeWeight a) : R) := by
  ext a b
  simp only [Matrix.map_apply, cartanMatrix_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [coroot'_simpleIndex_apply ht i]
  · simp

/-- Any matrix realization sending opposite root vectors to their integral matrices sends
 their bracket to the Cartan matrix. -/
theorem map_lie_eq_cartanMatrix {L : Type*} [LieRing L] [LieAlgebra R L]
    (f : L →ₗ⁅R⁆ Matrix (Fin 56) (Fin 56) R) (x y : L) (i : Fin 7)
    (hx : f x = (raisingMatrix i).map (Int.cast : ℤ → R))
    (hy : f y = (loweringMatrix i).map (Int.cast : ℤ → R)) :
    f ⁅x, y⁆ = (cartanMatrix i).map (Int.cast : ℤ → R) := by
  rw [LieHom.map_lie, hx, hy]
  simpa only [Function.comp_apply, matrixIntCastLieHom_eq_map] using
    (isSerreSystem.map (matrixIntCastLieHom R)).lie_E_F_self i

variable {H : Type*} [CommRing H] [Bialgebra R H]
  (q : GeneralLinear.coordinateHopfAlgebra R 56 →ₐc[R] H)
  (τ : H →ₐc[R] MonoidAlgebra R (Multiplicative (Fin 7 →₀ ℤ)))
  (hτ : τ.comp q = GeneralLinear.weightTorusCoordinateBialgHom (S := R)
    DynkinType.e7MinusculeWeight)

include hτ

/-- In any carrier of the minuscule weight torus, the coordinate-coroot differential has
 the diagonal matrix of the named simple-coroot pairings. -/
theorem generalLinearTangentMatrixLieHom_derivationComp_cocharacter_applyAddHom
    (ht : DynkinType.E7.Valid) (i : Fin 7) :
    GeneralLinear.tangentMatrixLieHom q
        (derivationComp (τ.cocharacter (Finsupp.applyAddHom i).toMultiplicative)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R))) =
      Matrix.diagonal fun a ↦
        ((DynkinType.E7.simplyConnectedRootDatum ht).coroot'
          (DynkinType.E7.simpleIndex ht i) (DynkinType.e7MinusculeWeight a) : R) := by
  rw [GeneralLinear.tangentMatrixLieHom_apply,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hτ]
  congr 1
  ext a
  rw [coroot'_simpleIndex_apply ht i]
  simp

end

end TauCeti.E7Minuscule
