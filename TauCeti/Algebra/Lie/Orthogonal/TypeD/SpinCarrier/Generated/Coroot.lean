/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.WeightTorus
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent

/-!
# Simple-coroot differentials of the generated type-D spin group

Evaluation of a fundamental-weight coordinate defines a numbered cocharacter through the
weight torus of the ground-ring-generated full-spin group. Its differential is the diagonal
matrix of the corresponding spin weights. These differentials form a basis of the toral
tangent image over every commutative coefficient algebra, including in characteristic two.

The cocharacters are identified with the simple coroots of the named simply connected root
datum. No maximality of the torus or identification with an independently pinned group scheme
is asserted. The generated group is not identified with the specialization of the integral
toral closure either; constructions transfer between these groups only along a proved
identification. In particular, the integral carrier's Cartan vectors are not silently used as
tangent vectors of the generated group.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.

The cocharacter and tangent-basis interface follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot` and the integral type-D calculation in
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Coroot`. The matrix formula uses the
general represented weight-torus differential.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier

noncomputable section

universe u v

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The numbered simple coroot, obtained by evaluating a fundamental-weight coordinate on
the torus generator of the generated full-spin group. -/
def generatedCorootCocharacter (i : Fin n) :
    generatedCoordinateHopfAlgebra n hn R →ₐc[R] LaurentPolynomial R :=
  (generatedWeightTorusCoordinateMap n hn R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The cocharacter is induced by evaluation at its fundamental-weight coordinate. -/
theorem generatedCorootCocharacter_def (i : Fin n) :
    generatedCorootCocharacter n hn R i =
      (generatedWeightTorusCoordinateMap n hn R).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- These cocharacters are the simple coroots of the named simply connected type-D datum,
not those of an adjoint or half-spin form. -/
theorem generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex (i : Fin n) :
    generatedCorootCocharacter n hn R i =
      (generatedWeightTorusCoordinateMap n hn R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          (((DynkinType.D n).simplyConnectedRootDatum (DynkinType.valid_D.mpr hn)).coroot
            ((DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i))) := by
  rw [generatedCorootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  exact (SplitTorus.cocharEquiv_applyAddHom i).trans
    ((DynkinType.D n).coroot_simpleIndex (DynkinType.valid_D.mpr hn) i).symm

/-- A simple-coroot differential is the diagonal matrix of its spin-weight pairings times
its multiplicative tangent parameter, over any commutative coefficient algebra. -/
@[simp]
theorem tangentMatrix_derivationComp_generatedCorootCocharacter (i : Fin n)
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (generatedCoordinateMap n hn R).hom
          (derivationComp (generatedCorootCocharacter n hn R i) d)) =
      Matrix.diagonal (fun a ↦ basisWeight n a i • MultiplicativeGroup.tangentLinearEquiv d) := by
  have hπ : (generatedWeightTorusCoordinateMap n hn R).hom.comp
      (generatedCoordinateMap n hn R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) (basisWeight n) := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [generatedCorootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  simp

/-- The numbered Cartan vector: the simple-coroot differential at the unit tangent vector. -/
def generatedCartanVector (i : Fin n) :
    Derivation R (generatedCoordinateHopfAlgebra n hn R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra n hn R) B) :=
  derivationComp (generatedCorootCocharacter n hn R i)
    ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1)

/-- The Cartan vector uses the tangent parameter normalized to one. -/
theorem generatedCartanVector_def (i : Fin n) :
    generatedCartanVector n hn R (B := B) i =
      derivationComp (generatedCorootCocharacter n hn R i)
        ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1) :=
  (rfl)

/-- The Cartan vector has the integral spin weights as diagonal entries. -/
@[simp]
theorem tangentMatrix_generatedCartanVector (i : Fin n) :
    GeneralLinear.tangentMatrix (dimension n)
        (derivationComp (generatedCoordinateMap n hn R).hom
          (generatedCartanVector n hn R (B := B) i)) =
      Matrix.diagonal (fun a ↦ (basisWeight n a i : B)) := by
  rw [generatedCartanVector_def, tangentMatrix_derivationComp_generatedCorootCocharacter,
    LinearEquiv.apply_symm_apply]
  simp only [zsmul_eq_mul, mul_one]

/-- The coordinate cocharacter differential is the numbered Cartan vector. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter (i : Fin n) :
    derivationCompLieHom
        ((generatedWeightTorusCoordinateMap n hn R).hom.cocharacter
          (Finsupp.applyAddHom i).toMultiplicative)
        ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1) =
      generatedCartanVector n hn R (B := B) i := by
  rw [derivationCompLieHom_apply, generatedCartanVector_def, generatedCorootCocharacter_def]

/-- The differential of the torus generator sends its coordinate tangent basis to the
numbered Cartan vectors. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis (i : Fin n) :
    derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n hn R).hom
        (SplitTorus.tangentBasis (R := R) (B := B) i) =
      generatedCartanVector n hn R (B := B) i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter]

/-- The toral tangent image is exactly the span of the numbered Cartan vectors. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n hn R).hom).toLinearMap =
      Submodule.span B (Set.range (generatedCartanVector n hn R (B := B))) := by
  simpa only [derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter n hn R
    (B := B)] using
    SplitTorus.range_derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n hn R).hom

/-- Cartan vectors are independent over every commutative coefficient algebra, including in
characteristic two, because the full-spin weights span the character lattice. -/
theorem linearIndependent_generatedCartanVector :
    LinearIndependent B (generatedCartanVector n hn R (B := B)) := by
  simpa only [derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter n hn R
    (B := B)] using
    SplitTorus.linearIndependent_derivationCompLieHom_cocharacter (B := B)
      (generatedWeightTorusCoordinateMap n hn R).hom
      (derivationCompLieHom_generatedWeightTorusCoordinateMap_injective n hn R B)

/-- The Cartan vectors form a basis of their span, the toral tangent image. -/
def generatedCartanBasis :
    Module.Basis (Fin n) B
      (Submodule.span B (Set.range (generatedCartanVector n hn R (B := B)))) :=
  Module.Basis.span (linearIndependent_generatedCartanVector n hn R)

/-- Including a Cartan basis vector into the tangent algebra recovers its numbered vector. -/
@[simp]
theorem coe_generatedCartanBasis (i : Fin n) :
    (generatedCartanBasis n hn R (B := B) i :
      Derivation R (generatedCoordinateHopfAlgebra n hn R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra n hn R) B)) =
      generatedCartanVector n hn R (B := B) i :=
  Module.Basis.coe_span_apply (linearIndependent_generatedCartanVector n hn R) i

end

end TauCeti.TypeDSpinCarrier
