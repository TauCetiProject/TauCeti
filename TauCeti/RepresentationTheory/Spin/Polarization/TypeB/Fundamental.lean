/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Lie.HighestWeight.Irreducible
public import TauCeti.Algebra.Lie.HighestWeight.Verma
import TauCeti.RepresentationTheory.Spin.Polarization.Irreducible
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.LastFundamentalWeight

/-!
# The type-B spin fundamental representation

The spin module of the split odd orthogonal Lie algebra is the irreducible highest-weight module
at the terminal short node. More precisely, for the Cartan, Borel, and abstract root-system base
fixed by `TauCeti.typeBLieBasis`, the module `ExteriorAlgebra K P.W` is isomorphic to the canonical
irreducible quotient `L(ωₗ)` of the Verma module whose weight is the last vector of the dual simple-
coroot basis.

The all-coordinate exterior spinor supplies the highest-weight vector. Its Cartan weight is the
last fundamental weight, and every positive simple-root generator annihilates it; the Lie-basis
Borel comparison promotes those concrete equations to the abstract highest-weight predicate.
Irreducibility of the spin module then makes the identification with `L(ωₗ)` unique up to a
noncanonical Lie-module equivalence.

## Main result

* `TauCeti.SpinPolarizationData.nonempty_lieModuleEquiv_typeBSpin_irreducibleQuotient`
  identifies the type-`B` spin module with `L(ωₗ)`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
-/

public section

open CliffordAlgebra LieAlgebra LieModule Module

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {n : ℕ} (b : Module.Basis (Fin (n + 1)) K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]
  [LieModule.IsTriangularizable K
    (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
    (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1) → K)]

/-- **The type-`B` spin module is the irreducible highest-weight module `L(ωₗ)`.** Here `ωₗ`
is the dual Cartan basis vector at the terminal short node of `typeBLieBasis`, so the equivalence
uses its compatible Borel and abstract type-`B` root-system base. -/
theorem nonempty_lieModuleEquiv_typeBSpin_irreducibleQuotient :
    letI := isKilling_typeB (K := K) (ι := Fin (n + 1))
    letI := (typeBLieBasis (K := K) n).isCartanSubalgebra
    letI := (typeBLieBasis (K := K) n).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    Nonempty (ExteriorAlgebra K P.W ≃ₗ⁅K, LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K⁆
      irreducibleQuotient (typeBLieBasis (K := K) n).base
        ((typeBLieBasis (K := K) n).cartanBasis.dualBasis (Fin.last n))) := by
  let _ := isKilling_typeB (K := K) (ι := Fin (n + 1))
  let _ := (typeBLieBasis (K := K) n).isCartanSubalgebra
  let _ := (typeBLieBasis (K := K) n).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule.IsIrreducible K
      (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K) (ExteriorAlgebra K P.W) :=
    P.isIrreducible_typeBSpinLieRep b z hz
  exact nonempty_lieModuleEquiv_of_isHighestWeightVector
    (P.isHighestWeightVector_typeBSpinLieRep_exteriorBasis_univ b z hz)
    (isHighestWeightVector_irreducibleQuotientGenerator _ _)

end TauCeti.SpinPolarizationData
