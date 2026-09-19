/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Serre.Presentation
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootGenerators

/-!
# Comparing the matrix and Clifford type-D Serre realizations

An even polarization identifies the standard split orthogonal Lie algebra with the quadratic
Clifford Lie algebra. The two algebras already carry separately normalized type-`D` root and
coroot generators. This file proves that the equivalence identifies their complete Serre
realizations, not merely the individual matrices.

Consequently, the rational spin representation of the presented Lie algebra factors through the
explicit split orthogonal matrix algebra. This records the chain and fork signs in a single
equality of homomorphisms and makes the matrix carrier available to consumers of the existing
spin-action formulas.

## Main results

* `TauCeti.SpinPolarizationData.typeDQuadraticEquiv_comp_serreRepresentation`: the quadratic
  equivalence carries the matrix Serre realization to the Clifford realization.
* `TauCeti.SpinPolarizationData.typeDSpinSerreRepresentation_eq_comp_serreRepresentation`: the
  spin representation factors through the explicit matrix realization.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
-/

public section

open CliffordAlgebra

namespace TauCeti.SpinPolarizationData

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) [Invertible (2 : K)]
  {n : ℕ} (b : Module.Basis (Fin n) K P.W)

/-- **The quadratic equivalence identifies the matrix and Clifford type-`D` Serre
realizations.** This fixes the normalization simultaneously on all Cartan, positive, and negative
presented generators. -/
theorem typeDQuadraticEquiv_comp_serreRepresentation (hn : 4 ≤ n) (hline : P.line = ⊥) :
    (P.typeDQuadraticEquiv b hline).toLieHom.comp
        (TypeDStd.serreRepresentation n hn) =
      TauCeti.serreLift
        (P.isSerreSystem_typeDSimpleRootBivector_quadraticLieSubalgebra b hn) := by
  apply TauCeti.serre_hom_ext
  · intro i
    apply Subtype.ext
    simp
  · intro i
    apply Subtype.ext
    simp
  · intro i
    apply Subtype.ext
    simp

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type v} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (P : SpinPolarizationData Q)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ P.W)

/-- **The rational type-`D` spin representation factors through the explicit split orthogonal
matrix realization.** -/
theorem typeDSpinSerreRepresentation_eq_comp_serreRepresentation
    (hn : 4 ≤ n) (hline : P.line = ⊥) :
    P.typeDSpinSerreRepresentation b hn =
      (spinAction Q P).toLieHom.comp
        ((quadraticLieSubalgebra Q).incl.comp
          ((P.typeDQuadraticEquiv b hline).toLieHom.comp
            (TypeDStd.serreRepresentation n hn))) := by
  apply TauCeti.serre_hom_ext
  · intro i
    rw [P.typeDSpinSerreRepresentation_serreH]
    simp
  · intro i
    rw [P.typeDSpinSerreRepresentation_serreE]
    simp
  · intro i
    rw [P.typeDSpinSerreRepresentation_serreF]
    simp

end TauCeti.SpinPolarizationData
