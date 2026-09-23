/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.SpinWeight
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootGenerators

/-!
# Concrete type-D Cartan weights on spinors

The split orthogonal model and the Clifford polarization use different coordinates for the same
Cartan subalgebra.  This file records their common weight calculation: a simple-coroot bivector,
and hence the numbered matrix Cartan generator, acts on an exterior-basis spinor by the
corresponding integral type-D spin weight.  The arbitrary-field calculation factors the rational
specialization in `TypeD/KostantLattice.lean` and supplies the concrete Cartan-action bridge
needed when transporting highest-weight data between the orthogonal Lie algebra and the abstract
type-D root datum.

## Main declarations

* `SpinPolarizationData.spinAction_typeDQuadraticEquiv_cartanGenerator_basis`: the concrete
  numbered Cartan generator acts on each exterior-basis vector by its type-D spin weight.
* `SpinPolarizationData.spinAction_typeDSimpleCorootBivector_basis`: the corresponding reusable
  simple-coroot calculation over any field with invertible `2`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
-/

public section

namespace TauCeti.SpinPolarizationData

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {n : ℕ} (b : Module.Basis (Fin n) K P.W) [Invertible (2 : K)]

/-- A type-`D` simple-coroot bivector acts on an exterior-basis spinor by the corresponding
integral spin weight in the simply connected root datum. -/
theorem spinAction_typeDSimpleCorootBivector_basis
    (hn : 2 ≤ n) (i : Fin n) (s : Finset (Fin n)) :
    spinAction Q P (P.typeDSimpleCorootBivector b hn i) (b.ExteriorAlgebra s) =
      algebraMap ℤ K (DynkinType.typeDSpinWeight s i) • b.ExteriorAlgebra s := by
  rw [P.typeDSimpleCorootBivector_eq_diagonalBivector b hn i]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [dite_eq_left hnext, map_sub, LinearMap.sub_apply,
      P.spinAction_diagonalBivector_basis b, P.spinAction_diagonalBivector_basis b,
      ← sub_smul]
    have hwt := DynkinType.algebraMap_typeDSpinWeight_apply (K := K) s i
    rw [dite_eq_left hnext] at hwt
    exact (congrArg (fun z : K => z • b.ExteriorAlgebra s)
      hwt).symm
  · rw [dite_eq_right hnext, map_add, LinearMap.add_apply,
      P.spinAction_diagonalBivector_basis b, P.spinAction_diagonalBivector_basis b,
      ← add_smul]
    have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    have hprev :
        (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) =
          (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    have hspin : spinWeight K s i = spinWeight K s (⟨n - 1, by omega⟩ : Fin n) :=
      congrArg (spinWeight K s) hi
    have hwt := DynkinType.algebraMap_typeDSpinWeight_apply (K := K) s i
    rw [dite_eq_right hnext, hprev, hspin] at hwt
    simpa only [hprev, hspin] using
      (congrArg (fun z : K => z • b.ExteriorAlgebra s) hwt).symm

/-- The numbered type-`D` Cartan generator acts on an exterior-basis spinor by the corresponding
integral spin weight in the simply connected root datum. -/
theorem spinAction_typeDQuadraticEquiv_cartanGenerator_basis
    (hn : 4 ≤ n) (hline : P.line = ⊥) (i : Fin n) (s : Finset (Fin n)) :
    spinAction Q P
        (P.typeDQuadraticEquiv b hline (TypeDStd.cartanGenerator n hn i))
        (b.ExteriorAlgebra s) =
      algebraMap ℤ K (DynkinType.typeDSpinWeight s i) • b.ExteriorAlgebra s := by
  rw [P.typeDQuadraticEquiv_cartanGenerator b hn hline i]
  exact P.spinAction_typeDSimpleCorootBivector_basis b (by omega) i s

end TauCeti.SpinPolarizationData
