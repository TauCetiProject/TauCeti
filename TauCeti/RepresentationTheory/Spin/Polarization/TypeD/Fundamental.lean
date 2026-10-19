/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Lie.HighestWeight.Irreducible
public import TauCeti.Algebra.Lie.HighestWeight.Verma
import TauCeti.RepresentationTheory.Spin.Polarization.Irreducible
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.HighestWeight

/-!
# The type-D half-spin fundamental representations

The two half-spin modules of the split type-`Dₙ` Lie algebra are the irreducible highest-weight
modules at the two fork nodes. The all-coordinate exterior vector has terminal fork weight, while
erasing its final coordinate gives the penultimate fork weight. Their exterior degrees determine
which half-spin module contains them: in even rank the terminal weight belongs to `S⁺` and the
penultimate weight to `S⁻`; in odd rank the assignment is reversed.

This file packages those identifications as Lie-module equivalences with the canonical irreducible
quotients of the corresponding Verma modules. The equivalences are noncanonical, so the results
assert their existence. The source irreducibility is supplied by the Clifford action, and the
identification itself uses uniqueness of irreducible highest-weight modules.

## Main results

* `nonempty_lieModuleEquiv_typeDSpinPlus_irreducibleQuotient_terminal_of_even`
  identifies `S⁺` with the terminal-fork irreducible in even rank.
* `nonempty_lieModuleEquiv_typeDSpinMinus_irreducibleQuotient_terminal_of_odd`
  identifies `S⁻` with the terminal-fork irreducible in odd rank.
* `nonempty_lieModuleEquiv_typeDSpinPlus_irreducibleQuotient_penultimate_of_odd`
  identifies `S⁺` with the penultimate-fork irreducible in odd rank.
* `nonempty_lieModuleEquiv_typeDSpinMinus_irreducibleQuotient_penultimate_of_even`
  identifies `S⁻` with the penultimate-fork irreducible in even rank.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
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
  {n : ℕ} (b : Module.Basis (Fin n) K P.W) [Invertible (2 : K)]

/-- In even rank, the positive half-spin module is the irreducible highest-weight module at the
terminal fork node. -/
theorem nonempty_lieModuleEquiv_typeDSpinPlus_irreducibleQuotient_terminal_of_even
    (hn : 4 ≤ n) (hline : P.line = ⊥) (heven : Even n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    Nonempty (spinPlus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD (Fin n) K⁆
      irreducibleQuotient (TypeDStd.lieBasis (K := K) n hn).base
        ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
          (⟨n - 1, by omega⟩ : Fin n))) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieModule.IsIrreducible K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    P.isIrreducible_typeDSpinPlusLieRep b hline
  exact nonempty_lieModuleEquiv_of_isHighestWeightVector
    (P.isHighestWeightVector_typeDSpinPlusLieRep_exteriorBasis_univ_of_even b hn hline heven)
    (isHighestWeightVector_irreducibleQuotientGenerator _ _)

/-- In odd rank, the negative half-spin module is the irreducible highest-weight module at the
terminal fork node. -/
theorem nonempty_lieModuleEquiv_typeDSpinMinus_irreducibleQuotient_terminal_of_odd
    (hn : 4 ≤ n) (hline : P.line = ⊥) (hodd : Odd n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    Nonempty (spinMinus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD (Fin n) K⁆
      irreducibleQuotient (TypeDStd.lieBasis (K := K) n hn).base
        ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
          (⟨n - 1, by omega⟩ : Fin n))) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  have hW : P.W ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    let i : Fin n := ⟨0, by omega⟩
    exact ⟨b i, (b i).property,
      fun h => Module.Basis.ne_zero b i (Subtype.ext h)⟩
  let _ : LieModule.IsIrreducible K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    P.isIrreducible_typeDSpinMinusLieRep b hline hW
  exact nonempty_lieModuleEquiv_of_isHighestWeightVector
    (P.isHighestWeightVector_typeDSpinMinusLieRep_exteriorBasis_univ_of_odd b hn hline hodd)
    (isHighestWeightVector_irreducibleQuotientGenerator _ _)

/-- In odd rank, the positive half-spin module is the irreducible highest-weight module at the
penultimate fork node. -/
theorem nonempty_lieModuleEquiv_typeDSpinPlus_irreducibleQuotient_penultimate_of_odd
    (hn : 4 ≤ n) (hline : P.line = ⊥) (hodd : Odd n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    Nonempty (spinPlus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD (Fin n) K⁆
      irreducibleQuotient (TypeDStd.lieBasis (K := K) n hn).base
        ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
          (⟨n - 2, by omega⟩ : Fin n))) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieModule.IsIrreducible K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    P.isIrreducible_typeDSpinPlusLieRep b hline
  exact nonempty_lieModuleEquiv_of_isHighestWeightVector
    (P.isHighestWeightVector_typeDSpinPlusLieRep_exteriorBasis_univ_erase_last_of_odd
      b hn hline hodd)
    (isHighestWeightVector_irreducibleQuotientGenerator _ _)

/-- In even rank, the negative half-spin module is the irreducible highest-weight module at the
penultimate fork node. -/
theorem nonempty_lieModuleEquiv_typeDSpinMinus_irreducibleQuotient_penultimate_of_even
    (hn : 4 ≤ n) (hline : P.line = ⊥) (heven : Even n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    Nonempty (spinMinus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD (Fin n) K⁆
      irreducibleQuotient (TypeDStd.lieBasis (K := K) n hn).base
        ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
          (⟨n - 2, by omega⟩ : Fin n))) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  have hW : P.W ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    let i : Fin n := ⟨0, by omega⟩
    exact ⟨b i, (b i).property,
      fun h => Module.Basis.ne_zero b i (Subtype.ext h)⟩
  let _ : LieModule.IsIrreducible K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    P.isIrreducible_typeDSpinMinusLieRep b hline hW
  exact nonempty_lieModuleEquiv_of_isHighestWeightVector
    (P.isHighestWeightVector_typeDSpinMinusLieRep_exteriorBasis_univ_erase_last_of_even
      b hn hline heven)
    (isHighestWeightVector_irreducibleQuotientGenerator _ _)

end TauCeti.SpinPolarizationData
