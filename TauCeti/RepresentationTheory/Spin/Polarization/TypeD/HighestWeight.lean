/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Cartan
public import TauCeti.Algebra.Lie.HighestWeight.Basis
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Killing
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Weight
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Borel

/-!
# Highest weights of the type-D half-spin representations

For the standard split type-`Dₙ` Lie basis, the all-coordinate exterior vector and the vector
obtained by erasing the final coordinate are highest-weight vectors. Their weights are the dual
basis vectors at the terminal and penultimate fork nodes, respectively. Thus they are the two
spin fundamental weights in Bourbaki numbering.

The parity of `n` determines which restricted half-spin representation contains each vector. The
all-coordinate vector belongs to `S⁺` in even rank and to `S⁻` in odd rank; erasing one coordinate
reverses the assignment. The four restricted theorems below record this convention explicitly,
so an application cannot exchange the fork weights by silently choosing a parity convention.

## Main results

* `TauCeti.typeDWeightEquiv_spinWeight_apply_cartanGenerator` compares the orthonormal
  sign-vector functional with its integral coordinates on the numbered simple coroots.
* `TauCeti.SpinPolarizationData.isHighestWeightVector_typeDSpinLieRep_exteriorBasis_univ` and
  its `univ_erase_last` counterpart exhibit the two fork highest vectors in the full spin module.
* The four `typeDSpinPlusLieRep` and `typeDSpinMinusLieRep` variants exhibit the same vectors in
  the parity summand selected by the rank.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
-/

public section

open CliffordAlgebra LieAlgebra LieModule Module

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

/-! ## Fork weights in the concrete Cartan -/

section CommRing

variable {K : Type u} [CommRing K] [Invertible (2 : K)] {n : ℕ}

/-- Evaluating a spin sign-vector functional on a numbered type-`D` Cartan generator gives its
corresponding integral fundamental-weight coordinate. -/
@[simp 1100]
theorem typeDWeightEquiv_spinWeight_apply_cartanGenerator
    (hn : 4 ≤ n) (s : Finset (Fin n)) (i : Fin n) :
    typeDWeightEquiv (spinWeight K s)
        ⟨TypeDStd.cartanGenerator n hn i,
          TypeDStd.cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ =
      algebraMap ℤ K (DynkinType.typeDSpinWeight s i) := by
  rw [typeDWeightEquiv_apply, TypeDStd.val_cartanGenerator,
    DynkinType.algebraMap_typeDSpinWeight_eq_dotProduct hn]
  simp only [typeDDiagonalMatrix_apply, typeDDiagonalValue_inl, eq_self, ite_true]
  simp [dotProduct]

end CommRing

section Field

variable {K : Type u} [Field K] [Invertible (2 : K)] {n : ℕ}

private theorem typeDWeightEquiv_spinWeight_eq_dualBasis
    (hn : 4 ≤ n) (s : Finset (Fin n)) (j : Fin n)
    (hs : DynkinType.typeDSpinWeight s = Pi.single j 1) :
    typeDWeightEquiv (spinWeight K s) =
      (TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis j := by
  apply (TypeDStd.lieBasis (K := K) n hn).cartanBasis.ext
  intro i
  have hcartan : (TypeDStd.lieBasis (K := K) n hn).cartanBasis i =
      ⟨TypeDStd.cartanGenerator n hn i,
        TypeDStd.cartanGenerator_mem_typeDDiagonalCartan n hn i⟩ := by
    apply Subtype.ext
    simp
  rw [Module.Basis.dualBasis_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  rw [hcartan, typeDWeightEquiv_spinWeight_apply_cartanGenerator hn, hs, Pi.single_apply]
  simp

/-- The all-coordinate spin weight is the dual Cartan basis vector at the terminal fork node. -/
theorem typeDWeightEquiv_spinWeight_univ (hn : 4 ≤ n) :
    typeDWeightEquiv (spinWeight K (Finset.univ : Finset (Fin n))) =
      (TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 1, by omega⟩ : Fin n) := by
  apply typeDWeightEquiv_spinWeight_eq_dualBasis hn
  exact DynkinType.typeDSpinWeight_univ_eq_single (by omega)

/-- Erasing the final coordinate gives the dual Cartan basis vector at the penultimate fork
node. -/
theorem typeDWeightEquiv_spinWeight_univ_erase_last (hn : 4 ≤ n) :
    typeDWeightEquiv
        (spinWeight K ((Finset.univ : Finset (Fin n)).erase
          (⟨n - 1, by omega⟩ : Fin n))) =
      (TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 2, by omega⟩ : Fin n) := by
  apply typeDWeightEquiv_spinWeight_eq_dualBasis hn
  exact DynkinType.typeDSpinWeight_univ_erase_last_eq_single (by omega)

end Field

namespace SpinPolarizationData

/-! ## Highest vectors in the full spin module -/

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {n : ℕ} (b : Module.Basis (Fin n) K P.W) [Invertible (2 : K)]

/-- The all-coordinate exterior vector is a highest-weight vector of terminal fork weight for the
full type-`D` spin representation. -/
theorem isHighestWeightVector_typeDSpinLieRep_exteriorBasis_univ
    (hn : 4 ≤ n) (hline : P.line = ⊥) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
    IsHighestWeightVector (TypeDStd.lieBasis (K := K) n hn).base
      ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 1, by omega⟩ : Fin n))
      (b.ExteriorAlgebra (Finset.univ : Finset (Fin n))) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
  rw [(TypeDStd.lieBasis (K := K) n hn).isHighestWeightVector_iff_forall_e]
  refine ⟨(b.ExteriorAlgebra).ne_zero _, ?_, ?_⟩
  · intro A
    rw [← typeDWeightEquiv_spinWeight_univ (K := K) hn]
    exact P.typeDSpinLieRep_apply_cartan_exteriorBasis b hline A _
  · intro i
    exact P.typeDSpinLieRep_lieBasis_e_exteriorBasis_univ_eq_zero b hn hline i

/-- The exterior vector obtained by erasing the final coordinate is a highest-weight vector of
penultimate fork weight for the full type-`D` spin representation. -/
theorem isHighestWeightVector_typeDSpinLieRep_exteriorBasis_univ_erase_last
    (hn : 4 ≤ n) (hline : P.line = ⊥) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
    IsHighestWeightVector (TypeDStd.lieBasis (K := K) n hn).base
      ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 2, by omega⟩ : Fin n))
      (b.ExteriorAlgebra
        ((Finset.univ : Finset (Fin n)).erase (⟨n - 1, by omega⟩ : Fin n))) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
  rw [(TypeDStd.lieBasis (K := K) n hn).isHighestWeightVector_iff_forall_e]
  refine ⟨(b.ExteriorAlgebra).ne_zero _, ?_, ?_⟩
  · intro A
    rw [← typeDWeightEquiv_spinWeight_univ_erase_last (K := K) hn]
    exact P.typeDSpinLieRep_apply_cartan_exteriorBasis b hline A _
  · intro i
    exact P.typeDSpinLieRep_lieBasis_e_exteriorBasis_univ_erase_last_eq_zero b hn hline i

/-! ## Highest vectors in the half-spin modules -/

/-- In even rank, the all-coordinate vector is the terminal-fork highest vector in `S⁺`. -/
theorem isHighestWeightVector_typeDSpinPlusLieRep_exteriorBasis_univ_of_even
    (hn : 4 ≤ n) (hline : P.line = ⊥) (heven : Even n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    IsHighestWeightVector (TypeDStd.lieBasis (K := K) n hn).base
      ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 1, by omega⟩ : Fin n))
      (⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin n)),
        (basis_mem_spinPlus_iff P b _).mpr (by simpa using heven)⟩ : spinPlus Q P) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
  have hv := P.isHighestWeightVector_typeDSpinLieRep_exteriorBasis_univ b hn hline
  rw [isHighestWeightVector_iff] at hv ⊢
  refine ⟨fun hzero => hv.1 (congrArg Subtype.val hzero), fun x => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_smul]
    rw [P.coe_typeDSpinPlusLieRep_apply]
    exact hv.2.1 x
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_zero]
    rw [P.coe_typeDSpinPlusLieRep_apply]
    exact hv.2.2 x hx

/-- In odd rank, the all-coordinate vector is the terminal-fork highest vector in `S⁻`. -/
theorem isHighestWeightVector_typeDSpinMinusLieRep_exteriorBasis_univ_of_odd
    (hn : 4 ≤ n) (hline : P.line = ⊥) (hodd : Odd n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    IsHighestWeightVector (TypeDStd.lieBasis (K := K) n hn).base
      ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 1, by omega⟩ : Fin n))
      (⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin n)),
        (basis_mem_spinMinus_iff P b _).mpr (by simpa using hodd)⟩ : spinMinus Q P) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
  have hv := P.isHighestWeightVector_typeDSpinLieRep_exteriorBasis_univ b hn hline
  rw [isHighestWeightVector_iff] at hv ⊢
  refine ⟨fun hzero => hv.1 (congrArg Subtype.val hzero), fun x => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_smul]
    rw [P.coe_typeDSpinMinusLieRep_apply]
    exact hv.2.1 x
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_zero]
    rw [P.coe_typeDSpinMinusLieRep_apply]
    exact hv.2.2 x hx

/-- In odd rank, erasing the final coordinate gives the penultimate-fork highest vector in
`S⁺`. -/
theorem isHighestWeightVector_typeDSpinPlusLieRep_exteriorBasis_univ_erase_last_of_odd
    (hn : 4 ≤ n) (hline : P.line = ⊥) (hodd : Odd n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    IsHighestWeightVector (TypeDStd.lieBasis (K := K) n hn).base
      ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 2, by omega⟩ : Fin n))
      (⟨b.ExteriorAlgebra
          ((Finset.univ : Finset (Fin n)).erase (⟨n - 1, by omega⟩ : Fin n)),
        (basis_mem_spinMinus_iff_basis_erase_mem_spinPlus P b (Finset.mem_univ _)).mp
          ((basis_mem_spinMinus_iff P b _).mpr (by simpa using hodd))⟩ : spinPlus Q P) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinPlus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
  have hv := P.isHighestWeightVector_typeDSpinLieRep_exteriorBasis_univ_erase_last b hn hline
  rw [isHighestWeightVector_iff] at hv ⊢
  refine ⟨fun hzero => hv.1 (congrArg Subtype.val hzero), fun x => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_smul]
    rw [P.coe_typeDSpinPlusLieRep_apply]
    exact hv.2.1 x
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_zero]
    rw [P.coe_typeDSpinPlusLieRep_apply]
    exact hv.2.2 x hx

/-- In even rank, erasing the final coordinate gives the penultimate-fork highest vector in
`S⁻`. -/
theorem isHighestWeightVector_typeDSpinMinusLieRep_exteriorBasis_univ_erase_last_of_even
    (hn : 4 ≤ n) (hline : P.line = ⊥) (heven : Even n) :
    letI := TypeDStd.isKilling_typeD (K := K) n hn
    letI := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
    letI := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    IsHighestWeightVector (TypeDStd.lieBasis (K := K) n hn).base
      ((TypeDStd.lieBasis (K := K) n hn).cartanBasis.dualBasis
        (⟨n - 2, by omega⟩ : Fin n))
      (⟨b.ExteriorAlgebra
          ((Finset.univ : Finset (Fin n)).erase (⟨n - 1, by omega⟩ : Fin n)),
        (basis_mem_spinPlus_iff_basis_erase_mem_spinMinus P b (Finset.mem_univ _)).mp
          ((basis_mem_spinPlus_iff P b _).mpr (by simpa using heven))⟩ : spinMinus Q P) := by
  let _ := TypeDStd.isKilling_typeD (K := K) n hn
  let _ := (TypeDStd.lieBasis (K := K) n hn).isCartanSubalgebra
  let _ := (TypeDStd.lieBasis (K := K) n hn).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K) (spinMinus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeDSpinLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeDSpinLieRep b hline)
  have hv := P.isHighestWeightVector_typeDSpinLieRep_exteriorBasis_univ_erase_last b hn hline
  rw [isHighestWeightVector_iff] at hv ⊢
  refine ⟨fun hzero => hv.1 (congrArg Subtype.val hzero), fun x => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_smul]
    rw [P.coe_typeDSpinMinusLieRep_apply]
    exact hv.2.1 x
  · apply Subtype.ext
    simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, Submodule.coe_zero]
    rw [P.coe_typeDSpinMinusLieRep_apply]
    exact hv.2.2 x hx

end SpinPolarizationData
end TauCeti
