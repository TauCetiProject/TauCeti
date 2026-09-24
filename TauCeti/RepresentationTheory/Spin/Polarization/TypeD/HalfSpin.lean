/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Split
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Weight

/-!
# Half-spin parity in the split type-D model

The split type-`D` spinor model has two distinguished exterior-basis vectors: the vector with every
coordinate occupied and the vector obtained by erasing the final coordinate.  The generic
half-spin API identifies the summand of an exterior-basis vector from the parity of its degree.
This file records that identification for those two vectors, so their Cartan weights and their
half-spin summands can be used together by the highest-weight construction.

The four equivalences below are the only specialization needed: the all-coordinate vector lies in
the even or odd summand according to the parity of `n`, while erasing the final coordinate flips
that parity.  The index bound is only needed to form the final element of `Fin n`.

The conventions agree with the parity decomposition of the exterior algebra in Fulton and Harris,
*Representation Theory: A First Course*, §20.2.
-/

public section

open CliffordAlgebra

namespace TauCeti

/-- The all-coordinate split type-`D` basis vector lies in `S⁺` exactly when the rank is even. -/
theorem typeDSplitBasis_mem_spinPlus_univ_iff_even (n : ℕ) :
    (typeDSplitBasis n).ExteriorAlgebra (Finset.univ : Finset (Fin n)) ∈
      spinPlus _ (typeDSplitPolarization n) ↔ Even n := by
  rw [basis_mem_spinPlus_iff]
  simp

/-- The all-coordinate split type-`D` basis vector lies in `S⁻` exactly when the rank is odd. -/
theorem typeDSplitBasis_mem_spinMinus_univ_iff_odd (n : ℕ) :
    (typeDSplitBasis n).ExteriorAlgebra (Finset.univ : Finset (Fin n)) ∈
      spinMinus _ (typeDSplitPolarization n) ↔ Odd n := by
  rw [basis_mem_spinMinus_iff]
  simp

/-- Erasing the final coordinate puts the split type-`D` basis vector in `S⁺` exactly when the
rank is odd. -/
theorem typeDSplitBasis_mem_spinPlus_univ_erase_last_iff_odd {n : ℕ} (hn : 1 ≤ n) :
    (typeDSplitBasis n).ExteriorAlgebra
        ((Finset.univ : Finset (Fin n)).erase (⟨n - 1, by omega⟩ : Fin n)) ∈
      spinPlus _ (typeDSplitPolarization n) ↔ Odd n := by
  rw [basis_mem_spinPlus_iff]
  have hlast : (⟨n - 1, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := by simp
  rw [Finset.card_erase_of_mem hlast, Finset.card_univ, Fintype.card_fin]
  rw [Nat.even_sub (by omega)]
  simp

/-- Erasing the final coordinate puts the split type-`D` basis vector in `S⁻` exactly when the
rank is even. -/
theorem typeDSplitBasis_mem_spinMinus_univ_erase_last_iff_even {n : ℕ} (hn : 1 ≤ n) :
    (typeDSplitBasis n).ExteriorAlgebra
        ((Finset.univ : Finset (Fin n)).erase (⟨n - 1, by omega⟩ : Fin n)) ∈
      spinMinus _ (typeDSplitPolarization n) ↔ Even n := by
  rw [basis_mem_spinMinus_iff]
  have hlast : (⟨n - 1, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := by simp
  rw [Finset.card_erase_of_mem hlast, Finset.card_univ, Fintype.card_fin]
  rw [Nat.odd_sub (by omega)]
  simp

end TauCeti
