/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.SpinWeight
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Simple root operators on the type-D spin basis

A positive simple root operator sends a spin basis vector of simple-coroot weight `-1` to
its reflected basis vector, up to an integral unit. A negative operator does the same at
weight `1`. At a chain node this exchanges an occupied and an unoccupied coordinate;
at the fork node it creates or contracts the last two coordinates. Thus these moves preserve
half-spin parity and connect the weight lines within each half-spin constituent.

The signs are units of `ℤ`, so these formulas remain effective after reduction in any
characteristic. They supply the root moves needed to recognize invariant subspaces in the
spin representation of the corresponding integral matrix carrier.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, §20.2.
* The proof follows the creation and contraction calculations in
  `TauCeti.TypeBSpinCarrier.exists_rep_rootGenerator_inl_exteriorBasis` and
  `TauCeti.TypeBSpinCarrier.exists_rep_rootGenerator_inr_exteriorBasis`.
-/

public section

namespace TauCeti.SpinPolarizationData

open CliffordAlgebra
open TauCeti.DynkinType

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {n : ℕ} (b : Module.Basis (Fin n) ℚ P.W) (hn : 4 ≤ n)

/-- A positive simple-root operator carries every spin basis vector of simple-coroot weight
`-1` to its simple reflection, with coefficient an integral unit. -/
theorem exists_typeDSpinRep_serreE_exteriorBasis (i : Fin n) (s : Finset (Fin n))
    (hs : typeDSpinWeight s i = -1) :
    ∃ c : ℤˣ, P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra s) = c • b.ExteriorAlgebra (typeDSpinReflection i s) := by
  classical
  by_cases hi : (i : ℕ) + 1 < n
  · let q : Fin n := ⟨(i : ℕ) + 1, hi⟩
    have hmem : i ∉ s ∧ q ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      split_ifs at hs <;> simp_all [q]
    have hrefl : typeDSpinReflection i s = insert i (s.erase q) := by
      ext x
      rw [mem_typeDSpinReflection_of_add_one_lt hi]
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases hxi : x = i <;> by_cases hxq : x = q <;>
        simp_all [Equiv.swap_apply_def, q]
    rw [P.typeDSpinRep_serreE_eq_spinAction b hn, P.typeDSimpleRootBivector_def b,
      dite_eq_left hi, map_mul, Module.End.mul_apply, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector, TauCeti.spinAction_ι_wedge,
      TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left hmem.2, mul_smul_comm,
      TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_right (by simp [hmem.1]), smul_smul, hrefl]
    exact ⟨_, rfl⟩
  · let p : Fin n := ⟨n - 2, by omega⟩
    let q : Fin n := ⟨n - 1, by omega⟩
    have hiq : i = q := Fin.ext (by have := i.isLt; dsimp [q]; omega)
    have hip : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) = p :=
      Fin.ext (by have := i.isLt; dsimp [p]; omega)
    have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
    have hmem : p ∉ s ∧ q ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi, hip, hiq] at hs
      split_ifs at hs <;> simp_all
    have hrefl : typeDSpinReflection i s = insert p (insert q s) := by
      ext x
      rw [mem_typeDSpinReflection_of_not_add_one_lt hi, hip, hiq]
      simp only [Finset.mem_insert]
      by_cases hxp : x = p <;> by_cases hxq : x = q <;>
        simp_all [Equiv.swap_apply_def]
    rw [P.typeDSpinRep_serreE_eq_spinAction b hn, P.typeDSimpleRootBivector_def b,
      dite_eq_right hi, map_mul, Module.End.mul_apply, TauCeti.spinAction_ι_wedge,
      TauCeti.spinAction_ι_wedge, TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_right hmem.2,
      mul_smul_comm, TauCeti.ExteriorAlgebra.ι_mul_basis,
      ite_eq_right (by
        rw [Finset.mem_insert]; exact not_or.mpr ⟨hpq, hmem.1⟩), smul_smul, hrefl]
    exact ⟨_, rfl⟩

/-- A negative simple-root operator carries every spin basis vector of simple-coroot weight
`1` to its simple reflection, with coefficient an integral unit. -/
theorem exists_typeDSpinRep_serreF_exteriorBasis (i : Fin n) (s : Finset (Fin n))
    (hs : typeDSpinWeight s i = 1) :
    ∃ c : ℤˣ, P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra s) = c • b.ExteriorAlgebra (typeDSpinReflection i s) := by
  classical
  by_cases hi : (i : ℕ) + 1 < n
  · let q : Fin n := ⟨(i : ℕ) + 1, hi⟩
    have hmem : i ∈ s ∧ q ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      split_ifs at hs <;> simp_all [q]
    have hrefl : typeDSpinReflection i s = insert q (s.erase i) := by
      ext x
      rw [mem_typeDSpinReflection_of_add_one_lt hi]
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases hxi : x = i <;> by_cases hxq : x = q <;>
        simp_all [Equiv.swap_apply_def, q]
    rw [P.typeDSpinRep_serreF_eq_spinAction b hn, P.typeDSimpleNegativeRootBivector_def b,
      dite_eq_left hi, map_mul, Module.End.mul_apply, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector, TauCeti.spinAction_ι_wedge,
      TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left hmem.1, mul_smul_comm,
      TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_right (by
        rw [Finset.mem_erase]; exact fun h => hmem.2 h.2), smul_smul, hrefl]
    exact ⟨_, rfl⟩
  · let p : Fin n := ⟨n - 2, by omega⟩
    let q : Fin n := ⟨n - 1, by omega⟩
    have hiq : i = q := Fin.ext (by have := i.isLt; dsimp [q]; omega)
    have hip : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) = p :=
      Fin.ext (by have := i.isLt; dsimp [p]; omega)
    have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
    have hmem : p ∈ s ∧ q ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi, hip, hiq] at hs
      split_ifs at hs <;> simp_all
    have hrefl : typeDSpinReflection i s = (s.erase p).erase q := by
      ext x
      rw [mem_typeDSpinReflection_of_not_add_one_lt hi, hip, hiq]
      simp only [Finset.mem_erase]
      by_cases hxp : x = p <;> by_cases hxq : x = q <;>
        simp_all [Equiv.swap_apply_def]
    rw [P.typeDSpinRep_serreF_eq_spinAction b hn, P.typeDSimpleNegativeRootBivector_def b,
      dite_eq_right hi, map_mul, Module.End.mul_apply, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector, TauCeti.spinAction_ι_contract, P.pairingEquiv_dualVector,
      TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left hmem.1]
    simp only [Units.smul_def, map_zsmul]
    rw [TauCeti.ExteriorAlgebra.contractLeft_coord_basis,
      ite_eq_left (Finset.mem_erase.mpr ⟨hpq.symm, hmem.2⟩),
      hrefl]
    refine ⟨TauCeti.ExteriorAlgebra.basisEraseSign p s *
      TauCeti.ExteriorAlgebra.basisEraseSign q (s.erase p), ?_⟩
    simp only [Units.smul_def, smul_smul, Units.val_mul]
    rfl

end TauCeti.SpinPolarizationData
