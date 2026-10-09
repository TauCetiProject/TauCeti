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
its reflected basis vector, with coefficient exactly one. A negative operator does the same at
weight `1`; both operators vanish on the other weight lines. At a chain node this exchanges an
occupied and an unoccupied coordinate, while at the fork node it creates or contracts the last
two coordinates. The two exterior shuffle signs coincide, so their product is one.

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

private theorem negOnePow_mul_self (m : ℕ) :
    ((-1 : ℤˣ) ^ m) * ((-1 : ℤˣ) ^ m) = 1 := by
  rw [← pow_two, ← pow_mul]
  simp

private theorem chainRaisingShuffleSign (i : Fin n) (s : Finset (Fin n))
    (hi : (i : ℕ) + 1 < n) (his : i ∉ s)
    (hjs : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ∈ s) :
    TauCeti.ExteriorAlgebra.basisEraseSign ⟨(i : ℕ) + 1, hi⟩ s *
        TauCeti.ExteriorAlgebra.basisEraseSign i
          (insert i (s.erase ⟨(i : ℕ) + 1, hi⟩)) = 1 := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt j s,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt i
      (insert i (s.erase j))]
  have hfilter : s.filter (fun x ↦ x < j) =
      (insert i (s.erase j)).filter (fun x ↦ x < i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, hxj⟩
      have hxi : x ≠ i := fun h ↦ his (h ▸ hxs)
      have hxival : x.val ≠ i.val := fun h ↦ hxi (Fin.ext h)
      refine ⟨Or.inr ⟨ne_of_lt hxj, hxs⟩, ?_⟩
      simp only [Fin.lt_def] at hxj ⊢
      dsimp [j] at hxj
      omega
    · rintro ⟨hxmem, hxi⟩
      rcases hxmem with rfl | ⟨_, hxs⟩
      · exact (lt_irrefl _ hxi).elim
      · refine ⟨hxs, lt_trans hxi ?_⟩
        simp [j, Fin.lt_def]
  rw [hfilter]
  exact negOnePow_mul_self _

private theorem chainLoweringShuffleSign (i : Fin n) (s : Finset (Fin n))
    (hi : (i : ℕ) + 1 < n) :
    TauCeti.ExteriorAlgebra.basisEraseSign i s *
        TauCeti.ExteriorAlgebra.basisEraseSign ⟨(i : ℕ) + 1, hi⟩
          (insert ⟨(i : ℕ) + 1, hi⟩ (s.erase i)) = 1 := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt i s,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt j
      (insert j (s.erase i))]
  have hfilter : s.filter (fun x ↦ x < i) =
      (insert j (s.erase i)).filter (fun x ↦ x < j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, hxi⟩
      refine ⟨Or.inr ⟨ne_of_lt hxi, hxs⟩, lt_trans hxi ?_⟩
      simp [j, Fin.lt_def]
    · rintro ⟨hxmem, hxj⟩
      rcases hxmem with rfl | ⟨hxi, hxs⟩
      · exact (lt_irrefl j hxj).elim
      · refine ⟨hxs, ?_⟩
        have hxival : x.val ≠ i.val := fun h ↦ hxi (Fin.ext h)
        simp only [Fin.lt_def] at hxj ⊢
        dsimp [j] at hxj
        omega
  rw [hfilter]
  exact negOnePow_mul_self _

private theorem forkRaisingShuffleSign (s : Finset (Fin n))
    (hp : (⟨n - 2, by omega⟩ : Fin n) ∉ s) :
    TauCeti.ExteriorAlgebra.basisEraseSign ⟨n - 1, by omega⟩
        (insert ⟨n - 1, by omega⟩ s) *
      TauCeti.ExteriorAlgebra.basisEraseSign ⟨n - 2, by omega⟩
        (insert ⟨n - 2, by omega⟩ (insert ⟨n - 1, by omega⟩ s)) = 1 := by
  let p : Fin n := ⟨n - 2, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hp' : p ∉ s := by simpa [p] using hp
  have hpq : p < q := by
    simp only [p, q, Fin.lt_def]
    omega
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt q (insert q s),
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt p
      (insert p (insert q s))]
  have hfilter : (insert q s).filter (fun x ↦ x < q) =
      (insert p (insert q s)).filter (fun x ↦ x < p) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hxmem, hxq⟩
      rcases hxmem with rfl | hxs
      · exact (lt_irrefl q hxq).elim
      · have hxp : x ≠ p := fun h ↦ hp' (h ▸ hxs)
        have hxpval : x.val ≠ p.val := fun h ↦ hxp (Fin.ext h)
        refine ⟨Or.inr (Or.inr hxs), ?_⟩
        simp only [Fin.lt_def] at hxq ⊢
        dsimp [p, q] at hxq hxpval ⊢
        omega
    · rintro ⟨hxmem, hxp⟩
      rcases hxmem with rfl | rfl | hxs
      · exact (lt_irrefl p hxp).elim
      · exact (not_lt_of_ge hpq.le hxp).elim
      · exact ⟨Or.inr hxs, lt_trans hxp hpq⟩
  rw [hfilter]
  exact negOnePow_mul_self _

private theorem forkLoweringShuffleSign (s : Finset (Fin n)) :
    TauCeti.ExteriorAlgebra.basisEraseSign ⟨n - 2, by omega⟩ s *
      TauCeti.ExteriorAlgebra.basisEraseSign ⟨n - 1, by omega⟩
        (s.erase ⟨n - 2, by omega⟩) = 1 := by
  let p : Fin n := ⟨n - 2, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p < q := by
    simp only [p, q, Fin.lt_def]
    omega
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt p s,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt q (s.erase p)]
  have hfilter : s.filter (fun x ↦ x < p) =
      (s.erase p).filter (fun x ↦ x < q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, hxp⟩
      exact ⟨⟨ne_of_lt hxp, hxs⟩, lt_trans hxp hpq⟩
    · rintro ⟨⟨hxp, hxs⟩, hxq⟩
      refine ⟨hxs, ?_⟩
      have hxpval : x.val ≠ p.val := fun h ↦ hxp (Fin.ext h)
      simp only [Fin.lt_def] at hxq ⊢
      dsimp [p, q] at hxq hxpval ⊢
      omega
  rw [hfilter]
  exact negOnePow_mul_self _

/-- A positive simple-root operator carries a spin basis vector of simple-coroot weight `-1`
to its simple reflection with coefficient exactly `1`. -/
theorem typeDSpinRep_serreE_exteriorBasis (i : Fin n) (s : Finset (Fin n))
    (hs : typeDSpinWeight s i = -1) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra s) = b.ExteriorAlgebra (typeDSpinReflection i s) := by
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
    rw [P.typeDSpinRep_serreE_eq_spinAction b hn, hrefl]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_left hi, map_mul, Module.End.mul_apply,
      TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract, P.pairingEquiv_dualVector]
    rw [TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis_of_not_mem_of_mem
      b i q s hmem.1 hmem.2, chainRaisingShuffleSign i s hi hmem.1 hmem.2, one_smul]
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
    rw [P.typeDSpinRep_serreE_eq_spinAction b hn, hrefl]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_right hi, map_mul, Module.End.mul_apply,
      TauCeti.spinAction_ι_wedge]
    -- Unfolding the Fock action exposes the two exterior multiplications at the fork node.
    change ExteriorAlgebra.ι ℚ (b p) *
      (ExteriorAlgebra.ι ℚ (b q) * b.ExteriorAlgebra s) = _
    simp only [TauCeti.ExteriorAlgebra.ι_mul_basis, hmem.2, ite_false, hmem.1,
      Finset.mem_insert, hpq, false_or, ite_false, mul_smul_comm, smul_smul]
    have hsign : TauCeti.ExteriorAlgebra.basisEraseSign q (insert q s) *
        TauCeti.ExteriorAlgebra.basisEraseSign p (insert p (insert q s)) = 1 := by
      simpa [p, q] using forkRaisingShuffleSign (hn := hn) s hmem.1
    rw [hsign, one_smul]

/-- A negative simple-root operator carries a spin basis vector of simple-coroot weight `1`
to its simple reflection with coefficient exactly `1`. -/
theorem typeDSpinRep_serreF_exteriorBasis (i : Fin n) (s : Finset (Fin n))
    (hs : typeDSpinWeight s i = 1) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra s) = b.ExteriorAlgebra (typeDSpinReflection i s) := by
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
    rw [P.typeDSpinRep_serreF_eq_spinAction b hn, hrefl]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_left hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector]
    rw [TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis_of_not_mem_of_mem
      b q i s hmem.2 hmem.1, chainLoweringShuffleSign i s hi, one_smul]
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
    rw [P.typeDSpinRep_serreF_eq_spinAction b hn, hrefl]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_right hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_contract, P.pairingEquiv_dualVector]
    -- Unfolding the Fock action exposes the two successive contractions at the fork node.
    change contractLeft (Q := (0 : QuadraticForm ℚ P.W)) (b.coord q)
      (contractLeft (Q := (0 : QuadraticForm ℚ P.W)) (b.coord p)
        (b.ExteriorAlgebra s)) = _
    simp only [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, hmem.1, ite_true,
      Units.smul_def, map_zsmul]
    rw [ite_eq_left (Finset.mem_erase.mpr ⟨Ne.symm hpq, hmem.2⟩), smul_smul]
    have hsign := forkLoweringShuffleSign (hn := hn) s
    rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign p s) with hp' | hp' <;>
      rcases Int.units_eq_one_or
        (TauCeti.ExteriorAlgebra.basisEraseSign q (s.erase p)) with hq' | hq' <;>
      simp [p, q, hp', hq'] at hsign ⊢

/-- A positive simple-root operator kills a spin basis vector unless its simple-coroot weight
is `-1`. -/
theorem typeDSpinRep_serreE_exteriorBasis_eq_zero (i : Fin n) (s : Finset (Fin n))
    (hs : typeDSpinWeight s i ≠ -1) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra s) = 0 := by
  classical
  by_cases hi : (i : ℕ) + 1 < n
  · let q : Fin n := ⟨(i : ℕ) + 1, hi⟩
    have hnot : i ∈ s ∨ q ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      by_cases his : i ∈ s <;> by_cases hqs : q ∈ s <;> simp_all [q]
    rw [P.typeDSpinRep_serreE_eq_spinAction b hn]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_left hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector]
    -- Unfolding the Fock action exposes creation after coordinate contraction at a chain node.
    change ExteriorAlgebra.ι ℚ (b i) *
      contractLeft (Q := (0 : QuadraticForm ℚ P.W)) (b.coord q) (b.ExteriorAlgebra s) = 0
    have hiq : i ≠ q := by
      intro h
      have := congrArg Fin.val h
      simp [q] at this
    rcases hnot with his | hqs
    · by_cases hqs : q ∈ s
      · rw [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left hqs,
          mul_smul_comm]
        simp [TauCeti.ExteriorAlgebra.ι_mul_basis, his, hiq]
      · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, hqs]
    · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, hqs]
  · let p : Fin n := ⟨n - 2, by omega⟩
    let q : Fin n := ⟨n - 1, by omega⟩
    have hiq : i = q := Fin.ext (by have := i.isLt; dsimp [q]; omega)
    have hip : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) = p :=
      Fin.ext (by have := i.isLt; dsimp [p]; omega)
    have hnot : p ∈ s ∨ q ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi, hip, hiq] at hs
      by_cases hp : p ∈ s <;> by_cases hq : q ∈ s <;> simp_all
    rw [P.typeDSpinRep_serreE_eq_spinAction b hn]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_right hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge]
    -- Unfolding the Fock action exposes the two exterior multiplications at the fork node.
    change ExteriorAlgebra.ι ℚ (b p) *
      (ExteriorAlgebra.ι ℚ (b q) * b.ExteriorAlgebra s) = 0
    rcases hnot with hp | hq
    · by_cases hq : q ∈ s
      · simp [TauCeti.ExteriorAlgebra.ι_mul_basis, hq]
      · simp [TauCeti.ExteriorAlgebra.ι_mul_basis, hq, hp, mul_smul_comm]
    · simp [TauCeti.ExteriorAlgebra.ι_mul_basis, hq]

/-- A negative simple-root operator kills a spin basis vector unless its simple-coroot weight
is `1`. -/
theorem typeDSpinRep_serreF_exteriorBasis_eq_zero (i : Fin n) (s : Finset (Fin n))
    (hs : typeDSpinWeight s i ≠ 1) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra s) = 0 := by
  classical
  by_cases hi : (i : ℕ) + 1 < n
  · let q : Fin n := ⟨(i : ℕ) + 1, hi⟩
    have hnot : i ∉ s ∨ q ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      by_cases his : i ∈ s <;> by_cases hqs : q ∈ s <;> simp_all [q]
    rw [P.typeDSpinRep_serreF_eq_spinAction b hn]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_left hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector]
    -- Unfolding the Fock action exposes creation after coordinate contraction at a chain node.
    change ExteriorAlgebra.ι ℚ (b q) *
      contractLeft (Q := (0 : QuadraticForm ℚ P.W)) (b.coord i) (b.ExteriorAlgebra s) = 0
    have hqi : q ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp [q] at this
    rcases hnot with his | hqs
    · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, his]
    · by_cases his : i ∈ s
      · rw [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left his,
          mul_smul_comm]
        simp [TauCeti.ExteriorAlgebra.ι_mul_basis, hqs, hqi]
      · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, his]
  · let p : Fin n := ⟨n - 2, by omega⟩
    let q : Fin n := ⟨n - 1, by omega⟩
    have hiq : i = q := Fin.ext (by have := i.isLt; dsimp [q]; omega)
    have hip : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) = p :=
      Fin.ext (by have := i.isLt; dsimp [p]; omega)
    have hnot : p ∉ s ∨ q ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi, hip, hiq] at hs
      by_cases hp : p ∈ s <;> by_cases hq : q ∈ s <;> simp_all
    rw [P.typeDSpinRep_serreF_eq_spinAction b hn]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_right hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_contract, P.pairingEquiv_dualVector]
    rcases hnot with hp | hq
    · simp [p, hp]
    · by_cases hp : p ∈ s <;> simp [p, q, hp, hq]

end TauCeti.SpinPolarizationData
