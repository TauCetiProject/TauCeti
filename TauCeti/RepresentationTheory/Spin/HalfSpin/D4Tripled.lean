/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Basic
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Rational
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.D4SpinIndex
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootBasis
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The exterior half-spin basis in the tripled type-D4 representation

The exterior basis of the split spin representation is indexed by subsets of four polarization
coordinates. The last sixteen coordinates of the tripled type-`D₄` minuscule table carry the
same weights. This file compares the two bases with all signs fixed.

At a chain node, a root operator contracts one coordinate and creates the adjacent one. At the
fork node it creates or contracts the adjacent final pair. In both cases the two exterior shuffle
signs are equal, hence their product is `1`. Thus the standard exterior basis already agrees with
the unsigned Chevalley basis of the tripled table; no diagonal sign correction is required.

## Main declarations

* `SpinPolarizationData.typeDSpinRep_serreE_exteriorBasis_four` and
  `typeDSpinRep_serreF_exteriorBasis_four`: exact positive and negative simple-root actions on the
  exterior basis in type `D₄`.
* `SpinPolarizationData.d4HalfSpinEquiv`: the exterior spinor module in four polarization
  coordinates, reindexed by the two half-spin blocks of the tripled table.
* `SpinPolarizationData.d4HalfSpinEquiv_exteriorBasis`: the equivalence sends each exterior basis
  vector to the standard coordinate at its landed tripled-table index.
* `SpinPolarizationData.d4HalfSpinEquiv_serreE` and
  `SpinPolarizationData.d4HalfSpinEquiv_serreF`: the resulting intertwining equations on the full
  exterior spinor module.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

open scoped Matrix

namespace TauCeti.SpinPolarizationData

open CliffordAlgebra
open TauCeti.DynkinType

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) (b : Module.Basis (Fin 4) ℚ P.W)

private theorem negOnePow_mul_self (m : ℕ) :
    ((-1 : ℤˣ) ^ m) * ((-1 : ℤˣ) ^ m) = 1 := by
  rw [← pow_two, ← pow_mul]
  simp

private theorem chainRaisingShuffleSign (i : Fin 4) (s : Finset (Fin 4))
    (hi : (i : ℕ) + 1 < 4) (his : i ∉ s)
    (hjs : (⟨(i : ℕ) + 1, hi⟩ : Fin 4) ∈ s) :
    TauCeti.ExteriorAlgebra.basisEraseSign ⟨(i : ℕ) + 1, hi⟩ s *
        TauCeti.ExteriorAlgebra.basisEraseSign i
          (insert i (s.erase ⟨(i : ℕ) + 1, hi⟩)) = 1 := by
  let j : Fin 4 := ⟨(i : ℕ) + 1, hi⟩
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt j s hjs,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt i
      (insert i (s.erase j)) (Finset.mem_insert_self i _)]
  have hfilter : s.filter (fun x ↦ x < j) =
      (insert i (s.erase j)).filter (fun x ↦ x < i) := by
    fin_cases i <;> norm_num at hi
    all_goals ext x; fin_cases x <;> simp_all [j]
  rw [hfilter]
  exact negOnePow_mul_self _

private theorem chainLoweringShuffleSign (i : Fin 4) (s : Finset (Fin 4))
    (hi : (i : ℕ) + 1 < 4) (his : i ∈ s)
    (hjs : (⟨(i : ℕ) + 1, hi⟩ : Fin 4) ∉ s) :
    TauCeti.ExteriorAlgebra.basisEraseSign i s *
        TauCeti.ExteriorAlgebra.basisEraseSign ⟨(i : ℕ) + 1, hi⟩
          (insert ⟨(i : ℕ) + 1, hi⟩ (s.erase i)) = 1 := by
  let j : Fin 4 := ⟨(i : ℕ) + 1, hi⟩
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt i s his,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt j
      (insert j (s.erase i)) (Finset.mem_insert_self j _)]
  have hfilter : s.filter (fun x ↦ x < i) =
      (insert j (s.erase i)).filter (fun x ↦ x < j) := by
    fin_cases i <;> norm_num at hi
    all_goals ext x; fin_cases x <;> simp_all [j]
  rw [hfilter]
  exact negOnePow_mul_self _

private theorem forkRaisingShuffleSign (s : Finset (Fin 4))
    (h2 : (2 : Fin 4) ∉ s) (h3 : (3 : Fin 4) ∉ s) :
    TauCeti.ExteriorAlgebra.basisEraseSign 3 (insert 3 s) *
        TauCeti.ExteriorAlgebra.basisEraseSign 2 (insert 2 (insert 3 s)) = 1 := by
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt 3
      (insert 3 s) (Finset.mem_insert_self 3 _),
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt 2
      (insert 2 (insert 3 s)) (Finset.mem_insert_self 2 _)]
  have hfilter : (insert 3 s).filter (fun x ↦ x < (3 : Fin 4)) =
      (insert 2 (insert 3 s)).filter (fun x ↦ x < (2 : Fin 4)) := by
    ext x
    fin_cases x <;> simp_all
  rw [hfilter]
  exact negOnePow_mul_self _

private theorem forkLoweringShuffleSign (s : Finset (Fin 4))
    (h2 : (2 : Fin 4) ∈ s) (h3 : (3 : Fin 4) ∈ s) :
    TauCeti.ExteriorAlgebra.basisEraseSign 2 s *
        TauCeti.ExteriorAlgebra.basisEraseSign 3 (s.erase 2) = 1 := by
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt 2 s h2,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt 3 (s.erase 2)
      (Finset.mem_erase.mpr ⟨by decide, h3⟩)]
  have hfilter : s.filter (fun x ↦ x < (2 : Fin 4)) =
      (s.erase 2).filter (fun x ↦ x < (3 : Fin 4)) := by
    ext x
    fin_cases x <;> simp_all
  rw [hfilter]
  exact negOnePow_mul_self _

/-- In type `D₄`, a positive simple-root generator sends a basis vector of weight `-1` to
its reflected basis vector with coefficient exactly `1`. -/
theorem typeDSpinRep_serreE_exteriorBasis_four (i : Fin 4) (s : Finset (Fin 4))
    (hs : typeDSpinWeight s i = -1) :
    P.typeDSpinRep b (by omega)
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D 4) i))
        (b.ExteriorAlgebra s) = b.ExteriorAlgebra (typeDSpinReflection i s) := by
  classical
  by_cases hi : (i : ℕ) + 1 < 4
  · let j : Fin 4 := ⟨(i : ℕ) + 1, hi⟩
    have hmem : i ∉ s ∧ j ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      split_ifs at hs <;> simp_all [j]
    have hrefl : typeDSpinReflection i s = insert i (s.erase j) := by
      ext x
      rw [mem_typeDSpinReflection_of_add_one_lt hi]
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases hxi : x = i <;> by_cases hxj : x = j <;>
        simp_all [Equiv.swap_apply_def, j]
    rw [P.typeDSpinRep_serreE_eq_spinAction b (by omega), hrefl]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_left hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector]
    rw [TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis_of_not_mem_of_mem
      b i j s hmem.1 hmem.2, chainRaisingShuffleSign i s hi hmem.1 hmem.2, one_smul]
  · have hi3 : i = 3 := Fin.ext (by have := i.isLt; omega)
    subst i
    have hmem : (2 : Fin 4) ∉ s ∧ (3 : Fin 4) ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi] at hs
      split_ifs at hs <;> simp_all
    have hrefl : typeDSpinReflection (3 : Fin 4) s = insert 2 (insert 3 s) := by
      ext x
      rw [mem_typeDSpinReflection_of_not_add_one_lt hi]
      fin_cases x <;> simp_all [Equiv.swap_apply_def]
    rw [P.typeDSpinRep_serreE_eq_spinAction b (by omega), hrefl]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_right hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge]
    simp [TauCeti.ExteriorAlgebra.ι_mul_basis, hmem,
      forkRaisingShuffleSign s hmem.1 hmem.2, mul_smul_comm, smul_smul]

/-- In type `D₄`, a negative simple-root generator sends a basis vector of weight `1` to
its reflected basis vector with coefficient exactly `1`. -/
theorem typeDSpinRep_serreF_exteriorBasis_four (i : Fin 4) (s : Finset (Fin 4))
    (hs : typeDSpinWeight s i = 1) :
    P.typeDSpinRep b (by omega)
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D 4) i))
        (b.ExteriorAlgebra s) = b.ExteriorAlgebra (typeDSpinReflection i s) := by
  classical
  by_cases hi : (i : ℕ) + 1 < 4
  · let j : Fin 4 := ⟨(i : ℕ) + 1, hi⟩
    have hmem : i ∈ s ∧ j ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      split_ifs at hs <;> simp_all [j]
    have hrefl : typeDSpinReflection i s = insert j (s.erase i) := by
      ext x
      rw [mem_typeDSpinReflection_of_add_one_lt hi]
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases hxi : x = i <;> by_cases hxj : x = j <;>
        simp_all [Equiv.swap_apply_def, j]
    rw [P.typeDSpinRep_serreF_eq_spinAction b (by omega), hrefl]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_left hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector]
    rw [TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis_of_not_mem_of_mem
      b j i s hmem.2 hmem.1, chainLoweringShuffleSign i s hi hmem.1 hmem.2, one_smul]
  · have hi3 : i = 3 := Fin.ext (by have := i.isLt; omega)
    subst i
    have hmem : (2 : Fin 4) ∈ s ∧ (3 : Fin 4) ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi] at hs
      split_ifs at hs <;> simp_all
    have hrefl : typeDSpinReflection (3 : Fin 4) s = (s.erase 2).erase 3 := by
      ext x
      rw [mem_typeDSpinReflection_of_not_add_one_lt hi]
      fin_cases x <;> simp_all [Equiv.swap_apply_def]
    rw [P.typeDSpinRep_serreF_eq_spinAction b (by omega), hrefl]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_right hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_contract, P.pairingEquiv_dualVector]
    norm_num
    simp only [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, hmem.1, ite_true,
      Units.smul_def, map_zsmul]
    rw [ite_eq_left (Finset.mem_erase.mpr ⟨by decide, hmem.2⟩), smul_smul]
    have hsign := forkLoweringShuffleSign s hmem.1 hmem.2
    rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign 2 s) with h2 | h2 <;>
      rcases Int.units_eq_one_or
        (TauCeti.ExteriorAlgebra.basisEraseSign 3 (s.erase 2)) with h3 | h3 <;>
      simp [h2, h3] at hsign ⊢

/-- In type `D₄`, a positive simple-root generator kills every exterior-basis vector whose
simple-coroot weight is not `-1`. -/
theorem typeDSpinRep_serreE_exteriorBasis_four_eq_zero (i : Fin 4)
    (s : Finset (Fin 4)) (hs : typeDSpinWeight s i ≠ -1) :
    P.typeDSpinRep b (by omega)
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D 4) i))
        (b.ExteriorAlgebra s) = 0 := by
  classical
  by_cases hi : (i : ℕ) + 1 < 4
  · let j : Fin 4 := ⟨(i : ℕ) + 1, hi⟩
    have hnot : i ∈ s ∨ j ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      by_cases his : i ∈ s <;> by_cases hjs : j ∈ s <;> simp_all [j]
    rw [P.typeDSpinRep_serreE_eq_spinAction b (by omega)]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_left hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector]
    change ExteriorAlgebra.ι ℚ (b i) *
      contractLeft (Q := (0 : QuadraticForm ℚ P.W)) (b.coord j) (b.ExteriorAlgebra s) = 0
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp [j] at this
    rcases hnot with his | hjs
    · by_cases hjs : j ∈ s
      · rw [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left hjs,
          mul_smul_comm]
        simp [TauCeti.ExteriorAlgebra.ι_mul_basis, his, hij]
      · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, hjs]
    · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, hjs]
  · have hi3 : i = 3 := Fin.ext (by have := i.isLt; omega)
    subst i
    have hnot : (2 : Fin 4) ∈ s ∨ (3 : Fin 4) ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi] at hs
      by_cases h2 : (2 : Fin 4) ∈ s <;> by_cases h3 : (3 : Fin 4) ∈ s <;> simp_all
    rw [P.typeDSpinRep_serreE_eq_spinAction b (by omega)]
    simp only [P.typeDSimpleRootBivector_def b, dite_eq_right hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge]
    norm_num
    rcases hnot with h2 | h3
    · by_cases h3 : (3 : Fin 4) ∈ s
      · simp [h3]
      · intro _
        rw [mul_smul_comm]
        simp [TauCeti.ExteriorAlgebra.ι_mul_basis, h2]
    · simp [h3]

/-- In type `D₄`, a negative simple-root generator kills every exterior-basis vector whose
simple-coroot weight is not `1`. -/
theorem typeDSpinRep_serreF_exteriorBasis_four_eq_zero (i : Fin 4)
    (s : Finset (Fin 4)) (hs : typeDSpinWeight s i ≠ 1) :
    P.typeDSpinRep b (by omega)
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D 4) i))
        (b.ExteriorAlgebra s) = 0 := by
  classical
  by_cases hi : (i : ℕ) + 1 < 4
  · let j : Fin 4 := ⟨(i : ℕ) + 1, hi⟩
    have hnot : i ∉ s ∨ j ∈ s := by
      rw [typeDSpinWeight_apply, dite_eq_left hi] at hs
      by_cases his : i ∈ s <;> by_cases hjs : j ∈ s <;> simp_all [j]
    rw [P.typeDSpinRep_serreF_eq_spinAction b (by omega)]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_left hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_wedge, TauCeti.spinAction_ι_contract,
      P.pairingEquiv_dualVector]
    change ExteriorAlgebra.ι ℚ (b j) *
      contractLeft (Q := (0 : QuadraticForm ℚ P.W)) (b.coord i) (b.ExteriorAlgebra s) = 0
    have hij : j ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp [j] at this
    rcases hnot with his | hjs
    · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, his]
    · by_cases his : i ∈ s
      · rw [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_left his,
          mul_smul_comm]
        simp [TauCeti.ExteriorAlgebra.ι_mul_basis, hjs, hij]
      · simp [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, his]
  · have hi3 : i = 3 := Fin.ext (by have := i.isLt; omega)
    subst i
    have hnot : (2 : Fin 4) ∉ s ∨ (3 : Fin 4) ∉ s := by
      rw [typeDSpinWeight_apply, dite_eq_right hi] at hs
      by_cases h2 : (2 : Fin 4) ∈ s <;> by_cases h3 : (3 : Fin 4) ∈ s <;> simp_all
    rw [P.typeDSpinRep_serreF_eq_spinAction b (by omega)]
    simp only [P.typeDSimpleNegativeRootBivector_def b, dite_eq_right hi, map_mul,
      Module.End.mul_apply, TauCeti.spinAction_ι_contract, P.pairingEquiv_dualVector]
    norm_num
    rcases hnot with h2 | h3
    · simp [h2]
    · by_cases h2 : (2 : Fin 4) ∈ s <;>
        simp [h2, h3]

/-- Exterior spinors in four polarization coordinates, written in the coordinates of the two
half-spin blocks of the tripled type-`D₄` weight table. -/
noncomputable def d4HalfSpinEquiv :
    ExteriorAlgebra ℚ P.W ≃ₗ[ℚ]
      ({a : Fin 24 // d4TripledSummand a ≠ 0} → ℚ) :=
  b.ExteriorAlgebra.equivFun.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ ↦ ℚ) d4SpinIndexEquiv)

/-- The D4 half-spin coordinate equivalence sends an exterior-basis vector to the standard
coordinate carrying the same spin weight. -/
@[simp]
theorem d4HalfSpinEquiv_exteriorBasis (s : Finset (Fin 4)) :
    P.d4HalfSpinEquiv b (b.ExteriorAlgebra s) = Pi.single (d4SpinIndexEquiv s) 1 := by
  classical
  ext a
  simp [d4HalfSpinEquiv, LinearEquiv.piCongrLeft'_apply, Pi.single_apply,
    Finsupp.single_apply, Equiv.eq_symm_apply, eq_comm]

/-- On every active weight line, the exterior positive root action agrees with the restriction
of the tripled rational raising matrix to its two half-spin blocks. -/
private theorem d4HalfSpinEquiv_serreE_exteriorBasis (i : Fin 4) (s : Finset (Fin 4))
    (hs : typeDSpinWeight s i = -1) :
    P.d4HalfSpinEquiv b
        (P.typeDSpinRep b (by omega)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D 4) i))
          (b.ExteriorAlgebra s)) =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4HalfSpinEquiv b (b.ExteriorAlgebra s) := by
  rw [P.typeDSpinRep_serreE_exteriorBasis_four b i s hs,
    P.d4HalfSpinEquiv_exteriorBasis b, P.d4HalfSpinEquiv_exteriorBasis b,
    Matrix.mulVec_single_one]
  ext a
  change (Pi.single (d4SpinIndexEquiv (typeDSpinReflection i s)) (1 : ℚ) :
      {a : Fin 24 // d4TripledSummand a ≠ 0} → ℚ) a =
    D4Tripled.weightTable.raisingMatrixQ i (a : Fin 24) (d4SpinIndexEquiv s : Fin 24)
  rw [TauCeti.MinusculeWeightTable.raisingMatrixQ_apply]
  simp only [D4Tripled.weightTable_weight, coe_d4SpinIndexEquiv,
    d4TripledWeight_d4SpinIndex, hs, true_and, Pi.single_apply]
  have hindex : (a : Fin 24) = d4TripledReflection i (d4SpinIndex s) ↔
      a = d4TripledHalfSpinReflection i (d4SpinIndexEquiv s) := by
    constructor
    · intro h
      apply Subtype.ext
      simpa using h
    · intro h
      simp [h]
  rw [D4Tripled.weightTable_reflection, d4SpinIndexEquiv_typeDSpinReflection]
  exact if_congr hindex.symm rfl rfl

/-- On every active weight line, the exterior negative root action agrees with the restriction
of the tripled rational lowering matrix to its two half-spin blocks. -/
private theorem d4HalfSpinEquiv_serreF_exteriorBasis (i : Fin 4) (s : Finset (Fin 4))
    (hs : typeDSpinWeight s i = 1) :
    P.d4HalfSpinEquiv b
        (P.typeDSpinRep b (by omega)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D 4) i))
          (b.ExteriorAlgebra s)) =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4HalfSpinEquiv b (b.ExteriorAlgebra s) := by
  rw [P.typeDSpinRep_serreF_exteriorBasis_four b i s hs,
    P.d4HalfSpinEquiv_exteriorBasis b, P.d4HalfSpinEquiv_exteriorBasis b,
    Matrix.mulVec_single_one]
  ext a
  change (Pi.single (d4SpinIndexEquiv (typeDSpinReflection i s)) (1 : ℚ) :
      {a : Fin 24 // d4TripledSummand a ≠ 0} → ℚ) a =
    D4Tripled.weightTable.loweringMatrixQ i (a : Fin 24) (d4SpinIndexEquiv s : Fin 24)
  rw [TauCeti.MinusculeWeightTable.loweringMatrixQ_apply]
  simp only [D4Tripled.weightTable_weight, coe_d4SpinIndexEquiv,
    d4TripledWeight_d4SpinIndex, hs, true_and, Pi.single_apply]
  have hindex : (a : Fin 24) = d4TripledReflection i (d4SpinIndex s) ↔
      a = d4TripledHalfSpinReflection i (d4SpinIndexEquiv s) := by
    constructor
    · intro h
      apply Subtype.ext
      simpa using h
    · intro h
      simp [h]
  rw [D4Tripled.weightTable_reflection, d4SpinIndexEquiv_typeDSpinReflection]
  exact if_congr hindex.symm rfl rfl

/-- The exterior positive simple-root action agrees with the restricted tripled raising matrix
on every exterior-basis vector. -/
private theorem d4HalfSpinEquiv_serreE_exteriorBasis_all (i : Fin 4) (s : Finset (Fin 4)) :
    P.d4HalfSpinEquiv b
        (P.typeDSpinRep b (by omega)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D 4) i))
          (b.ExteriorAlgebra s)) =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4HalfSpinEquiv b (b.ExteriorAlgebra s) := by
  by_cases hs : typeDSpinWeight s i = -1
  · exact P.d4HalfSpinEquiv_serreE_exteriorBasis b i s hs
  · rw [P.typeDSpinRep_serreE_exteriorBasis_four_eq_zero b i s hs, map_zero,
      P.d4HalfSpinEquiv_exteriorBasis b, Matrix.mulVec_single_one]
    ext a
    change 0 = D4Tripled.weightTable.raisingMatrixQ i (a : Fin 24)
      (d4SpinIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.raisingMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, false_and, ↓reduceIte]

/-- The exterior negative simple-root action agrees with the restricted tripled lowering matrix
on every exterior-basis vector. -/
private theorem d4HalfSpinEquiv_serreF_exteriorBasis_all (i : Fin 4) (s : Finset (Fin 4)) :
    P.d4HalfSpinEquiv b
        (P.typeDSpinRep b (by omega)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D 4) i))
          (b.ExteriorAlgebra s)) =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4HalfSpinEquiv b (b.ExteriorAlgebra s) := by
  by_cases hs : typeDSpinWeight s i = 1
  · exact P.d4HalfSpinEquiv_serreF_exteriorBasis b i s hs
  · rw [P.typeDSpinRep_serreF_exteriorBasis_four_eq_zero b i s hs, map_zero,
      P.d4HalfSpinEquiv_exteriorBasis b, Matrix.mulVec_single_one]
    ext a
    change 0 = D4Tripled.weightTable.loweringMatrixQ i (a : Fin 24)
      (d4SpinIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.loweringMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, false_and, ↓reduceIte]

private theorem d4HalfSpinEquiv_intertwines (f : Module.End ℚ (ExteriorAlgebra ℚ P.W))
    (M : Matrix {a : Fin 24 // d4TripledSummand a ≠ 0}
      {a : Fin 24 // d4TripledSummand a ≠ 0} ℚ)
    (hbasis : ∀ s, P.d4HalfSpinEquiv b (f (b.ExteriorAlgebra s)) =
      M *ᵥ P.d4HalfSpinEquiv b (b.ExteriorAlgebra s))
    (x : ExteriorAlgebra ℚ P.W) :
    P.d4HalfSpinEquiv b (f x) = M *ᵥ P.d4HalfSpinEquiv b x := by
  have hmap :
      (P.d4HalfSpinEquiv b).toLinearMap.comp f =
        (Matrix.mulVecLin M).comp (P.d4HalfSpinEquiv b).toLinearMap := by
    apply b.ExteriorAlgebra.ext
    intro s
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Matrix.mulVecLin_apply] using hbasis s
  exact LinearMap.congr_fun hmap x

/-- The half-spin coordinate equivalence intertwines each positive simple-root operator with the
corresponding restricted tripled raising matrix. -/
theorem d4HalfSpinEquiv_serreE (i : Fin 4) (x : ExteriorAlgebra ℚ P.W) :
    P.d4HalfSpinEquiv b
        (P.typeDSpinRep b (by omega)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreE ℚ (CartanMatrix.D 4) i)) x) =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4HalfSpinEquiv b x := by
  apply P.d4HalfSpinEquiv_intertwines b
  exact P.d4HalfSpinEquiv_serreE_exteriorBasis_all b i

/-- The half-spin coordinate equivalence intertwines each negative simple-root operator with the
corresponding restricted tripled lowering matrix. -/
theorem d4HalfSpinEquiv_serreF (i : Fin 4) (x : ExteriorAlgebra ℚ P.W) :
    P.d4HalfSpinEquiv b
        (P.typeDSpinRep b (by omega)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreF ℚ (CartanMatrix.D 4) i)) x) =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4HalfSpinEquiv b x := by
  apply P.d4HalfSpinEquiv_intertwines b
  exact P.d4HalfSpinEquiv_serreF_exteriorBasis_all b i

end TauCeti.SpinPolarizationData
