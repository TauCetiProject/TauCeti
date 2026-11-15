/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.Determinant3
public import TauCeti.NumberTheory.IntegralLattice.Mass
import TauCeti.NumberTheory.IntegralLattice.Binary.NormOne

/-!
# The genus and mass of `A₂`

The genus of `A₂` consists of a single isometry class, by the classification of positive
definite even binary lattices of determinant three. Its proper class number is also one:
the symmetry interchanging the two simple roots reverses orientation. The proper isometry
group has order six, from the units of the quadratic order of discriminant `-3`; the full
isometry group has order twelve. Thus the full and proper masses are `1/12` and `1/6`.
These are direct computations, independent of a mass formula.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §§2 and 7.
* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. R. Soc. Lond. A 419 (1988), §2, equation (1).
-/

public section

namespace TauCeti.IntegralLattice

/-- **The genus of `A₂` is a single class.** -/
theorem genusClasses_typeARootLattice_two :
    (typeARootLattice 2).genusClasses = {(typeARootLattice 2).isometryClass} := by
  ext c
  obtain ⟨M, rfl⟩ := isometryClass_surjective c
  rw [isometryClass_mem_genusClasses_iff, Set.mem_singleton_iff, eq_comm,
    isometryClass_eq_isometryClass_iff]
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.sameGenus⟩
  obtain ⟨e⟩ :=
    (h.isPosDef_iff.mp (isPosDef_typeARootLattice 2)).nonempty_isometry_typeARootLattice_two
      (h.isEven_iff.mp (isEven_typeARootLattice 2))
      (h.finrank_eq.symm.trans (by rw [finrank_carrier, Module.finrank_fin_fun]))
      (h.determinant_eq.symm.trans (by norm_num [determinant_typeARootLattice]))
  exact ⟨e.symm⟩

/-- The class number of `A₂` is one. -/
@[simp]
theorem classNumber_typeARootLattice_two : (typeARootLattice 2).classNumber = 1 := by
  rw [classNumber_def, genusClasses_typeARootLattice_two, Nat.card_unique]

private theorem primPart_two_neg_two_two :
    (⟨2, -2, 2⟩ : BinaryQuadraticForm ℤ).primPart = ⟨1, -1, 1⟩ := by
  ext <;> norm_num [BinaryQuadraticForm.primPart_a, BinaryQuadraticForm.primPart_b,
    BinaryQuadraticForm.primPart_c, BinaryQuadraticForm.content_def]

/-- **`A₂` has an orientation-reversing automorphism**, so its proper isometry subgroup has
index two. -/
theorem index_specialOrthogonalGroup_typeARootLattice_two :
    (specialOrthogonalGroup (typeARootLattice 2)).index = 2 := by
  rw [index_specialOrthogonalGroup_eq_two_iff_reflected (typeASimpleRootBasis 2),
    binaryNormForm_typeASimpleRootBasis_two, primPart_two_neg_two_two]
  refine ⟨ModularGroup.S, ?_⟩
  rw [BinaryQuadraticForm.S_smul]
  ext <;> norm_num

/-- The genus of `A₂` also consists of a single proper class. -/
theorem genusProperClasses_typeARootLattice_two :
    (typeARootLattice 2).genusProperClasses = {(typeARootLattice 2).properIsometryClass} := by
  ext c
  rw [mem_genusProperClasses_iff, genusClasses_typeARootLattice_two]
  exact Set.ext_iff.mp (preimage_toIsometryQuotient_eq_singleton_of_index_eq_two
    index_specialOrthogonalGroup_typeARootLattice_two) c

/-- The proper class number of `A₂` is one. -/
@[simp]
theorem properClassNumber_typeARootLattice_two : (typeARootLattice 2).properClassNumber = 1 := by
  rw [properClassNumber_def, genusProperClasses_typeARootLattice_two, Nat.card_unique]

/-- The primitive binary discriminant of `A₂` is minus three. -/
@[simp]
theorem binaryDiscriminant_typeARootLattice_two :
    (typeARootLattice 2).binaryDiscriminant (Module.finrank_fin_fun ℚ) = -3 := by
  rw [binaryDiscriminant_eq_discrim_primPart _ (typeASimpleRootBasis 2),
    binaryNormForm_typeASimpleRootBasis_two, primPart_two_neg_two_two]
  norm_num [BinaryQuadraticForm.discrim_def, discrim]

/-- The proper isometry group of `A₂` has order six. -/
theorem card_specialOrthogonalGroup_typeARootLattice_two :
    Nat.card (specialOrthogonalGroup (typeARootLattice 2)) = 6 := by
  have hV : Module.finrank ℚ (Fin 2 → ℚ) = 2 := Module.finrank_fin_fun ℚ
  rw [card_specialOrthogonalGroup_of_binaryDiscriminant_neg hV
    (by rw [binaryDiscriminant_typeARootLattice_two]; norm_num), binaryOrder_def,
    QuadraticOrder.card_units_of_neg _ _
      (by rw [binaryDiscriminant_typeARootLattice_two]; norm_num),
    binaryDiscriminant_typeARootLattice_two]
  norm_num

/-- The full isometry group of `A₂` has order twelve. -/
@[simp]
theorem card_isometry_typeARootLattice_two :
    Nat.card (Isometry (typeARootLattice 2) (typeARootLattice 2)) = 12 := by
  rw [← (specialOrthogonalGroup (typeARootLattice 2)).card_mul_index,
    card_specialOrthogonalGroup_typeARootLattice_two,
    index_specialOrthogonalGroup_typeARootLattice_two]

/-- **The mass of the genus of `A₂` is `1/12`.** -/
@[simp]
theorem mass_typeARootLattice_two : (typeARootLattice 2).mass = 12⁻¹ := by
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp
    (isometryClass_out (typeARootLattice 2).isometryClass)
  rw [mass_def, genusClasses_typeARootLattice_two, finsum_mem_singleton,
    e.natCard_isometry_eq, card_isometry_typeARootLattice_two, Nat.cast_ofNat]

/-- **The proper mass of the genus of `A₂` is `1/6`.** -/
@[simp]
theorem properMass_typeARootLattice_two : (typeARootLattice 2).properMass = 6⁻¹ := by
  rw [properMass_eq_two_mul_mass (isPosDef_typeARootLattice 2).finite_genusClasses
    (by rw [finrank_carrier, Module.finrank_fin_fun]; norm_num), mass_typeARootLattice_two]
  norm_num

end TauCeti.IntegralLattice
