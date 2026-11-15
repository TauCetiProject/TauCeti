/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Separability between `IsLocalRing.ResidueField` and maximal-ideal quotients

For a local algebra homomorphism `A → B` of local rings, `Algebra.IsSeparable` between
`IsLocalRing.ResidueField`s agrees with that between maximal-ideal quotients, mirroring
`Algebra.isSeparable_residueField_iff`.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

attribute [local instance] Ideal.Quotient.field

/-- For a local algebra map `A → B`, `ResidueField B / ResidueField A` is separable iff
`(B ⧸ maximalIdeal B) / (A ⧸ maximalIdeal A)` is separable. -/
theorem isSeparable_residueField_iff {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) ↔
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) := by
  refine Algebra.IsSeparable.iff_of_equiv_equiv
    (TauCeti.residueFieldAlgEquivOfSurjective
      (ψ := Algebra.ofId A (A ⧸ maximalIdeal A)) Ideal.Quotient.mk_surjective).toRingEquiv
    (TauCeti.residueFieldAlgEquivOfSurjective
      (ψ := Algebra.ofId B (B ⧸ maximalIdeal B)) Ideal.Quotient.mk_surjective).toRingEquiv
    (RingHom.ext fun x ↦ ?_)
  obtain ⟨a, rfl⟩ := residue_surjective x
  have hA := TauCeti.residueFieldAlgEquivOfSurjective_residue
    (ψ := Algebra.ofId A (A ⧸ maximalIdeal A)) Ideal.Quotient.mk_surjective a
  have hB := TauCeti.residueFieldAlgEquivOfSurjective_residue
    (ψ := Algebra.ofId B (B ⧸ maximalIdeal B)) Ideal.Quotient.mk_surjective (algebraMap A B a)
  simp [hA, hB, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_mk_of_liesOver]

end TauCeti.IsLocalRing
