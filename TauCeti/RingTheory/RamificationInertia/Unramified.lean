/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Unramifiedness and separability at one prime

An essentially finite type algebra is unramified at a prime exactly when its ramification index
is one and its residue field extension is separable. The separability condition concerns only
the selected prime, rather than every prime above its contraction. This distinction matters
over imperfect residue fields, where ramification index one alone does not imply unramifiedness.
At a maximal prime over a maximal ideal the residue fields may be replaced by the quotient fields.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Unramifiedness at a prime is ramification index one together with separability of the
selected residue extension. No separability assumption is imposed at other primes. -/
theorem isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField
    (q : Ideal S) [q.IsPrime] [Algebra.EssFiniteType R S] :
    Algebra.IsUnramifiedAt R q ↔ q.ramificationIdx R = 1 ∧
      let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := by
  -- The length reduction follows Mathlib's Ideal.ramificationIdx_eq_one_iff, combined with
  -- the local criterion Algebra.isUnramifiedAt_iff_map_eq.
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have he : q.ramificationIdx R = 1 ↔
      (q.under R).map (algebraMap R (Localization.AtPrime q)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff]
  rw [Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q, he, and_comm]

/-- At a maximal prime `q` over a maximal ideal `p`, unramifiedness is ramification index one
together with separability of the extension of quotient fields `(S ⧸ q) / (R ⧸ p)`. -/
theorem isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_quotient
    (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsMaximal] [q.LiesOver p]
    [Algebra.EssFiniteType R S] :
    Algebra.IsUnramifiedAt R q ↔
      q.ramificationIdx R = 1 ∧ Algebra.IsSeparable (R ⧸ p) (S ⧸ q) := by
  obtain rfl := q.over_def p
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  rw [isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField,
    Algebra.isSeparable_residueField_iff]

/-- At a maximal ideal `q` of `S` lying over the maximal ideal of a local ring `R`, separability
of `(S ⧸ q) / (R ⧸ maximalIdeal R)` is equivalent to separability of
`ResidueField (Localization.AtPrime q) / ResidueField R`. -/
theorem isSeparable_quotient_iff_residueField [IsLocalRing R] (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))] :
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    letI := Ideal.Quotient.field q
    Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ q) ↔
      Algebra.IsSeparable (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) := by
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let := Ideal.Quotient.field q
  let eR : (R ⧸ IsLocalRing.maximalIdeal R) ≃+* IsLocalRing.ResidueField R :=
    (Ideal.quotEquivOfEq (IsLocalRing.ker_residue (R := R)).symm).trans
      (RingHom.quotientKerEquivOfSurjective IsLocalRing.residue_surjective)
  let eS : (S ⧸ q) ≃+* IsLocalRing.ResidueField (Localization.AtPrime q) :=
    RingEquiv.ofBijective (algebraMap (S ⧸ q) q.ResidueField)
      q.bijective_algebraMap_quotient_residueField
  refine Algebra.IsSeparable.iff_of_equiv_equiv eR eS ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
  have heR : eR (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) = IsLocalRing.residue R r := by
    simp [eR]
  have hquot : algebraMap (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ q)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) =
      algebraMap S (S ⧸ q) (algebraMap R S r) := by
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply R _ (S ⧸ q),
      IsScalarTower.algebraMap_apply R S (S ⧸ q)]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  rw [heR, IsLocalRing.ResidueField.algebraMap_residue, hquot, RingEquiv.ofBijective_apply,
    ← IsScalarTower.algebraMap_apply S (S ⧸ q) q.ResidueField,
    IsScalarTower.algebraMap_apply S (Localization.AtPrime q) q.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]

end Ideal
